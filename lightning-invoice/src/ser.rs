use core::fmt;
use core::fmt::{Display, Formatter};
use core::{array, iter};

use bech32::{u5, WriteBase32};
use bech32_11::{ByteIterExt, Fe32, Fe32IterExt};
use crate::prelude::*;

use lightning::ln::features::Bolt11InvoiceFeatures;
use lightning::routing::router::RouteHintHop;

use super::{Bolt11Invoice, Sha256, TaggedField, ExpiryTime, MinFinalCltvExpiryDelta, Fallback, PaymentSecret, PayeePubKey, Bolt11InvoiceSignature, PositiveTimestamp,
	PrivateRoute, Description, RawTaggedField, Currency, RawHrp, SiPrefix, constants, SignedRawBolt11Invoice, RawDataPart};


/// Objects that can be encoded to a formatter in bech32.
///
/// Private to this module to avoid polluting the API.
trait Bech32Iterable {
	/// In future we want to replace this Box<dyn Iterator> with an explicit
	/// associated type, to avoid the allocation. But we cannot do this until
	/// Rust 1.65 and GATs since the iterator may contain a reference to self.
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's>;

	fn fmt_bech32(&self, f: &mut Formatter) -> fmt::Result {
		for fe in self.fe_iter() {
			fe.to_char().fmt(f)?;
		}
		Ok(())
	}
}

/// Helper function to encode byte data as a bech32 string, with no checksum or HRP
fn encode_bytes_bech32(bytes: &[u8], f: &mut Formatter) -> fmt::Result {
	for fe in bytes.iter().copied().bytes_to_fes() {
		fe.to_char().fmt(f)?;
	}
	Ok(())
}

struct BeIntFeIter {
	iter: core::iter::Skip<bech32_11::primitives::iter::BytesToFes<core::array::IntoIter<u8, 8>>>,
}

impl BeIntFeIter {
	/// Constructor for an iterator which writes an integer as a variable-length
	/// big-endian bech32 string.
	fn var_len(int: u64) -> Self {
		let bit_len = 64 - int.leading_zeros() as usize; // cast ok as value is in 0..=64.
		let fe_len = (bit_len + 4) / 5;

		BeIntFeIter {
			iter: int.to_be_bytes().into_iter().bytes_to_fes().skip(13 - fe_len),
		}
	}

	/// Constructor for an iterator which writes an integer as a fixed-length
	/// big-endian bech32 string.
	///
	/// Panics if the integer would not fit into the provided length.
	fn fixed_len(int: u64, len: usize) -> Self {
		assert_eq!(int >> (len * 5), 0);
		BeIntFeIter {
			iter: int.to_be_bytes().into_iter().bytes_to_fes().skip(13 - len),
		}
	}
}

impl Iterator for BeIntFeIter {
	type Item = Fe32;

	fn next(&mut self) -> Option<Self::Item> {
		self.iter.next()
	}
	
	fn size_hint(&self) -> (usize, Option<usize>) {
		self.iter.size_hint()
	}
}

impl ExactSizeIterator for BeIntFeIter {
	fn len(&self) -> usize {
		self.iter.len()
	}
}


/// Helper function to minimally encode an integer in big-endian bech32 characters.
fn encode_int_be_base32(int: u64, pad_to_bytes: Option<usize>, f: &mut fmt::Formatter) -> fmt::Result {
	if let Some(pad_to_bytes) = pad_to_bytes {
		for _ in encoded_int_be_base32_size(int)..pad_to_bytes {
			Fe32::Q.to_char().fmt(f)?;
		}
	}
	for fe in int.to_be_bytes().into_iter().bytes_to_fes().skip_while(|fe| *fe == Fe32::Q) {
		fe.to_char().fmt(f)?;
	}
	Ok(())
}

/// The length of the output of `encode_int_be_base32`.
fn encoded_int_be_base32_size(int: u64) -> usize {
	let bit_len = 64 - int.leading_zeros() as usize; // cast ok as value is in 0..=64.
	(bit_len + 4) / 5
}

impl Bech32Iterable for [u8] {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(self.iter().copied().bytes_to_fes())
	}
}

impl<const N: usize> Bech32Iterable for [u8; N] {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new((*self).into_iter().bytes_to_fes())
	}
}


/// Converts a stream of bytes written to it to base32. On finalization the according padding will
/// be applied. That means the results of writing two data blocks with one or two `BytesToBase32`
/// converters will differ.
struct BytesToBase32<'a, W: WriteBase32 + 'a> {
	/// Target for writing the resulting `u5`s resulting from the written bytes
	writer: &'a mut W,
	/// Holds all unwritten bits left over from last round. The bits are stored beginning from
	/// the most significant bit. E.g. if buffer_bits=3, then the byte with bits a, b and c will
	/// look as follows: [a, b, c, 0, 0, 0, 0, 0]
	buffer: u8,
	/// Amount of bits left over from last round, stored in buffer.
	buffer_bits: u8,
}

impl<'a, W: WriteBase32> BytesToBase32<'a, W> {
	/// Create a new bytes-to-base32 converter with `writer` as  a sink for the resulting base32
	/// data.
	pub fn new(writer: &'a mut W) -> BytesToBase32<'a, W> {
		BytesToBase32 {
			writer,
			buffer: 0,
			buffer_bits: 0,
		}
	}

	/// Add more bytes to the current conversion unit
	pub fn append(&mut self, bytes: &[u8]) -> Result<(), W::Err> {
		for b in bytes {
			self.append_u8(*b)?;
		}
		Ok(())
	}

	pub fn append_u8(&mut self, byte: u8) -> Result<(), W::Err> {
		// Write first u5 if we have to write two u5s this round. That only happens if the
		// buffer holds too many bits, so we don't have to combine buffer bits with new bits
		// from this rounds byte.
		if self.buffer_bits >= 5 {
			self.writer.write_u5(
				u5::try_from_u8((self.buffer & 0b11111000) >> 3 ).expect("<32")
			)?;
			self.buffer <<= 5;
			self.buffer_bits -= 5;
		}

		// Combine all bits from buffer with enough bits from this rounds byte so that they fill
		// a u5. Save remaining bits from byte to buffer.
		let from_buffer = self.buffer >> 3;
		let from_byte = byte >> (3 + self.buffer_bits); // buffer_bits <= 4

		self.writer.write_u5(u5::try_from_u8(from_buffer | from_byte).expect("<32"))?;
		self.buffer = byte << (5 - self.buffer_bits);
		self.buffer_bits += 3;

		Ok(())
	}

	pub fn finalize(mut self) ->  Result<(), W::Err> {
		self.inner_finalize()?;
		core::mem::forget(self);
		Ok(())
	}

	fn inner_finalize(&mut self) -> Result<(), W::Err>{
		// There can be at most two u5s left in the buffer after processing all bytes, write them.
		if self.buffer_bits >= 5 {
			self.writer.write_u5(
				u5::try_from_u8((self.buffer & 0b11111000) >> 3).expect("<32")
			)?;
			self.buffer <<= 5;
			self.buffer_bits -= 5;
		}

		if self.buffer_bits != 0 {
			self.writer.write_u5(u5::try_from_u8(self.buffer >> 3).expect("<32"))?;
		}

		Ok(())
	}
}

impl<'a, W: WriteBase32> Drop for BytesToBase32<'a, W> {
	fn drop(&mut self) {
		self.inner_finalize()
			.expect("Unhandled error when finalizing conversion on drop. User finalize to handle.")
	}
}

/// Calculates the base32 encoded size of a byte slice
fn bytes_size_to_base32_size(byte_size: usize) -> usize {
	let bits = byte_size * 8;
	if bits % 5 == 0 {
		// without padding bits
		bits / 5
	} else {
		// with padding bits
		bits / 5 + 1
	}
}

impl Display for Bolt11Invoice {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		self.signed_invoice.fmt(f)
	}
}

impl Display for SignedRawBolt11Invoice {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		let hrp = self.raw_invoice.hrp.to_hrp();

		for ch in self.raw_invoice.data.fe_iter().chain(self.signature.fe_iter()).with_checksum::<bech32_11::Bech32>(&hrp).chars() {
			write!(f, "{}", ch)?;
		}
		Ok(())
	}
}

/// This is not exported to bindings users
impl Display for RawHrp {
       fn fmt(&self, f: &mut Formatter) -> fmt::Result {
               let amount = match self.raw_amount {
                       Some(ref amt) => amt.to_string(),
                       None => String::new(),
               };

               let si_prefix = match self.si_prefix {
                       Some(ref si) => si.to_string(),
                       None => String::new(),
               };

               write!(
                       f,
                       "ln{}{}{}",
                       self.currency,
                       amount,
                       si_prefix
               )
       }
}

impl Display for Currency {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		let currency_code = match *self {
			Currency::Bitcoin => "bc",
			Currency::BitcoinTestnet => "tb",
			Currency::Regtest => "bcrt",
			Currency::Simnet => "sb",
			Currency::Signet => "tbs",
		};
		write!(f, "{}", currency_code)
	}
}

impl Display for SiPrefix {
	fn fmt(&self, f: &mut Formatter) -> fmt::Result {
		write!(f, "{}",
			match *self {
				SiPrefix::Milli => "m",
				SiPrefix::Micro => "u",
				SiPrefix::Nano => "n",
				SiPrefix::Pico => "p",
			}
		)
	}
}

fn encode_int_be_base256<T: Into<u64>>(int: T) -> Vec<u8> {
	let base = 256u64;

	let mut out_vec = Vec::<u8>::new();

	let mut rem_int: u64 = int.into();
	while rem_int != 0 {
		out_vec.push((rem_int % base) as u8);
		rem_int /= base;
	}

	out_vec.reverse();
	out_vec
}

/// Appends the default value of `T` to the front of the `in_vec` till it reaches the length
/// `target_length`. If `in_vec` already is too lang `None` is returned.
fn try_stretch<T>(mut in_vec: Vec<T>, target_len: usize) -> Option<Vec<T>>
	where T: Default + Copy
{
	if in_vec.len() > target_len {
		None
	} else if in_vec.len() == target_len {
		Some(in_vec)
	} else {
		let mut out_vec = Vec::<T>::with_capacity(target_len);
		out_vec.append(&mut vec![T::default(); target_len - in_vec.len()]);
		out_vec.append(&mut in_vec);
		Some(out_vec)
	}
}

impl Bech32Iterable for RawDataPart {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		let ts_iter = self.timestamp.fe_iter();
		let fields_iter = self.tagged_fields.iter().map(RawTaggedField::fe_iter).flatten();
		Box::new(ts_iter.chain(fields_iter))
	}
}

impl RawDataPart {
	pub(super) fn byte_iter<'s>(&'s self) -> impl Iterator<Item = u8> + 's {
		self.fe_iter().fes_to_bytes()
	}
}

impl Bech32Iterable for PositiveTimestamp {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(BeIntFeIter::fixed_len(self.as_unix_timestamp(), 7))
	}
}


impl Bech32Iterable for RawTaggedField {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		// Annoyingly, when we move to explicit types, we will need an
		// explicit enum holding the two iterator variants.
		match *self {
			RawTaggedField::UnknownSemantics(ref content) => {
				Box::new(content.iter().copied().map(|u5| Fe32::try_from(u5.to_u8()).unwrap()))
			},
			RawTaggedField::KnownSemantics(ref tagged_field) => tagged_field.fe_iter(),
		}
	}
}

impl Bech32Iterable for Sha256 {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(self.0[..].fe_iter())
	}
}

impl Bech32Iterable for Description {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(self.0.0.as_bytes().fe_iter())
	}
}

impl Bech32Iterable for PayeePubKey {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(self.serialize().into_iter().bytes_to_fes())
	}
}

impl Bech32Iterable for ExpiryTime {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(BeIntFeIter::var_len(self.as_seconds()))
	}
}

impl Bech32Iterable for MinFinalCltvExpiryDelta {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(BeIntFeIter::var_len(self.0))
	}
}

impl Bech32Iterable for Fallback {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(match *self {
			Fallback::SegWitProgram {version: v, program: ref p} => {
				let v = Fe32::try_from(v.to_num()).expect("valid version");
				core::iter::once(v).chain(p[..].fe_iter())
			}
			Fallback::PubKeyHash(ref hash) => {
				core::iter::once(Fe32::_3).chain(hash[..].fe_iter())
			}
			Fallback::ScriptHash(ref hash) => {
				core::iter::once(Fe32::J).chain(hash[..].fe_iter())
			}
		})
	}
}

// Rust makes me write this type...
type RouteHintHopIter = iter::Chain<iter::Chain<iter::Chain<iter::Chain<array::IntoIter<u8, 33>, array::IntoIter<u8, 8>>, array::IntoIter<u8, 4>>, array::IntoIter<u8, 4>>, array::IntoIter<u8, 2>>;

impl Bech32Iterable for PrivateRoute {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		fn serialize_to_iter(hop: &RouteHintHop) -> RouteHintHopIter {
			let i1 = hop.src_node_id.serialize().into_iter();
			let i2 = u64::to_be_bytes(hop.short_channel_id).into_iter();
			let i3 = u32::to_be_bytes(hop.fees.base_msat).into_iter();
			let i4 = u32::to_be_bytes(hop.fees.proportional_millionths).into_iter();
			let i5 = u16::to_be_bytes(hop.cltv_expiry_delta).into_iter();
			i1.chain(i2).chain(i3).chain(i4).chain(i5)
		}

		Box::new(self.0.0.iter().map(serialize_to_iter).flatten().bytes_to_fes())
	}
}

impl Bech32Iterable for PaymentSecret {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(self.0[..].fe_iter())
	}
}

impl Bech32Iterable for Bolt11InvoiceSignature {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		let (recovery_id, signature) = self.0.serialize_compact();
		Box::new(signature.into_iter().chain(core::iter::once(recovery_id.to_i32() as u8)).bytes_to_fes())
	}
}

impl Bech32Iterable for Bolt11InvoiceFeatures {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		Box::new(self.as_le_bytes().iter().copied().rev().bytes_to_fes())
	}
}

type TaggedFieldIter<I> = core::iter::Chain<core::array::IntoIter<Fe32, 3>, I>;

impl Bech32Iterable for TaggedField {
	fn fe_iter<'s>(&'s self) -> Box<dyn Iterator<Item = Fe32> + 's> {
		/// Writes a tagged field: tag, length and data. `tag` should be in `0..32` otherwise the
		/// function will panic.
		fn write_tagged_field<'s, P>(tag: u8, payload: &'s P) -> TaggedFieldIter<Box<dyn Iterator<Item = Fe32> + 's>>
			where P: Bech32Iterable + ?Sized
		{
			let (one, two) = payload.fe_iter().size_hint();
			assert_eq!(Some(one), two, "sigh FIXME");
			let len = one;
			assert!(len < 1024, "Every tagged field data can be at most 1023 bytes long.");

			[
				Fe32::try_from(tag).expect("invalid tag, not in 0..32"),
				Fe32::try_from((len / 32) as u8).expect("< 32"),
				Fe32::try_from((len % 32) as u8).expect("< 32"),
			].into_iter().chain(payload.fe_iter())
		}

                // ...we will also need a giant enum for this
		Box::new(match *self {
			TaggedField::PaymentHash(ref hash) => {
				write_tagged_field(constants::TAG_PAYMENT_HASH, hash)
			},
			TaggedField::Description(ref description) => {
				write_tagged_field(constants::TAG_DESCRIPTION, description)
			},
			TaggedField::PayeePubKey(ref pub_key) => {
				write_tagged_field(constants::TAG_PAYEE_PUB_KEY, pub_key)
			},
			TaggedField::DescriptionHash(ref hash) => {
				write_tagged_field(constants::TAG_DESCRIPTION_HASH, hash)
			},
			TaggedField::ExpiryTime(ref duration) => {
				write_tagged_field(constants::TAG_EXPIRY_TIME, duration)
			},
			TaggedField::MinFinalCltvExpiryDelta(ref expiry) => {
				write_tagged_field(constants::TAG_MIN_FINAL_CLTV_EXPIRY_DELTA, expiry)
			},
			TaggedField::Fallback(ref fallback_address) => {
				write_tagged_field(constants::TAG_FALLBACK, fallback_address)
			},
			TaggedField::PrivateRoute(ref route_hops) => {
				write_tagged_field(constants::TAG_PRIVATE_ROUTE, route_hops)
			},
			TaggedField::PaymentSecret(ref payment_secret) => {
				write_tagged_field(constants::TAG_PAYMENT_SECRET, payment_secret)
			},
			TaggedField::PaymentMetadata(ref payment_metadata) => {
				write_tagged_field(constants::TAG_PAYMENT_METADATA, &payment_metadata[..])
			},
			TaggedField::Features(ref features) => {
				write_tagged_field(constants::TAG_FEATURES, features)
			},
		})
	}
}

#[cfg(test)]
mod test {
	use bech32::CheckBase32;

	#[test]
	fn test_currency_code() {
		use crate::Currency;

		assert_eq!("bc", Currency::Bitcoin.to_string());
		assert_eq!("tb", Currency::BitcoinTestnet.to_string());
		assert_eq!("bcrt", Currency::Regtest.to_string());
		assert_eq!("sb", Currency::Simnet.to_string());
		assert_eq!("tbs", Currency::Signet.to_string());
	}

	#[test]
	fn test_raw_hrp() {
		use crate::{Currency, RawHrp, SiPrefix};

		let hrp = RawHrp {
			currency: Currency::Bitcoin,
			raw_amount: Some(100),
			si_prefix: Some(SiPrefix::Micro),
		};

		assert_eq!(hrp.to_string(), "lnbc100u");
	}

	#[test]
	fn test_encode_int_be_base32() {
		use crate::ser::encode_int_be_base32;

		let input: u64 = 33764;
		let expected_out = CheckBase32::check_base32(&[1, 0, 31, 4]).unwrap();

		assert_eq!(expected_out, encode_int_be_base32(input));
	}

	#[test]
	fn test_encode_int_be_base256() {
		use crate::ser::encode_int_be_base256;

		let input: u64 = 16842530;
		let expected_out = vec![1, 0, 255, 34];

		assert_eq!(expected_out, encode_int_be_base256(input));
	}
}
