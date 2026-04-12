import OpSem.AbstractByte
import MIR.ConstValue
import Core.Dsl.DefFn

open AbstractByte in
defFn decodeBool (.plain "decode_bool")
  "Decode a byte sequence as a boolean value. \
   Returns `None` if the sequence is not exactly one byte, \
   or if the byte is not `0` or `1`. \
   Based on the logic defined here: \
   https://github.com/minirust/minirust/blob/master/spec/lang/representation.md#bool"
  (bytes "The bytes to decode." : List AbstractByte)
  : Option ConstValue where
  | [.init 0] => Some ConstValue.bool ‹false›
  | [.init 1] => Some ConstValue.bool ‹true›
  | _ => None

open AbstractByte in
defFn data (.plain "data")
  "Extract the concrete byte values from a sequence of \
   abstract bytes. Returns `None` if any byte is uninitialised."
  (bs "The abstract bytes." : List AbstractByte)
  : Option (List UInt8) where
  | [] => Some []
  | .uninit :: _ => None
  | .init v :: rest =>
      let vs ← data ‹rest› ;
      Some (v :: vs)

/-- Decode a little-endian unsigned integer from a list of
    bytes (least-significant byte first). -/
def decodeLeUnsigned : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * decodeLeUnsigned rest

/-- Encode a natural number as `numBytes` little-endian
    abstract bytes (least-significant byte first). Higher
    bits are truncated if `n` does not fit. -/
def encodeLeUnsigned (n : Nat) : Nat → List AbstractByte
  | 0 => []
  | k + 1 =>
    .init (UInt8.ofNat (n % 256)) :: encodeLeUnsigned (n / 256) k

/-- Build an `IntValue` from a decoded natural number based
    on the target size (in bytes). -/
def intValueOfNat : Nat → Nat → Option IntValue
  | 1, n => some (.u8 (UInt8.ofNat n))
  | 2, n => some (.u16 (UInt16.ofNat n))
  | 4, n => some (.u32 (UInt32.ofNat n))
  | 8, n => some (.u64 (UInt64.ofNat n))
  | _, _ => none

defFn intValueToNat (.plain "int_value_to_nat")
  "Extract the nat payload of an `IntValue`."
  (iv "The integer value." : IntValue)
  : Nat where
  | .u8 x => x · toNat
  | .u16 x => x · toNat
  | .u32 x => x · toNat
  | .u64 x => x · toNat
  | .usize x => x · toNat

/-- Number of bytes in an `IntValue`'s representation. -/
def intValueBytes : IntValue → Nat
  | .u8 _ => 1
  | .u16 _ => 2
  | .u32 _ => 4
  | .u64 _ => 8
  | .usize _ => 8

defFn decodeInt (.plain "decode_int")
  "Decode a byte sequence as an `IntValue`. Endianness is \
   hardcoded to little-endian. Returns `None` on length \
   mismatch, uninit bytes, signed types, or unsupported sizes."
  (it "The target integer type." : IntType)
  (bs "The bytes to decode." : List AbstractByte)
  : Option IntValue :=
    if it↦signed ∨ bs·length ≠ it↦size·bytes then None
    else
      let raw ← data ‹bs› ;
      intValueOfNat ‹it↦size·bytes, decodeLeUnsigned ‹raw››

defFn encodeInt (.plain "encode_int")
  "Encode an `IntValue` as a little-endian byte sequence."
  (iv "The integer value to encode." : IntValue)
  : List AbstractByte :=
    encodeLeUnsigned ‹intValueToNat ‹iv›, intValueBytes ‹iv››

open AbstractByte in
defFn encodeBool (.plain "encode_bool")
  "Encode a boolean value as a byte sequence. \
   Based on the logic defined here: \
   https://github.com/minirust/minirust/blob/master/spec/lang/representation.md#bool"
  (b "The boolean to encode." : Bool)
  : List AbstractByte where
  | true => [AbstractByte.init‹1›]
  | false => [AbstractByte.init‹0›]
