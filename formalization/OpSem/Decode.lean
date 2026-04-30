import OpSem.AbstractByte
import OpSem.Value
import Core.Dsl.DefFn
import Core.Dsl.DefRaw

open AbstractByte in
defFn decodeBool (.plain "decode_bool")
  (.seq [.plain "Decode a byte sequence as a boolean value. \
    Returns ", .code "None", .plain " if the sequence is \
    not exactly one byte, or if the byte is not ",
    .code "0", .plain " or ", .code "1", .plain ". Based \
    on the logic defined ",
    .link (.plain "here")
      "https://github.com/minirust/minirust/blob/master/spec/lang/representation.md#bool",
    .plain "."])
  (bytes "The bytes to decode." : List AbstractByte)
  : Option Bool where
  | [.init 0] => Some false
  | [.init 1] => Some true
  | _ => None

open AbstractByte in
defFn data (.plain "data")
  (.seq [.plain "Extract the concrete byte values from a \
    sequence of abstract bytes. Returns ", .code "None",
    .plain " if any byte is uninitialised."])
  (bs "The abstract bytes." : List AbstractByte)
  : Option (List UInt8) where
  | [] => Some []
  | .uninit :: _ => None
  | .init v :: rest =>
      let vs ← data ‹rest› ;
      Some (v :: vs)

defFn decodeLeUnsigned (.plain "decode_le_unsigned")
  (.plain "Decode a little-endian unsigned integer from a \
    list of bytes (least-significant byte first).")
  (bs "The bytes to decode." : List UInt8)
  : Nat where
  | [] => 0
  | b :: rest => b · toNat + (256 * decodeLeUnsigned ‹rest›)

-- The DSL doesn't model raw `def f : T₁ → T₂ → R | pat₁ => …`
-- with structurally-recursive Nat patterns at top level, so
-- `encodeLeUnsigned` / `intValueOfNat` are spelled as
-- `defRaw` blocks: a single source for both the source-side
-- elaboration and the export.
defRaw before =>
/-- Encode a natural number as `numBytes` little-endian
    abstract bytes (least-significant byte first). -/
def encodeLeUnsigned (n : Nat) : Nat → List AbstractByte
  | 0 => []
  | k + 1 =>
    .init (UInt8.ofNat (n % 256)) ::
      encodeLeUnsigned (n / 256) k

defRaw before =>
/-- Build an `IntValue` from a decoded natural number
    based on the target size (in bytes). -/
def intValueOfNat : Nat → Nat → Option IntValue
  | 1, n => some (.u8 (UInt8.ofNat n))
  | 2, n => some (.u16 (UInt16.ofNat n))
  | 4, n => some (.u32 (UInt32.ofNat n))
  | 8, n => some (.u64 (UInt64.ofNat n))
  | _, _ => none

defFn intValueToNat (.plain "int_value_to_nat")
  (.seq [.plain "Extract the nat payload of an ",
    .code "IntValue", .plain "."])
  (iv "The integer value." : IntValue)
  : Nat where
  | .u8 x => x · toNat
  | .u16 x => x · toNat
  | .u32 x => x · toNat
  | .u64 x => x · toNat
  | .usize x => x · toNat

defFn intValueBytes (.plain "int_value_bytes")
  (.plain "Number of bytes in an `IntValue`'s \
    representation.")
  (iv "The integer value." : IntValue)
  : Nat where
  | .u8 _ => 1
  | .u16 _ => 2
  | .u32 _ => 4
  | .u64 _ => 8
  | .usize _ => 8

defFn decodeInt (.plain "decode_int")
  (.seq [.plain "Decode a byte sequence as an ",
    .code "IntValue", .plain ". Endianness is hardcoded \
    to little-endian. Returns ", .code "None",
    .plain " on length mismatch, uninit bytes, signed \
    types, or unsupported sizes."])
  (it "The target integer type." : IntType)
  (bs "The bytes to decode." : List AbstractByte)
  : Option IntValue :=
    if it↦signed ∨ bs·length ≠ sizeBytes ‹it↦size› then None
    else
      let raw ← data ‹bs› ;
      intValueOfNat ‹sizeBytes ‹it↦size›, decodeLeUnsigned ‹raw››

defFn encodeInt (.plain "encode_int")
  (.seq [.plain "Encode an ", .code "IntValue",
    .plain " as a little-endian byte sequence."])
  (iv "The integer value to encode." : IntValue)
  : List AbstractByte :=
    encodeLeUnsigned ‹intValueToNat ‹iv›, intValueBytes ‹iv››

defFn decode (.plain "decode")
  (.seq [.plain "Decode a byte sequence as a runtime \
    value of the given type. Returns ", .code "None",
    .plain " if the type is not decodable or the bytes \
    cannot be decoded."])
  (ty "The type to decode as." : Ty)
  (bs "The bytes to decode." : List AbstractByte)
  : Option Value where
  | .bool ; bs =>
      let b ← decodeBool ‹bs› ;
      Some (Value.bool‹b›)
  | .int it ; bs =>
      let iv ← decodeInt ‹it, bs› ;
      Some (Value.int‹iv›)
  | _ ; _ => None

open AbstractByte in
defFn encodeBool (.plain "encode_bool")
  (.seq [.plain "Encode a boolean value as a byte \
    sequence. Based on the logic defined ",
    .link (.plain "here")
      "https://github.com/minirust/minirust/blob/master/spec/lang/representation.md#bool",
    .plain "."])
  (b "The boolean to encode." : Bool)
  : List AbstractByte where
  | true => [AbstractByte.init‹1›]
  | false => [AbstractByte.init‹0›]

defFn encode (.plain "encode")
  (.plain "Encode a runtime value as a byte sequence. \
   Returns the empty list for values that cannot \
   be encoded (tuples, arrays, pointers, function \
   pointers — pointer round-tripping through abstract \
   bytes is not yet modelled).")
  (v "The value to encode." : Value)
  : List AbstractByte where
  | .bool b => encodeBool ‹b›
  | .int iv => encodeInt ‹iv›
  | .tuple _ => []
  | .array _ => []
  | .ptr _ => []
  | .fnPtr _ => []
