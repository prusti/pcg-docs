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
  (doc! "Extract the concrete byte values from a sequence of abstract bytes. Returns `None` if any \
    byte is uninitialised or carries pointer provenance — pointer-fragment bytes don't have a \
    standalone concrete byte value.")
  (bs "The abstract bytes." : List AbstractByte)
  : Option (List UInt8) where
  | [] => Some []
  | .uninit :: _ => None
  | .ptrFragment _ _ _ :: _ => None
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
  (doc! "Extract the nat payload of an #IntValue.")
  (iv "The integer value." : IntValue)
  : Nat where
  | .u8 x => x · toNat
  | .u16 x => x · toNat
  | .u32 x => x · toNat
  | .u64 x => x · toNat
  | .usize x => x · toNat

defFn intValueBytes (.plain "int_value_bytes")
  (doc! "Number of bytes in an #[IntValue]'s representation.")
  (iv "The integer value." : IntValue)
  : Nat where
  | .u8 _ => 1
  | .u16 _ => 2
  | .u32 _ => 4
  | .u64 _ => 8
  | .usize _ => 8

defFn decodeInt (.plain "decode_int")
  (doc! "Decode a byte sequence as an #IntValue. Endianness is hardcoded to little-endian. Returns \
    `None` on length mismatch, uninit bytes, signed types, or unsupported sizes.")
  (it "The target integer type." : IntType)
  (bs "The bytes to decode." : List AbstractByte)
  : Option IntValue :=
    if it↦signed ∨ bs·length ≠ sizeBytes ‹it↦size› then None
    else
      let raw ← data ‹bs› ;
      intValueOfNat ‹sizeBytes ‹it↦size›, decodeLeUnsigned ‹raw››

defFn encodeInt (.plain "encode_int")
  (doc! "Encode an #IntValue as a little-endian byte sequence.")
  (iv "The integer value to encode." : IntValue)
  : List AbstractByte :=
    encodeLeUnsigned ‹intValueToNat ‹iv›, intValueBytes ‹iv››

defFn decodePtr (.plain "decode_ptr")
  (doc! "Decode an 8-byte pointer encoding back into a #ThinPointer. Each input byte is expected to \
    be a `ptrFragment` carrying the full address and provenance index redundantly (the encoder \
    writes the same pair into all eight fragments), so reading the first fragment is sufficient. \
    Returns `None` if the list is not exactly one `ptrFragment` followed by seven trailing bytes \
    (their contents are not inspected).")
  (bs "The bytes to decode." : List AbstractByte)
  : Option ThinPointer where
  | .ptrFragment provIdx addr _ :: _ =>
      let prov := match provIdx with
        | .some i => Some Provenance⟨AllocId⟨i⟩⟩
        | .none => None
        end ;
      Some ThinPointer⟨Address⟨addr⟩, prov⟩
  | _ => None

defFn decode (.plain "decode")
  (doc! "Decode a byte sequence as a runtime value of the \
    given type. Returns `None` if the type is not decodable \
    or the bytes cannot be decoded. References and `Box` \
    pointers decode through #decodePtr into #Value.ptr.")
  (ty "The type to decode as." : Ty)
  (bs "The bytes to decode." : List AbstractByte)
  : Option Value where
  | .bool ; bs =>
      let b ← decodeBool ‹bs› ;
      Some (Value.bool‹b›)
  | .int it ; bs =>
      let iv ← decodeInt ‹it, bs› ;
      Some (Value.int‹iv›)
  | .ref _ _ _ ; bs =>
      let ptr ← decodePtr ‹bs› ;
      Some (Value.ptr‹ptr›)
  | .box _ ; bs =>
      let ptr ← decodePtr ‹bs› ;
      Some (Value.ptr‹ptr›)
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

defFn encodePtr (.plain "encode_ptr")
  (doc! "Encode a #ThinPointer as eight `ptrFragment` bytes. Each fragment redundantly carries the \
    full address and the optional allocation index of the pointer's provenance plus its position \
    within the pointer (0–7), so #decodePtr can reconstruct the pointer from the head fragment \
    alone.")
  (ptr "The pointer to encode." : ThinPointer)
  : List AbstractByte :=
    let prov := ptr↦provenance ;
    let provIdx := match prov with
      | .some p => Some p↦id↦index
      | .none => None
      end ;
    let addr := ptr↦addr↦addr ;
    [AbstractByte.ptrFragment‹provIdx, addr, 0›,
     AbstractByte.ptrFragment‹provIdx, addr, 1›,
     AbstractByte.ptrFragment‹provIdx, addr, 2›,
     AbstractByte.ptrFragment‹provIdx, addr, 3›,
     AbstractByte.ptrFragment‹provIdx, addr, 4›,
     AbstractByte.ptrFragment‹provIdx, addr, 5›,
     AbstractByte.ptrFragment‹provIdx, addr, 6›,
     AbstractByte.ptrFragment‹provIdx, addr, 7›]

defFn encode (.plain "encode")
  (doc! "Encode a runtime value as a byte sequence. \
   Returns the empty list for tuples, arrays, and function \
   pointers (compound values aren't laid out as flat bytes in \
   this model; function-pointer encoding is not modelled). \
   Pointers go through #encodePtr.")
  (v "The value to encode." : Value)
  : List AbstractByte where
  | .bool b => encodeBool ‹b›
  | .int iv => encodeInt ‹iv›
  | .tuple _ => []
  | .array _ => []
  | .ptr p => encodePtr ‹p›
  | .fnPtr _ => []
