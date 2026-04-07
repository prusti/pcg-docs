import OpSem.AbstractByte
import MIR.Ty
import Core.Dsl.DefFn

open AbstractByte in
defFn decodeBool (.plain "decode_bool")
  "Decode a byte sequence as a boolean value. \
   Returns `None` if the sequence is not exactly one byte, \
   or if the byte is not `0` or `1`. \
   Based on the logic defined here: \
   https://github.com/minirust/minirust/blob/master/spec/lang/representation.md#bool"
  (bytes "The bytes to decode." : List AbstractByte)
  : Option Value :=
    match bytes with
    | b :: [] =>
        match b with
        | .init 0 => Some Value.bool ‹false›
        | .init 1 => Some Value.bool ‹true›
        | _ => None
        end
    | _ => None
    end
