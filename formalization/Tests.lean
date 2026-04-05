import LSpec
import Core.Dsl.DslType

open LSpec DSLType

def dslTypeParseTests : TestSeq :=
  group "DSLType.parse" $
    test "Nat" (parse "Nat" == .prim .nat) $
    test "Option Nat"
      (parse "Option Nat" == .option (.prim .nat)) $
    test "Option (Option UInt8)"
      (parse "Option (Option UInt8)" ==
        .option (.option (.prim .u8))) $
    test "List (Option String)"
      (parse "List (Option String)" ==
        .list (.option (.prim .string))) $
    test "Option (List Bool)"
      (parse "Option (List Bool)" ==
        .option (.list (.prim .bool))) $
    test "UInt64"
      (parse "UInt64" == .prim .u64) $
    test "named type"
      (parse "Place" == .named ⟨"Place"⟩) $
    .done

def main (args : List String) : IO UInt32 :=
  lspecIO (.ofList [("DSLType", [dslTypeParseTests])]) args
