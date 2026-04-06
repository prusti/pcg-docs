import Core.Dsl.DefStruct

defStruct Address (.raw "a", .cal (.raw "A"))
  "Addresses"
  "A memory address {def}."
  constructor "Address"
where
  | addr "The address value." : Nat
