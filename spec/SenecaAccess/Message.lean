/-!
# Messages

A Seneca message is a set of named properties. The access rule asks a
message only one kind of question: *what is the value of this key?* A
message is modelled as exactly the answer to that question, and nothing
else about it is visible to the rule.
-/

namespace SenecaAccess

/--
A Seneca message.

`Key` and `Value` are left open. The rule never looks inside a key, and
the only thing it does with a value is compare it to another value, so any
types will do provided values can be compared for equality.

Only the top-level properties of a message are visible.
-/
structure Message (Key Value : Type) where
  /-- The value of the property named `key`, or `none` when the message
  has no such property. -/
  get : Key → Option Value

namespace Message

variable {Key Value : Type}

/--
The message with the listed properties. This is how a message is written
down in examples and tests.

A key is expected to be listed once. If it is listed again, the first
listing is the one that counts.
-/
def ofList [DecidableEq Key] (properties : List (Key × Value)) : Message Key Value where
  get key := properties.lookup key

/--
`wider.Extends message` says that `wider` has every property of `message`,
with the same value, and may have further properties besides.
-/
def Extends (wider message : Message Key Value) : Prop :=
  ∀ key value, message.get key = some value → wider.get key = some value

end Message

end SenecaAccess
