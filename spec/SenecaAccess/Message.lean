import Std.Data.ExtTreeMap

/-!
# Messages

A Seneca message is a set of named properties. It is modelled as a map
from keys to values, the way a JavaScript object is: each key is a string
and has at most one value.
-/

namespace SenecaAccess

/--
A Seneca message: a map from string keys to values.

A key has at most one value, by construction. Two messages with the same
properties are the same message, however they were written down.

`Value` is left open. The only thing the rule does with a value is compare
it to another value, so any type will do provided its values can be
compared for equality. Only the top-level properties of a message are
visible.

Keys are kept in ascending order, which is the alphabetical order patrun
checks them in. (The two can differ only for characters outside Unicode's
Basic Multilingual Plane.) No answer in this spec depends on that order.
-/
abbrev Message (Value : Type) := Std.ExtTreeMap String Value

namespace Message

variable {Value : Type}

/--
The message with the listed properties. This is how a message is written
down in examples and tests.

If a key is listed more than once, the last listing is the one that
counts, as in a JavaScript object literal.
-/
def ofList (properties : List (String × Value)) : Message Value :=
  Std.ExtTreeMap.ofList properties

/--
`part.Within whole` says that every property of `part` is a property of
`whole`, with the same value. `whole` may have further properties besides.
-/
def Within (part whole : Message Value) : Prop :=
  ∀ (key : String) (value : Value), part[key]? = some value → whole[key]? = some value

/--
Whether one message is within another can be computed: look up each
property of `part` in `whole`, taking the keys in ascending order. All
this needs is a way to tell whether two values are equal.
-/
instance [DecidableEq Value] (part whole : Message Value) : Decidable (part.Within whole) :=
  decidable_of_iff (∀ property ∈ part.toList, whole[property.1]? = some property.2)
    ⟨fun h key value hget =>
       h (key, value) (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hget),
     fun h property hmem =>
       h property.1 property.2 (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem)⟩

variable {part middle whole : Message Value}

/-- Every message is within itself. -/
theorem Within.refl (message : Message Value) : message.Within message :=
  fun _ _ hget => hget

/-- Being within is transitive. -/
theorem Within.trans (hfirst : part.Within middle) (hsecond : middle.Within whole) :
    part.Within whole :=
  fun key value hget => hsecond key value (hfirst key value hget)

/--
Two messages that are each within the other are the same message. A
message is nothing more than its properties.
-/
theorem Within.antisymm (hfirst : part.Within whole) (hsecond : whole.Within part) :
    part = whole := by
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  cases hpart : part[key]? with
  | some value => exact (hfirst key value hpart).symm
  | none =>
    cases hwhole : whole[key]? with
    | none => rfl
    | some value =>
      rw [hsecond key value hwhole] at hpart
      cases hpart

/-- The empty message is within every message. -/
theorem empty_within (whole : Message Value) : Within ∅ whole :=
  fun key value hget => by
    rw [Std.ExtTreeMap.getElem?_empty] at hget
    cases hget

end Message

end SenecaAccess
