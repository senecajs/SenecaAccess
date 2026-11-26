import SenecaAccess.Message

/-!
# Patterns

A pattern is what patrun calls a pattern: a set of key/value pairs that a
message must contain. Matching is by subset. A message matches when it has
all of the pattern's pairs, whatever else it has.

Values are literal. A pattern value is met only by an equal message value.
-/

namespace SenecaAccess

/--
A pattern has the same shape as a message. It is a partial message: the
properties a message must have in order to match.

The patrun pattern `{ sys: 'entity', cmd: 'load' }` is the map with those
two properties. Like any map it has at most one value for a key, so a
pattern cannot ask for two different values of the same key.
-/
abbrev Pattern (Value : Type) := Message Value

namespace Pattern

variable {Value : Type}

/--
A message matches a pattern when the pattern is within the message: every
property of the pattern is a property of the message, with the same value.

Properties the pattern does not name are not examined.
-/
def Matches (pattern : Pattern Value) (message : Message Value) : Prop :=
  Message.Within pattern message

/--
Matching can be computed: look up each property of the pattern in the
message, taking the keys in ascending order as patrun does.
-/
instance [DecidableEq Value] (pattern : Pattern Value) (message : Message Value) :
    Decidable (pattern.Matches message) :=
  inferInstanceAs (Decidable (Message.Within pattern message))

variable {pattern general specific : Pattern Value}
variable {message wider other : Message Value}

/-- The empty pattern asks for nothing, so every message matches it. -/
theorem matches_empty (message : Message Value) : Matches ∅ message :=
  Message.empty_within message

/--
Asking for less matches more. If a message matches a pattern, it also
matches every pattern that is within that pattern.
-/
theorem Matches.weaken (h : specific.Matches message) (hless : Message.Within general specific) :
    general.Matches message :=
  Message.Within.trans hless h

/--
Extra properties are ignored. If a message matches a pattern, so does
every message it is within.
-/
theorem Matches.extend (h : pattern.Matches message) (hmore : message.Within wider) :
    pattern.Matches wider :=
  Message.Within.trans h hmore

/--
A pattern looks only at the keys it names. Two messages that agree on
those keys are matched alike, however they differ elsewhere.
-/
theorem matches_congr (hagree : ∀ key, key ∈ pattern → message[key]? = other[key]?) :
    pattern.Matches message ↔ pattern.Matches other := by
  have named : ∀ (key : String) (value : Value), pattern[key]? = some value → key ∈ pattern :=
    fun key value hget => Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hget]; rfl)
  constructor
  · intro h key value hget
    rw [← hagree key (named key value hget)]
    exact h key value hget
  · intro h key value hget
    rw [hagree key (named key value hget)]
    exact h key value hget

end Pattern

end SenecaAccess
