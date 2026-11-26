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
A pattern: a finite list of requirements. The requirement `(key, value)`
asks that the message has a property named `key` whose value is exactly
`value`.

The patrun pattern `{ sys: 'entity', cmd: 'load' }` is the list
`[("sys", "entity"), ("cmd", "load")]`.
-/
abbrev Pattern (Key Value : Type) := List (Key × Value)

namespace Pattern

variable {Key Value : Type}

/--
A message matches a pattern when it meets every requirement in it.

Properties the pattern does not name are not examined, and the order in
which the requirements are listed makes no difference.
-/
def Matches (pattern : Pattern Key Value) (message : Message Key Value) : Prop :=
  ∀ key value, (key, value) ∈ pattern → message.get key = some value

/--
Matching can be computed: check each requirement in turn. All this needs
is a way to tell whether two values are equal.
-/
instance [DecidableEq Value] (pattern : Pattern Key Value) (message : Message Key Value) :
    Decidable (pattern.Matches message) :=
  decidable_of_iff (∀ requirement ∈ pattern, message.get requirement.1 = some requirement.2)
    ⟨fun h key value hmem => h (key, value) hmem,
     fun h requirement hmem => h requirement.1 requirement.2 hmem⟩

variable {pattern general specific : Pattern Key Value}
variable {message wider other : Message Key Value}

/-- The empty pattern asks for nothing, so every message matches it. -/
theorem matches_nil (message : Message Key Value) : Matches [] message :=
  fun _ _ hmem => nomatch hmem

/--
Adding a requirement to a pattern narrows it by exactly that requirement.
-/
theorem matches_cons {key : Key} {value : Value} :
    Matches ((key, value) :: pattern) message ↔
      message.get key = some value ∧ pattern.Matches message := by
  constructor
  · intro h
    exact ⟨h key value (List.mem_cons_self ..),
      fun key' value' hmem => h key' value' (List.mem_cons_of_mem _ hmem)⟩
  · intro ⟨hhead, htail⟩ key' value' hmem
    cases hmem with
    | head => exact hhead
    | tail _ hmem => exact htail key' value' hmem

/--
Asking for less matches more. If a message matches a pattern, it also
matches any pattern made from a subset of that pattern's requirements.
-/
theorem Matches.of_subset (h : specific.Matches message) (hsub : general ⊆ specific) :
    general.Matches message :=
  fun key value hmem => h key value (hsub hmem)

/--
Extra properties are ignored. If a message matches a pattern, so does
every message that extends it.
-/
theorem Matches.of_extends (h : pattern.Matches message) (hext : wider.Extends message) :
    pattern.Matches wider :=
  fun key value hmem => hext key value (h key value hmem)

/--
A pattern looks only at the keys it names. Two messages that agree on
those keys are matched alike, however they differ elsewhere.
-/
theorem matches_congr
    (hagree : ∀ key value, (key, value) ∈ pattern → message.get key = other.get key) :
    pattern.Matches message ↔ pattern.Matches other :=
  ⟨fun h key value hmem => hagree key value hmem ▸ h key value hmem,
   fun h key value hmem => (hagree key value hmem).symm ▸ h key value hmem⟩

/--
A pattern that asks for two different values of the same key can never be
met, because a message has at most one value for a key. Such a pattern is
harmless: it matches nothing.
-/
theorem not_matches_of_conflict {key : Key} {value value' : Value}
    (h : (key, value) ∈ pattern) (h' : (key, value') ∈ pattern) (hne : value ≠ value') :
    ¬ pattern.Matches message :=
  fun hmatch => hne (Option.some.inj ((hmatch key value h).symm.trans (hmatch key value' h')))

end Pattern

end SenecaAccess
