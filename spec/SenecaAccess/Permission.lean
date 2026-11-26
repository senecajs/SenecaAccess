import SenecaAccess.Pattern

/-!
# Permissions

A permission is a set of patterns. Each pattern is a grant: it permits the
messages that match it. A permission permits a message when any one of its
patterns does.
-/

namespace SenecaAccess

/--
A permission: a finite set of patterns.

It is written as a list, but only membership matters. Order and repetition
have no effect (`Permission.permits_congr`).
-/
abbrev Permission (Key Value : Type) := List (Pattern Key Value)

namespace Permission

variable {Key Value : Type}

/-- A permission permits a message when at least one of its patterns
matches the message. -/
def Permits (permission : Permission Key Value) (message : Message Key Value) : Prop :=
  ∃ pattern ∈ permission, pattern.Matches message

/-- Whether a permission permits a message can be computed: try each
pattern in turn. -/
instance [DecidableEq Value] (permission : Permission Key Value) (message : Message Key Value) :
    Decidable (permission.Permits message) :=
  inferInstanceAs (Decidable (∃ pattern ∈ permission, Pattern.Matches pattern message))

variable {permission larger first second : Permission Key Value}
variable {pattern general specific : Pattern Key Value}
variable {message wider : Message Key Value}

/-- **Default deny.** The empty permission permits nothing. -/
theorem not_permits_nil : ¬ Permits ([] : Permission Key Value) message :=
  fun ⟨_, hmem, _⟩ => nomatch hmem

/--
Adding a pattern to a permission adds exactly the messages that pattern
matches.
-/
theorem permits_cons :
    Permits (pattern :: permission) message ↔
      pattern.Matches message ∨ permission.Permits message := by
  constructor
  · intro ⟨candidate, hmem, hmatch⟩
    cases hmem with
    | head => exact .inl hmatch
    | tail _ hmem => exact .inr ⟨candidate, hmem, hmatch⟩
  · intro h
    cases h with
    | inl hmatch => exact ⟨pattern, List.mem_cons_self .., hmatch⟩
    | inr h =>
      let ⟨candidate, hmem, hmatch⟩ := h
      exact ⟨candidate, List.mem_cons_of_mem _ hmem, hmatch⟩

/--
Putting two permissions together permits exactly what either one permits.
-/
theorem permits_append :
    Permits (first ++ second) message ↔ first.Permits message ∨ second.Permits message := by
  constructor
  · intro ⟨candidate, hmem, hmatch⟩
    cases List.mem_append.mp hmem with
    | inl hmem => exact .inl ⟨candidate, hmem, hmatch⟩
    | inr hmem => exact .inr ⟨candidate, hmem, hmatch⟩
  · intro h
    cases h with
    | inl h =>
      let ⟨candidate, hmem, hmatch⟩ := h
      exact ⟨candidate, List.mem_append.mpr (.inl hmem), hmatch⟩
    | inr h =>
      let ⟨candidate, hmem, hmatch⟩ := h
      exact ⟨candidate, List.mem_append.mpr (.inr hmem), hmatch⟩

/--
**Grants only add.** A permission with more patterns permits at least as
much. No pattern can take away what another pattern grants.
-/
theorem Permits.mono (h : permission.Permits message) (hsub : permission ⊆ larger) :
    larger.Permits message :=
  let ⟨candidate, hmem, hmatch⟩ := h
  ⟨candidate, hsub hmem, hmatch⟩

/--
**A permission is a set.** Two permissions with the same patterns permit
the same messages, whatever the order or repetition of those patterns.
-/
theorem permits_congr (hsame : ∀ pattern, pattern ∈ permission ↔ pattern ∈ larger) :
    permission.Permits message ↔ larger.Permits message :=
  ⟨fun h => h.mono fun _ hmem => (hsame _).mp hmem,
   fun h => h.mono fun _ hmem => (hsame _).mpr hmem⟩

/-- A permission that contains the empty pattern permits every message. -/
theorem permits_of_nil_mem (hmem : [] ∈ permission) : permission.Permits message :=
  ⟨[], hmem, Pattern.matches_nil message⟩

/--
Extra properties are ignored. A permitted message stays permitted when
properties are added to it.
-/
theorem Permits.of_extends (h : permission.Permits message) (hext : wider.Extends message) :
    permission.Permits wider :=
  let ⟨candidate, hmem, hmatch⟩ := h
  ⟨candidate, hmem, hmatch.of_extends hext⟩

/--
**Specificity does not matter.** Adding a pattern that asks for everything
an existing pattern asks for, and possibly more, changes nothing: whatever
the new pattern matches, the existing one already matched.
-/
theorem permits_cons_of_subset (hmem : general ∈ permission) (hsub : general ⊆ specific) :
    Permits (specific :: permission) message ↔ permission.Permits message :=
  ⟨fun h =>
     (permits_cons.mp h).elim (fun hmatch => ⟨general, hmem, hmatch.of_subset hsub⟩) id,
   fun h => permits_cons.mpr (.inr h)⟩

end Permission

end SenecaAccess
