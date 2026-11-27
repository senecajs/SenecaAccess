import SenecaAccess.Permission

/-!
# Allowances and the found value

In patrun a pattern is stored with data, and finding a pattern hands that
data back. An allowance is a pattern with such data, for example a note of
where the permission came from.

When several allowances match, one of them is the one found. The rule is
patrun's intended rule: the pattern with the most keys wins, and
alphabetical order of the keys only breaks ties between patterns of the
same size.

Which allowance is found never changes the yes or no answer. It only says
which of the matching allowances speaks for the decision.
-/

namespace SenecaAccess

namespace Pattern

variable {Value : Type}

/--
`first.Outranks second`: when both patterns match, `first` is preferred.

The pattern with more keys wins. Between two patterns with the same number
of keys, the one whose keys come first in alphabetical order wins.
-/
def Outranks (first second : Pattern Value) : Prop :=
  second.size < first.size ∨ (first.size = second.size ∧ first.keys < second.keys)

instance (first second : Pattern Value) : Decidable (first.Outranks second) :=
  inferInstanceAs
    (Decidable (second.size < first.size ∨ (first.size = second.size ∧ first.keys < second.keys)))

variable {first second third : Pattern Value} {facts : Message Value}

/-- No pattern outranks itself. -/
theorem Outranks.irrefl (pattern : Pattern Value) : ¬ pattern.Outranks pattern := by
  intro h
  cases h with
  | inl hsize => exact Nat.lt_irrefl _ hsize
  | inr hkeys => exact List.lt_irrefl _ hkeys.2

/-- Outranking is transitive. -/
theorem Outranks.trans (h₁ : first.Outranks second) (h₂ : second.Outranks third) :
    first.Outranks third := by
  cases h₁ with
  | inl hsize₁ =>
    cases h₂ with
    | inl hsize₂ => exact .inl (Nat.lt_trans hsize₂ hsize₁)
    | inr hkeys₂ => exact .inl (hkeys₂.1 ▸ hsize₁)
  | inr hkeys₁ =>
    cases h₂ with
    | inl hsize₂ => exact .inl (hkeys₁.1 ▸ hsize₂)
    | inr hkeys₂ => exact .inr ⟨hkeys₁.1.trans hkeys₂.1, List.lt_trans hkeys₁.2 hkeys₂.2⟩

/-- **The longer pattern wins.** A pattern with more keys outranks one with fewer. -/
theorem outranks_of_size_lt (hsize : second.size < first.size) : first.Outranks second :=
  .inl hsize

/--
**No ties.** Two different patterns that both match the same facts are
never level: one of them outranks the other.
-/
theorem eq_of_not_outranks (hfirst : first.Matches facts) (hsecond : second.Matches facts)
    (h₁ : ¬ first.Outranks second) (h₂ : ¬ second.Outranks first) : first = second := by
  have hsize : first.size = second.size := by
    apply Nat.le_antisymm
    · exact Nat.le_of_not_lt fun hlt => h₁ (.inl hlt)
    · exact Nat.le_of_not_lt fun hlt => h₂ (.inl hlt)
  have hkeys : first.keys = second.keys :=
    List.le_antisymm (fun hlt => h₂ (.inr ⟨hsize.symm, hlt⟩)) (fun hlt => h₁ (.inr ⟨hsize, hlt⟩))
  apply Std.ExtTreeMap.ext_getElem?
  intro key
  cases hget : first[key]? with
  | some value =>
    have hmem : key ∈ second := by
      apply Std.ExtTreeMap.mem_keys.mp
      rw [← hkeys]
      exact Std.ExtTreeMap.mem_keys.mpr
        (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hget]; rfl))
    cases hother : second[key]? with
    | none =>
      have := Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hmem
      rw [hother] at this
      cases this
    | some other =>
      have hsame := (hfirst key value hget).symm.trans (hsecond key other hother)
      exact hsame
  | none =>
    cases hother : second[key]? with
    | none => rfl
    | some other =>
      have hmem : key ∈ first := by
        apply Std.ExtTreeMap.mem_keys.mp
        rw [hkeys]
        exact Std.ExtTreeMap.mem_keys.mpr
          (Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hother]; rfl))
      have := Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hmem
      rw [hget] at this
      cases this

end Pattern

/--
An allowance: a pattern, and the data found when that pattern is the one
that decides. The data plays no part in matching.
-/
structure Allowance (Value Data : Type) where
  /-- What the facts must contain for this allowance to apply. -/
  pattern : Pattern Value
  /-- What is handed back when this allowance is the one found. -/
  data : Data

/--
The allowances that apply to one decision: the union of every permission
that is relevant to it. Later entries were added later.
-/
abbrev Allowances (Value Data : Type) := List (Allowance Value Data)

namespace Allowances

variable {Value Data : Type}

/-- The permission that allowances amount to once their data is set aside. -/
def permission (allowances : Allowances Value Data) : Permission Value :=
  allowances.map (·.pattern)

/--
The better of one candidate and the best found so far. The candidate takes
over only if it matches and outranks the best so far.
-/
def pick [DecidableEq Value] (facts : Message Value) (candidate : Allowance Value Data) :
    Option (Allowance Value Data) → Option (Allowance Value Data)
  | none => if candidate.pattern.Matches facts then some candidate else none
  | some best =>
    if candidate.pattern.Matches facts ∧ candidate.pattern.Outranks best.pattern then
      some candidate
    else some best

/--
The allowance found for a set of facts, if any matches.

Of the allowances that match, it is the one whose pattern outranks the
others. If the same pattern was added more than once, the one added last is
found, as when patrun overwrites the data of an existing pattern.
-/
def find? [DecidableEq Value] :
    Allowances Value Data → Message Value → Option (Allowance Value Data)
  | [], _ => none
  | candidate :: rest, facts => pick facts candidate (find? rest facts)

variable [DecidableEq Value]
variable {allowances : Allowances Value Data} {facts : Message Value}
variable {found other : Allowance Value Data}

/-- What a correct result looks like, for each of the two possible outcomes. -/
private def Correct (allowances : Allowances Value Data) (facts : Message Value) :
    Option (Allowance Value Data) → Prop
  | none => ∀ allowance ∈ allowances, ¬ allowance.pattern.Matches facts
  | some found =>
    found ∈ allowances ∧ found.pattern.Matches facts ∧
      ∀ other ∈ allowances, other.pattern.Matches facts →
        ¬ other.pattern.Outranks found.pattern

private theorem find?_correct (allowances : Allowances Value Data) (facts : Message Value) :
    Correct allowances facts (allowances.find? facts) := by
  induction allowances with
  | nil => exact fun _ hmem => nomatch hmem
  | cons candidate rest ih =>
    show Correct (candidate :: rest) facts (pick facts candidate (find? rest facts))
    cases hrest : find? rest facts with
    | none =>
      rw [hrest] at ih
      have hnone : ∀ allowance ∈ rest, ¬ allowance.pattern.Matches facts := ih
      show Correct (candidate :: rest) facts
        (if candidate.pattern.Matches facts then some candidate else none)
      by_cases hmatch : candidate.pattern.Matches facts
      · rw [ite_eq_left hmatch]
        refine ⟨List.mem_cons_self .., hmatch, fun other hmem hother => ?_⟩
        cases hmem with
        | head => exact Pattern.Outranks.irrefl _
        | tail _ hmem => exact absurd hother (hnone other hmem)
      · rw [ite_eq_right hmatch]
        intro allowance hmem
        cases hmem with
        | head => exact hmatch
        | tail _ hmem => exact hnone allowance hmem
    | some best =>
      rw [hrest] at ih
      have hbest : best ∈ rest ∧ best.pattern.Matches facts ∧
          ∀ other ∈ rest, other.pattern.Matches facts →
            ¬ other.pattern.Outranks best.pattern := ih
      show Correct (candidate :: rest) facts
        (if candidate.pattern.Matches facts ∧ candidate.pattern.Outranks best.pattern then
          some candidate
        else some best)
      by_cases hboth : candidate.pattern.Matches facts ∧ candidate.pattern.Outranks best.pattern
      · rw [ite_eq_left hboth]
        refine ⟨List.mem_cons_self .., hboth.1, fun other hmem hother => ?_⟩
        cases hmem with
        | head => exact Pattern.Outranks.irrefl _
        | tail _ hmem => exact fun hout => hbest.2.2 other hmem hother (hout.trans hboth.2)
      · rw [ite_eq_right hboth]
        refine ⟨List.mem_cons_of_mem _ hbest.1, hbest.2.1, fun other hmem hother => ?_⟩
        cases hmem with
        | head => exact fun hout => hboth ⟨hother, hout⟩
        | tail _ hmem => exact hbest.2.2 other hmem hother

/-- Nothing is found exactly when no allowance matches. -/
theorem find?_eq_none_iff :
    allowances.find? facts = none ↔
      ∀ allowance ∈ allowances, ¬ allowance.pattern.Matches facts := by
  have hcorrect := find?_correct allowances facts
  constructor
  · intro hnone
    rw [hnone] at hcorrect
    exact hcorrect
  · intro hall
    cases hfound : allowances.find? facts with
    | none => rfl
    | some found =>
      rw [hfound] at hcorrect
      have hsome : found ∈ allowances ∧ found.pattern.Matches facts ∧ _ := hcorrect
      exact absurd hsome.2.1 (hall found hsome.1)

/-- What is found is one of the allowances. -/
theorem mem_of_find? (h : allowances.find? facts = some found) : found ∈ allowances := by
  have hcorrect := find?_correct allowances facts
  rw [h] at hcorrect
  have hsome : found ∈ allowances ∧ found.pattern.Matches facts ∧ _ := hcorrect
  exact hsome.1

/-- What is found matches the facts. -/
theorem matches_of_find? (h : allowances.find? facts = some found) :
    found.pattern.Matches facts := by
  have hcorrect := find?_correct allowances facts
  rw [h] at hcorrect
  have hsome : found ∈ allowances ∧ found.pattern.Matches facts ∧ _ := hcorrect
  exact hsome.2.1

/-- What is found is not outranked by any other allowance that matches. -/
theorem not_outranks_of_find? (h : allowances.find? facts = some found)
    (hmem : other ∈ allowances) (hmatch : other.pattern.Matches facts) :
    ¬ other.pattern.Outranks found.pattern := by
  have hcorrect := find?_correct allowances facts
  rw [h] at hcorrect
  have hsome : found ∈ allowances ∧ found.pattern.Matches facts ∧
      ∀ other ∈ allowances, other.pattern.Matches facts →
        ¬ other.pattern.Outranks found.pattern := hcorrect
  exact hsome.2.2 other hmem hmatch

/--
**The found value never changes the answer.** Something is found exactly
when the allowances, taken as a permission, permit the facts.
-/
theorem find?_isSome_iff :
    (allowances.find? facts).isSome ↔ allowances.permission.Permits facts := by
  constructor
  · intro hsome
    cases hfound : allowances.find? facts with
    | none => rw [hfound] at hsome; exact nomatch hsome
    | some found =>
      exact ⟨found.pattern, List.mem_map.mpr ⟨found, mem_of_find? hfound, rfl⟩,
        matches_of_find? hfound⟩
  · intro ⟨pattern, hmem, hmatch⟩
    obtain ⟨allowance, hin, rfl⟩ := List.mem_map.mp hmem
    cases hfound : allowances.find? facts with
    | none => exact absurd hmatch (find?_eq_none_iff.mp hfound allowance hin)
    | some found => rfl

/--
**The longest pattern wins.** No allowance that matches has more keys than
the one found.
-/
theorem size_le_of_find? (h : allowances.find? facts = some found)
    (hmem : other ∈ allowances) (hmatch : other.pattern.Matches facts) :
    other.pattern.size ≤ found.pattern.size :=
  Nat.le_of_not_lt fun hlt => not_outranks_of_find? h hmem hmatch (.inl hlt)

/--
**Alphabetical order only breaks ties.** Among the matching allowances with
as many keys as the one found, none has keys that come earlier.
-/
theorem not_keys_lt_of_find? (h : allowances.find? facts = some found)
    (hmem : other ∈ allowances) (hmatch : other.pattern.Matches facts)
    (hsize : other.pattern.size = found.pattern.size) :
    ¬ other.pattern.keys < found.pattern.keys :=
  fun hlt => not_outranks_of_find? h hmem hmatch (.inr ⟨hsize, hlt⟩)

/--
**The order of adding does not matter.** Two lists holding the same
allowances find the same pattern for the same facts.
-/
theorem find?_pattern_eq {reordered : Allowances Value Data} {again : Allowance Value Data}
    (hsame : ∀ allowance, allowance ∈ allowances ↔ allowance ∈ reordered)
    (h : allowances.find? facts = some found) (hagain : reordered.find? facts = some again) :
    found.pattern = again.pattern :=
  Pattern.eq_of_not_outranks (matches_of_find? h) (matches_of_find? hagain)
    (not_outranks_of_find? hagain ((hsame found).mp (mem_of_find? h)) (matches_of_find? h))
    (not_outranks_of_find? h ((hsame again).mpr (mem_of_find? hagain)) (matches_of_find? hagain))

end Allowances

end SenecaAccess
