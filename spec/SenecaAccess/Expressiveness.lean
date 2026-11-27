import SenecaAccess.Policy
import SenecaAccess.Entity

/-!
# What the core can express, and where it stops

A permission is a list of alternatives, and each alternative asks for some
facts to have exact values. This file shows two familiar models as special
cases, and states three things no such permission can say.

Expressible:

* **Roles.** A role is a permission, and an actor holds the union of the
  permissions of their roles.
* **Access lists.** A grant on particular records is one pattern per record.

Not expressible:

* **Exceptions.** Whatever is permitted stays permitted when facts are added.
* **Absence.** A permission cannot require that a key is missing.
* **Relating two facts.** A permission cannot require that two keys hold the
  same value, whatever that value is. It can only list the values one by one.
-/

namespace SenecaAccess

namespace Pattern

variable {Value : Type}

/-- The pattern that asks for exactly one property. -/
def single (key : String) (value : Value) : Pattern Value :=
  (∅ : Pattern Value).insert key value

/-- A message matches a single-property pattern exactly when it has that property. -/
theorem single_matches_iff {key : String} {value : Value} {message : Message Value} :
    (single key value).Matches message ↔ message[key]? = some value := by
  constructor
  · intro h
    exact h key value Std.ExtTreeMap.getElem?_insert_self
  · intro h other found hget
    have hget' : (if compare key other = .eq then some value else (∅ : Pattern Value)[other]?)
        = some found := by
      rw [← Std.ExtTreeMap.getElem?_insert]
      exact hget
    by_cases hsame : compare key other = .eq
    · rw [ite_eq_left hsame] at hget'
      have hkey : key = other := Std.LawfulEqOrd.compare_eq_iff_eq.mp hsame
      rw [← hkey, ← Option.some.inj hget']
      exact h
    · rw [ite_eq_right hsame, Std.ExtTreeMap.getElem?_empty] at hget'
      exact nomatch hget'

end Pattern

namespace Permission

variable {Value : Type}
variable {message : Message Value}

/-! ## Roles -/

/--
The union of the permissions of several roles permits a message exactly
when the permission of one of those roles does.
-/
theorem permits_flatMap {Role : Type} {roles : List Role} {grants : Role → Permission Value} :
    Permits (roles.flatMap grants) message ↔ ∃ role ∈ roles, (grants role).Permits message := by
  constructor
  · intro ⟨pattern, hmem, hmatch⟩
    obtain ⟨role, hrole, hin⟩ := List.mem_flatMap.mp hmem
    exact ⟨role, hrole, pattern, hin, hmatch⟩
  · intro ⟨role, hrole, pattern, hin, hmatch⟩
    exact ⟨pattern, List.mem_flatMap.mpr ⟨role, hrole, hin⟩, hmatch⟩

/-! ## Access lists -/

/--
A grant on listed values of one key: one single-property pattern for each
value. With the key `id`, this is a grant on particular records.
-/
def ofValues (key : String) (values : List Value) : Permission Value :=
  values.map (Pattern.single key)

/--
**Access lists are a special case.** A grant on listed values permits a
message exactly when the message has one of those values for the key.
-/
theorem permits_ofValues_iff {key : String} {values : List Value} :
    (ofValues key values).Permits message ↔ ∃ value ∈ values, message[key]? = some value := by
  constructor
  · intro ⟨pattern, hmem, hmatch⟩
    obtain ⟨value, hvalue, rfl⟩ := List.mem_map.mp hmem
    exact ⟨value, hvalue, Pattern.single_matches_iff.mp hmatch⟩
  · intro ⟨value, hvalue, hget⟩
    exact ⟨Pattern.single key value, List.mem_map.mpr ⟨value, hvalue, rfl⟩,
      Pattern.single_matches_iff.mpr hget⟩

/-! ## Limits -/

/--
**No exceptions.** If some facts are permitted, adding facts cannot make
them refused. So a permission cannot say "all of these, except the ones
that are also that".
-/
theorem no_exception (permission : Permission Value) {facts more : Message Value}
    (hmore : facts.Within more) : ¬ (permission.Permits facts ∧ ¬ permission.Permits more) :=
  fun ⟨hpermits, hrefused⟩ => hrefused (hpermits.extend hmore)

/--
**Absence cannot be required.** No permission permits exactly the facts in
which a given key is missing.
-/
theorem no_permission_requires_absence (key : String) (value : Value) :
    ¬ ∃ permission : Permission Value,
        ∀ facts : Message Value, permission.Permits facts ↔ facts[key]? = none := by
  intro ⟨permission, hexact⟩
  have hempty : permission.Permits (∅ : Message Value) :=
    (hexact ∅).mpr Std.ExtTreeMap.getElem?_empty
  have hsingle : permission.Permits (Pattern.single key value) :=
    hempty.extend (Message.empty_within _)
  have hnone := (hexact (Pattern.single key value)).mp hsingle
  have hsome : (Pattern.single key value)[key]? = some value :=
    Std.ExtTreeMap.getElem?_insert_self
  rw [hsome] at hnone
  exact nomatch hnone

/--
**Two facts cannot be related.** When there is no end of possible values,
no permission permits exactly the facts in which two different keys hold
the same value. A pattern can ask for `owner` to be `alice` and `actor` to
be `alice`, but nothing can ask for `owner` to equal `actor` whoever that
is: it takes one pattern for each value.
-/
theorem no_permission_relates_two_keys {first second : String} (hne : first ≠ second)
    (hfresh : ∀ values : List Value, ∃ value, value ∉ values) :
    ¬ ∃ permission : Permission Value, ∀ facts : Message Value,
        permission.Permits facts ↔
          ∃ value, facts[first]? = some value ∧ facts[second]? = some value := by
  intro ⟨permission, hexact⟩
  -- a value that no pattern asks `first` to have
  obtain ⟨fresh, hfreshNot⟩ := hfresh (permission.filterMap fun pattern => pattern[first]?)
  have hfirstNe : ¬ compare second first = .eq :=
    fun h => hne (Std.LawfulEqOrd.compare_eq_iff_eq.mp h).symm
  -- facts in which both keys hold that value are permitted
  let both : Message Value := ((∅ : Message Value).insert first fresh).insert second fresh
  have hbothFirst : both[first]? = some fresh := by
    show (((∅ : Message Value).insert first fresh).insert second fresh)[first]? = some fresh
    rw [Std.ExtTreeMap.getElem?_insert, ite_eq_right hfirstNe]
    exact Std.ExtTreeMap.getElem?_insert_self
  have hbothSecond : both[second]? = some fresh := Std.ExtTreeMap.getElem?_insert_self
  obtain ⟨pattern, hmem, hmatch⟩ := (hexact both).mpr ⟨fresh, hbothFirst, hbothSecond⟩
  -- the pattern that permits them cannot mention `first`
  have hpatternFirst : pattern[first]? = none := by
    cases hget : pattern[first]? with
    | none => rfl
    | some value =>
      have hvalue : value = fresh :=
        Option.some.inj ((hmatch first value hget).symm.trans hbothFirst)
      exact absurd (List.mem_filterMap.mpr ⟨pattern, hmem, hvalue ▸ hget⟩) hfreshNot
  -- so it also matches the facts that have `second` alone
  let alone : Message Value := (∅ : Message Value).insert second fresh
  have halone : pattern.Matches alone := by
    intro key value hget
    have hboth : (if compare second key = .eq then some fresh
        else ((∅ : Message Value).insert first fresh)[key]?) = some value := by
      rw [← Std.ExtTreeMap.getElem?_insert]
      exact hmatch key value hget
    show ((∅ : Message Value).insert second fresh)[key]? = some value
    rw [Std.ExtTreeMap.getElem?_insert]
    by_cases hsecond : compare second key = .eq
    · rw [ite_eq_left hsecond] at hboth
      rw [ite_eq_left hsecond]
      exact hboth
    · rw [ite_eq_right hsecond, Std.ExtTreeMap.getElem?_insert] at hboth
      by_cases hfirst : compare first key = .eq
      · have hkey : first = key := Std.LawfulEqOrd.compare_eq_iff_eq.mp hfirst
        rw [← hkey, hpatternFirst] at hget
        exact nomatch hget
      · rw [ite_eq_right hfirst, Std.ExtTreeMap.getElem?_empty] at hboth
        exact nomatch hboth
  -- but those facts must be refused, because `first` is missing
  obtain ⟨value, hget, _⟩ := (hexact alone).mp ⟨pattern, hmem, halone⟩
  have haloneFirst : alone[first]? = none := by
    show ((∅ : Message Value).insert second fresh)[first]? = none
    rw [Std.ExtTreeMap.getElem?_insert, ite_eq_right hfirstNe]
    exact Std.ExtTreeMap.getElem?_empty
  rw [haloneFirst] at hget
  exact nomatch hget

end Permission

namespace Policy

variable {Actor Role Value : Type}

/--
A role-based policy. Each actor holds some roles, each role is a
permission, and the actor's permission is the union over their roles.
-/
def ofRoles (roles : Actor → List Role) (grants : Role → Permission Value) :
    Policy Actor Value where
  permission actor := (roles actor).flatMap grants

/--
**Role-based access control is a special case.** Under a role-based policy
an actor may call a message exactly when one of their roles permits it.
-/
theorem ofRoles_allows_iff {roles : Actor → List Role} {grants : Role → Permission Value}
    {actor : Actor} {message : Message Value} :
    (ofRoles roles grants).Allows actor message ↔
      ∃ role ∈ roles actor, (grants role).Permits message :=
  Permission.permits_flatMap

end Policy

end SenecaAccess
