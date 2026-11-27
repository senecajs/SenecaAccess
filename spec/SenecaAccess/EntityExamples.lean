import SenecaAccess.Expressiveness

/-!
# Worked examples: entities

Notes are entities with an `id`, an `owner` and an `org`. Each example is a
proof by `decide`, so the build fails if any of them is false.
-/

namespace SenecaAccess.EntityExamples

/-- A set of key and value pairs: a context, an actor, an entity or a pattern. -/
def props (properties : List (String × String)) : Message String :=
  Message.ofList properties

/-! ## Contexts, actor and entities -/

/-- The context of reading a note. -/
def reading := props [("sys", "entity"), ("cmd", "load"), ("name", "note")]

/-- The context of saving a note. -/
def saving := props [("sys", "entity"), ("cmd", "save"), ("name", "note")]

/-- The context of removing a note. -/
def removing := props [("sys", "entity"), ("cmd", "remove"), ("name", "note")]

/-- What is known about the actor. -/
def alice := props [("user", "alice")]

/-- A note alice owns. -/
def own := props [("id", "n1"), ("owner", "alice"), ("org", "acme")]

/-- A note in alice's organisation that bob owns. -/
def colleague := props [("id", "n2"), ("owner", "bob"), ("org", "acme")]

/-- A note in another organisation. -/
def outside := props [("id", "n3"), ("owner", "carol"), ("org", "zeta")]

/--
Alice's permission.

* She may read any note in the organisation `acme`.
* She may save a note she owns.
-/
def permission : Permission String :=
  [ props [("sys", "entity"), ("cmd", "load"), ("name", "note"), ("org", "acme")],
    props [("sys", "entity"), ("cmd", "save"), ("name", "note"), ("owner", "alice")] ]

/-! ## Load: checked on the stored entity -/

example : permission.PermitsOperation reading alice (.load own) := by decide
example : permission.PermitsOperation reading alice (.load colleague) := by decide
example : ¬ permission.PermitsOperation reading alice (.load outside) := by decide

-- No pattern alice holds is for removing.
example : ¬ permission.PermitsOperation removing alice (.remove own) := by decide

/-! ## List: the readable entities, and no others -/

example : permission.visible reading alice [own, colleague, outside] = [own, colleague] := by
  decide
example : permission.visible reading alice [outside] = [] := by decide

/-! ## Save: the stored entity and the new one must both be permitted -/

/-- Alice's own note with its organisation changed. -/
def ownMoved := props [("id", "n1"), ("owner", "alice"), ("org", "zeta")]

/-- Alice's own note handed to bob. -/
def ownGivenAway := props [("id", "n1"), ("owner", "bob"), ("org", "acme")]

/-- Bob's note rewritten to name alice as its owner. -/
def colleagueTaken := props [("id", "n2"), ("owner", "alice"), ("org", "acme")]

-- She may change a note she owns, while she still owns the result.
example : permission.PermitsOperation saving alice (.update own ownMoved) := by decide

-- Taking over: the new values name her as owner, but the stored note is bob's.
example : ¬ permission.PermitsOperation saving alice (.update colleague colleagueTaken) := by
  decide

-- Giving away: the stored note is hers, but the result would not be.
example : ¬ permission.PermitsOperation saving alice (.update own ownGivenAway) := by decide

-- Creating: only the new entity is checked.
example : permission.PermitsOperation saving alice (.create own) := by decide
example : ¬ permission.PermitsOperation saving alice (.create colleague) := by decide

/-! ## The found value: where a permission came from -/

/-- Allowances for reading notes, each recording its source. -/
def allowances : Allowances String String :=
  [ ⟨props [("sys", "entity"), ("cmd", "load"), ("name", "note")], "role reader"⟩,
    ⟨props [("sys", "entity"), ("cmd", "load"), ("name", "note"), ("org", "acme")], "org acme"⟩,
    ⟨props [("sys", "entity"), ("cmd", "load"), ("name", "note"), ("id", "n1")], "share n1"⟩ ]

/-- The source found for reading an entity. -/
def source (entity : Entity String) : Option String :=
  (allowances.findEntity? reading alice entity).map (·.data)

-- Only the three-key pattern matches.
example : source outside = some "role reader" := by decide

-- Two patterns match. The longer one is found.
example : source colleague = some "org acme" := by decide

-- All three match, and two have four keys. Their keys are `cmd, id, name, sys` and
-- `cmd, name, org, sys`, and `id` comes before `name`.
example : source own = some "share n1" := by decide

/-! ## Where patrun 7.3.0 gives a different value

These are the answers the rule requires. The comments give what patrun
7.3.0 returns for the same patterns and facts.
-/

/-- The data found among patterns written with their data. -/
def found (stored : List (List (String × String) × String)) (facts : List (String × String)) :
    Option String :=
  let allowances : Allowances String String := stored.map fun entry => ⟨props entry.1, entry.2⟩
  (Allowances.find? allowances (props facts)).map (·.data)

-- patrun 7.3.0 returns `A`: it follows the alphabetically first key and stops.
example : found [([("a", "1")], "A"), ([("b", "1"), ("c", "1")], "BC")]
    [("a", "1"), ("b", "1"), ("c", "1")] = some "BC" := by decide

-- patrun 7.3.0 returns `ROOT`: the pattern `{a:1, b:1}` does not match, yet it stops
-- the search from reaching `{c:1}`.
example : found [([], "ROOT"), ([("c", "1")], "C"), ([("a", "1"), ("b", "1")], "AB")]
    [("a", "1"), ("c", "1")] = some "C" := by decide

-- Here patrun 7.3.0 agrees: patterns of the same size, decided alphabetically.
example : found [([("c", "1")], "C"), ([("a", "1")], "A")]
    [("a", "1"), ("c", "1")] = some "A" := by decide

/-! ## Roles -/

/-- Which roles each actor holds. -/
def roles : String → List String
  | "alice" => ["reader", "author"]
  | "bob" => ["reader"]
  | _ => []

/-- What each role grants. -/
def grants : String → Permission String
  | "reader" => [props [("sys", "entity"), ("cmd", "load"), ("name", "note")]]
  | "author" => [props [("sys", "entity"), ("cmd", "save"), ("name", "note")]]
  | _ => []

-- Alice holds a role that grants saving. Bob does not.
example : (Policy.ofRoles roles grants).Allows "alice" saving := by decide
example : ¬ (Policy.ofRoles roles grants).Allows "bob" saving := by decide
example : (Policy.ofRoles roles grants).Allows "bob" reading := by decide

end SenecaAccess.EntityExamples
