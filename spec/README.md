# SenecaAccess specification

A [Lean 4](https://lean-lang.org) specification of the core of the
SenecaAccess permission model: a set of key and value facts checked against
a set of patterns.

It covers whether an actor may call a message, and how the same check
applies to entities. For what this core can and cannot express, and how it
compares with role-based, attribute-based and relationship-based systems,
see [docs/models.md](docs/models.md).

## The rule

An actor may call a Seneca message only with permission, and the answer is
always yes or no. A permission is a set of patterns of the kind patrun
uses. The actor may call the message when it matches at least one pattern
in the permission they hold.

| Concept    | Lean                 | Meaning                                                |
| ---------- | -------------------- | ------------------------------------------------------ |
| Message    | `Message`            | A map from string keys to values.                      |
| Pattern    | `Pattern`            | A partial message: the properties a message must have. |
| Within     | `Message.Within`     | Every property of one map is a property of the other.  |
| Match      | `Pattern.Matches`    | The pattern is within the message.                     |
| Permission | `Permission`         | A set of patterns.                                     |
| Permit     | `Permission.Permits` | At least one pattern in the set matches the message.   |
| Policy     | `Policy`             | The permission each actor holds.                       |
| The rule   | `Policy.Allows`      | The permission the actor holds permits the message.    |

With every definition unfolded, the rule reads (`Policy.allows_iff`):

```lean
policy.Allows actor message ↔
  ∃ pattern ∈ policy.permission actor,
    ∀ (key : String) (value : Value),
      pattern[key]? = some value → message[key]? = some value
```

Messages and patterns are maps, as JavaScript objects are. A key is a
string and has at most one value. Values and actors are type parameters:
the rule never looks inside an actor, and all it does with a value is
compare it for equality.

## Entities

An entity is a record of fields. Its fields are not in the message that
asks for it, so they are known only after it has been loaded. The check is
the same rule applied to more facts: those of the context, the actor and
the loaded entity, gathered into one set.

| Concept          | Lean                          | Meaning                                              |
| ---------------- | ----------------------------- | ---------------------------------------------------- |
| Entity           | `Entity`                      | A record: a map from field names to values.          |
| Facts            | `Facts`, `Facts.collect`      | What is known for one decision, from three sources.  |
| Entity check     | `Permission.PermitsEntity`    | The permission permits the gathered facts.           |
| Operation        | `EntityOperation`             | `load`, `remove`, `create` or `update`.              |
| Operation check  | `Permission.PermitsOperation` | What each operation must have permitted.             |
| List             | `Permission.visible`          | The entities of a result that the actor may read.    |

What each operation checks:

| Operation | Checked                                              |
| --------- | ---------------------------------------------------- |
| load      | the stored entity                                    |
| remove    | the stored entity                                    |
| create    | the entity to be written                             |
| update    | the stored entity and the entity to be written, both |
| list      | the read check on each entity returned               |

## The found value

A pattern can carry data, as it does in patrun. An `Allowance` is a pattern
with data, and `Allowances.find?` gives the one found for a set of facts.
The pattern with the most keys wins, and alphabetical order of the keys
only breaks ties. Which one is found never changes the yes or no answer.

## What is proved

| Property                                      | Where                                                  |
| --------------------------------------------- | ------------------------------------------------------ |
| Keys are unique                               | by construction: messages and patterns are maps        |
| Binary: the answer can be computed            | the `Decidable` instance for `Policy.Allows`           |
| Default deny                                  | `Permission.not_permits_nil`, `Policy.not_allows_of_permission_eq_nil` |
| Grants only add, none takes away              | `Permission.Permits.mono`, `Policy.Allows.mono`        |
| A permission is a set                         | `Permission.permits_congr`, `Permission.permits_append` |
| Specificity does not matter to the answer     | `Permission.permits_cons_of_within`                    |
| Each actor stands alone                       | `Policy.allows_congr`                                  |
| Asking for less matches more                  | `Pattern.Matches.weaken`                               |
| Extra message properties are ignored          | `Pattern.Matches.extend`, `Pattern.matches_congr`, `Policy.Allows.extend` |
| The empty pattern matches everything          | `Pattern.matches_empty`, `Permission.permits_of_empty_mem` |
| A message is nothing more than its properties | `Message.Within.antisymm`                              |
| A list shows exactly the readable entities    | `Permission.mem_visible_iff`                           |
| An update needs the stored entity permitted   | `Permission.permitsEntity_stored_of_update`            |
| An update needs the written entity permitted  | `Permission.permitsEntity_updated_of_update`           |
| Grants only add, for entities and lists       | `Permission.PermitsOperation.mono`, `Permission.mem_visible_mono` |
| The found value never changes the answer      | `Allowances.find?_isSome_iff`                          |
| The longest pattern is the one found          | `Allowances.size_le_of_find?`                          |
| Alphabetical order only breaks ties           | `Allowances.not_keys_lt_of_find?`                      |
| The order of adding does not matter           | `Allowances.find?_pattern_eq`                          |
| Roles are a special case                      | `Policy.ofRoles_allows_iff`                            |
| Access lists are a special case               | `Permission.permits_ofValues_iff`                      |
| No exceptions can be expressed                | `Permission.no_exception`                              |
| Absence cannot be required                    | `Permission.no_permission_requires_absence`            |
| Two facts cannot be related                   | `Permission.no_permission_relates_two_keys`            |

Every theorem is proved in full. There is no `sorry`. The worked examples
are proofs as well.

The map type comes from Lean's standard library, and with it come Lean's
three standard axioms: `propext`, `Classical.choice` and `Quot.sound`. No
theorem here depends on anything beyond those.

## Scope

- Pattern values are literal, and are compared for exact equality.
- Only the top-level properties of a message are visible.
- Permissions only allow. There are no exclusions yet.
- Entity fields come from the store. A value the caller writes in a
  message is never taken as a fact about a stored entity.
- Permissions on individual fields are not covered. Nor is a key used by
  more than one of the context, the actor and the entity: `Facts.collect`
  takes the context's value first, then the actor's.
- How an actor's permission is assembled, from roles, groups or anything
  else, is outside the core. The core takes the union as given.
- The yes or no answer is fixed by the set of patterns alone. It does not
  depend on the order patterns were added in or on which match is the most
  specific. An implementation conforms when its answers agree with
  `Policy.Allows` and `Permission.PermitsOperation`.
- The found value follows patrun's intended rule. patrun 7.3.0 does not
  always return it. See [docs/models.md](docs/models.md).
- patrun always checks keys in alphabetical order. The maps here keep
  their keys in that order too, and matching visits them in it. No yes or
  no answer depends on the order. (Lean orders strings by code point and
  JavaScript by UTF-16 code unit. The two agree except on some characters
  outside Unicode's Basic Multilingual Plane.)

## Reading the Lean

- A `def` is a definition and a `theorem` is a proved fact about the
  definitions.
- A `Prop` is a statement that is either true or false. `Within`,
  `Matches`, `Permits` and `Allows` are statements of this kind.
- `m[k]?` looks the key `k` up in the map `m`. The answer is `some value`,
  or `none` when the map has no such key.
- An `instance : Decidable …` is the procedure that computes whether such a
  statement is true. It is what makes the rule executable.
- An `example` is a proved fact that is not given a name. Each one in
  `SenecaAccess/Examples.lean` and `SenecaAccess/EntityExamples.lean` is
  proved `by decide`, which runs the decision procedure and accepts the
  answer only if it is the one stated.

## Checking the spec

The Lean version is pinned in `lean-toolchain`. With Lean installed:

```bash
cd spec
lake build --wfail
```

The build checks every proof, the worked examples included. `--wfail` turns
warnings into failures, so a proof left as `sorry` fails the build.
