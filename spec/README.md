# SenecaAccess specification

A [Lean 4](https://lean-lang.org) specification of the SenecaAccess
permission model. It covers layer one: whether an actor may call a message.

## Layer one

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

## What is proved

| Property                                      | Where                                                  |
| --------------------------------------------- | ------------------------------------------------------ |
| Keys are unique                               | by construction: messages and patterns are maps        |
| Binary: the answer can be computed            | the `Decidable` instance for `Policy.Allows`           |
| Default deny                                  | `Permission.not_permits_nil`, `Policy.not_allows_of_permission_eq_nil` |
| Grants only add, none takes away              | `Permission.Permits.mono`, `Policy.Allows.mono`        |
| A permission is a set                         | `Permission.permits_congr`, `Permission.permits_append` |
| Specificity does not matter                   | `Permission.permits_cons_of_within`                    |
| Each actor stands alone                       | `Policy.allows_congr`                                  |
| Asking for less matches more                  | `Pattern.Matches.weaken`                               |
| Extra message properties are ignored          | `Pattern.Matches.extend`, `Pattern.matches_congr`, `Policy.Allows.extend` |
| The empty pattern matches everything          | `Pattern.matches_empty`, `Permission.permits_of_empty_mem` |
| A message is nothing more than its properties | `Message.Within.antisymm`                              |

Every theorem is proved in full. There is no `sorry`. The worked examples
are proofs as well.

The map type comes from Lean's standard library, and with it come Lean's
three standard axioms: `propext`, `Classical.choice` and `Quot.sound`. No
theorem here depends on anything beyond those.

## Scope

- Pattern values are literal, and are compared for exact equality.
- Only the top-level properties of a message are visible.
- The rule is fixed by the set of patterns alone. patrun's trie and its
  `find` search are not modelled, so nothing here depends on the order
  patterns were added in or on which match is the most specific. An
  implementation conforms when its yes or no answers agree with
  `Policy.Allows`.
- patrun always checks keys in alphabetical order. The maps here keep
  their keys in that order too, and matching visits them in it. No answer
  depends on the order. (Lean orders strings by code point and JavaScript
  by UTF-16 code unit. The two agree except on some characters outside
  Unicode's Basic Multilingual Plane.)

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
  `SenecaAccess/Examples.lean` is proved `by decide`, which runs the
  decision procedure and accepts the answer only if it is the one stated.

## Checking the spec

The Lean version is pinned in `lean-toolchain`. With Lean installed:

```bash
cd spec
lake build --wfail
```

The build checks every proof, the worked examples included. `--wfail` turns
warnings into failures, so a proof left as `sorry` fails the build.
