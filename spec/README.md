# SenecaAccess specification

A [Lean 4](https://lean-lang.org) specification of the SenecaAccess
permission model. It covers layer one: whether an actor may call a message.

## Layer one

An actor may call a Seneca message only with permission, and the answer is
always yes or no. A permission is a set of patterns of the kind patrun
uses. The actor may call the message when it matches at least one pattern
in the permission they hold.

| Concept    | Lean                 | Meaning                                                  |
| ---------- | -------------------- | -------------------------------------------------------- |
| Message    | `Message`            | Look up a key and get its value, or nothing.             |
| Pattern    | `Pattern`            | A list of `(key, value)` pairs a message must contain.   |
| Match      | `Pattern.Matches`    | The message has every pair in the pattern.               |
| Permission | `Permission`         | A set of patterns.                                       |
| Permit     | `Permission.Permits` | At least one pattern in the set matches the message.     |
| Policy     | `Policy`             | The permission each actor holds.                         |
| The rule   | `Policy.Allows`      | The permission the actor holds permits the message.      |

With every definition unfolded, the rule reads (`Policy.allows_iff`):

```lean
policy.Allows actor message ↔
  ∃ pattern ∈ policy.permission actor,
    ∀ key value, (key, value) ∈ pattern → message.get key = some value
```

Keys, values and actors are type parameters. The rule never looks inside a
key or an actor, and all it does with a value is compare it for equality.

## What is proved

| Property                             | Where                                                                |
| ------------------------------------ | -------------------------------------------------------------------- |
| Binary: the answer can be computed   | the `Decidable` instance for `Policy.Allows`                         |
| Default deny                         | `Permission.not_permits_nil`, `Policy.not_allows_of_permission_eq_nil` |
| Grants only add, none takes away     | `Permission.Permits.mono`, `Policy.Allows.mono`                      |
| A permission is a set                | `Permission.permits_congr`, `Permission.permits_append`              |
| Specificity does not matter          | `Permission.permits_cons_of_subset`                                  |
| Each actor stands alone              | `Policy.allows_congr`                                                |
| Extra message properties are ignored | `Pattern.Matches.of_extends`, `Pattern.matches_congr`, `Policy.Allows.of_extends` |
| The empty pattern matches everything | `Pattern.matches_nil`, `Permission.permits_of_nil_mem`               |

Every theorem is proved in full. There is no `sorry`. The worked examples
are proofs as well.

## Scope

- Pattern values are literal, and are compared for exact equality.
- Only the top-level properties of a message are visible.
- The rule is fixed by the set of patterns alone. patrun's trie and its
  `find` search are not modelled, so nothing here depends on the order
  patterns were added in or on which match is the most specific. An
  implementation conforms when its yes or no answers agree with
  `Policy.Allows`.

## Reading the Lean

- A `def` is a definition and a `theorem` is a proved fact about the
  definitions.
- A `Prop` is a statement that is either true or false. `Matches`,
  `Permits` and `Allows` are statements of this kind.
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
