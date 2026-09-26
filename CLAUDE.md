# Static site generator in Lean

Lean 4 nightly (see `lean-toolchain`), module system (`module` header, `public`/`@[expose]`).

Rules that must hold everywhere:
- No `partial`, `noncomputable`, `unsafe`, `implemented_by`, `native_decide`, `sorry`,
  `opaque` or new `axiom`s. `scripts/check.sh` greps for them and `Test.lean` pins the axioms
  of the headline theorems with `#guard_msgs`.
- Prefer structural recursion with explicit fuel over well-founded recursion for anything that
  must reduce inside the kernel (`decide`); WF definitions are irreducible to `decide`.
- Proofs about strings work over `List Char`; convert at the boundary with
  `String.toList`/`String.ofList` (`String.toList_ofList`, `String.ofList_toList`).

Verification stack used here: `Std.WP` with `vcgen` and the intrinsic `requires`/`ensures`/
`invariant` syntax (`set_option experimental.vcgen true`, `experimental.intrinsic true`).
`mvcgen`/`Std.Do` is the deprecated predecessor; do not add new uses.

Build and check: `lake build`, `lake build Test`, `scripts/check.sh`.
The CLI is `.lake/build/bin/sites build|serve`.

See `docs/semantics.agents.md` for the planned deep-embedding phase.
