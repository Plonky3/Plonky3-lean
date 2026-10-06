import Plonky3Lean.Proofs
import Plonky3Lean.Claims.BabyBear

/-!
# Claims

Every statement this repository asserts about Plonky3, and nothing else. This
module is what a reader audits.

Each claim restates its theorem in full and takes its proof from
`Plonky3Lean.Proofs`:

```
theorem baby_bear.BabyBearParameters.PRIME.is_prime :
    Nat.Prime PRIME.val :=
  Proofs.BabyBear.baby_bear.BabyBearParameters.PRIME.is_prime
```

A proof whose statement drifts no longer typechecks against its claim, so a
claim changes only through a change to this module. CODEOWNERS assigns this
module to the Plonky3 maintainers. CI checks the axioms of every claim against
`claims.toml`.

Group claims by subject in submodules (`Claims/BabyBear.lean`) and import each
one here.
-/
