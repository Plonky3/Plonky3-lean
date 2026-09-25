import Plonky3Lean.Proofs

/-!
# Claims

Every statement this repository asserts about Plonky3, and nothing else. This
module is what a reader audits.

Each claim restates its theorem in full and takes its proof from
`Plonky3Lean.Proofs`:

```
theorem modulus_prime :
    Nat.Prime (MontyParameters.PRIME BabyBearParameters).toNat :=
  Proofs.BabyBear.monty_prime_is_prime
```

A proof whose statement drifts no longer typechecks against its claim, so a
claim changes only through a change to this module. CODEOWNERS assigns this
module to the Plonky3 maintainers. CI checks the axioms of every claim against
`claims.toml`.

Group claims by subject in submodules (`Claims/BabyBear.lean`) and import each
one here.
-/
