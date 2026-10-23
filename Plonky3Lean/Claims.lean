module

public import Plonky3Lean.Claims.Air
public import Plonky3Lean.Claims.BabyBear
public import Plonky3Lean.Claims.Blake2s
public import Plonky3Lean.Claims.Blake3
public import Plonky3Lean.Claims.Commit
public import Plonky3Lean.Claims.Dft
public import Plonky3Lean.Claims.BinaryField
public import Plonky3Lean.Claims.Goldilocks
public import Plonky3Lean.Claims.KoalaBear
public import Plonky3Lean.Claims.Matrix
public import Plonky3Lean.Claims.Mersenne31
public import Plonky3Lean.Claims.Security
public import Plonky3Lean.Claims.Monty31
public import Plonky3Lean.Claims.Sha256
public import Plonky3Lean.Claims.Symmetric
public import Plonky3Lean.Claims.Util
public import Plonky3Lean.Claims.ZkCodes
public import Plonky3Lean.Proofs
public import Plonky3Lean.Claims.MerkleTree

@[expose] public section

/-!
# Claims

Every statement this repository asserts about Plonky3, and nothing else. This
module is what a reader audits.

Each claim restates its theorem in full and takes its proof from
`Plonky3Lean.Proofs`:

```
theorem baby_bear.BabyBearParameters.PRIME.is_prime :
    Nat.Prime PRIME.val :=
  Proofs.P3BabyBear.baby_bear.BabyBearParameters.PRIME.is_prime
```

A proof whose statement drifts no longer typechecks against its claim, so a
claim changes only through a change to this module. CODEOWNERS assigns this
module to the Plonky3 maintainers. CI checks the axioms of every claim against
`claims.toml`.

Group claims by subject in submodules (`Claims/BabyBear.lean`) and import each
one here.
-/
