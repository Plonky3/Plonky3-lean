import Plonky3Lean.Lib
import Plonky3Lean.Proofs.Field.BabyBear
import Plonky3Lean.Proofs.Field.BabyBear.Arith
import Plonky3Lean.Proofs.Field.BabyBear.Constants
import Plonky3Lean.Proofs.Field.BabyBear.Element
import Plonky3Lean.Proofs.Field.BabyBear.Extension
import Plonky3Lean.Proofs.Field.BabyBear.Generic
import Plonky3Lean.Proofs.Field.KoalaBear
import Plonky3Lean.Proofs.Field.KoalaBear.Arith
import Plonky3Lean.Proofs.Field.KoalaBear.Constants
import Plonky3Lean.Proofs.Field.KoalaBear.Extension
import Plonky3Lean.Proofs.Field.KoalaBear.Poseidon
import Plonky3Lean.Proofs.Field.Monty31.Arith
import Plonky3Lean.Proofs.Field.Monty31.Convert
import Plonky3Lean.Proofs.Field.Monty31.Element
import Plonky3Lean.Proofs.Field.Monty31.Findings
import Plonky3Lean.Proofs.Field.Monty31.Inverse
import Plonky3Lean.Proofs.Field.Monty31.PowersOfTwo
import Plonky3Lean.Proofs.Field.Monty31.Reduce
import Plonky3Lean.Proofs.Field.Monty31.Utils
import Plonky3Lean.Proofs.Util.GcdInversion
import Plonky3Lean.Spec

/-!
# Proofs

Proofs of the statements in `Plonky3Lean.Claims`, laid out by subject
(`Proofs/Field/BabyBear/Constants.lean`). Proofs may be restructured freely: the
claims pin what they must establish.
-/
