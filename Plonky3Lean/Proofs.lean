module

public import Plonky3Lean.Lib
public import Plonky3Lean.Spec
public import Plonky3Lean.Proofs.Field.BabyBear
public import Plonky3Lean.Proofs.Field.BabyBear.Arith
public import Plonky3Lean.Proofs.Field.BabyBear.Constants
public import Plonky3Lean.Proofs.Field.BabyBear.Element
public import Plonky3Lean.Proofs.Field.BabyBear.Extension
public import Plonky3Lean.Proofs.Field.BabyBear.Generic
public import Plonky3Lean.Proofs.Field.Goldilocks.Arith
public import Plonky3Lean.Proofs.Field.Goldilocks.Basic
public import Plonky3Lean.Proofs.Field.Goldilocks.Constants
public import Plonky3Lean.Proofs.Field.Goldilocks.Convert
public import Plonky3Lean.Proofs.Field.Goldilocks.Field
public import Plonky3Lean.Proofs.Field.Goldilocks.Inverse
public import Plonky3Lean.Proofs.Field.Goldilocks.PowersOfTwo
public import Plonky3Lean.Proofs.Field.Goldilocks.Sum
public import Plonky3Lean.Proofs.Field.KoalaBear
public import Plonky3Lean.Proofs.Field.KoalaBear.Arith
public import Plonky3Lean.Proofs.Field.KoalaBear.Constants
public import Plonky3Lean.Proofs.Field.KoalaBear.Extension
public import Plonky3Lean.Proofs.Field.KoalaBear.Generic
public import Plonky3Lean.Proofs.Field.KoalaBear.Poseidon
public import Plonky3Lean.Proofs.Field.Mersenne31.Basic
public import Plonky3Lean.Proofs.Field.Mersenne31.Complex
public import Plonky3Lean.Proofs.Field.Mersenne31.Constants
public import Plonky3Lean.Proofs.Field.Mersenne31.Conversions
public import Plonky3Lean.Proofs.Field.Mersenne31.DotProduct
public import Plonky3Lean.Proofs.Field.Mersenne31.DotProductLoop
public import Plonky3Lean.Proofs.Field.Mersenne31.Field
public import Plonky3Lean.Proofs.Field.Mersenne31.Inverse
public import Plonky3Lean.Proofs.Field.Mersenne31.NewArray
public import Plonky3Lean.Proofs.Field.Mersenne31.Sum
public import Plonky3Lean.Proofs.Field.Monty31.Arith
public import Plonky3Lean.Proofs.Field.Monty31.Convert
public import Plonky3Lean.Proofs.Field.Monty31.Element
public import Plonky3Lean.Proofs.Field.Monty31.Findings
public import Plonky3Lean.Proofs.Field.Monty31.Inverse
public import Plonky3Lean.Proofs.Field.Monty31.PowersOfTwo
public import Plonky3Lean.Proofs.Field.Monty31.QuotientMap
public import Plonky3Lean.Proofs.Field.Monty31.Reduce
public import Plonky3Lean.Proofs.Field.Monty31.Utils
public import Plonky3Lean.Proofs.Util.GcdInversion

@[expose] public section

/-!
# Proofs

Proofs of the statements in `Plonky3Lean.Claims`, laid out by subject
(`Proofs/Field/BabyBear/Constants.lean`). Proofs may be restructured freely: the
claims pin what they must establish.
-/
