import ToCompPoly.Data.Nat.PowMod
import ToCompPoly.Fields.BabyBear
import ToCompPoly.Fields.BabyBear.Extension
import ToCompPoly.Fields.Binary.NatPoly
import ToCompPoly.Fields.Binary.Poly192.Basic
import ToCompPoly.Fields.Binary.Poly64.Basic
import ToCompPoly.Fields.Goldilocks
import ToCompPoly.Fields.KoalaBear
import ToCompPoly.Fields.KoalaBear.Extension
import ToCompPoly.Fields.KoalaBear.Quintic
import ToCompPoly.Fields.Mersenne
import ToCompPoly.Fields.Mersenne.Complex
import ToCompPoly.Fields.Mersenne.Extension
import ToCompPoly.ToMathlib.Order.OrderOfSq
import ToCompPoly.ToMathlib.Polynomial.CoeffList
import ToCompPoly.ToMathlib.Polynomial.IrreducibleOfOrder
import ToCompPoly.ToMathlib.Polynomial.Rabin
import ToCompPoly.ToMathlib.Polynomial.XPowSubC

/-!
# Staged for CompPoly

Field specifications and supporting lemmas that Plonky3-lean's claims need and
CompPoly does not have yet. See `ToCompPoly/README.md`.
-/
