/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import CompPoly.Fields.Binary.BF64.Ext3

@[expose] public section

/-!
# Products in `BF64.Ext3` from coefficients

`BF64.Ext3` is `GF(2^64)[Y] / (Y^3 + Y + 1)`, with an element stored as its three coefficients.

- `ofVector_mul_ofVector`: the product of two elements, with `Y^3 = Y + 1` and `Y^4 = Y^2 + Y`.
- `ofVector_mul_algebraMap`: scaling by a base-field element scales each coefficient.
-/

namespace BF64

open Polynomial CompPoly.Extension

/-- `GF(2^64)` has characteristic two. -/
theorem two_eq_zero : (2 : BF64) = 0 := by decide

theorem two_eq_zero_poly : (2 : BF64[X]) = 0 := by
  rw [show (2 : BF64[X]) = C 2 from (map_ofNat C 2).symm, two_eq_zero, map_zero]

/-- An element given by its three coefficients, in the quotient. -/
theorem toQuot_ofVector (c₀ c₁ c₂ : BF64) :
    Ext.toQuot (Ext.ofVector (P := ext3Params) #v[c₀, c₁, c₂]) =
      AdjoinRoot.mk ext3Params.poly (C c₀ + C c₁ * X + C c₂ * X ^ 2) := by
  rw [Ext.toQuot_eq_mk]
  show AdjoinRoot.mk _ (∑ i : Fin 3, C ((Ext.ofVector (P := ext3Params) #v[c₀, c₁, c₂]).coeff i) *
    X ^ (i : ℕ)) = _
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
  rfl

/-- The product of two elements of `Ext3`, from their coefficients. -/
theorem ofVector_mul_ofVector (a₀ a₁ a₂ b₀ b₁ b₂ : BF64) :
    (Ext.ofVector #v[a₀, a₁, a₂] : Ext3) * Ext.ofVector #v[b₀, b₁, b₂] =
      Ext.ofVector #v[a₀ * b₀ + a₁ * b₂ + a₂ * b₁,
        a₀ * b₁ + a₁ * b₀ + a₁ * b₂ + a₂ * b₁ + a₂ * b₂,
        a₀ * b₂ + a₁ * b₁ + a₂ * b₀ + a₂ * b₂] := by
  apply Ext.toQuot_injective
  rw [Ext.toQuot_mul, toQuot_ofVector, toQuot_ofVector, toQuot_ofVector, ← map_mul,
    AdjoinRoot.mk_eq_mk, ext3Params_poly]
  refine ⟨C (a₁ * b₂ + a₂ * b₁) + C (a₂ * b₂) * X, ?_⟩
  simp only [map_add, map_mul]
  unfold ext3Poly
  linear_combination (-(C a₁ * C b₂ + C a₂ * C b₁ + C a₂ * C b₂ * X) * (X + 1)) *
    two_eq_zero_poly

/-- Scaling an element of `Ext3` by an element of `GF(2^64)`. -/
theorem ofVector_mul_algebraMap (a₀ a₁ a₂ k : BF64) :
    (Ext.ofVector #v[a₀, a₁, a₂] : Ext3) * algebraMap BF64 Ext3 k =
      Ext.ofVector #v[a₀ * k, a₁ * k, a₂ * k] := by
  apply Ext.toQuot_injective
  rw [Ext.toQuot_mul, Ext.algebraMap_eq_ofBase, Ext.toQuot_ofBase, toQuot_ofVector,
    toQuot_ofVector, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, ← map_mul]
  congr 1
  simp only [map_mul]
  ring

end BF64
