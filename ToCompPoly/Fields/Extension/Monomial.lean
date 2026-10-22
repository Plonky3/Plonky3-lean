/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import CompPoly.Fields.Extension

/-!
# Monomials in a binomial extension

`Ext.monomial k c` is `c · X ^ k`: the element whose only nonzero coefficient is `c`, at
`X ^ k`. In a binomial extension `F[X] / (X ^ d - W)`, a product of two monomials is again a
monomial, with `X ^ d = W` folded in when the degrees overflow. That is enough to compute with
the sparse elements extension tables are often made of, such as two-adic generators.

## Main results

* `Ext.monomial_eq`: `monomial k c = ofBase c * gen ^ k` for `k < d`.
* `Ext.monomial_mul_monomial`: `monomial k a * monomial l b = monomial (k + l) (a * b)` when
  `k + l < d`.
* `Ext.monomial_mul_monomial_of_le`: `monomial k a * monomial l b = monomial (k + l - d) (a * b * W)`
  when `d ≤ k + l < 2 * d`.
* `Ext.orderOf_ofBase`: `ofBase` preserves orders.
-/

@[expose] public section

namespace CompPoly.Extension.Ext

open Polynomial

variable {F : Type*} [Field F]

section General

variable {P : ExtensionParams F}

/-- `c · X ^ k`: the element whose only nonzero coefficient is `c`, at `X ^ k`. -/
def monomial (k : ℕ) (c : F) : Ext P := ofFn fun i => if (i : ℕ) = k then c else 0

@[simp] theorem coeff_monomial (k : ℕ) (c : F) (i : Fin P.d) :
    coeff (monomial (P := P) k c) i = if (i : ℕ) = k then c else 0 :=
  coeff_ofFn _ _

/-- A monomial below the degree is `ofBase c * gen ^ k`. -/
theorem monomial_eq (k : ℕ) (hk : k < P.d) (c : F) :
    (monomial k c : Ext P) = ofBase c * gen ^ k := by
  apply toQuot_injective
  rw [toQuot_mul, toQuot_ofBase, toQuot_pow, toQuot_gen, toQuot,
    Finset.sum_eq_single_of_mem ⟨k, hk⟩ (Finset.mem_univ _)]
  · simp
  · intro i _ hi
    have : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
    simp [this]

/-- The constant monomial is `ofBase`. -/
theorem monomial_zero (c : F) : (monomial 0 c : Ext P) = ofBase c := by
  rw [monomial_eq 0 P.d_pos, pow_zero, mul_one]

/-- `ofBase` is injective: it lands on the constant coefficient. -/
theorem ofBase_injective : Function.Injective (ofBase (P := P)) := by
  intro a b h
  have := congrArg (fun x => coeff x ⟨0, P.d_pos⟩) h
  simpa using this

/-- `ofBase` preserves orders. -/
theorem orderOf_ofBase (c : F) : orderOf (ofBase c : Ext P) = orderOf c :=
  orderOf_injective (ofBaseRingHom P).toMonoidHom ofBase_injective c

/-- A product of monomials whose degrees stay below `d`. -/
theorem monomial_mul_monomial (k l : ℕ) (hkl : k + l < P.d) (a b : F) :
    (monomial k a : Ext P) * monomial l b = monomial (k + l) (a * b) := by
  rw [monomial_eq k (by omega), monomial_eq l (by omega), monomial_eq (k + l) hkl,
    ← ofBaseRingHom_apply, ← ofBaseRingHom_apply, ← ofBaseRingHom_apply, map_mul, pow_add]
  ring

end General

section Binomial

variable (P : BinomialParams F)

/-- A product of monomials whose degrees overflow `d` once: `X ^ d = W` is folded in. -/
theorem monomial_mul_monomial_of_le (k l : ℕ) (hk : k < P.d) (hl : l < P.d)
    (hkl : P.d ≤ k + l) (a b : F) :
    (monomial k a : Ext P.toExtensionParams) * monomial l b =
      monomial (k + l - P.d) (a * b * P.W) := by
  have hd : P.toExtensionParams.d = P.d := rfl
  rw [monomial_eq k (by omega), monomial_eq l (by omega), monomial_eq (k + l - P.d) (by omega),
    ← ofBaseRingHom_apply, ← ofBaseRingHom_apply, ← ofBaseRingHom_apply, map_mul, map_mul]
  have hpow : (gen : Ext P.toExtensionParams) ^ (k + l) =
      gen ^ P.d * gen ^ (k + l - P.d) := by
    rw [← pow_add]; congr 1; omega
  have hW : (gen : Ext P.toExtensionParams) ^ P.d = ofBaseRingHom _ P.W := gen_pow_d_binomial P
  calc ofBaseRingHom _ a * gen ^ k * (ofBaseRingHom _ b * gen ^ l)
      = ofBaseRingHom _ a * ofBaseRingHom _ b * gen ^ (k + l) := by rw [pow_add]; ring
    _ = _ := by rw [hpow, hW]; ring

end Binomial

end CompPoly.Extension.Ext
