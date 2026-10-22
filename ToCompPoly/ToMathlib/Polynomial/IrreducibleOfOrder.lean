/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Irreducibility from an element of maximal order

`R[X] / (f)`, for `f` monic of degree `d` over a finite field `K` with `q` elements, has `q ^ d` elements.

If one of them has multiplicative order `q ^ d - 1`, its powers are every nonzero element.
So every nonzero element is a unit, the quotient is a domain, and `f` is irreducible.

This turns irreducibility into a computation, `irreducible_of_orderOf`.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {K : Type*} [Field K] [Fintype K]

/-- `K[X] / (f)` has `q ^ deg f` elements, for `f` monic. -/
theorem AdjoinRoot.nat_card_of_monic {f : K[X]} (hf : f.Monic) :
    Nat.card (AdjoinRoot f) = Fintype.card K ^ f.natDegree := by
  rw [Nat.card_congr (AdjoinRoot.powerBasis' hf).basis.equivFun.toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin,
    AdjoinRoot.powerBasis'_dim]

/-- A monic `f` of positive degree is irreducible once `K[X] / (f)` has an element of order `q ^ deg f - 1`. -/
theorem irreducible_of_orderOf {f : K[X]} (hf : f.Monic) (hd : 0 < f.natDegree)
    {g : AdjoinRoot f} (hg : orderOf g = Fintype.card K ^ f.natDegree - 1) : Irreducible f := by
  classical
  have : Nontrivial (AdjoinRoot f) := AdjoinRoot.nontrivial f (by
    rw [degree_eq_natDegree hf.ne_zero]; exact_mod_cast hd.ne')
  have : Finite (AdjoinRoot f) := by
    have := AdjoinRoot.nat_card_of_monic hf
    exact Nat.finite_of_card_ne_zero (by rw [this]; exact pow_ne_zero _ Fintype.card_ne_zero)
  let : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  set n := Fintype.card K ^ f.natDegree - 1 with hn
  have hcard : Fintype.card (AdjoinRoot f) = n + 1 := by
    rw [← Nat.card_eq_fintype_card, AdjoinRoot.nat_card_of_monic hf, hn,
      Nat.sub_add_cancel (Nat.one_le_pow _ _ Fintype.card_pos)]
  have hn0 : 0 < n := by
    by_contra h0
    have h1 : n = 0 := by omega
    have : Fintype.card (AdjoinRoot f) = 1 := by rw [hcard, h1]
    exact (Fintype.one_lt_card (α := AdjoinRoot f)).ne' this
  have hpow : g ^ n = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hunit : IsUnit g := IsUnit.of_pow_eq_one hpow hn0.ne'
  -- The powers of `g` below its order are distinct units, so they are every nonzero element.
  let S : Finset (AdjoinRoot f) := (Finset.range n).image (g ^ ·)
  have hS : S.card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have := pow_injOn_Iio_orderOf (x := g)
    exact this (by rw [hg]; simpa using hi) (by rw [hg]; simpa using hj) hij
  have hsub : S ⊆ Finset.univ.erase 0 := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨(hunit.pow i).ne_zero, Finset.mem_univ _⟩
  have heq : S = Finset.univ.erase 0 := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard, hS]; omega)
  have hall : ∀ x : AdjoinRoot f, x ≠ 0 → IsUnit x := by
    intro x hx
    have : x ∈ S := by rw [heq]; exact Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp this
    exact hunit.pow i
  -- Every nonzero element is a unit, so the quotient is a domain, and `(f)` is prime.
  have : IsDomain (AdjoinRoot f) := by
    refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      obtain ⟨u, rfl⟩ := hall a ha
      simpa using congrArg (fun y => (↑u⁻¹ : AdjoinRoot f) * y) hab
  have hprime : (Ideal.span {f}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp this
  exact ((Ideal.span_singleton_prime hf.ne_zero).mp hprime).irreducible

end Polynomial
