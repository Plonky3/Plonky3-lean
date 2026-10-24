module

public import Plonky3Lean.Proofs.Stir.Base
public import Plonky3Lean.Proofs.Stir.Vanishing
public import Plonky3Lean.Proofs.Stir.DegCor
public import Plonky3Lean.Proofs.Stir.Lagrange

@[expose] public section

/-!
# The virtual oracle

Take a round with answer polynomial Ans, interpolation points G and combination challenge r.

The next oracle is read at x as

```text
    f(x) = (g(x) - Ans(x)) / Z_G(x)  *  sum_{t <= |G|} (x r)^t

    Z_G = prod_{y in G} (X - y)
```

which is DegCor(d, r, Quotient(g, G, Ans), d - |G|) of Definitions 4.2 and 4.12.
-/

namespace Plonky3Lean.Proofs.Stir

open Polynomial Finset Plonky3Lean.Spec.Stir p3_stir.mirror p3_stir.utils.mirror p3_dft.mirror
open p3_stir.verifier.mirror

set_option linter.unusedSectionVars false

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF]

/-- The value of the virtual oracle at x, for the opened value v. -/
noncomputable def virtualVal (r : EF) (ans pts : List EF) (x v : EF) : EF :=
  (v - (coeffPoly ans).eval x) / (pts.map fun y => x - y).prod *
    ∑ t ∈ range (pts.length + 1), (x * r) ^ t

theorem eval_vanishing (pts : List EF) (x : EF) :
    (coeffPoly (vanishing_poly_from_roots pts)).eval x = (pts.map fun y => x - y).prod := by
  rw [(vanishing_poly_from_roots_eq pts).1, eval_list_prod]
  simp [Function.comp_def]

theorem prod_sub_eq_zero_iff (pts : List EF) (x : EF) :
    (pts.map fun y => x - y).prod = 0 ↔ x ∈ pts := by
  simp [List.prod_eq_zero_iff, sub_eq_zero]

/-- The virtual oracle read on a fiber after a round.

It is none when a fiber point is an interpolation point.

Otherwise it is the virtual oracle at every fiber point. -/
theorem materialize_virtual_fiber_eq {ζ u0 shift : F} {arity : ℕ} (hζ : IsPrimitiveRoot ζ arity)
    (harity : 0 < arity) (row : List EF) (hrow : row.length = arity) (r : EF) (ans pts : List EF) :
    materialize_virtual_fiber row (shiftedPowersList ζ u0 arity) shift
        (some (finish_ctx r ans pts)) =
      if ∃ l < arity, algebraMap F EF (shift * (u0 * ζ ^ l)) ∈ pts then some none
      else some (some ((List.range arity).map fun l =>
        virtualVal r ans pts (algebraMap F EF (shift * (u0 * ζ ^ l))) (row.getD l 0))) := by
  set x : ℕ → F := fun l => shift * (u0 * ζ ^ l) with hx
  set ι := algebraMap F EF
  have hpts : (shiftedPowersList ζ u0 arity).map (shift * ·) = (List.range arity).map x := by
    simp [shiftedPowersList, x, Function.comp_def]
  have hhead : ((List.range arity).map x).head? = some (shift * u0) := by
    rcases arity with _ | a
    · omega
    · simp [List.range_succ_eq_map, x]
  have hpow : ∀ l, x l ^ arity = (shift * u0) ^ arity := fun l => by
    simp only [x]
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm l, pow_mul, hζ.pow_eq_one, one_pow, mul_one, mul_pow]
  obtain ⟨ar, har, -, hans⟩ := reduce_mod_x_pow_minus_c_eq harity ans ((shift * u0) ^ arity)
  obtain ⟨vr, hvr, -, hvan⟩ := reduce_mod_x_pow_minus_c_eq harity
    (vanishing_poly_from_roots pts) ((shift * u0) ^ arity)
  have hansx : ∀ l, eval_poly_at_base ar (x l) = (coeffPoly ans).eval (ι (x l)) :=
    fun l => by rw [eval_poly_at_base_eq, hans _ (by rw [← map_pow, hpow])]
  have hvanx : ∀ l, eval_poly_at_base vr (x l) = (pts.map fun y => ι (x l) - y).prod :=
    fun l => by rw [eval_poly_at_base_eq, hvan _ (by rw [← map_pow, hpow]), eval_vanishing]
  show _ = if ∃ l < arity, ι (x l) ∈ pts then some none
    else some (some ((List.range arity).map fun l => virtualVal r ans pts (ι (x l)) (row.getD l 0)))
  simp only [materialize_virtual_fiber, finish_ctx, hrow, hpts, hhead, Option.bind_eq_bind,
    Option.bind_some, har, hvr]
  have hmemiff : (0 : EF) ∈ ((List.range arity).map x).map (fun x => eval_poly_at_base vr x) ↔
      ∃ l < arity, ι (x l) ∈ pts := by
    simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_def, hvanx]
    constructor
    · rintro ⟨l, hl, h⟩; exact ⟨l, hl, (prod_sub_eq_zero_iff _ _).1 h⟩
    · rintro ⟨l, hl, h⟩; exact ⟨l, hl, (prod_sub_eq_zero_iff _ _).2 h⟩
  by_cases hmem : ∃ l < arity, ι (x l) ∈ pts
  · simp only [hmemiff.2 hmem, hmem, ↓reduceIte]
  have h0 := mt hmemiff.1 hmem
  simp only [h0, hmem, ↓reduceIte]
  push Not at hmem
  have hZ : ∀ l < arity, (pts.map fun y => ι (x l) - y).prod ≠ 0 := fun l hl h =>
    (hmem l hl) ((prod_sub_eq_zero_iff _ _).1 h)
  set D : ℕ → EF := fun l => if r * ι (x l) ≠ 1 then
    (pts.map fun y => ι (x l) - y).prod * (1 - r * ι (x l)) else (pts.map fun y => ι (x l) - y).prod
  have hzip : List.zipWith (fun denom step => if step ≠ 1 then denom * (1 - step) else denom)
      (((List.range arity).map x).map fun x => eval_poly_at_base vr x)
      (((List.range arity).map x).map fun x => r * ι x) = (List.range arity).map D := by
    simp only [List.map_map, List.zipWith_map, Function.comp_def, List.zipWith_self, hvanx, D]
  have hnz : (0 : EF) ∉ (List.range arity).map D := by
    simp only [List.mem_map, List.mem_range, not_exists, not_and, D]
    intro l hl h
    split_ifs at h with hs
    · exact mul_ne_zero (hZ l hl) (sub_ne_zero.2 (Ne.symm hs)) h
    · exact hZ l hl h
  rw [hzip]
  simp only [batchInv, hnz, ↓reduceIte, Option.bind_some]
  congr 2
  refine List.ext_getElem (by simp) fun l h1 h2 => ?_
  simp only [List.length_map, List.length_range, min_self] at h1
  simp only [List.getElem_map, List.getElem_range, List.map_map, Function.comp_def]
  rw [getD_map_range _ _ h1, getD_map_range _ _ h1, getD_map_range _ _ h1, hansx]
  have hZl := hZ l h1
  simp only [virtualVal, D, map_pow]
  generalize ι (x l) = y at hZl ⊢
  rw [geom_sum_closed, mul_comm y r]
  by_cases hs : r * y = 1
  · simp only [hs, ↓reduceIte, ne_eq, not_true_eq_false, div_eq_mul_inv]
  · have h1s : 1 - r * y ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
    simp only [hs, ↓reduceIte, ne_eq, not_false_eq_true, mul_pow]
    field_simp

end Plonky3Lean.Proofs.Stir
