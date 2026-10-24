module

public import Plonky3Lean.Proofs.Whir.Complete
public import P3Whir.Utils

@[expose] public section

/-!
# The zero-evader of HVZK-WHIR

The out-of-domain answer of a hiding round evaluates the message followed by fresh randomness.

This is eprint 2026/391, Construction 9.7:

```text
    y = msg^(rho) + rho^l rand^(rho)
```

Take rho nonzero.

Then one randomness coefficient already makes y uniform, independent of the message.

This is Lemma 9.3 at r = 1.
-/

namespace Plonky3Lean.Proofs.Whir

open Finset Plonky3Lean.Spec.Whir p3_whir.utils.mirror

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

theorem uni_cons (a : EF) (c : List EF) (y : EF) : uni (a :: c) y = a + y * uni c y := by
  rw [uni, uni, List.length_cons, sum_range_succ', mul_sum]
  simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun b _ => by ring

theorem uni_append (a b : List EF) (y : EF) : uni (a ++ b) y = uni a y + y ^ a.length * uni b y := by
  induction a with
  | nil => simp [uni]
  | cons x a ih => rw [List.cons_append, uni_cons, ih, uni_cons, List.length_cons, pow_succ]; ring

/-- The zero-evader evaluation is the polynomial with the given coefficients at the point. -/
theorem eval_ze_star_n_eq (point : F) : ∀ c : List EF, eval_ze_star_n point c = uni c (algebraMap F EF point)
  | [] => by simp [eval_ze_star_n, uni]
  | a :: c => by
    rw [eval_ze_star_n, List.foldr_cons, ← eval_ze_star_n, eval_ze_star_n_eq point c, uni_cons]
    ring

/-- The padded out-of-domain answer, for one randomness coefficient, is a polynomial.

It is the polynomial of the message followed by the randomness. -/
theorem padded_ood_t1_eq (point : F) (msg rand : List EF) :
    padded_ood_t1 point msg rand = uni (msg ++ rand) (algebraMap F EF point) := by
  rw [padded_ood_t1, eval_ze_star_n_eq, eval_ze_star_n_eq, uni_append, map_pow]
  ring

/-- Lemma 9.3 at r = 1.

At a nonzero point, the answer is a bijection of the one randomness coefficient, whatever the message. -/
theorem padded_ood_t1_bijective {point : F} (hp : point ≠ 0) (msg : List EF) :
    Function.Bijective fun x : EF => padded_ood_t1 point msg [x] := by
  have hy : algebraMap F EF point ^ msg.length ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero (algebraMap F EF)).mpr hp)
  have h : (fun x : EF => padded_ood_t1 point msg [x]) =
      fun x => uni msg (algebraMap F EF point) + algebraMap F EF point ^ msg.length * x := by
    funext x
    rw [padded_ood_t1_eq, uni_append]
    simp [uni]
  rw [h]
  refine ⟨fun a b hab => mul_left_cancel₀ hy (add_left_cancel hab), fun z =>
    ⟨(z - uni msg (algebraMap F EF point)) / algebraMap F EF point ^ msg.length, ?_⟩⟩
  simp only
  rw [mul_div_cancel₀ _ hy]
  ring

/-- At the point zero the answer is the message's constant coefficient, whatever the randomness.

The prover only debug-asserts a nonzero point. -/
theorem padded_ood_t1_zero (a : EF) (msg rand : List EF) : padded_ood_t1 (0 : F) (a :: msg) rand = a := by
  rw [padded_ood_t1_eq, List.cons_append, uni_cons]
  simp

/-- The parallel zero-evader evaluation panics on a zero chunk length. -/
theorem par_eval_ze_star_n.panics (point : F) (coeffs : List EF) : par_eval_ze_star_n point coeffs 0 = none := rfl

end Plonky3Lean.Proofs.Whir
