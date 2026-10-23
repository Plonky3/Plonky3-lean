/-
Transcriptions of utils.rs, the helpers of HVZK-WHIR (eprint 2026/391).

A parallel reduction adds its partial results, which field addition makes independent of the split.
-/
module

public import P3Whir.Model

@[expose] public section

namespace p3_whir.utils.mirror

variable {F EF : Type _} [Field F] [Field EF] [Algebra F EF]

/-- eval_ze_star_n: Horner's rule from the last coefficient, the point in the base field. -/
def eval_ze_star_n (point : F) (coeffs : List EF) : EF :=
  coeffs.foldr (fun c acc => acc * algebraMap F EF point + c) 0

/-- par_eval_ze_star_n: each run of chunk_len coefficients by Horner, shifted by point^(c chunk_len), which asserts chunk_len is positive. -/
def par_eval_ze_star_n (point : F) (coeffs : List EF) (chunk_len : ℕ) : Option EF :=
  if chunk_len = 0 then none
  else some ((List.range ((coeffs.length + chunk_len - 1) / chunk_len)).map fun c =>
    eval_ze_star_n point ((coeffs.drop (c * chunk_len)).take chunk_len) *
      algebraMap F EF (point ^ (c * chunk_len))).sum

/-- par_add_scaled_powers: add coeff point^b into slot b, each run restarting its power, which asserts chunk_len is positive. -/
def par_add_scaled_powers (out : List EF) (point coeff : EF) (chunk_len : ℕ) : Option (List EF) :=
  if chunk_len = 0 then none
  else some ((List.range ((out.length + chunk_len - 1) / chunk_len)).flatMap fun c =>
    (((out.drop (c * chunk_len)).take chunk_len).foldl (fun (acc : List EF × EF) dst =>
      (acc.1 ++ [dst + acc.2], acc.2 * point)) ([], coeff * point ^ (c * chunk_len))).1)

/-- padded_ood_t1: the message's polynomial, plus point^l times the randomness's polynomial. -/
def padded_ood_t1 (point : F) (msg rand : List EF) : EF :=
  eval_ze_star_n point msg + eval_ze_star_n point rand * algebraMap F EF (point ^ msg.length)

end p3_whir.utils.mirror
