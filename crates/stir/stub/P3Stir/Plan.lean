/-
Transcription of the PCS plan's Combine coefficients (stir/src/pcs/plan.rs).
-/
module

public import P3Stir.Model

@[expose] public section

namespace p3_stir.pcs.plan.mirror

/-- combine_coefficients: r_i = r^(running exponent) and gap_i = d* - d_i, the exponent advancing by gap_i + 1.

It panics when a class degree exceeds d*. -/
def combine_coefficients {EF : Type _} [Monoid EF] (r_comb : EF) (log_d_star : ℕ)
    (sorted_log_ds : List ℕ) : Option (List (EF × ℕ)) :=
  let d_star := 2 ^ log_d_star
  (sorted_log_ds.foldlM (fun (st : List (EF × ℕ) × ℕ) log_d =>
    let r_i := r_comb ^ st.2
    if 2 ^ log_d ≤ d_star then
      let gap := d_star - 2 ^ log_d
      some (st.1 ++ [(r_i, gap)], st.2 + (1 + gap))
    else none) ([], 0)).map (·.1)

end p3_stir.pcs.plan.mirror
