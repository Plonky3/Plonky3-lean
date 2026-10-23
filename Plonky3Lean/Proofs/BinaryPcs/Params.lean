module

public import P3BinaryPcs
public import Plonky3Lean.Proofs.Security.Binary

@[expose] public section

/-!
# The schedule of p3-binary-pcs

A schedule the constructors accept satisfies a list of invariants.

Every later step of the protocol reads only those invariants.

# Overview

- The constructor accepts exactly the schedules whose invariants hold.
- It panics only when the alphabet is narrower than a byte, which no encodable level is.
- Changing the folding factor of an accepted schedule never panics, and keeps the invariants.
- On an accepted schedule, the security model exists, and the transcript shape never panics.
- The fold and sumcheck errors fit the target, with one bit kept for the queries unless they are exhaustive.
-/

namespace Plonky3Lean.Proofs.BinaryPcs

open p3_binary_pcs.params.mirror p3_binary_pcs.transcript.mirror

/-- The model of a schedule: its challenge width, arity, rate, factor, queries and grinding. -/
def regimeOf (c : BinaryPcsConfig) : BinaryPcsRegime :=
  ⟨c.challenge_field_bits, c.num_variables, c.params.log_inv_rate, c.log_folding_factor,
    c.num_queries, c.params.pow_bits⟩

/-- The invariants of an accepted schedule. -/
structure Inv (c : BinaryPcsConfig) : Prop where
  n_pos : 0 < c.num_variables
  r_pos : 0 < c.params.log_inv_rate
  lff_pos : 0 < c.log_folding_factor
  lff_le : c.log_folding_factor ≤ c.num_variables
  word : c.num_variables + c.params.log_inv_rate < 64
  domain : c.num_variables + c.params.log_inv_rate ≤ c.committed_field_bits
  q_pos : 0 < c.num_queries
  K8 : 8 ≤ c.challenge_field_bits
  K128 : c.challenge_field_bits ≤ 128
  Kpow : c.challenge_field_bits.isPowerOfTwo
  F8 : 8 ≤ c.committed_field_bits
  pow_le : c.params.pow_bits ≤ min c.committed_field_bits 64 - 8
  pow_lt : c.params.pow_bits < c.params.security_level
  sec : c.params.security_level ≤ (regimeOf c).max_security_bits

theorem new_eq_some {K n r f q p : ℕ} {s : BinaryPcsRegime} :
    BinaryPcsRegime.new K n r f q p = some s ↔
      s = ⟨K, n, r, f, q, p⟩ ∧ 8 ≤ K ∧ K ≤ 128 ∧ K.isPowerOfTwo ∧ n ≠ 0 ∧ r ≠ 0 ∧ n + r < 64 ∧
        f ≠ 0 ∧ f ≤ n ∧ q ≠ 0 := by
  unfold BinaryPcsRegime.new
  split_ifs with h <;> simp only [BINARY_PCS_FIELD_BITS, USIZE_BITS] at h
  · simp only [false_iff]
    rintro ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    rcases h with h | h | h | h | h | h | h | h | h <;> first | exact h h3 | omega
  · simp only [Option.some.injEq]; constructor
    · rintro rfl; push Not at h; exact ⟨rfl, by omega, h.2.1, h.2.2.1, by omega⟩
    · rintro ⟨rfl, -⟩; rfl

theorem Inv.new {c : BinaryPcsConfig} (h : Inv c) :
    BinaryPcsRegime.new c.challenge_field_bits c.num_variables c.params.log_inv_rate
      c.log_folding_factor c.num_queries c.params.pow_bits = some (regimeOf c) :=
  new_eq_some.2 ⟨rfl, h.K8, h.K128, h.Kpow, h.n_pos.ne', h.r_pos.ne', h.word, h.lff_pos.ne',
    h.lff_le, h.q_pos.ne'⟩

theorem Inv.try_security_regime {c : BinaryPcsConfig} (h : Inv c) :
    c.try_security_regime = .ok (regimeOf c) := by
  rw [BinaryPcsConfig.try_security_regime, h.new]

/-- The constructor accepts exactly the schedules whose invariants hold. -/
theorem try_new_with_folding_ok (Q : ℕ → ℕ → ℕ → ℕ) (fBits efBits n : ℕ) (params : BinaryPcsParams)
    (lff : ℕ) (c : BinaryPcsConfig) :
    try_new_with_folding Q fBits efBits n params lff = some (.ok c) ↔
      c = ⟨params, fBits, efBits, n, Q params.security_level params.log_inv_rate params.pow_bits, lff⟩ ∧
        Inv c := by
  unfold try_new_with_folding
  simp only [USIZE_BITS, POW_COUNTER_BITS, POW_HEADER_BITS]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  all_goals first
    | (simp only [reduceCtorEq, Option.some.injEq, false_iff, not_and]
       rintro rfl ⟨h_n, h_r, h_l, h_ll, h_w, h_d, h_q, -, -, -, h_F8, h_pl, h_pt, -⟩
       dsimp only at *
       omega)
    | (unfold BinaryPcsConfig.validate_security BinaryPcsConfig.security_regime
         BinaryPcsConfig.try_security_regime
       dsimp only
       cases hn : BinaryPcsRegime.new efBits n params.log_inv_rate lff
           (Q params.security_level params.log_inv_rate params.pow_bits) params.pow_bits with
       | none =>
         simp only [Option.some.injEq, reduceCtorEq, false_iff, not_and]
         rintro rfl hi
         rw [hi.new] at hn
         cases hn
       | some s =>
         obtain ⟨rfl, K8, K128, Kp, -, hr0, -, -, -, -⟩ := new_eq_some.1 hn
         simp only [Option.bind_eq_bind, Option.bind_some, gt_iff_lt, pure]
         split_ifs with hs
         · simp only [reduceCtorEq, Option.some.injEq, false_iff, not_and]
           rintro rfl hi
           exact hs.not_ge hi.sec
         · simp only [Option.some.injEq, Except.ok.injEq]
           refine ⟨fun h => ?_, fun h => h.1.symm⟩
           subst h
           refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, K8, K128, Kp, ?_, ?_, ?_, not_lt.1 hs⟩⟩ <;> dsimp only <;>
             omega)

/-- The constructor panics only below a byte-wide alphabet, once the earlier checks pass. -/
theorem try_new_with_folding_none (Q : ℕ → ℕ → ℕ → ℕ) (fBits efBits n : ℕ)
    (params : BinaryPcsParams) (lff : ℕ) :
    try_new_with_folding Q fBits efBits n params lff = none ↔
      n + params.log_inv_rate < 64 ∧ n ≠ 0 ∧ 0 < lff ∧ lff ≤ n ∧ n + params.log_inv_rate ≤ fBits ∧
        fBits < 8 := by
  unfold try_new_with_folding
  simp only [USIZE_BITS, POW_COUNTER_BITS, POW_HEADER_BITS]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  all_goals first
    | (simp only [false_iff]; omega)
    | (simp only [true_iff]; omega)
    | (unfold BinaryPcsConfig.validate_security BinaryPcsConfig.security_regime
         BinaryPcsConfig.try_security_regime
       dsimp only
       cases BinaryPcsRegime.new efBits n params.log_inv_rate lff
           (Q params.security_level params.log_inv_rate params.pow_bits) params.pow_bits <;>
         simp only [Option.bind_eq_bind, Option.bind_some, pure] <;> try split_ifs
       all_goals simp only [reduceCtorEq, false_iff]; omega)

/-- On an accepted schedule, the security model exists. -/
theorem Inv.security_regime {c : BinaryPcsConfig} (h : Inv c) : c.security_regime = some (regimeOf c) := by
  simp [BinaryPcsConfig.security_regime, h.try_security_regime]

/-- Changing the folding factor of an accepted schedule never panics, and accepts exactly the factors that keep the invariants. -/
theorem Inv.try_with_folding {c : BinaryPcsConfig} (h : Inv c) (lff : ℕ) :
    (∃ r, c.try_with_folding lff = some r) ∧
      ∀ c', c.try_with_folding lff = some (.ok c') ↔
        c' = { c with log_folding_factor := lff } ∧ Inv c' := by
  unfold BinaryPcsConfig.try_with_folding
  split_ifs with hl
  · refine ⟨⟨_, rfl⟩, fun c' => ?_⟩
    simp only [Option.some.injEq, reduceCtorEq, false_iff, not_and]
    rintro rfl hi
    have := hi.lff_pos; have := hi.lff_le
    dsimp only at *
    omega
  · have hn : BinaryPcsRegime.new c.challenge_field_bits c.num_variables c.params.log_inv_rate
        lff c.num_queries c.params.pow_bits = some (regimeOf { c with log_folding_factor := lff }) :=
      new_eq_some.2 ⟨rfl, h.K8, h.K128, h.Kpow, h.n_pos.ne', h.r_pos.ne', h.word, by omega, by omega,
        h.q_pos.ne'⟩
    unfold BinaryPcsConfig.validate_security BinaryPcsConfig.security_regime
      BinaryPcsConfig.try_security_regime
    dsimp only
    rw [hn]
    simp only [Option.bind_eq_bind, Option.bind_some, pure]
    split_ifs with hs
    · refine ⟨⟨_, rfl⟩, fun c' => ?_⟩
      simp only [Option.some.injEq, reduceCtorEq, false_iff, not_and]
      rintro rfl hi
      exact hs.not_ge hi.sec
    · refine ⟨⟨_, rfl⟩, fun c' => ⟨fun h' => ?_, fun h' => by rw [h'.1]⟩⟩
      cases h'
      exact ⟨rfl, ⟨h.n_pos, h.r_pos, by dsimp only; omega, by dsimp only; omega, h.word, h.domain,
        h.q_pos, h.K8, h.K128, h.Kpow, h.F8, h.pow_le, h.pow_lt, not_lt.1 hs⟩⟩

theorem log2_strict_usize_pow (k : ℕ) : log2_strict_usize (2 ^ k) = some k := by
  simp [log2_strict_usize, Nat.log2_two_pow]

theorem pow_shiftRight_div {e k : ℕ} (hk : 0 < k) (h : k ≤ e) : 2 ^ e >>> (k - 1) / 2 = 2 ^ (e - k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_div (by omega) (by norm_num),
    show e - (k - 1) = e - k + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem Inv.domain_size {c : BinaryPcsConfig} (h : Inv c) :
    c.domain_size = some (2 ^ (c.num_variables + c.params.log_inv_rate)) := by
  simp [BinaryPcsConfig.domain_size, BinaryPcsConfig.log_domain_size, USIZE_BITS, h.word]

theorem Inv.num_fold_batches {c : BinaryPcsConfig} (h : Inv c) :
    c.num_fold_batches = some ((c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor) := by
  simp [BinaryPcsConfig.num_fold_batches, h.lff_pos.ne']

theorem Inv.batches_pos {c : BinaryPcsConfig} (h : Inv c) :
    0 < (c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor :=
  Nat.div_pos (by have := h.lff_le; have := h.n_pos; omega) h.lff_pos

/-- The transcript shape of an accepted schedule never panics, and its numbers are these. -/
theorem Inv.shape {c : BinaryPcsConfig} (h : Inv c) :
    BinaryPcsShape.new c = some ⟨c.num_variables, c.log_folding_factor,
      (c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor - 1,
      2 ^ c.params.log_inv_rate, c.params.pow_bits,
      c.num_variables + c.params.log_inv_rate - c.log_folding_factor,
      min c.num_queries (2 ^ (c.num_variables + c.params.log_inv_rate - c.log_folding_factor))⟩ := by
  have hb := h.batches_pos
  have hl := h.lff_pos
  have hle := h.lff_le
  have hr := h.r_pos
  have hw := h.word
  simp only [BinaryPcsShape.new, h.domain_size, h.num_fold_batches, Option.bind_eq_bind,
    Option.bind_some, BinaryPcsConfig.log_final_len, USIZE_BITS,
    pow_shiftRight_div hl (by omega : c.log_folding_factor ≤ c.num_variables + c.params.log_inv_rate),
    log2_strict_usize_pow, num_distinct_queries]
  simp only [show c.log_folding_factor ≠ 0 by omega, show (c.num_variables + c.log_folding_factor - 1) /
    c.log_folding_factor ≠ 0 by omega, show ¬ 64 ≤ c.params.log_inv_rate by omega, ite_false]
  rfl

/-- The multiples of k below n are the first ceil(n / k) multiples. -/
theorem range_filter_dvd {n k : ℕ} (hk : 0 < k) :
    (List.range n).filter (· % k = 0) = (List.range ((n + k - 1) / k)).map (· * k) := by
  have hs₁ : ((List.range n).filter (· % k = 0)).Pairwise (· < ·) :=
    (List.pairwise_lt_range).filter _
  have hs₂ : ((List.range ((n + k - 1) / k)).map (· * k)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun h => Nat.mul_lt_mul_of_pos_right h hk
  refine List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => by omega) hs₁ hs₂
    ((List.perm_ext_iff_of_nodup hs₁.nodup hs₂.nodup).2 fun x => ?_)
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_map]
  constructor
  · rintro ⟨hx, hd⟩
    refine ⟨x / k, ?_, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)⟩
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hk, add_mul]
    omega
  · rintro ⟨b, hb, rfl⟩
    refine ⟨?_, Nat.mul_mod_left _ _⟩
    rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hk, add_mul] at hb
    omega

/-- The fold batches of an accepted schedule: batch b starts at b lff and folds at most lff variables. -/
theorem Inv.fold_batches {c : BinaryPcsConfig} (h : Inv c) :
    c.fold_batches = some ((List.range ((c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor)).map
      fun b => (b * c.log_folding_factor, min c.log_folding_factor (c.num_variables - b * c.log_folding_factor))) := by
  simp [BinaryPcsConfig.fold_batches, h.lff_pos.ne', range_filter_dvd h.lff_pos]

/-- On an accepted schedule, the fold and sumcheck errors fit the target.

Fold j costs 2^(r + j + 1) + 1, and its sumcheck round 2, over the challenge field size 2^K.

One bit is kept for the queries unless every coset is queried. -/
theorem Inv.field_error {c : BinaryPcsConfig} (h : Inv c) :
    (∑ j ∈ Finset.range c.num_variables, (2 ^ (c.params.log_inv_rate + j + 1) + 1 + 2)) *
        2 ^ (c.params.security_level + if (regimeOf c).queries_are_exhaustive then 0 else 1) ≤
      2 ^ c.challenge_field_bits := by
  open Security.Binary in
  have hsec := h.sec
  have hc := numeratorSpec_closed c.num_variables c.params.log_inv_rate
  have hN7 := numeratorSpec_ge c.num_variables c.params.log_inv_rate h.n_pos.ne' h.r_pos.ne'
  have hNe : (regimeOf c).field_error_numerator = numeratorSpec c.num_variables c.params.log_inv_rate := by
    have : 2 ^ c.params.log_inv_rate ≤ 2 ^ (c.num_variables + c.params.log_inv_rate) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [BinaryPcsRegime.field_error_numerator, regimeOf]; omega
  have hK : (regimeOf c).challenge_field_bits = c.challenge_field_bits := rfl
  show numeratorSpec _ _ * _ ≤ _
  set N := numeratorSpec c.num_variables c.params.log_inv_rate
  set res := if (regimeOf c).queries_are_exhaustive then 0 else 1
  set L := Nat.log2 (N - 1) + 1
  have hL : L + (c.params.security_level + res) ≤ c.challenge_field_bits := by
    simp only [BinaryPcsRegime.max_security_bits, BinaryPcsRegime.field_security_bits, hNe, hK] at hsec
    have := h.pow_lt
    omega
  have hNL : N ≤ 2 ^ L := by
    have := @Nat.lt_log2_self (N - 1); rw [pow_succ]; omega
  calc N * 2 ^ (c.params.security_level + res) ≤ 2 ^ L * 2 ^ (c.params.security_level + res) :=
        Nat.mul_le_mul_right _ hNL
    _ = 2 ^ (L + (c.params.security_level + res)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ c.challenge_field_bits := Nat.pow_le_pow_right (by norm_num) hL

end Plonky3Lean.Proofs.BinaryPcs
