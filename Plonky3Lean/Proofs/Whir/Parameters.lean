module

public import Plonky3Lean.Proofs.Whir.Complete

@[expose] public section

/-!
# The parameter schedule

The configuration checks the first folded domain against the encoder's capacity, and no later one.
-/

namespace Plonky3Lean.Proofs.Whir

open p3_whir.mirror p3_whir.parameters.mirror

/-- BabyBear, 28 variables, rate 1/4, schedule [8, 2, 18], rates [10, 10]: accepted, and round 1 queries a folded domain of 2^28 points. -/
theorem later_fold_exceeds (cs : Counts) :
    ∃ c, schedule cs 28 2 [8, 2, 18] [10, 10] 27 = .ok c ∧
      (c.round_parameters.map (·.log_folded_domain_size)) = [22, 28] := by
  have h30 : Nat.log 2 1073741824 = 30 := by
    rw [show (1073741824 : ℕ) = 2 ^ 30 by norm_num, Nat.log_pow (by norm_num)]
  refine ⟨_, rfl, ?_⟩
  simp [h30]

end Plonky3Lean.Proofs.Whir

namespace Plonky3Lean.Proofs.Whir

open p3_whir.mirror p3_whir.parameters.mirror

/-- The variables folded by the first j folds. -/
def pre (folding : List ℕ) (j : ℕ) : ℕ := (folding.take j).sum

/-- The rate of the codeword queried in round j. -/
def rateAt (rate0 : ℕ) (rates : List ℕ) (j : ℕ) : ℕ := if j = 0 then rate0 else rates.getD (j - 1) 0

theorem pre_succ (folding : List ℕ) {j : ℕ} (hj : j < folding.length) :
    pre folding (j + 1) = pre folding j + folding.getD j 0 := by
  rw [pre, pre, List.take_add_one, List.sum_append, List.getElem?_eq_getElem hj, Option.toList_some,
    List.sum_singleton, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-- The loop state after j rounds. -/
structure LoopInv (cs : Counts) (n rate0 : ℕ) (folding rates : List ℕ) (j : ℕ) (st : LoopState) : Prop where
  len : st.rounds.length = j
  round : ∀ i < j, st.rounds[i]? = some ⟨cs.pow i, cs.folding_pow i, cs.queries (rateAt rate0 rates i),
    cs.ood (n - pre folding (i + 1)) (rates.getD i 0), n - pre folding (i + 1), folding.getD i 0,
    2 ^ (n - pre folding i + rateAt rate0 rates i), n - pre folding i + rateAt rate0 rates i - folding.getD i 0⟩
  nv : st.num_variables = n - pre folding (j + 1)
  rate : st.log_inv_rate = rateAt rate0 rates j
  domain : st.domain_size = 2 ^ (n - pre folding j + rateAt rate0 rates j)
  grow : ∀ i < j, rates.getD i 0 ≤ rateAt rate0 rates i + folding.getD i 0

theorem two_pow_shiftRight {e k : ℕ} (h : k ≤ e) : 2 ^ e >>> k = 2 ^ (e - k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_div h (by norm_num)]

/-- One accepted iteration of the round loop moves the invariant on. -/
theorem loopInv_step (cs : Counts) {n rate0 : ℕ} {folding rates : List ℕ} {j : ℕ} {st st' : LoopState}
    (hinv : LoopInv cs n rate0 folding rates j st) (hj : j + 1 < folding.length) (hn : pre folding (j + 1 + 1) ≤ n)
    (hok : p3_whir.parameters.mirror.roundStep cs folding st (j, rates.getD j 0) = .ok st') :
    LoopInv cs n rate0 folding rates (j + 1) st' := by
  unfold p3_whir.parameters.mirror.roundStep at hok
  simp only at hok
  split_ifs at hok with hgrow
  simp only [pure, Except.pure, Except.ok.injEq] at hok
  subst hok
  have h1 := pre_succ folding (j := j) (by omega)
  have h2 := pre_succ folding (j := j + 1) hj
  have hrate : rateAt rate0 rates (j + 1) = rates.getD j 0 := by simp [rateAt]
  rw [hinv.rate] at hgrow ⊢
  refine ⟨by simp [hinv.len], fun i hi => ?_, ?_, hrate, ?_, fun i hi => ?_⟩
  · by_cases hij : i < j
    · rw [List.getElem?_append_left (by rw [hinv.len]; exact hij)]
      exact hinv.round i hij
    · have : i = j := by omega
      subst this
      rw [List.getElem?_append_right (by rw [hinv.len]), hinv.len, Nat.sub_self, List.getElem?_cons_zero]
      rw [hinv.nv, hinv.domain, Nat.log_pow (by norm_num)]
  · simp only [hinv.nv]
    omega
  · simp only [hinv.domain, hrate]
    rw [two_pow_shiftRight (by omega)]
    congr 1
    omega
  · by_cases hij : i < j
    · exact hinv.grow i hij
    · have : i = j := by omega
      subst this
      omega

theorem pre_le_sum (folding : List ℕ) (j : ℕ) : pre folding j ≤ folding.sum := by
  unfold pre
  conv_rhs => rw [← List.take_append_drop j folding]
  rw [List.sum_append]
  omega

theorem pairs_getElem (rates : List ℕ) {j : ℕ} (hj : j < rates.length) :
    (rates.zipIdx.map fun e => (e.2, e.1))[j]'(by simpa using hj) = (j, rates.getD j 0) := by
  simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- The round loop of an accepted schedule keeps the invariant: after j rounds, the rest of the loop runs from a state of the expected shape. -/
theorem fold_inv (cs : Counts) {n rate0 : ℕ} {folding rates : List ℕ} (hlen : rates.length + 1 = folding.length)
    (hsum : folding.sum ≤ n) {stF : LoopState}
    (hok : (rates.zipIdx.map fun e => (e.2, e.1)).foldlM (p3_whir.parameters.mirror.roundStep cs folding)
      ⟨[], n - folding.getD 0 0, rate0, 2 ^ (n + rate0)⟩ = .ok stF) :
    ∀ j ≤ rates.length, ∃ st, LoopInv cs n rate0 folding rates j st ∧
      ((rates.zipIdx.map fun e => (e.2, e.1)).drop j).foldlM (p3_whir.parameters.mirror.roundStep cs folding) st =
        .ok stF
  | 0, _ => by
    refine ⟨_, ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _), ?_, by simp [rateAt], by simp [pre, rateAt],
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩, hok⟩
    have := pre_succ folding (j := 0) (by omega)
    simp only [pre, List.take_zero, List.sum_nil, zero_add] at this ⊢
    rw [this]
  | j + 1, hj => by
    obtain ⟨st, hinv, hrest⟩ := fold_inv cs hlen hsum hok j (by omega)
    rw [List.drop_eq_getElem_cons (by simpa using hj), pairs_getElem rates (by omega), List.foldlM_cons] at hrest
    rcases hstep : p3_whir.parameters.mirror.roundStep cs folding st (j, rates.getD j 0) with e | st'
    · rw [hstep] at hrest; cases hrest
    · rw [hstep] at hrest
      refine ⟨st', loopInv_step cs hinv (by omega) ((pre_le_sum folding _).trans hsum) hstep, hrest⟩

/-- An accepted schedule is its round loop over every rate, from the initial domain. -/
theorem schedule_ok {cs : Counts} {n rate0 : ℕ} {folding rates : List ℕ} {max_log : ℕ} {c : WhirConfig}
    (hok : schedule cs n rate0 folding rates max_log = .ok c) :
    n + rate0 < 64 ∧ rates.length = folding.length - 1 ∧ ∃ stF,
      (rates.zipIdx.map fun e => (e.2, e.1)).foldlM (p3_whir.parameters.mirror.roundStep cs folding)
        ⟨[], n - folding.getD 0 0, rate0, 2 ^ (n + rate0)⟩ = .ok stF ∧
      c = { round_parameters := stF.rounds, folding_schedule := folding,
            starting_folding_pow_bits := cs.starting_folding_pow, final_sumcheck_rounds := n - folding.sum,
            final_folding_pow_bits := cs.final_folding_pow, terminal_num_queries := cs.queries stF.log_inv_rate,
            terminal_pow_bits := cs.final_pow,
            final_round_config := finalRoundConfig cs n rate0 folding stF.rounds rates,
            stratified_queries := false } := by
  unfold schedule at hok
  simp only [bind, Except.bind] at hok
  split_ifs at hok with h1 h2 h3 h4
  simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at hok
  split at hok
  · cases hok
  split at hok
  · cases hok
  next stF hst =>
  simp only [Except.ok.injEq] at hok
  refine ⟨by omega, by omega, stF, by simpa [List.getD_eq_getElem?_getD] using hst, hok.symm⟩

theorem querySite_pow {e k : ℕ} (hk : k ≤ e) (q p : ℕ) : (querySite (2 ^ e) k q p).isSome := by
  simp only [querySite, two_pow_shiftRight hk, Nat.log_pow (by norm_num : 1 < 2)]
  simp

theorem getD_le_pre (folding : List ℕ) {j : ℕ} (hj : j < folding.length) :
    folding.getD j 0 ≤ pre folding (j + 1) := by
  rw [pre_succ folding hj]; omega

theorem pre_length (folding : List ℕ) : pre folding folding.length = folding.sum := by
  simp [pre]

/-- An accepted schedule satisfies every hypothesis of completeness and of the absence of panics, except that later folded domains fit the two-adicity: the configuration checks only the first. -/
theorem valid_of_schedule {cs : Counts} {n rate0 : ℕ} {folding rates : List ℕ} {max_log : ℕ} {c : WhirConfig}
    (hok : schedule cs n rate0 folding rates max_log = .ok c) (hne : folding ≠ []) (hsum : folding.sum ≤ n)
    {adicity : ℕ} (had : ∀ t ≤ c.n_rounds, (queried c t).log_folded_domain_size ≤ adicity) :
    Valid c n adicity := by
  obtain ⟨h64, hlen, stF, hf, hc⟩ := schedule_ok hok
  have hlen' : rates.length + 1 = folding.length := by
    have := List.length_pos_of_ne_nil hne; omega
  obtain ⟨st, hinv, hrest⟩ := fold_inv cs hlen' hsum hf rates.length le_rfl
  rw [List.drop_of_length_le (by simp)] at hrest
  simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hrest
  subst hrest
  have hrp : c.round_parameters = st.rounds := by rw [hc]
  have hfs : c.folding_schedule = folding := by rw [hc]
  have hfr : c.final_sumcheck_rounds = n - folding.sum := by rw [hc]
  have hfc : c.final_round_config = finalRoundConfig cs n rate0 folding st.rounds rates := by rw [hc]
  have htp : c.terminal_pow_bits = cs.final_pow := by rw [hc]
  have hn : c.n_rounds = rates.length := by rw [WhirConfig.n_rounds, hrp, hinv.len]
  have hpre : pre folding (rates.length + 1) = folding.sum := by rw [hlen', pre_length]
  have hqr : ∀ t < rates.length, queried c t = ⟨cs.pow t, cs.folding_pow t, cs.queries (rateAt rate0 rates t),
      cs.ood (n - pre folding (t + 1)) (rates.getD t 0), n - pre folding (t + 1), folding.getD t 0,
      2 ^ (n - pre folding t + rateAt rate0 rates t),
      n - pre folding t + rateAt rate0 rates t - folding.getD t 0⟩ := by
    intro t ht
    simp only [queried, hn, ht, ↓reduceIte, hrp, List.getD_eq_getElem?_getD, hinv.round t ht, Option.getD_some]
  have hqf : queried c rates.length = finalRoundConfig cs n rate0 folding st.rounds rates := by
    simp [queried, hn, hfc]
  have hfin : (queried c rates.length).num_variables = n - folding.sum ∧
      (queried c rates.length).folding_factor = folding.getD rates.length 0 ∧
      (queried c rates.length).pow_bits = cs.final_pow ∧
      ∃ e, (queried c rates.length).domain_size = 2 ^ e ∧ folding.getD rates.length 0 ≤ e := by
    rw [hqf]
    rcases hm : rates.length with _ | m
    · have hr0 : st.rounds = [] := List.eq_nil_of_length_eq_zero (by rw [hinv.len, hm])
      have hsum0 : folding.sum = folding.getD 0 0 := by
        have := hpre; rw [hm] at this; rw [← this, pre_succ folding (by omega), pre]; simp
      simp only [finalRoundConfig, hr0, List.getLast?_nil]
      refine ⟨by rw [hsum0], trivial, trivial, n + rate0, rfl, ?_⟩
      have := getD_le_pre folding (j := 0) (by omega)
      have := pre_le_sum folding 1
      omega
    · have hlast : st.rounds.getLast? = some (queried c m) := by
        rw [List.getLast?_eq_getElem?, hinv.len, hm, Nat.add_sub_cancel, hinv.round m (by omega),
          hqr m (by omega)]
      simp only [finalRoundConfig, hlast, hinv.len, hm, Nat.add_sub_cancel, hqr m (by omega)]
      have h1 := pre_succ folding (j := m) (by omega)
      have h2 := pre_succ folding (j := m + 1) (by omega)
      have hg := hinv.grow m (by omega)
      have hpm : pre folding (m + 1 + 1) = folding.sum := by rw [← hm]; exact hpre
      refine ⟨by omega, trivial, trivial, n - pre folding (m + 1) + rates.getD m 0, ?_, by omega⟩
      have hrm : (if m = 0 then rate0 else rates.getD (m - 1) 0) = rateAt rate0 rates m := rfl
      rw [hrm, two_pow_shiftRight (by omega)]
      congr 1
      omega
  obtain ⟨hfnv, hffold, hfpow, e, he, hek⟩ := hfin
  have hcf : c.final_round_config = queried c rates.length := by rw [hqf, hfc]
  have hsmall : ∀ t ≤ rates.length, folding.getD t 0 ≤ n := fun t ht => by
    have := getD_le_pre folding (j := t) (by omega)
    have := pre_le_sum folding (t + 1)
    omega
  refine ⟨by rw [hn, hfs]; omega, fun t ht => ?_, fun t ht => ?_, ?_, fun t ht => ?_, ⟨?_, ?_⟩, fun t ht => ?_,
    by rw [hcf, hfpow, htp], fun t ht => had t ht⟩
  · rw [hfs]
    rcases Nat.lt_or_eq_of_le (hn ▸ ht) with ht | rfl
    · rw [hqr t ht]
    · exact hffold
  · rw [hfs]; have := hsmall t (hn ▸ ht); omega
  · rw [hfs]
    rcases Nat.eq_zero_or_pos rates.length with h0 | h0
    · have hq0 : queried c 0 = queried c rates.length := by rw [h0]
      have hp1 := hpre
      rw [h0, pre_succ folding (by omega)] at hp1
      simp only [pre, List.take_zero, List.sum_nil, zero_add] at hp1
      rw [hq0, hfnv]
      omega
    · rw [hqr 0 h0, pre_succ folding (by omega)]
      simp only [pre, List.take_zero, List.sum_nil, zero_add]
      have := hsmall 0 (by omega); omega
  · rw [hfs]
    have ht' : t < rates.length := hn ▸ ht
    have h1 := pre_succ folding (j := t + 1) (by omega)
    have h2 := pre_le_sum folding (t + 1 + 1)
    rcases Nat.lt_or_eq_of_le (show t + 1 ≤ rates.length by omega) with h3 | h3
    · simp only [hqr t ht', hqr (t + 1) h3]; omega
    · have hf' : (queried c (t + 1)).num_variables = n - folding.sum := h3 ▸ hfnv
      simp only [hqr t ht', hf']
      have : pre folding (t + 1 + 1) = folding.sum := by rw [h3]; exact hpre
      omega
  · rw [hcf, hfnv, hfr]
  · rw [hfr]; omega
  · rcases Nat.lt_or_eq_of_le (hn ▸ ht) with ht | rfl
    · simp only [WhirConfig.site, hn, ht, ↓reduceIte, hrp, WhirConfig.round_folding_factor, hfs]
      rw [List.getElem?_eq_getElem (by rw [hinv.len]; exact ht),
        List.getElem?_eq_getElem (show t < folding.length by omega)]
      have hr := hinv.round t ht
      rw [List.getElem?_eq_getElem (by rw [hinv.len]; exact ht), Option.some.injEq] at hr
      simp only [hr]
      rw [show folding[t] = folding.getD t 0 by simp [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show t < folding.length by omega)]]
      have := getD_le_pre folding (j := t) (by omega)
      have := pre_succ folding (j := t) (by omega)
      have := pre_le_sum folding (t + 1)
      exact querySite_pow (by omega) _ _
    · simp only [WhirConfig.site, hn, lt_irrefl, ↓reduceIte, hcf]
      rw [he, hffold]
      exact querySite_pow hek _ _

end Plonky3Lean.Proofs.Whir
