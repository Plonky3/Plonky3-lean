module

public import Plonky3Lean.Proofs.BinaryPcs.Params
public import Plonky3Lean.Proofs.BinaryPcs.Fold

@[expose] public section

/-!
# The query phase of the verifier never panics

On an accepted schedule, the query phase answers every proof with an acceptance or a typed rejection.

The proof is arbitrary: its round count, row counts, row widths, final codeword and witness are all adversarial.

The shape checks run before any index is read, and they bound every index the fold chain reads.
-/

namespace Plonky3Lean.Proofs.BinaryPcs

open p3_sumcheck.mirror p3_binary_dft.mirror p3_binary_pcs.mirror p3_binary_pcs.params.mirror
open p3_binary_pcs.transcript.mirror p3_binary_pcs.fold.mirror p3_binary_pcs.verifier.mirror

/-! ## Generic facts -/

theorem mapM_exists {α β : Type _} (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, ∃ y, f a = some y) → ∃ ys, l.mapM f = some ys ∧ ys.length = l.length
  | [], _ => ⟨[], rfl, rfl⟩
  | a :: l, h => by
    obtain ⟨y, hy⟩ := h a (by simp)
    obtain ⟨ys, hys, hl⟩ := mapM_exists f l fun b hb => h b (by simp [hb])
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys], by simp [hl]⟩

theorem firstError_ne_none {α ε : Type _} (xs : List α) (f : α → Option (Except ε Unit))
    (h : ∀ x ∈ xs, f x ≠ none) : firstError xs f ≠ none := by
  unfold firstError
  suffices ∀ acc : Except ε Unit, xs.foldlM (fun acc x => match acc with
      | .error e => pure (.error e)
      | .ok () => f x) acc ≠ none from this _
  induction xs with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    rw [List.foldlM_cons]
    rcases acc with e | ⟨⟩
    · exact ih (fun y hy => h y (by simp [hy])) _ |> fun h' => by simpa [pure] using h'
    · obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 (h x (by simp))
      simpa [hr] using ih (fun y hy => h y (by simp [hy])) r

theorem firstError_ok {α ε : Type _} (xs : List α) (f : α → Option (Except ε Unit))
    (h : firstError xs f = some (.ok ())) : ∀ x ∈ xs, f x = some (.ok ()) := by
  unfold firstError at h
  suffices ∀ acc : Except ε Unit, xs.foldlM (fun acc x => match acc with
      | .error e => pure (.error e)
      | .ok () => f x) acc = some (.ok ()) → acc = .ok () ∧ ∀ x ∈ xs, f x = some (.ok ()) from
    (this _ h).2
  clear h
  induction xs with
  | nil => intro acc h; simpa using h
  | cons x xs ih =>
    intro acc hacc
    rw [List.foldlM_cons] at hacc
    rcases acc with e | ⟨⟩
    · simp only [pure, Option.bind_eq_bind, Option.bind_some] at hacc
      exact absurd (ih _ hacc).1 (by simp)
    · cases hx : f x with
      | none => simp [hx] at hacc
      | some r =>
        simp only [hx, Option.bind_eq_bind, Option.bind_some] at hacc
        obtain ⟨rfl, hrest⟩ := ih r hacc
        exact ⟨rfl, by simpa [hx] using hrest⟩

theorem bind_ne_none {α β : Type _} {o : Option α} {f : α → Option β} (ho : o ≠ none)
    (hf : ∀ a, o = some a → f a ≠ none) : o.bind f ≠ none := by
  obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.1 ho
  simpa using hf a rfl

variable {F EF ComT ComX MPT MPX E : Type} [Field F] [Field EF] [Algebra F EF] [DecidableEq F]
  [DecidableEq EF]

omit [Field F] [DecidableEq F] in
theorem check_round_shape_ok {A : Type _} (round : ℕ) (rows : List (List A)) (e : ℕ) :
    check_round_shape (F := F) (E := E) round rows e = .ok () →
      rows.length = e ∧ ∀ q < rows.length, (rows.getD q []).length = 1 := by
  unfold check_round_shape
  split_ifs with h
  · simp
  · split
    · simp
    · rename_i hf
      refine fun _ => ⟨by omega, fun q hq => ?_⟩
      have := List.find?_eq_none.1 hf q (List.mem_range.2 hq)
      simpa using this

/-! ## The folds never panic inside the domain -/

omit [DecidableEq EF] in
theorem fold_pair_exists {A : Type _} [Field A] [Algebra A EF] (L : Level A) {m idx : ℕ}
    (hidx : 2 * idx < 2 ^ m) (hm : m ≤ 2 ^ L.logBits) (hw : m ≤ 64) (beta : EF) (lo hi : A) :
    ∃ y, fold_pair L idx beta lo hi = some y := by
  have hmod : 2 * idx % 2 ^ 64 = 2 * idx :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by norm_num) hw))
  have hin : 2 * idx < 2 ^ 2 ^ L.logBits := lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by norm_num) hm)
  simp only [fold_pair_eq, hmod, hin, ite_true]
  exact ⟨_, rfl⟩

omit [DecidableEq EF] in
theorem coset_loop_exists (L : Level EF) (ci : ℕ) {m : ℕ} (hm : m ≤ 2 ^ L.logBits) (hw : m ≤ 64) :
    ∀ (rest : List EF) (scratch : List EF), 2 ^ rest.length ≤ scratch.length →
      (ci + 1) * 2 ^ rest.length ≤ 2 ^ m →
      ∃ out, rest.foldlM (fun (acc : ℕ × List EF) beta => do
          let len := acc.1 / 2
          let layer ← coset_layer L ci len beta acc.2
          pure (len, layer ++ acc.2.drop len)) (2 ^ rest.length, scratch) = some out ∧ out.2 ≠ [] := by
  intro rest
  induction rest with
  | nil =>
    intro scratch hl _
    refine ⟨(_, scratch), rfl, List.ne_nil_of_length_pos ?_⟩
    simp only [List.length_nil, pow_zero] at hl
    exact hl
  | cons b rest ih =>
    intro scratch hl hci
    simp only [List.length_cons] at hl hci
    have hm2 : 2 ^ (rest.length + 1) / 2 = 2 ^ rest.length := by rw [pow_succ]; simp
    obtain ⟨layer, hlay, hlen⟩ := mapM_exists
      (fun i => fold_pair L (ci * 2 ^ rest.length + i) b (scratch.getD (2 * i) 0)
        (scratch.getD (2 * i + 1) 0)) (List.range (2 ^ rest.length)) fun i hi => by
      have := List.mem_range.1 hi
      refine fold_pair_exists L (m := m) ?_ hm hw b _ _
      have : (ci + 1) * 2 ^ (rest.length + 1) = 2 * (ci * 2 ^ rest.length + 2 ^ rest.length) := by ring
      omega
    obtain ⟨out, hout, hne⟩ := ih (layer ++ scratch.drop (2 ^ rest.length))
      (by simp [hlen]) (by rw [pow_succ] at hci; nlinarith [Nat.two_pow_pos rest.length])
    refine ⟨out, ?_, hne⟩
    rw [List.foldlM_cons]
    simp only [List.length_cons, hm2, Option.bind_eq_bind, pure]
    rw [show coset_layer L ci (2 ^ rest.length) b scratch = some layer from hlay, Option.bind_some]
    exact hout

omit [DecidableEq EF] in
/-- The coset fold never panics on a coset of the domain, whatever the values. -/
theorem fold_coset_exists {A : Type _} [Field A] [Algebra A EF] (LA : Level A) (LE : Level EF)
    (ci : ℕ) (values : List A) (bs : List EF) (hbs : bs ≠ []) (hv : values.length = 2 ^ bs.length)
    {m : ℕ} (hci : (ci + 1) * 2 ^ bs.length ≤ 2 ^ m) (hA : m ≤ 2 ^ LA.logBits) (hE : m ≤ 2 ^ LE.logBits)
    (hw : m ≤ 64) : ∃ y, fold_coset LA LE ci values bs = some y := by
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hbs
  simp only [List.length_cons] at hv hci
  have hm2 : 2 ^ (rest.length + 1) / 2 = 2 ^ rest.length := by rw [pow_succ]; simp
  obtain ⟨first, hfirst, hlen⟩ := mapM_exists
    (fun i => fold_pair LA (ci * 2 ^ rest.length + i) b (values.getD (2 * i) 0)
      (values.getD (2 * i + 1) 0)) (List.range (2 ^ rest.length)) fun i hi => by
    have := List.mem_range.1 hi
    refine fold_pair_exists LA (m := m) ?_ hA hw b _ _
    have : (ci + 1) * 2 ^ (rest.length + 1) = 2 * (ci * 2 ^ rest.length + 2 ^ rest.length) := by ring
    omega
  obtain ⟨out, hout, hne⟩ := coset_loop_exists LE ci hE hw rest first (by simp [hlen])
    (by rw [pow_succ] at hci; nlinarith [Nat.two_pow_pos rest.length])
  obtain ⟨y, l', hy⟩ := List.ne_nil_iff_exists_cons.1 hne
  refine ⟨y, ?_⟩
  unfold fold_coset
  simp only [hv, List.length_cons, ne_eq, not_true_eq_false, ite_false, List.head?_cons,
    List.tail_cons, Option.bind_eq_bind, Option.bind_some, hm2]
  rw [show (List.range (2 ^ rest.length)).mapM _ = some first from hfirst, Option.bind_some]
  refine (congrArg (fun o => Option.bind o fun x => x.2.head?) hout).trans ?_
  simp [hy]

/-! ## One fold check never panics -/

variable (V : Env F EF ComT ComX MPT MPX E)

omit [DecidableEq EF] [Algebra F EF] [DecidableEq F] in
/-- The fold of one queried coset never panics when the rows have the checked shape. -/
theorem fold_query_coset_exists {A : Type} [Field A] [Algebra A EF] (L : Level A)
    (rows : List (List A)) {T q np : ℕ} (bs : List EF) (hbs : bs ≠ [])
    (hrows : rows.length = T * 2 ^ bs.length) (hw1 : ∀ x ∈ rows, x.length = 1) (hq : q < T) {m : ℕ}
    (hnp : (np + 1) * 2 ^ bs.length ≤ 2 ^ m) (hA : m ≤ 2 ^ L.logBits) (hE : m ≤ 2 ^ V.LE.logBits)
    (hw : m ≤ 64) : ∃ y, fold_query_coset V L rows q np bs = some y := by
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hbs
  have row0 : ∀ i (hi : i < rows.length), ∃ a, rows[i][0]? = some a := fun i hi => by
    have := hw1 _ (List.getElem_mem hi)
    exact ⟨rows[i][0]'(by omega), List.getElem?_eq_getElem _⟩
  cases rest with
  | nil =>
    simp only [List.length_cons, List.length_nil, zero_add, pow_one] at hrows hnp
    have h1 : 2 * q + 1 < rows.length := by rw [hrows]; omega
    obtain ⟨lo, hlo⟩ := row0 (2 * q) (by omega)
    obtain ⟨hi, hhi⟩ := row0 (2 * q + 1) h1
    obtain ⟨y, hy⟩ := fold_pair_exists L (m := m) (idx := np) (by omega) hA hw b lo hi
    refine ⟨y, ?_⟩
    simp only [fold_query_coset, List.getElem?_eq_getElem (show 2 * q < rows.length by omega),
      List.getElem?_eq_getElem h1, Option.bind_eq_bind, Option.bind_some, hlo, hhi, hy]
  | cons b' rest =>
    obtain ⟨size, hsize⟩ : ∃ k, k = 2 ^ (b :: b' :: rest).length := ⟨_, rfl⟩
    rw [← hsize] at hrows hnp
    have hsz : (q + 1) * size ≤ rows.length := by rw [hrows]; exact Nat.mul_le_mul_right _ hq
    have hlen : ((rows.drop (q * size)).take size).length = size := by
      simp only [List.length_take, List.length_drop]; rw [add_mul, one_mul] at hsz; omega
    obtain ⟨gather, hg, hgl⟩ := mapM_exists (fun x : List A => x[0]?) ((rows.drop (q * size)).take size)
      fun x hx => by
        have := hw1 x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
        exact ⟨x[0]'(by omega), List.getElem?_eq_getElem _⟩
    obtain ⟨y, hy⟩ := fold_coset_exists L V.LE np gather (b :: b' :: rest) (by simp)
      (by rw [hgl, hlen, hsize]) (by rw [← hsize]; exact hnp) hA hE hw
    refine ⟨y, ?_⟩
    simp only [fold_query_coset, ← hsize, hlen, ne_eq, not_true_eq_false, ite_false,
      Option.bind_eq_bind, hg, Option.bind_some, hy]

theorem ceil_mul {n k : ℕ} (hk : 0 < k) {b : ℕ} (hb : b < (n + k - 1) / k) : b * k < n := by
  have := (Nat.le_div_iff_mul_le hk).1 (Nat.succ_le_of_lt hb)
  rw [Nat.succ_eq_add_one, add_mul, one_mul] at this
  clear hb
  omega

theorem le_ceil_mul {n k : ℕ} (hk : 0 < k) : n ≤ (n + k - 1) / k * k := by
  have h1 := Nat.div_add_mod (n + k - 1) k
  have h2 := Nat.mod_lt (n + k - 1) hk
  rw [mul_comm]; omega

/-- The schedule facts the fold check reads, for a batch below the batch count. -/
theorem batch_facts {n lff : ℕ} (hk : 0 < lff) {batch : ℕ} (hb : batch < (n + lff - 1) / lff) :
    batch * lff < n ∧ 0 < min lff (n - batch * lff) ∧ batch * lff + min lff (n - batch * lff) ≤ n ∧
      (batch + 1 < (n + lff - 1) / lff → min lff (n - batch * lff) = lff) ∧
      (¬ batch + 1 < (n + lff - 1) / lff → batch * lff + min lff (n - batch * lff) = n) := by
  have h1 := ceil_mul hk hb
  refine ⟨by omega, by omega, by omega, fun h => ?_, fun h => ?_⟩
  · have := ceil_mul hk h; rw [add_mul, one_mul] at this; omega
  · have h2 := le_ceil_mul (n := n) hk
    have : (n + lff - 1) / lff = batch + 1 := by omega
    rw [this, add_mul, one_mul] at h2; omega

theorem next_position_bound {n r s a index : ℕ} (hsa : s + a ≤ n + r) (hidx : index < 2 ^ (n + r)) :
    (index >>> (s + a) + 1) * 2 ^ a ≤ 2 ^ (n + r - s) := by
  rw [Nat.shiftRight_eq_div_pow]
  have hsplit : 2 ^ (n + r) = 2 ^ (n + r - (s + a)) * 2 ^ (s + a) := by
    rw [← pow_add]; congr 1; omega
  have hlt : index / 2 ^ (s + a) < 2 ^ (n + r - (s + a)) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← hsplit]; exact hidx
  calc (index / 2 ^ (s + a) + 1) * 2 ^ a ≤ 2 ^ (n + r - (s + a)) * 2 ^ a :=
        Nat.mul_le_mul_right _ hlt
    _ = 2 ^ (n + r - s) := by rw [← pow_add]; congr 1; omega

omit [DecidableEq F] in
/-- One fold check never panics, once the shape checks have passed. -/
theorem foldCheck_ne_none {n r lff T : ℕ} (hk : 0 < lff) (betas : List EF) (hb : betas.length = n)
    (proof : BinaryPcsProof F EF ComX MPT MPX) (hLF : n + r ≤ 2 ^ V.LF.logBits)
    (hLE : n + r ≤ 2 ^ V.LE.logBits) (hw : n + r ≤ 64)
    (hbase : proof.base_opened_values.length = T * 2 ^ min lff n)
    (hbase1 : ∀ x ∈ proof.base_opened_values, x.length = 1)
    (hrl : proof.rounds.length = (n + lff - 1) / lff - 1)
    (hround : ∀ i (hi : i < proof.rounds.length),
      proof.rounds[i].opened_values.length = T * 2 ^ min lff (n - (i + 1) * lff))
    (hround1 : ∀ i (hi : i < proof.rounds.length), ∀ x ∈ proof.rounds[i].opened_values, x.length = 1)
    (hfin : proof.final_codeword.length = 2 ^ r) {q index batch : ℕ} (hq : q < T)
    (hidx : index < 2 ^ (n + r)) (hbatch : batch < (n + lff - 1) / lff) :
    foldCheck V betas proof ((List.range ((n + lff - 1) / lff)).map
      fun b => (b * lff, min lff (n - b * lff))) q index batch ≠ none := by
  obtain ⟨hs, ha, hsa, hmid, hlast⟩ := batch_facts hk hbatch
  have hbs : ((betas.drop (batch * lff)).take (min lff (n - batch * lff))).length =
      min lff (n - batch * lff) := by simp [hb]
  have hbsne : (betas.drop (batch * lff)).take (min lff (n - batch * lff)) ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  have hnp := next_position_bound (r := r) (s := batch * lff) (a := min lff (n - batch * lff))
    (by omega) hidx
  have hnp' : (index >>> (batch * lff + min lff (n - batch * lff)) + 1) *
      2 ^ ((betas.drop (batch * lff)).take (min lff (n - batch * lff))).length ≤
      2 ^ (n + r - batch * lff) := by rw [hbs]; exact hnp
  -- The folded coset.
  obtain ⟨y, hy⟩ : ∃ y, (if batch = 0 then
      fold_query_coset V V.LF proof.base_opened_values q (index >>> (batch * lff + min lff (n - batch * lff)))
        ((betas.drop (batch * lff)).take (min lff (n - batch * lff)))
    else do
      let r ← proof.rounds[batch - 1]?
      fold_query_coset V V.LE r.opened_values q (index >>> (batch * lff + min lff (n - batch * lff)))
        ((betas.drop (batch * lff)).take (min lff (n - batch * lff)))) = some y := by
    split_ifs with h0
    · exact fold_query_coset_exists V V.LF _ _ hbsne (by rw [hbs, hbase, h0]; simp) hbase1 hq hnp'
        (by omega) (by omega) (by omega)
    · have hi : batch - 1 < proof.rounds.length := by omega
      obtain ⟨y, hy⟩ := fold_query_coset_exists V V.LE proof.rounds[batch - 1].opened_values _ hbsne
        (by rw [hbs, hround _ hi, show batch - 1 + 1 = batch by omega]) (hround1 _ hi) hq hnp'
        (by omega) (by omega) (by omega)
      exact ⟨y, by simp only [List.getElem?_eq_getElem hi, Option.bind_eq_bind, Option.bind_some, hy]⟩
  have hlt : ¬ betas.length < batch * lff + min lff (n - batch * lff) := by omega
  simp only [foldCheck, List.getElem?_map, List.getElem?_range hbatch, Option.map_some,
    Option.bind_eq_bind, Option.bind_some, hlt, ite_false]
  set np := index >>> (batch * lff + min lff (n - batch * lff))
  by_cases h1 : batch + 1 < (n + lff - 1) / lff
  · have hr : batch < proof.rounds.length := by omega
    set na := min lff (n - (batch + 1) * lff)
    have hmod : np % 2 ^ na < 2 ^ na := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hri : q * 2 ^ na + np % 2 ^ na < proof.rounds[batch].opened_values.length := by
      rw [hround batch hr]; nlinarith [Nat.two_pow_pos na]
    have hw1 := hround1 batch hr _ (List.getElem_mem hri)
    have hz : (proof.rounds[batch].opened_values[q * 2 ^ na + np % 2 ^ na])[0]? =
        some ((proof.rounds[batch].opened_values[q * 2 ^ na + np % 2 ^ na])[0]'(by omega)) :=
      List.getElem?_eq_getElem _
    rw [List.getElem?_range h1, Option.map_some]
    dsimp only
    simp only [List.getElem?_eq_getElem hr, Option.bind_some]
    split_ifs at hy ⊢ with h0
    · rw [hy]; simp; exact ⟨_, List.getElem?_eq_getElem hri, _, hz⟩
    · have hi : batch - 1 < proof.rounds.length := by omega
      simp only [List.getElem?_eq_getElem hi, Option.bind_eq_bind, Option.bind_some] at hy ⊢
      rw [hy]; simp; exact ⟨_, List.getElem?_eq_getElem hri, _, hz⟩
  · have hnone : (List.range ((n + lff - 1) / lff))[batch + 1]? = none :=
      List.getElem?_eq_none (by simp; omega)
    have hlastv := hlast h1
    have hnpr : np < proof.final_codeword.length := by
      rw [hfin]
      change index >>> (batch * lff + min lff (n - batch * lff)) < 2 ^ r
      have := next_position_bound (n := n) (r := r) (s := batch * lff) (a := min lff (n - batch * lff))
        (by omega) hidx
      rw [show n + r - batch * lff = r + min lff (n - batch * lff) by omega, pow_add] at this
      nlinarith [Nat.two_pow_pos (min lff (n - batch * lff))]
    rw [hnone, Option.map_none]
    simp only [List.getElem?_eq_getElem hnpr, Option.bind_some]
    split_ifs at hy ⊢ with h0
    · rw [hy]; simp
    · have hi : batch - 1 < proof.rounds.length := by omega
      simp only [List.getElem?_eq_getElem hi, Option.bind_eq_bind, Option.bind_some] at hy ⊢
      rw [hy]; simp

/-! ## The query phase never panics -/

omit [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF] in
theorem check_round_and_final_lengths_eq {c : BinaryPcsConfig} (hc : Inv c)
    (proof : BinaryPcsProof F EF ComX MPT MPX) :
    check_round_and_final_lengths (E := E) c proof = some
      (if proof.rounds.length ≠ (c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor - 1 then
        .error (.RoundCountMismatch ((c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor - 1)
          proof.rounds.length)
      else if proof.final_codeword.length ≠ 2 ^ c.params.log_inv_rate then
        .error (.FinalCodewordLengthMismatch (2 ^ c.params.log_inv_rate) proof.final_codeword.length)
      else .ok ()) := by
  have := hc.batches_pos
  have := hc.word
  simp only [check_round_and_final_lengths, hc.num_fold_batches, BinaryPcsConfig.log_final_len,
    USIZE_BITS, Option.bind_eq_bind, Option.bind_some]
  simp only [show (c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor ≠ 0 by omega,
    show ¬ 64 ≤ c.params.log_inv_rate by omega, ite_false]
  split_ifs <;> simp_all [pure]

omit [Field F] [Field EF] [Algebra F EF] [DecidableEq F] [DecidableEq EF] in
/-- The query indices: as many as the shape's pairs, each a pair index times 2^lff, below the domain. -/
theorem indices_facts (S : PSponge F EF) {c : BinaryPcsConfig} (hc : Inv c) {s : BinaryPcsShape}
    (hs : BinaryPcsShape.new c = some s) (h : List (Step F EF)) :
    let indices := (query_pairs S s h).1.map (· <<< (c.log_folding_factor - 1))
    indices.length = min c.num_queries (2 ^ (c.num_variables + c.params.log_inv_rate - c.log_folding_factor)) ∧
      ∀ x ∈ indices, x < 2 ^ (c.num_variables + c.params.log_inv_rate) := by
  rw [hc.shape] at hs
  cases hs
  intro indices
  have hl := hc.lff_pos
  have hle := hc.lff_le
  have hr := hc.r_pos
  refine ⟨by simp [indices, query_pairs, sorted_pairs], fun x hx => ?_⟩
  simp only [indices, query_pairs, sorted_pairs, List.map_map, List.mem_map,
    (List.mergeSort_perm _ _).mem_iff, List.mem_ofFn] at hx
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hx
  set p := (S.pairs h (c.num_variables + c.params.log_inv_rate - c.log_folding_factor) _ i : ℕ)
  have hp : p < 2 ^ (c.num_variables + c.params.log_inv_rate - c.log_folding_factor) := Fin.isLt _
  simp only [Function.comp, Nat.shiftLeft_eq]
  calc p * 2 ^ 1 * 2 ^ (c.log_folding_factor - 1) = p * 2 ^ c.log_folding_factor := by
        rw [mul_assoc, ← pow_add]; congr 2; omega
    _ < 2 ^ (c.num_variables + c.params.log_inv_rate - c.log_folding_factor) * 2 ^ c.log_folding_factor :=
        Nat.mul_lt_mul_of_pos_right hp (Nat.two_pow_pos _)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- On an accepted schedule, the query phase never panics on any proof.

The alphabet's and the field's domains must hold the codeword, as the schedule checks for the alphabet. -/
theorem verify_query_paths_ne_none {c : BinaryPcsConfig} (hc : Inv c)
    (hLF : c.committed_field_bits ≤ 2 ^ V.LF.logBits) (hLE : c.committed_field_bits ≤ 2 ^ V.LE.logBits)
    {s : BinaryPcsShape} (hs : BinaryPcsShape.new c = some s) (base_commitment : ComT) (betas : List EF)
    (hb : betas.length = c.num_variables) (proof : BinaryPcsProof F EF ComX MPT MPX)
    (h : List (Step F EF)) : verify_query_paths V c base_commitment betas proof s h ≠ none := by
  have hd := hc.domain
  have hw := hc.word
  have hk := hc.lff_pos
  unfold verify_query_paths
  simp only [BinaryPcsConfig.num_fold_rounds, hb, ne_eq, not_true_eq_false, ite_false,
    check_round_and_final_lengths_eq hc, hc.domain_size, hc.fold_batches, Option.bind_eq_bind,
    Option.bind_some]
  set nb := (c.num_variables + c.log_folding_factor - 1) / c.log_folding_factor with hnb
  set B := (List.range nb).map fun b =>
    (b * c.log_folding_factor, min c.log_folding_factor (c.num_variables - b * c.log_folding_factor)) with hB
  set T := min c.num_queries (2 ^ (c.num_variables + c.params.log_inv_rate) >>> c.log_folding_factor)
  have hnb0 : 0 < nb := hc.batches_pos
  have hBl : B.length = nb := by simp [hB]
  have hBi : ∀ i (hi : i < nb), B[i]? =
      some (i * c.log_folding_factor, min c.log_folding_factor (c.num_variables - i * c.log_folding_factor)) :=
    fun i hi => by simp [hB, List.getElem?_range hi]
  by_cases hR : proof.rounds.length = nb - 1
  swap
  · simp [hR, pure]
  by_cases hF : proof.final_codeword.length = 2 ^ c.params.log_inv_rate
  swap
  · simp [hR, hF, pure]
  simp only [hR, hF, not_true_eq_false, ite_false]
  rcases hp : check_canonical_pow_witness (E := E) c proof with e | ⟨⟨⟩⟩
  · simp [pure]
  simp only [hBl, hBi 0 hnb0, Option.bind_some]
  rcases hbs : check_round_shape (F := F) (E := E) 0 proof.base_opened_values
      (T <<< min c.log_folding_factor (c.num_variables - 0 * c.log_folding_factor)) with e | ⟨⟨⟩⟩
  · simp [pure]
  obtain ⟨hbl, hbw⟩ := check_round_shape_ok _ _ _ hbs
  set f1 := firstError (List.range (nb - 1)) fun i => B[i + 1]?.bind fun x =>
    proof.rounds[i]?.bind fun r => pure (check_round_shape (F := F) (E := E) (i + 1) r.opened_values (T <<< x.2))
    with hf1
  have hround_get : ∀ i (hi : i < nb - 1), proof.rounds[i]? = some (proof.rounds[i]'(by omega)) :=
    fun i hi => List.getElem?_eq_getElem _
  rcases hf : f1 with _ | e | ⟨⟨⟩⟩
  · exact absurd hf (firstError_ne_none _ _ fun i hi => by
      have hi := List.mem_range.1 hi
      simp [hBi (i + 1) (by omega), hround_get i hi, pure])
  · simp [pure]
  have hrs := firstError_ok _ _ hf
  have hround : ∀ i (hi : i < nb - 1), (proof.rounds[i]'(by omega)).opened_values.length =
        T <<< min c.log_folding_factor (c.num_variables - (i + 1) * c.log_folding_factor) ∧
      ∀ q < (proof.rounds[i]'(by omega)).opened_values.length,
        ((proof.rounds[i]'(by omega)).opened_values.getD q []).length = 1 := fun i hi => by
    have := hrs i (List.mem_range.2 hi)
    simp only [hBi (i + 1) (by omega), hround_get i hi, Option.bind_some, pure, Option.some.injEq] at this
    exact check_round_shape_ok _ _ _ this
  rcases hfc : final_codeword (F := F) s proof.final_codeword h with e | h1
  · simp [pure]
  rcases hqp : query_pow V.S s proof.pow_witness h1 with e | h2
  · simp only [hqp, Option.bind_some, pure, reduceCtorEq, not_false_eq_true]
  simp only [hk.ne', ite_false, zero_mul, Nat.sub_zero, pure]
  rcases hvb : V.mmcs.verifyBase base_commitment (1, 2 ^ (c.num_variables + c.params.log_inv_rate))
      (flat_coset_indices (List.map (fun x => x <<< (c.log_folding_factor - 1)) (query_pairs V.S s h2).1)
        0 (min c.log_folding_factor c.num_variables))
      proof.base_opened_values proof.base_multi_proof with e | ⟨⟨⟩⟩
  · simp only [hqp, hvb, Option.bind_some, reduceCtorEq, not_false_eq_true]
  simp only [hqp, hvb, Option.bind_some]
  obtain ⟨hlenI, hltI⟩ := indices_facts V.S hc hs h2
  have hT : T = min c.num_queries (2 ^ (c.num_variables + c.params.log_inv_rate - c.log_folding_factor)) := by
    simp only [T, Nat.shiftRight_eq_div_pow]
    rw [Nat.pow_div (by have := hc.lff_le; omega) (by norm_num)]
  refine bind_ne_none (firstError_ne_none _ _ fun i hi => ?_) fun a _ => ?_
  · have hi := List.mem_range.1 hi
    simp [hBi (i + 1) (by omega), hround_get i hi]
  rcases a with e | ⟨⟨⟩⟩
  · simp
  refine bind_ne_none (firstError_ne_none _ _ fun q hq => ?_) fun a _ => ?_
  · have hq := List.mem_range.1 hq
    rw [List.getElem?_eq_getElem hq]
    refine bind_ne_none (by simp) fun x hx => ?_
    simp only [Option.some.injEq] at hx
    subst hx
    refine firstError_ne_none _ _ fun batch hbatch => ?_
    have hbatch := List.mem_range.1 hbatch
    refine foldCheck_ne_none V (T := T) hk betas hb proof (by omega) (by omega) (by omega)
      (by rw [hbl, Nat.shiftLeft_eq]; simp) (fun x hx => ?_) (by omega) (fun i hi => ?_)
      (fun i hi => ?_) hF (by rw [hlenI] at hq; rw [hT]; exact hq) (hltI _ (List.getElem_mem _)) hbatch
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hbw j hj
    · rw [(hround i (by omega)).1, Nat.shiftLeft_eq]
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using (hround i (by omega)).2 j hj
  rcases a with e | ⟨⟨⟩⟩ <;> simp

/-! ## An honest coset passes its fold check -/

open Plonky3Lean.Spec.BinaryDft Plonky3Lean.Proofs.BinaryDft in
omit [DecidableEq EF] [Algebra F EF] [DecidableEq F] in
/-- The fold of an honest queried coset is the honest value of the next word.

The rows of the coset are the codeword of d over S_(l+a) at the coset's 2^a points.

The value is the codeword over S_l, in the challenge field, of d with its a lowest variables bound. -/
theorem fold_query_coset_honest {A : Type} [Field A] [CharP A 2] [Algebra A EF] [CharP EF 2] {L : Level A}
    (hL : Cantor L) (hE : Cantor V.LE)
    (hpre : ∀ r < 2 ^ L.logBits, V.LE.cantor r = algebraMap A EF (L.cantor r)) {l a : ℕ}
    (hla : l + a ≤ 2 ^ L.logBits) (hlaE : l + a ≤ 2 ^ V.LE.logBits) (hw : l + a ≤ 64) (d : ℕ → A)
    (bs : List EF) (hbs : bs.length = a) (ha : 0 < a) {np : ℕ} (hnp : np < 2 ^ l)
    (rows : List (List A)) (q : ℕ)
    (hrows : ∀ i < 2 ^ a, rows[q * 2 ^ a + i]? = some [ntt L.cantor (l + a) 0 d (np * 2 ^ a + i)]) :
    fold_query_coset V L rows q np bs = some (ntt V.LE.cantor l 0 (bindAll bs (algebraMap A EF ∘ d)) np) := by
  obtain ⟨b, rest, rfl⟩ : ∃ b rest, bs = b :: rest := by
    cases bs with
    | nil => simp at hbs; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  cases rest with
  | nil =>
    simp only [List.length_cons, List.length_nil, zero_add] at hbs
    subst hbs
    have h0 := hrows 0 (by norm_num)
    have h1 := hrows 1 (by norm_num)
    simp only [pow_one, add_zero] at h0 h1
    simp only [fold_query_coset, show 2 * q = q * 2 by ring, h0, h1,
      Option.bind_eq_bind, Option.bind_some, List.getElem?_cons_zero]
    rw [show np * 2 = 2 * np by ring, fold_pair_ntt hL (by omega) (by omega) d hnp b]
    exact congrArg some (ntt_congr_basis (fun r hr => (hpre r (by omega)).symm) _ _ hnp)
  | cons b' rest =>
    obtain ⟨size, hsize⟩ : ∃ k, k = 2 ^ (b :: b' :: rest).length := ⟨_, rfl⟩
    have hrows' : ∀ i < size, rows[q * size + i]? = some [ntt L.cantor (l + a) 0 d (np * size + i)] := by
      rw [hsize, hbs]; exact hrows
    have hcoset : (rows.drop (q * size)).take size =
        (List.range size).map fun i => [ntt L.cantor (l + a) 0 d (np * size + i)] := by
      refine List.ext_getElem? fun i => ?_
      rw [List.getElem?_take, List.getElem?_drop, List.getElem?_map]
      by_cases hi : i < size
      · simp [hi, hrows' i hi]
      · simp [hi]
    have hlen : ((rows.drop (q * size)).take size).length = size := by rw [hcoset]; simp
    have hg : ((rows.drop (q * size)).take size).mapM (·[0]?) =
        some ((List.range size).map fun i => ntt L.cantor (l + a) 0 d (np * size + i)) := by
      rw [hcoset, List.mapM_map]
      exact mapM_some _ _ _ fun i _ => rfl
    have hfc := fold_coset_ntt hL hE hpre (l := l) (a := a) ha hla hlaE hw d (b :: b' :: rest) hbs hnp
    rw [show 2 ^ a = size by rw [hsize, hbs]] at hfc
    simp only [fold_query_coset, ← hsize, hlen, ne_eq, not_true_eq_false, ite_false,
      Option.bind_eq_bind, hg, Option.bind_some]
    exact hfc

end Plonky3Lean.Proofs.BinaryPcs