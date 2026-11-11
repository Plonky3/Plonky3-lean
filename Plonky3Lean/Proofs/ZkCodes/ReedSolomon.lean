module

public import P3ZkCodes
public import Plonky3Lean.Proofs.Dft.Basic
public import Plonky3Lean.Proofs.ZkCodes.Hiding

@[expose] public section

/-!
# The Reed-Solomon transcriptions against the encoding of Proposition 3.19

The constructor, the evaluation points, the generating-matrix rows and the explicit-randomness encoding.
-/

set_option linter.unusedSectionVars false

namespace Plonky3Lean.Proofs.ZkCodes

open Finset Polynomial p3_dft.mirror Plonky3Lean.Spec.Dft Plonky3Lean.Spec.ZkCodes
open p3_zk_codes.reed_solomon.mirror Plonky3Lean.Proofs.Dft

variable {K : Type _} [Field K]

/-! ## The constructor -/

theorem isPow2_iff (m : ℕ) : (m ≠ 0 ∧ 2 ^ Nat.log 2 m = m) ↔ ∃ k, m = 2 ^ k := by
  constructor
  · rintro ⟨-, h⟩; exact ⟨_, h.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨by positivity, by rw [Nat.log_pow (by norm_num)]⟩

theorem new_eq_some {t l k : ℕ} (hle : l + t ≤ 2 ^ k) (hk : k < 64) :
    ReedSolomonZkEncoding.new t l (2 ^ k) = some ⟨t, l, 2 ^ k⟩ := by
  have h64 : l + t < 2 ^ 64 := lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by norm_num) hk)
  simp [ReedSolomonZkEncoding.new, hle]
  simpa using h64

theorem new_eq_none_of_not_pow {t l m : ℕ} (hm : ∀ k, m ≠ 2 ^ k) :
    ReedSolomonZkEncoding.new t l m = none := by
  have : ¬ (m ≠ 0 ∧ 2 ^ Nat.log 2 m = m) := fun h =>
    let ⟨k, hk⟩ := (isPow2_iff m).mp h; hm k hk
  simp [ReedSolomonZkEncoding.new, this]

theorem new_eq_none_of_lt {t l m : ℕ} (hm : m < l + t) : ReedSolomonZkEncoding.new t l m = none := by
  unfold ReedSolomonZkEncoding.new
  split_ifs <;> first | rfl | omega

/-- A configuration the constructor returns: m = 2^k and l + t <= m. -/
theorem new_eq_some_iff {t l m : ℕ} {rs : ReedSolomonZkEncoding} :
    ReedSolomonZkEncoding.new t l m = some rs ↔
      (∃ k, m = 2 ^ k) ∧ l + t ≤ m ∧ l + t < 2 ^ 64 ∧ rs = ⟨t, l, m⟩ := by
  unfold ReedSolomonZkEncoding.new
  split_ifs with h1 h2 h3
  · rw [isPow2_iff] at h1
    simp only [Option.some.injEq]
    exact ⟨fun h => ⟨h1, h3, h2, h.symm⟩, fun h => h.2.2.2.symm⟩
  · simp only [false_iff]; omega
  · simp only [false_iff]; omega
  · rw [isPow2_iff] at h1
    simp only [false_iff]
    exact fun h => h1 h.1

/-! ## Evaluation points and rows -/

theorem evaluation_point_eq (G : Gen K) {t l k : ℕ} (hk : k ≤ G.adicity) (p : ℕ) :
    (ReedSolomonZkEncoding.mk t l (2 ^ k)).evaluation_point G p = some (G.gen k ^ p) := by
  simp [ReedSolomonZkEncoding.evaluation_point, log2Strict_pow, gen_get_of_le G hk]

theorem evaluation_point_none (G : Gen K) {t l k : ℕ} (hk : G.adicity < k) (p : ℕ) :
    (ReedSolomonZkEncoding.mk t l (2 ^ k)).evaluation_point G p = none := by
  simp [ReedSolomonZkEncoding.evaluation_point, log2Strict_pow, gen_get_of_lt G hk]

/-- A primitive m-th root repeats with period m. -/
theorem pow_mod_of_primitive {ω : K} {m : ℕ} (hω : IsPrimitiveRoot ω m) (p : ℕ) :
    ω ^ p = ω ^ (p % m) := by
  conv_lhs => rw [← Nat.div_add_mod p m, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul]

theorem successorsTake_some (x a : K) (n : ℕ) :
    successorsTake (· * x) (some a) n = (List.range n).map fun j => a * x ^ j := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [successorsTake, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [pow_zero, mul_one, List.cons.injEq, true_and]
    refine List.map_congr_left fun j _ => ?_
    simp [Function.comp, pow_succ]; ring

theorem message_row_eq (G : Gen K) {t l k : ℕ} (hk : k ≤ G.adicity) (p : ℕ) :
    (ReedSolomonZkEncoding.mk t l (2 ^ k)).message_row G p =
      some ((List.range l).map fun j => (G.gen k ^ p) ^ j) := by
  simp [ReedSolomonZkEncoding.message_row, ReedSolomonZkEncoding.message_row_iter,
    evaluation_point_eq G hk, powersList]

theorem randomness_row_eq (G : Gen K) {t l k : ℕ} (hk : k ≤ G.adicity) (p : ℕ) :
    (ReedSolomonZkEncoding.mk t l (2 ^ k)).randomness_row G p =
      some ((List.range t).map fun j => (G.gen k ^ p) ^ (l + j)) := by
  simp only [ReedSolomonZkEncoding.randomness_row, ReedSolomonZkEncoding.randomness_row_iter,
    evaluation_point_eq G hk, Option.pure_def]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [successorsTake]
  · simp [ht, successorsTake_some, pow_add]

/-! ## The explicit-randomness encoding -/

/-- The coefficient vector: the message, then the randomness, then zeros. -/
theorem getD_resize {msg r : List K} {m : ℕ} (hm : msg.length + r.length ≤ m) (j : ℕ) :
    (resize (msg ++ r) m).getD j 0 =
      if j < msg.length then msg.getD j 0
      else if j < msg.length + r.length then r.getD (j - msg.length) 0 else 0 := by
  have hlen : (msg ++ r).length ≤ m := by simpa using hm
  unfold resize
  rw [List.take_of_length_le hlen]
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : j < msg.length
  · simp only [h1, ↓reduceIte]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left h1,
      List.getD_eq_getElem?_getD]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : j < msg.length + r.length
    · simp only [h2, ↓reduceIte]
      rw [List.getElem?_append_left (by simp; omega),
        List.getElem?_append_right (by omega), List.getD_eq_getElem?_getD]
    · simp only [h2, ↓reduceIte]
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.getElem?_replicate]
      split_ifs <;> rfl

/-- The transform of the coefficient vector is the message part plus the mask part, at omega^i. -/
theorem dft_coeffs (ω : K) {msg r : List K} {m : ℕ} (hm : msg.length + r.length ≤ m) (i : ℕ) :
    dft ω m (fun j => (resize (msg ++ r) m).getD j 0) i =
      ∑ j ∈ range msg.length, msg.getD j 0 * (ω ^ i) ^ j +
        ∑ j ∈ range r.length, r.getD j 0 * (ω ^ i) ^ (msg.length + j) := by
  unfold dft
  have hsplit : m = msg.length + r.length + (m - (msg.length + r.length)) := by omega
  rw [show range m = range (msg.length + r.length + (m - (msg.length + r.length))) by
    rw [← hsplit], sum_range_add, sum_range_add, sum_eq_zero (s := range (m - _)) fun j _ => by
    dsimp only; rw [getD_resize hm]; simp only [show ¬ (msg.length + r.length + j < msg.length) by omega,
      show ¬ (msg.length + r.length + j < msg.length + r.length) by omega, ↓reduceIte, smul_zero],
    add_zero]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    dsimp only; rw [getD_resize hm]
    simp only [mem_range.mp hj, ↓reduceIte, smul_eq_mul, ← pow_mul]
    rw [mul_comm]
  · refine sum_congr rfl fun j hj => ?_
    dsimp only; rw [getD_resize hm]
    simp only [show ¬ (msg.length + j < msg.length) by omega,
      show msg.length + j < msg.length + r.length by simp at hj; omega, ↓reduceIte, smul_eq_mul,
      ← pow_mul, Nat.add_sub_cancel_left]
    rw [mul_comm]

/-- The value of the encoding at a point: sum_j msg_j x^j + sum_j r_j x^(l+j). -/
def encValue (msg r : List K) (x : K) : K :=
  ∑ j ∈ range msg.length, msg.getD j 0 * x ^ j + ∑ j ∈ range r.length, r.getD j 0 * x ^ (msg.length + j)

/-- With a backend that computes the transform at omega, the encoding evaluates the polynomial at omega^i. -/
theorem encode_with_randomness_computes {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)} {ω : K}
    {rs : ReedSolomonZkEncoding} (hd : ∀ x, Computes (dft_batch rs.m x) rs.m (dft ω rs.m x))
    (hle : rs.msg_len + rs.t ≤ rs.m) {msg r : List K} (hmsg : msg.length = rs.msg_len)
    (hr : r.length = rs.t) :
    Computes (rs.encode_with_randomness dft_batch msg r) rs.m (fun i => encValue msg r (ω ^ i)) := by
  obtain ⟨y, hy, hyi⟩ := hd (fun i => (resize (msg ++ r) rs.m).getD i 0)
  refine ⟨y, ?_, fun i hi => ?_⟩
  · simp only [ReedSolomonZkEncoding.encode_with_randomness, hmsg, hr, ne_eq, not_true_eq_false,
      ↓reduceIte]
    exact hy
  · rw [hyi i hi, dft_coeffs ω (by omega)]; rfl

/-- A message of the wrong length panics. -/
theorem encode_with_randomness_msg_len (dft_batch : ℕ → (ℕ → K) → Option (ℕ → K))
    (rs : ReedSolomonZkEncoding) {msg : List K} (h : msg.length ≠ rs.msg_len) (r : List K) :
    rs.encode_with_randomness dft_batch msg r = none := by
  simp [ReedSolomonZkEncoding.encode_with_randomness, h]

/-- A randomness of the wrong length panics. -/
theorem encode_with_randomness_rand_len (dft_batch : ℕ → (ℕ → K) → Option (ℕ → K))
    (rs : ReedSolomonZkEncoding) (msg : List K) {r : List K} (h : r.length ≠ rs.t) :
    rs.encode_with_randomness dft_batch msg r = none := by
  simp only [ReedSolomonZkEncoding.encode_with_randomness]
  split_ifs <;> rfl

/-- When the backend panics on height m, so does the encoding. -/
theorem encode_with_randomness_dft_none {dft_batch : ℕ → (ℕ → K) → Option (ℕ → K)}
    {rs : ReedSolomonZkEncoding} (hd : ∀ x, dft_batch rs.m x = none) (msg r : List K) :
    rs.encode_with_randomness dft_batch msg r = none := by
  simp only [ReedSolomonZkEncoding.encode_with_randomness]
  split_ifs <;> simp [hd]

/-- The list value at a point is the polynomial of Proposition 3.19, for vectors written as lists. -/
theorem encValue_ofFn {l t : ℕ} (f : Fin l → K) (ρ : Fin t → K) (x : K) :
    encValue (List.ofFn f) (List.ofFn ρ) x = (rsZkPoly f ρ).eval x := by
  rw [rsZkPoly_eval, encValue, msgEval, List.length_ofFn, List.length_ofFn,
    ← Fin.sum_univ_eq_sum_range (fun j => (List.ofFn f).getD j 0 * x ^ j),
    ← Fin.sum_univ_eq_sum_range (fun j => (List.ofFn ρ).getD j 0 * x ^ (l + j))]
  simp [List.getD_eq_getElem?_getD]

theorem sum_zipWith_range (g : ℕ → K) (a : List K) :
    (List.zipWith (· * ·) ((List.range a.length).map g) a).sum =
      ∑ j ∈ range a.length, g j * a.getD j 0 := by
  induction a using List.reverseRecOn with
  | nil => simp
  | append_singleton a x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
      List.zipWith_append (by simp), List.sum_append, ih, sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
      List.sum_cons, List.sum_nil, add_zero]
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      rw [List.getD_append _ _ _ _ (mem_range.mp hj)]
    · simp

/-- The list value at a point is the generating-matrix row times the message plus the row times the randomness. -/
theorem encValue_rows (msg r : List K) (x : K) :
    encValue msg r x =
      (List.zipWith (· * ·) ((List.range msg.length).map fun j => x ^ j) msg).sum +
        (List.zipWith (· * ·) ((List.range r.length).map fun j => x ^ (msg.length + j)) r).sum := by
  rw [sum_zipWith_range, sum_zipWith_range, encValue]
  congr 1 <;> exact sum_congr rfl fun j _ => mul_comm _ _

end Plonky3Lean.Proofs.ZkCodes
