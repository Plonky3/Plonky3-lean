module

public import Plonky3Lean.Proofs.Hash.Blake3.Hash

@[expose] public section

/-!
# p3-blake3: the lane digest is the BLAKE3 digest

The model's chunk windows are the specification's chunks, its plain-block chaining value is the
specification's fold over a chunk's blocks, and its split of the tree is the specification's.
-/

open Aeneas Aeneas.Std CoreModels
open Plonky3Lean.Spec.Blake3 Plonky3Lean.Lib

namespace Plonky3Lean.Proofs.Blake3

theorem cvBytes_eq (cv : List Word) (h : cv.length = 8) :
    cvBytes cv = ((cv.take 8).map bytesOfWord).flatten := by
  match cv, h with
  | [a, b, c, d, e, f, g, k], _ => rfl

theorem pow2Below_eq (f n : ℕ) (hn : 2 ≤ n) : pow2Below f n = 2 ^ min f (Nat.log 2 (n - 1)) := by
  induction f with
  | zero => simp [pow2Below]
  | succ f ih =>
    rw [pow2Below, ih]
    by_cases hf : f < Nat.log 2 (n - 1)
    · have h1 : 2 * 2 ^ f < n := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show f + 1 ≤ Nat.log 2 (n - 1) by omega)
        have := Nat.pow_log_le_self 2 (show n - 1 ≠ 0 by omega)
        rw [pow_succ] at *; omega
      rw [Nat.min_eq_left hf.le, ite_eq_left_of_eq_true _ _ (eq_true h1), Nat.min_eq_left (by omega), pow_succ]
      ring
    · have hm : min f (Nat.log 2 (n - 1)) = Nat.log 2 (n - 1) := Nat.min_eq_right (by omega)
      have h1 : ¬ 2 * 2 ^ Nat.log 2 (n - 1) < n := by
        have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) (n - 1)
        rw [pow_succ] at this; omega
      rw [hm, ite_eq_right_of_eq_false _ _ (eq_false h1), Nat.min_eq_right (by omega)]

theorem leftChunks_eq (c : ℕ) (hc : 2 ≤ c) : leftChunks c = pow2Below c c := by
  rw [pow2Below_eq c c hc, Nat.min_eq_right]
  · rfl
  · have := Nat.log_le_self 2 (c - 1); omega

theorem ceil_step (m k : ℕ) (hk : 0 < k) (hm : 0 < m) :
    (m + k - 1) / k = (m - k + k - 1) / k + 1 := by
  by_cases h : k ≤ m
  · rw [show m + k - 1 = (m - k + k - 1) + k by omega, Nat.add_div_right _ hk]
  · rw [show m - k = 0 by omega, Nat.zero_add, Nat.div_eq_of_lt (show k - 1 < k by omega)]
    have h1 : (m + k - 1) / k < 2 := (Nat.div_lt_iff_lt_mul hk).2 (by omega)
    have h2 : 1 ≤ (m + k - 1) / k := (Nat.le_div_iff_mul_le hk).2 (by omega)
    omega

theorem piecesAux_spec (k : ℕ) (hk : 0 < k) (n : ℕ) (l : List (BitVec 8)) (hn : (l.length + k - 1) / k ≤ n) :
    (piecesAux k n l).length = (l.length + k - 1) / k ∧
      ∀ i < (l.length + k - 1) / k, (piecesAux k n l).getD i [] = (l.drop (k * i)).take k := by
  induction n generalizing l with
  | zero =>
    have h0 : (l.length + k - 1) / k = 0 := Nat.le_zero.mp hn
    have hl : l.length = 0 := by
      rcases Nat.div_eq_zero_iff.1 h0 with h | h <;> omega
    rw [h0]; simp [piecesAux]
  | succ n ih =>
    by_cases hl : l = []
    · subst hl
      simp [piecesAux, hk]
    · have hm : 0 < l.length := List.length_pos_iff.2 hl
      have hs := ceil_step l.length k hk hm
      have hd : (l.drop k).length = l.length - k := List.length_drop ..
      obtain ⟨ih1, ih2⟩ := ih (l.drop k) (by rw [hd]; omega)
      rw [hd] at ih1 ih2
      simp only [piecesAux, List.isEmpty_iff, hl, ite_false, List.length_cons, ih1, hs, true_and]
      intro i hi
      rcases i with _ | i
      · simp
      · simp only [List.getD_cons_succ, ih2 i (by omega), List.drop_drop]
        congr 2
        ring

theorem pieces_spec (k : ℕ) (hk : 0 < k) (l : List (BitVec 8)) :
    (pieces k l).length = (if l = [] then 1 else (l.length + k - 1) / k) ∧
      ∀ i < (pieces k l).length, (pieces k l).getD i [] = (l.drop (k * i)).take k := by
  unfold pieces
  by_cases hl : l = []
  · subst hl; simp
  · have hm : 0 < l.length := List.length_pos_iff.2 hl
    have hle : (l.length + k - 1) / k ≤ l.length := by
      have e1 : l.length - 1 ≤ (l.length - 1) * k := Nat.le_mul_of_pos_right _ hk
      have e2 : l.length * k = (l.length - 1) * k + k := by
        rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hm)]
      apply Nat.div_le_of_le_mul
      rw [Nat.mul_comm]; omega
    obtain ⟨h1, h2⟩ := piecesAux_spec k hk l.length l hle
    simp only [List.isEmpty_iff, hl, ite_false, h1]
    exact ⟨trivial, h2⟩

theorem getD_drop' {α : Type} (l : List α) (a p : ℕ) (d : α) : (l.drop a).getD p d = l.getD (a + p) d := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_take' {α : Type} (l : List α) (n p : ℕ) (d : α) :
    (l.take n).getD p d = if p < n then l.getD p d else d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs <;> rfl

theorem blockWords_congr (x y : List (BitVec 8)) (h : ∀ p < 64, x.getD p 0 = y.getD p 0) :
    blockWords x = blockWords y := by
  unfold blockWords
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- The bytes of chunk `idx` of the `len`-byte message at byte `s` of `B`. -/
def chunkAt (B : List (BitVec 8)) (s len idx : ℕ) : List (BitVec 8) :=
  ((((B.drop s).take len).drop (1024 * idx)).take 1024)

theorem length_chunkAt (B : List (BitVec 8)) (s len idx : ℕ) (hB : s + len ≤ B.length) :
    (chunkAt B s len idx).length = min len (idx * 1024 + 1024) - idx * 1024 := by
  simp [chunkAt]; omega

theorem block_getD (B : List (BitVec 8)) (s len idx i p : ℕ) :
    (((chunkAt B s len idx).drop (64 * i)).take 64).getD p 0 =
      if p < 64 ∧ 64 * i + p < 1024 ∧ 1024 * idx + (64 * i + p) < len then
        B.getD (s + (1024 * idx + (64 * i + p))) 0 else 0 := by
  simp only [chunkAt, getD_take', getD_drop']
  by_cases h1 : p < 64 <;> by_cases h2 : 64 * i + p < 1024 <;>
    by_cases h3 : 1024 * idx + (64 * i + p) < len <;> simp [h1, h2, h3]

theorem window_block (B : List (BitVec 8)) (s len idx i k : ℕ) (hk : k ≤ 64)
    (hlo : 64 * i + k ≤ 1024) (hhi : idx * 1024 + 64 * i + k ≤ len)
    (hfull : k < 64 → idx * 1024 + 64 * i + k = len ∨ 64 * i + k = 1024) :
    blockWords (window B (s + (idx * 1024 + 64 * i)) k) =
      blockWords (((chunkAt B s len idx).drop (64 * i)).take 64) := by
  apply blockWords_congr
  intro p hp
  rw [window_getD _ _ _ _ hp, block_getD]
  by_cases h : p < k
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true ⟨hp, by omega, by omega⟩)]
    congr 1; ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false (by
      rintro ⟨-, h2, h3⟩
      have := hfull (by omega)
      omega))]

theorem plainCv_fold (B : List (BitVec 8)) (s len idx P : ℕ) (blocks : List (List (BitVec 8)))
    (hblk : ∀ i < P, blocks.getD i [] = ((chunkAt B s len idx).drop (64 * i)).take 64)
    (hP : idx * 1024 + 64 * P ≤ len) (hP2 : 64 * P ≤ 1024) (k : ℕ) (hk : k ≤ P) :
    (List.range k).foldl (fun cv i => (compress cv (blockWords (blocks.getD i [])) idx 64
        (if i = 0 then CHUNK_START else 0)).take 8) IV = plainCv B (s + idx * 1024) idx k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil, plainCv,
      hblk k (by omega), ← window_block B s len idx k 64 le_rfl (by omega)
        (by generalize idx * 1024 = st at hP ⊢; omega) (by omega),
      Nat.add_assoc]

theorem chunkCv_spec (B : List (BitVec 8)) (s len idx : ℕ) (root : Word) (hB : s + len ≤ B.length)
    (hidx : idx * 1024 ≤ len) :
    chunkCv B s len idx root =
      (compress (chunkOutput (chunkAt B s len idx) idx).cv (chunkOutput (chunkAt B s len idx) idx).block idx
        (chunkOutput (chunkAt B s len idx) idx).blockLen
        ((chunkOutput (chunkAt B s len idx) idx).flags ||| root)).take 8 := by
  have hm := length_chunkAt B s len idx hB
  obtain ⟨hn, hg⟩ := pieces_spec 64 (by norm_num) (chunkAt B s len idx)
  unfold chunkCv chunkOutput
  dsimp only
  generalize hst : idx * 1024 = st at hm hidx ⊢
  generalize he : min len (st + 1024) = e at hm ⊢
  generalize hc : chunkAt B s len idx = C at hm hn hg ⊢
  have he1 : e ≤ len := by omega
  have he2 : st ≤ e := by omega
  have he3 : e ≤ st + 1024 := by omega
  generalize hP : (e - st - 1) / 64 = P
  have hd := Nat.div_mul_le_self (e - st - 1) 64
  have hmd := Nat.lt_div_mul_add (a := e - st - 1) (b := 64) (by norm_num)
  rw [hP] at hd hmd
  have hn' : (pieces 64 C).length = P + 1 := by
    rw [hn]
    by_cases h0 : C = []
    · subst h0; simp at hm; rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]; omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
      have : C.length ≠ 0 := fun h => h0 (List.length_eq_zero_iff.1 h)
      omega
  have hf := plainCv_fold B s len idx P (pieces 64 C) (fun i hi => by rw [hg i (by omega), hc])
    (by rw [hst]; omega) (by omega) P le_rfl
  have hw := window_block B s len idx P (e - (st + P * 64)) (by omega) (by omega) (by rw [hst]; omega)
    (by intro h; rw [hst]; omega)
  rw [hst, hc, Nat.mul_comm 64 P] at hw
  rw [hst] at hf
  have hl : ((pieces 64 C).getD P []).length = e - (st + P * 64) := by
    rw [hg P (by omega)]; simp [hm]; omega
  rw [hn', Nat.add_sub_cancel, hf, hl, hw, hg P (by omega), Nat.mul_comm 64 P]
  congr 3
  simp

/-- A node's chaining value with `root` added to its flags. -/
def compressOut (o : Output) (root : Word) : List Word :=
  (compress o.cv o.block o.counter o.blockLen (o.flags ||| root)).take 8

theorem compressOut_zero (o : Output) : compressOut o 0 = o.chainingValue := by
  simp [compressOut, Output.chainingValue]

theorem treeCv_spec (B : List (BitVec 8)) (s len : ℕ) (hB : s + len ≤ B.length)
    (chunks : List (List (BitVec 8)))
    (hch : ∀ i < chunks.length, chunks.getD i [] = chunkAt B s len i)
    (hidx : ∀ i < chunks.length, i * 1024 ≤ len) (c : ℕ) :
    ∀ (first f : ℕ) (root : Word), 1 ≤ c → first + c ≤ chunks.length → c ≤ f →
      treeCv B s len first c root = compressOut (subtreeOutput f ((chunks.drop first).take c) first) root := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro first f root hc hfc hf
  have hlen : ((chunks.drop first).take c).length = c := by simp; omega
  rw [treeCv]
  by_cases h1 : c = 1
  · subst h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true le_rfl)]
    have hg : ((chunks.drop first).take 1).getD 0 [] = chunkAt B s len first := by
      rw [getD_take', ite_eq_left_of_eq_true _ _ (eq_true (by norm_num)), getD_drop', Nat.add_zero,
        hch first (by omega)]
    have hs : subtreeOutput f ((chunks.drop first).take 1) first = chunkOutput (chunkAt B s len first) first := by
      rcases f with _ | f
      · simp only [subtreeOutput, hg]
      · rw [subtreeOutput, ite_eq_left_of_eq_true _ _ (eq_true (by omega)), hg]
    rw [hs, chunkCv_spec B s len first root hB (hidx first (by omega))]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hL := leftChunks_lt c (by omega)
    have hL0 := leftChunks_pos c
    rw [subtreeOutput, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hlen, ← leftChunks_eq c (by omega)]
    dsimp only
    rw [List.take_take, Nat.min_eq_left hL.le, List.drop_take, List.drop_drop,
      ih (leftChunks c) hL first f' 0 hL0 (by omega) (by omega),
      ih (c - leftChunks c) (by omega) (first + leftChunks c) f' 0 (by omega) (by omega) (by omega),
      compressOut_zero, compressOut_zero]
    simp only [compressOut, parentOutput]

theorem subtreeOutput_counter (f : ℕ) (l : List (List (BitVec 8))) : (subtreeOutput f l 0).counter = 0 := by
  rcases f with _ | f
  · rfl
  · rw [subtreeOutput]; split <;> rfl

/-- The lane digest is the BLAKE3 digest of the lane's message. -/
theorem laneDigest_eq (B : List (BitVec 8)) (s len : ℕ) (hB : s + len ≤ B.length) :
    laneDigest B s len = digest ((B.drop s).take len) := by
  have hml : ((B.drop s).take len).length = len := by simp; omega
  obtain ⟨hn, hg⟩ := pieces_spec 1024 (by norm_num) ((B.drop s).take len)
  have hN : (pieces 1024 ((B.drop s).take len)).length = nchunks len := by
    rw [hn, hml, nchunks]
    by_cases h0 : len = 0
    · have : (B.drop s).take len = [] := List.length_eq_zero_iff.1 (by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true this), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    · have : (B.drop s).take len ≠ [] := fun h => h0 (by rw [← hml, h]; rfl)
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
      split_ifs with h
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
      · rfl
  unfold laneDigest digest
  dsimp only
  rw [treeCv_spec B s len hB (pieces 1024 ((B.drop s).take len)) (fun i hi => hg i hi)
      (fun i hi => by
        rw [hN, nchunks] at hi
        split_ifs at hi with h
        · omega
        · have := (Nat.lt_div_iff_mul_lt (by norm_num)).1 hi
          omega)
      (nchunks len) 0 (nchunks len) ROOT (by unfold nchunks; split_ifs <;> omega) (by omega) le_rfl,
    ← hN, List.drop_zero, List.take_length,
    cvBytes_eq _ (by simp [compressOut, compress])]
  simp only [compressOut, Output.rootBytes, subtreeOutput_counter, List.take_take, Nat.min_self]

/-- The hasher's `hash_many`: each digest is the BLAKE3 digest of its message. -/
theorem hash_many_spec (self : p3_blake3.Blake3) (input : Slice Std.U8)
    (out : Slice (Std.Array Std.U8 32#usize)) (len : ℕ) (hn : 0 < out.val.length)
    (hlen : input.val.length = out.val.length * len) (h32 : input.val.length + 1024 < 2 ^ 32)
    (hn32 : out.val.length < 2 ^ 32) :
    ∃ r, p3_blake3.Blake3.Insts.P3_symmetricHasherCryptographicHasherU8ArrayU832.hash_many self input out = .ok r ∧
      r.val.map (fun a => a.val.map UScalar.bv) = (List.range out.val.length).map fun i =>
        digest (((input.val.map UScalar.bv).drop (i * len)).take len) := by
  obtain ⟨r, e, hr⟩ := hash_many_eq input out len hn hlen h32 hn32
  refine ⟨r, e, ?_⟩
  rw [hr, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  have hB : i * len + len ≤ (sbytes input).length := by
    simp only [sbytes, List.length_map, hlen]
    have := Nat.mul_le_mul_right len (show i + 1 ≤ out.val.length by omega)
    rw [Nat.add_mul, one_mul] at this; exact this
  simp only [Function.comp, digestArr]
  rw [barr_val _ _ (by simp [laneDigest, cvBytes]), List.map_map]
  have hid : (UScalar.bv ∘ fun b : BitVec 8 => (⟨b⟩ : Std.U8)) = id := rfl
  rw [hid, List.map_id, laneDigest_eq _ _ _ hB]
  rfl

end Plonky3Lean.Proofs.Blake3
