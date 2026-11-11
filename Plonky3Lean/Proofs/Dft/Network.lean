module

public import P3Dft
public import Plonky3Lean.Spec.Dft
public import Plonky3Lean.Proofs.Matrix.BitRev
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# Butterfly networks

A layer of a radix-2 network splits the rows into blocks of 2m and pairs row s of each block with row s + m.

The iterative Cooley-Tukey transform runs decimation-in-time layers on bit-reversed input.

The Gentleman-Sande transform runs decimation-in-frequency layers and leaves its output bit-reversed.

Both follow Cooley and Tukey (1965) and Cormen et al., Introduction to Algorithms, section 30.3.
-/

namespace Plonky3Lean.Proofs.Dft

open Finset p3_dft.mirror Plonky3Lean.Spec.Dft

/-! ## The two bit reversals agree -/

theorem bitRev_eq : p3_dft.mirror.bitRev = Plonky3Lean.Spec.Matrix.bitRev := by
  funext k i
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [p3_dft.mirror.bitRev, Plonky3Lean.Spec.Matrix.bitRev, ih]

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

theorem rev_double (j B : ℕ) : rev (j + 1) (2 * B) = rev j B := by
  simp only [Plonky3Lean.Spec.Matrix.bitRev]
  rw [show 2 * B % 2 = 0 by omega, show 2 * B / 2 = B by omega]
  ring

theorem rev_double_add_one (j B : ℕ) : rev (j + 1) (2 * B + 1) = 2 ^ j + rev j B := by
  simp only [Plonky3Lean.Spec.Matrix.bitRev]
  rw [show (2 * B + 1) % 2 = 1 by omega, show (2 * B + 1) / 2 = B by omega]
  ring

/-- Reversing a + b bits of B 2^a + r, for r < 2^a, puts the a-bit reversal of r on top. -/
theorem rev_split (a b B r : ℕ) (hr : r < 2 ^ a) :
    rev (a + b) (B * 2 ^ a + r) = rev a r * 2 ^ b + rev b B := by
  induction a generalizing r with
  | zero =>
    simp at hr; subst hr; simp [Plonky3Lean.Spec.Matrix.bitRev]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by ring]
    simp only [Plonky3Lean.Spec.Matrix.bitRev]
    have h1 : (B * 2 ^ (a + 1) + r) % 2 = r % 2 := by
      rw [pow_succ, ← mul_assoc]; omega
    have h2 : (B * 2 ^ (a + 1) + r) / 2 = B * 2 ^ a + r / 2 := by
      rw [pow_succ, ← mul_assoc]; omega
    rw [h1, h2, ih (r / 2) (by rw [pow_succ] at hr; omega)]
    ring

/-! ## Folding butterflies over disjoint pairs -/

section fold

variable {V : Type _}

/-- The rows a list of butterflies touches. -/
def touched (L : List (ℕ × ℕ × (V → V → V × V))) : List ℕ := L.flatMap fun e => [e.1, e.2.1]

/-- Run a list of butterflies in order. -/
def runB (L : List (ℕ × ℕ × (V → V → V × V))) (x : ℕ → V) : ℕ → V :=
  L.foldl (fun acc e => bfly e.2.2 e.1 e.2.1 acc) x

theorem runB_cons (e : ℕ × ℕ × (V → V → V × V)) (L) (x : ℕ → V) :
    runB (e :: L) x = runB L (bfly e.2.2 e.1 e.2.1 x) := rfl

theorem runB_untouched (L : List (ℕ × ℕ × (V → V → V × V))) (x : ℕ → V) (i : ℕ)
    (hi : i ∉ touched L) : runB L x i = x i := by
  induction L generalizing x with
  | nil => rfl
  | cons e L ih =>
    simp only [touched, List.flatMap_cons, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, not_or] at hi
    rw [runB_cons, ih _ hi.2]
    simp [bfly, hi.1.1, hi.1.2]

theorem runB_pair (L : List (ℕ × ℕ × (V → V → V × V))) (x : ℕ → V)
    (hnd : (touched L).Nodup) (e) (he : e ∈ L) :
    runB L x e.1 = (e.2.2 (x e.1) (x e.2.1)).1 ∧ runB L x e.2.1 = (e.2.2 (x e.1) (x e.2.1)).2 := by
  induction L generalizing x with
  | nil => simp at he
  | cons e' L ih =>
    simp only [touched, List.flatMap_cons, List.nodup_append, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨hne, -⟩, hL, hdisj⟩ := hnd
    have hp : e'.1 ∉ touched L := fun h => hdisj _ (by simp) _ h rfl
    have hq : e'.2.1 ∉ touched L := fun h => hdisj _ (by simp) _ h rfl
    rw [runB_cons]
    rcases List.mem_cons.mp he with rfl | he
    · rw [runB_untouched _ _ _ hp, runB_untouched _ _ _ hq]
      simp [bfly, Ne.symm hne]
    · have hep : e.1 ∈ touched L := List.mem_flatMap.mpr ⟨e, he, by simp⟩
      have heq : e.2.1 ∈ touched L := List.mem_flatMap.mpr ⟨e, he, by simp⟩
      have h1 : e.1 ≠ e'.1 := fun h => hp (h ▸ hep)
      have h2 : e.1 ≠ e'.2.1 := fun h => hq (h ▸ hep)
      have h3 : e.2.1 ≠ e'.1 := fun h => hp (h ▸ heq)
      have h4 : e.2.1 ≠ e'.2.1 := fun h => hq (h ▸ heq)
      rw [(ih _ hL he).1, (ih _ hL he).2]
      simp [bfly, h1, h2, h3, h4]

/-! ## Layers -/

/-- One layer: nb blocks of 2m rows, with op b s applied to rows (b 2m + s, b 2m + s + m). -/
def layer (op : ℕ → ℕ → V → V → V × V) (m nb : ℕ) (x : ℕ → V) : ℕ → V := fun i =>
  if i < nb * (2 * m) then
    if i % (2 * m) < m then (op (i / (2 * m)) (i % (2 * m)) (x i) (x (i + m))).1
    else (op (i / (2 * m)) (i % (2 * m) - m) (x (i - m)) (x i)).2
  else x i

theorem block_inj {m b b' s s' : ℕ} (hs : s < 2 * m) (hs' : s' < 2 * m)
    (h : b * (2 * m) + s = b' * (2 * m) + s') : b = b' ∧ s = s' := by
  have hm : 0 < 2 * m := by omega
  have e1 := congrArg (· / (2 * m)) h
  have e2 := congrArg (· % (2 * m)) h
  simp only [Nat.mul_comm b, Nat.mul_comm b', Nat.mul_add_div hm, Nat.div_eq_of_lt hs,
    Nat.div_eq_of_lt hs', Nat.mul_add_mod, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hs',
    add_zero] at e1 e2
  exact ⟨e1, e2⟩

/-- The butterflies of one layer, visited in the order of a list of (block, offset) pairs. -/
def layerList (op : ℕ → ℕ → V → V → V × V) (m : ℕ) (order : List (ℕ × ℕ)) :
    List (ℕ × ℕ × (V → V → V × V)) :=
  order.map fun bs => (bs.1 * (2 * m) + bs.2, bs.1 * (2 * m) + bs.2 + m, op bs.1 bs.2)

/-- Running a layer's butterflies, in any order that visits each (block, offset) once, gives the layer. -/
theorem runB_layerList (op : ℕ → ℕ → V → V → V × V) (m nb : ℕ) (hm : 0 < m)
    (order : List (ℕ × ℕ)) (hnd : order.Nodup)
    (hmem : ∀ b s, (b, s) ∈ order ↔ b < nb ∧ s < m) (x : ℕ → V) :
    runB (layerList op m order) x = layer op m nb x := by
  have hT : (touched (layerList op m order)).Nodup := by
    unfold touched layerList
    rw [List.flatMap_map, List.nodup_flatMap]
    refine ⟨fun bs _ => by simp; omega, ?_⟩
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp hnd)
    rintro ⟨b, s⟩ ⟨b', s'⟩ h1 h2 hne
    have hs := ((hmem b s).mp h1).2
    have hs' := ((hmem b' s').mp h2).2
    simp only [Function.onFun, List.disjoint_cons_left, List.mem_cons, List.not_mem_nil,
      or_false, List.disjoint_nil_left, and_true, not_or]
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_, fun h => ?_⟩
    · obtain ⟨rfl, rfl⟩ := block_inj (m := m) (b := b) (b' := b') (by omega) (by omega) h
      exact hne rfl
    · have := block_inj (m := m) (b := b) (b' := b') (s := s) (s' := s' + m) (by omega) (by omega)
        (by omega)
      omega
    · have := block_inj (m := m) (b := b) (b' := b') (s := s + m) (s' := s') (by omega) (by omega)
        (by omega)
      omega
    · obtain ⟨rfl, h⟩ := block_inj (m := m) (b := b) (b' := b') (s := s + m) (s' := s' + m)
        (by omega) (by omega) (by omega)
      exact hne (by simp; omega)
  funext i
  have hm2 : 0 < 2 * m := by omega
  unfold layer
  split_ifs with hi hr
  · have hb : i / (2 * m) < nb := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
    have he : ((i / (2 * m)) * (2 * m) + i % (2 * m), (i / (2 * m)) * (2 * m) + i % (2 * m) + m,
        op (i / (2 * m)) (i % (2 * m))) ∈ layerList op m order :=
      List.mem_map.mpr ⟨_, (hmem _ _).mpr ⟨hb, hr⟩, rfl⟩
    have := (runB_pair _ x hT _ he).1
    simp only [Nat.div_add_mod'] at this
    rw [this]
  · have hb : i / (2 * m) < nb := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
    have hlt : i % (2 * m) < 2 * m := Nat.mod_lt _ hm2
    have he : ((i / (2 * m)) * (2 * m) + (i % (2 * m) - m),
        (i / (2 * m)) * (2 * m) + (i % (2 * m) - m) + m,
        op (i / (2 * m)) (i % (2 * m) - m)) ∈ layerList op m order :=
      List.mem_map.mpr ⟨_, (hmem _ _).mpr ⟨hb, by omega⟩, rfl⟩
    have := (runB_pair _ x hT _ he).2
    have hd := Nat.div_add_mod' i (2 * m)
    have e1 : i / (2 * m) * (2 * m) + (i % (2 * m) - m) + m = i := by omega
    have e2 : i / (2 * m) * (2 * m) + (i % (2 * m) - m) = i - m := by omega
    rw [e1, e2] at this
    rw [this]
  · rw [runB_untouched]
    unfold touched layerList
    simp only [List.flatMap_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
      not_exists, not_and, Prod.forall]
    intro b s h
    obtain ⟨hb, hs⟩ := (hmem b s).mp h
    have : (b + 1) * (2 * m) ≤ nb * (2 * m) := Nat.mul_le_mul_right _ hb
    have h1 : b * (2 * m) + s < nb * (2 * m) := by nlinarith
    have h2 : b * (2 * m) + s + m < nb * (2 * m) := by nlinarith
    exact fun hc => hc.elim (fun hc => hi (hc ▸ h1)) (fun hc => hi (hc ▸ h2))

/-- The (block, offset) pairs of nb blocks of m offsets, blocks outer and offsets inner. -/
def blockOrder (nb m : ℕ) : List (ℕ × ℕ) :=
  (List.range nb).flatMap fun b => (List.range m).map fun s => (b, s)

theorem blockOrder_nodup (nb m : ℕ) : (blockOrder nb m).Nodup := by
  unfold blockOrder
  rw [List.nodup_flatMap]
  refine ⟨fun b _ => (List.nodup_range).map (fun _ _ h => by simpa using h), ?_⟩
  refine List.Pairwise.imp_of_mem ?_ (List.nodup_iff_pairwise_ne.mp List.nodup_range)
  intro b b' _ _ hne
  simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range]
  rintro _ ⟨s, _, rfl⟩ ⟨s', _, h⟩
  exact hne (congrArg Prod.fst h).symm

theorem mem_blockOrder (nb m b s : ℕ) : (b, s) ∈ blockOrder nb m ↔ b < nb ∧ s < m := by
  simp [blockOrder]

end fold

variable {K : Type _} [Field K] {V : Type _} [AddCommGroup V] [Module K V]

theorem pow_period {ω : K} {P : ℕ} (h : ω ^ P = 1) (a b : ℕ) : ω ^ (P * a + b) = ω ^ b := by
  rw [pow_add, pow_mul, h, one_pow, one_mul]

theorem pow_half {ω : K} {H : ℕ} (h : ω ^ H = -1) (b : ℕ) : ω ^ (H + b) = -ω ^ b := by
  rw [pow_add, h, neg_one_mul]

/-! ## The butterflies -/

/-- The decimation-in-time butterfly (a + t b, a - t b). -/
def dit (t : K) (a b : V) : V × V := (a + t • b, a - t • b)

/-- The decimation-in-frequency butterfly (a + b, t (a - b)). -/
def dif (t : K) (a b : V) : V × V := (a + b, t • (a - b))

/-- A decimation-in-time layer with twiddle t b s at block b, offset s. -/
def ditLayer (m nb : ℕ) (t : ℕ → ℕ → K) : (ℕ → V) → ℕ → V := layer (fun b s => dit (t b s)) m nb

/-- A decimation-in-frequency layer with twiddle t b s at block b, offset s. -/
def difLayer (m nb : ℕ) (t : ℕ → ℕ → K) : (ℕ → V) → ℕ → V := layer (fun b s => dif (t b s)) m nb

/-! ## Sums over even and odd indices -/

theorem sum_range_two_mul (n : ℕ) (f : ℕ → V) :
    ∑ m ∈ range (2 * n), f m = ∑ m ∈ range n, f (2 * m) + ∑ m ∈ range n, f (2 * m + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    abel

theorem neg_one_of_primitive {ω : K} {j : ℕ} (hω : IsPrimitiveRoot ω (2 ^ (j + 1))) :
    ω ^ (2 ^ j) = -1 := by
  have h2 : IsPrimitiveRoot (ω ^ 2 ^ j) 2 := by
    have := hω.pow_of_dvd (by positivity : (2 ^ j) ≠ 0) (by rw [pow_succ]; exact dvd_mul_right _ _)
    rwa [pow_succ, Nat.mul_div_cancel_left _ (by positivity)] at this
  exact h2.eq_neg_one_of_two_right

/-! ## Decimation in time -/

/-- The first L decimation-in-time layers of the transform of size 2^k at the root omega.

Layer l has blocks of 2^(l+1) rows and twiddle omega^(s 2^(k-1-l)) at offset s. -/
def ditNet (ω : K) (k : ℕ) : ℕ → (ℕ → V) → ℕ → V
  | 0, x => x
  | l + 1, x => ditLayer (2 ^ l) (2 ^ (k - 1 - l)) (fun _ s => ω ^ (s * 2 ^ (k - 1 - l)))
      (ditNet ω k l x)

/-- After L layers on bit-reversed input, each block of 2^L rows is the transform of a subsequence.

Block b holds the entries rev_(k-L)(b) + 2^(k-L) m, for m < 2^L, transformed at omega^(2^(k-L)). -/
theorem ditNet_apply {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → V) :
    ∀ L ≤ k, ∀ b < 2 ^ (k - L), ∀ t < 2 ^ L,
      ditNet ω k L (bitRevVec (rev k) x) (b * 2 ^ L + t) =
        ∑ m ∈ range (2 ^ L), (ω ^ (2 ^ (k - L) * t * m)) • x (rev (k - L) b + 2 ^ (k - L) * m) := by
  intro L
  induction L with
  | zero =>
    intro _ b _ t ht
    simp at ht; subst ht
    simp [ditNet, bitRevVec]
  | succ L ih =>
    intro hL B hB r hr
    obtain ⟨j, rfl⟩ : ∃ j, k = L + 1 + j := ⟨k - (L + 1), by omega⟩
    have e1 : L + 1 + j - (L + 1) = j := by omega
    have e2 : L + 1 + j - L = j + 1 := by omega
    have e3 : L + 1 + j - 1 - L = j := by omega
    rw [e1] at hB ⊢
    have ih' := ih (by omega)
    rw [e2] at ih'
    have hneg : ω ^ (2 ^ (L + j)) = -1 :=
      neg_one_of_primitive (j := L + j) (by rw [show L + j + 1 = L + 1 + j by ring]; exact hω)
    simp only [ditNet, ditLayer, layer, e3, dit]
    have hsz : B * 2 ^ (L + 1) + r < 2 ^ j * (2 * 2 ^ L) := by
      have : (B + 1) * 2 ^ (L + 1) ≤ 2 ^ j * 2 ^ (L + 1) := Nat.mul_le_mul_right _ hB
      have hr' : r < 2 ^ L * 2 := by rw [← pow_succ]; exact hr
      rw [pow_succ] at this ⊢; nlinarith
    have hmod : (B * 2 ^ (L + 1) + r) % (2 * 2 ^ L) = r := by
      rw [show 2 * 2 ^ L = 2 ^ (L + 1) by ring, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    simp only [hsz, ↓reduceIte, hmod]
    have hsplit : ∀ f : ℕ → V, ∑ m ∈ range (2 ^ (L + 1)), f m =
        ∑ m ∈ range (2 ^ L), f (2 * m) + ∑ m ∈ range (2 ^ L), f (2 * m + 1) := fun f => by
      rw [pow_succ, mul_comm, sum_range_two_mul]
    rw [hsplit]
    split_ifs with hrl
    · -- the upper row of the pair
      have i1 : B * 2 ^ (L + 1) + r = (2 * B) * 2 ^ L + r := by ring
      have i2 : B * 2 ^ (L + 1) + r + 2 ^ L = (2 * B + 1) * 2 ^ L + r := by ring
      rw [i2, i1, ih' (2 * B) (by rw [pow_succ]; omega) r hrl,
        ih' (2 * B + 1) (by rw [pow_succ]; omega) r hrl, rev_double, rev_double_add_one, smul_sum]
      congr 1
      · refine sum_congr rfl fun m _ => ?_
        congr 2
        · ring
        · ring
      · refine sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← pow_add]
        congr 2
        · ring
        · ring
    · -- the lower row of the pair
      obtain ⟨t, rfl⟩ : ∃ t, r = 2 ^ L + t := ⟨r - 2 ^ L, by omega⟩
      have ht : t < 2 ^ L := by rw [pow_succ] at hr; omega
      have i1 : B * 2 ^ (L + 1) + (2 ^ L + t) - 2 ^ L = (2 * B) * 2 ^ L + t := by
        rw [pow_succ]; ring_nf; omega
      have i2 : B * 2 ^ (L + 1) + (2 ^ L + t) = (2 * B + 1) * 2 ^ L + t := by ring
      rw [i1, i2, ih' (2 * B) (by rw [pow_succ]; omega) t ht,
        ih' (2 * B + 1) (by rw [pow_succ]; omega) t ht, rev_double, rev_double_add_one, smul_sum,
        show 2 ^ L + t - 2 ^ L = t by omega, sub_eq_add_neg, ← sum_neg_distrib]
      have hone : ω ^ (2 ^ (L + 1 + j)) = 1 := hω.pow_eq_one
      congr 1
      · refine sum_congr rfl fun m _ => ?_
        congr 1
        · rw [show 2 ^ j * (2 ^ L + t) * (2 * m) = 2 ^ (L + 1 + j) * m + 2 ^ (j + 1) * t * m by
            ring, pow_period hone m]
        · congr 1; ring
      · refine sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← pow_add, ← neg_smul]
        congr 1
        · rw [show 2 ^ j * (2 ^ L + t) * (2 * m + 1) = 2 ^ (L + 1 + j) * m +
            (2 ^ (L + j) + (t * 2 ^ j + 2 ^ (j + 1) * t * m)) by ring,
            pow_period hone m, pow_half hneg]
        · congr 1; ring

/-- The iterative Cooley-Tukey transform: k decimation-in-time layers on bit-reversed input. -/
theorem ditNet_eq_dft {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → V) {i : ℕ}
    (hi : i < 2 ^ k) : ditNet ω k k (bitRevVec (rev k) x) i = dft ω (2 ^ k) x i := by
  have := ditNet_apply hω x k le_rfl 0 (by simp) i hi
  simp only [zero_mul, zero_add, Nat.sub_self, pow_zero, one_mul] at this
  rw [this, dft]
  refine sum_congr rfl fun m _ => ?_
  simp [Plonky3Lean.Spec.Matrix.bitRev]

/-! ## Decimation in frequency -/

/-- The first c decimation-in-frequency layers of the transform of size 2^k at the root omega.

They are the layers with blocks of 2^k, 2^(k-1), and so on down.

The layer with half block 2^l has twiddle omega^(s 2^(k-1-l)) at offset s. -/
def difNet (ω : K) (k : ℕ) : ℕ → (ℕ → V) → ℕ → V
  | 0, x => x
  | c + 1, x => difLayer (2 ^ (k - 1 - c)) (2 ^ c) (fun _ s => ω ^ (s * 2 ^ c)) (difNet ω k c x)

/-- After c layers, block b of 2^(k-c) rows holds a twisted transform of the input. -/
theorem difNet_apply {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → V) :
    ∀ c ≤ k, ∀ b < 2 ^ c, ∀ t < 2 ^ (k - c),
      difNet ω k c x (b * 2 ^ (k - c) + t) =
        ∑ j ∈ range (2 ^ c), (ω ^ ((t + 2 ^ (k - c) * j) * rev c b)) • x (t + 2 ^ (k - c) * j) := by
  intro c
  induction c with
  | zero =>
    intro _ b hb t _
    simp at hb; subst hb
    simp [difNet, Plonky3Lean.Spec.Matrix.bitRev]
  | succ c ih =>
    intro hc B hB r hr
    obtain ⟨L, rfl⟩ : ∃ L, k = L + 1 + c := ⟨k - (c + 1), by omega⟩
    have e1 : L + 1 + c - (c + 1) = L := by omega
    have e2 : L + 1 + c - c = L + 1 := by omega
    have e3 : L + 1 + c - 1 - c = L := by omega
    rw [e1] at hr ⊢
    have ih' := ih (by omega)
    rw [e2] at ih'
    have hneg : ω ^ (2 ^ (L + c)) = -1 :=
      neg_one_of_primitive (j := L + c) (by rw [show L + c + 1 = L + 1 + c by ring]; exact hω)
    simp only [difNet, difLayer, layer, e3, dif]
    have hsplit : ∀ f : ℕ → V, ∑ m ∈ range (2 ^ (c + 1)), f m =
        ∑ m ∈ range (2 ^ c), f (2 * m) + ∑ m ∈ range (2 ^ c), f (2 * m + 1) := fun f => by
      rw [pow_succ, mul_comm, sum_range_two_mul]
    have hr2 : r < 2 ^ (L + 1) := by rw [pow_succ]; omega
    rcases Nat.even_or_odd' B with ⟨B', rfl | rfl⟩
    · -- B even: the upper row of the pair
      have hB' : B' < 2 ^ c := by rw [pow_succ] at hB; omega
      have hpos : 2 * B' * 2 ^ L + r = B' * 2 ^ (L + 1) + r := by ring
      have hsz : B' * 2 ^ (L + 1) + r < 2 ^ c * (2 * 2 ^ L) := by
        have : (B' + 1) * 2 ^ (L + 1) ≤ 2 ^ c * 2 ^ (L + 1) := Nat.mul_le_mul_right _ hB'
        rw [pow_succ] at this hr2 ⊢; nlinarith
      have hmod : (B' * 2 ^ (L + 1) + r) % (2 * 2 ^ L) = r := by
        rw [show 2 * 2 ^ L = 2 ^ (L + 1) by ring, Nat.mul_comm, Nat.mul_add_mod,
          Nat.mod_eq_of_lt hr2]
      simp only [hpos, hsz, ↓reduceIte, hmod, hr]
      rw [ih' B' hB' r hr2,
        show B' * 2 ^ (L + 1) + r + 2 ^ L = B' * 2 ^ (L + 1) + (r + 2 ^ L) by ring,
        ih' B' hB' (r + 2 ^ L) (by rw [pow_succ]; omega), rev_double, hsplit]
      congr 1
      · refine sum_congr rfl fun m _ => ?_
        congr 2
        · ring
        · ring
      · refine sum_congr rfl fun m _ => ?_
        congr 2
        · ring
        · ring
    · -- B odd: the lower row of the pair
      have hB' : B' < 2 ^ c := by rw [pow_succ] at hB; omega
      have hpos : (2 * B' + 1) * 2 ^ L + r = B' * 2 ^ (L + 1) + (2 ^ L + r) := by ring
      have hr3 : 2 ^ L + r < 2 ^ (L + 1) := by rw [pow_succ]; omega
      have hsz : B' * 2 ^ (L + 1) + (2 ^ L + r) < 2 ^ c * (2 * 2 ^ L) := by
        have : (B' + 1) * 2 ^ (L + 1) ≤ 2 ^ c * 2 ^ (L + 1) := Nat.mul_le_mul_right _ hB'
        rw [pow_succ] at this hr3 ⊢; nlinarith
      have hmod : (B' * 2 ^ (L + 1) + (2 ^ L + r)) % (2 * 2 ^ L) = 2 ^ L + r := by
        rw [show 2 * 2 ^ L = 2 ^ (L + 1) by ring, Nat.mul_comm, Nat.mul_add_mod,
          Nat.mod_eq_of_lt hr3]
      simp only [hpos, hsz, ↓reduceIte, hmod, show ¬ (2 ^ L + r < 2 ^ L) by omega,
        show 2 ^ L + r - 2 ^ L = r by omega]
      rw [show B' * 2 ^ (L + 1) + (2 ^ L + r) - 2 ^ L = B' * 2 ^ (L + 1) + r by
          rw [pow_succ]; omega,
        show B' * 2 ^ (L + 1) + (2 ^ L + r) = B' * 2 ^ (L + 1) + (r + 2 ^ L) by ring,
        ih' B' hB' r hr2, ih' B' hB' (r + 2 ^ L) (by rw [pow_succ]; omega),
        rev_double_add_one, hsplit, smul_sub, smul_sum, smul_sum, sub_eq_add_neg,
        ← sum_neg_distrib]
      have hone : ω ^ (2 ^ (L + 1 + c)) = 1 := hω.pow_eq_one
      congr 1
      · refine sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← pow_add]
        congr 1
        · rw [show (r + 2 ^ L * (2 * m)) * (2 ^ c + rev c B') = 2 ^ (L + 1 + c) * m +
            (r * 2 ^ c + (r + 2 ^ (L + 1) * m) * rev c B') by ring,
            pow_period hone m]
        · congr 1; ring
      · refine sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← pow_add, ← neg_smul]
        congr 1
        · rw [show (r + 2 ^ L * (2 * m + 1)) * (2 ^ c + rev c B') = 2 ^ (L + 1 + c) * m +
            (2 ^ (L + c) + (r * 2 ^ c + (r + 2 ^ L + 2 ^ (L + 1) * m) * rev c B')) by ring,
            pow_period hone m, pow_half hneg]
        · congr 1; ring

/-- The Gentleman-Sande transform: k decimation-in-frequency layers leave the transform bit-reversed. -/
theorem difNet_eq_dft {ω : K} {k : ℕ} (hω : IsPrimitiveRoot ω (2 ^ k)) (x : ℕ → V) {i : ℕ}
    (hi : i < 2 ^ k) : difNet ω k k x i = dft ω (2 ^ k) x (rev k i) := by
  have := difNet_apply hω x k le_rfl i hi 0 (by simp)
  simp only [Nat.sub_self, pow_zero, mul_one, add_zero, zero_add, one_mul] at this
  rw [this, dft]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_comm m]

end Plonky3Lean.Proofs.Dft
