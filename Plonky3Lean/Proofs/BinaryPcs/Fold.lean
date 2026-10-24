module

public import P3BinaryPcs
public import Plonky3Lean.Proofs.BinaryDft.Concrete

@[expose] public section

/-!
# The fold of an additive Reed-Solomon codeword

The codeword of coefficients d over S_(l+1) lists the values of P = sum_k d_k X_k.

For a Cantor basis, the novel basis splits at its lowest bit:

```text
    P(y) = P_even(y^2 + y) + y P_odd(y^2 + y)
```

The fold reads P at y = point(2 j) and y + 1 = point(2 j + 1).

Both points lie above point(j) = y^2 + y.

It recovers P_odd(point j) as their sum, and P_even(point j) from the first.

The fold at beta returns (1 - beta) P_even + beta P_odd at point(j).

That is the codeword over S_l of the coefficients (1 - beta) d_(2k) + beta d_(2k+1).

In other words, the lowest variable is bound to beta.

This is the folding lemma of FRI-Binius (Diamond and Posen, eprint 2024/504, section 4).
-/

namespace Plonky3Lean.Proofs.BinaryPcs

open Finset Plonky3Lean.Spec.BinaryDft Plonky3Lean.Proofs.BinaryDft

section Field

variable {F : Type _} [Field F] [CharP F 2]

/-- x -> x^2 + x is additive in characteristic 2. -/
def sqAdd : F →+ F where
  toFun x := x ^ 2 + x
  map_zero' := by simp
  map_add' x y := by
    have : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (x * y) * this

variable {β : ℕ → F} {N : ℕ}

/-- y^2 + y sends point(2 j) to point(j). -/
theorem point_double (hβ : IsCantor β N) {j : ℕ} (hj : j < 2 ^ (N - 1)) :
    point β (2 * j) ^ 2 + point β (2 * j) = point β j := by
  have h := point_two_mul_add β j (b := 0) (by norm_num)
  simp only [add_zero, zero_ne_one, ite_false] at h
  rw [h]
  show sqAdd _ = _
  rw [map_point sqAdd]
  refine point_congr hj fun r hr => ?_
  have := hβ.2 r (by omega)
  simp only [Function.comp, sqAdd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_comm 1 r, this]

omit [CharP F 2] in
/-- The partner of point(2 j) is point(2 j) + 1. -/
theorem point_double_succ (hβ : IsCantor β N) (j : ℕ) : point β (2 * j + 1) = point β (2 * j) + 1 := by
  have h1 := point_two_mul_add β j (b := 1) (by norm_num)
  have h0 := point_two_mul_add β j (b := 0) (by norm_num)
  simp only [add_zero, zero_ne_one, ite_false, ite_true] at h0 h1
  rw [h1, h0, hβ.1]

/-- The novel basis at its lowest bit: X_(2k+b)(y) = y^b X'_k(y^2 + y). -/
theorem novel_double (hβ : IsCantor β N) {l : ℕ} (hl : l + 1 ≤ N) (k : ℕ) {b : ℕ} (hb : b < 2)
    (y : F) : novel β (l + 1) (2 * k + b) y = (if b = 1 then y else 1) * novel β l k (y ^ 2 + y) := by
  rw [novel, prod_range_succ', novel, mul_comm]
  congr 1
  · rw [Nat.testBit_zero, normalized_eq_sqAddIter hβ (by omega)]
    interval_cases b <;> simp [sqAddIter]
  · refine prod_congr rfl fun j hj => ?_
    rw [Nat.testBit_succ, show (2 * k + b) / 2 = k by omega,
      normalized_eq_sqAddIter hβ (by simp at hj; omega),
      normalized_eq_sqAddIter hβ (by simp at hj; omega), sqAddIter, sqAddIter,
      Function.iterate_succ_apply]

theorem sum_range_double {M : Type _} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ,
      add_assoc]

variable {V : Type _} [AddCommGroup V] [Module F V]

/-- P(y) = P_even(y^2 + y) + y P_odd(y^2 + y). -/
theorem novelEval_double (hβ : IsCantor β N) {l : ℕ} (hl : l + 1 ≤ N) (d : ℕ → V) (y : F) :
    novelEval β (l + 1) d y =
      novelEval β l (fun k => d (2 * k)) (y ^ 2 + y) + y • novelEval β l (fun k => d (2 * k + 1)) (y ^ 2 + y) := by
  rw [novelEval, pow_succ, mul_comm, sum_range_double, sum_add_distrib, novelEval, novelEval, smul_sum]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    rw [show 2 * k = 2 * k + 0 by rfl, novel_double hβ hl k (by norm_num)]; simp
  · refine sum_congr rfl fun k _ => ?_
    rw [novel_double hβ hl k (by norm_num), smul_smul]; simp

end Field

/-! ## The fold, in the challenge field -/

section Fold

variable {F EF : Type _} [Field F] [CharP F 2] [Field EF] [Algebra F EF] {β : ℕ → F} {N : ℕ}

/-- The fold of the pair above point(j) of the codeword of d over S_(l+1).

It is the codeword over S_l, in the challenge field, of the coefficients.

The lowest variable of those coefficients is bound to beta. -/
theorem fold_ntt (hβ : IsCantor β N) {l : ℕ} (hl : l + 1 ≤ N) (d : ℕ → F) {j : ℕ} (hj : j < 2 ^ l)
    (beta : EF) :
    let lo := ntt β (l + 1) 0 d (2 * j)
    let hi := ntt β (l + 1) 0 d (2 * j + 1)
    let f1 := lo + hi
    let f0 := lo + point β (2 * j) * f1
    beta * algebraMap F EF (f0 + f1) + algebraMap F EF f0 =
      ntt (algebraMap F EF ∘ β) l 0
        (fun k => (1 - beta) * algebraMap F EF (d (2 * k)) + beta * algebraMap F EF (d (2 * k + 1))) j := by
  intro lo hi f1 f0
  have hj' : j < 2 ^ (N - 1) := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))
  set y := point β (2 * j)
  set E := novelEval β l (fun k => d (2 * k)) (point β j)
  set O := novelEval β l (fun k => d (2 * k + 1)) (point β j)
  have hlo : lo = E + y * O := by
    simp only [lo, ntt, zero_add, novelEval_double hβ hl, point_double hβ hj', smul_eq_mul, E, O, y]
  have hhi : hi = E + (y + 1) * O := by
    have h2 : (y + 1) ^ 2 + (y + 1) = y ^ 2 + y := by
      have : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination (y + 1) * this
    rw [show hi = novelEval β (l + 1) d (y + 1) by simp [hi, ntt, y, point_double_succ hβ],
      novelEval_double hβ hl, h2, point_double hβ hj']
    rfl
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hf1 : f1 = O := by simp only [f1, hlo, hhi]; linear_combination (E + y * O) * h2F
  have hf0 : f0 = E := by simp only [f0, hf1, hlo]; linear_combination (y * O) * h2F
  have hE : algebraMap F EF E = ntt (algebraMap F EF ∘ β) l 0 (fun k => algebraMap F EF (d (2 * k))) j := by
    have := map_ntt (algebraMap F EF) β l 0 (fun k => d (2 * k)) j
    simp only [ntt, zero_add, map_zero] at this
    rw [ntt, zero_add]; exact this
  have hO : algebraMap F EF O = ntt (algebraMap F EF ∘ β) l 0 (fun k => algebraMap F EF (d (2 * k + 1))) j := by
    have := map_ntt (algebraMap F EF) β l 0 (fun k => d (2 * k + 1)) j
    simp only [ntt, zero_add, map_zero] at this
    rw [ntt, zero_add]; exact this
  have : CharP EF 2 := charP_of_injective_algebraMap (algebraMap F EF).injective 2
  rw [hf0, hf1, map_add, hE, hO, CharTwo.sub_eq_add]
  simp only [ntt, novelEval, smul_eq_mul, mul_add, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun k _ => by ring

end Fold

/-! ## The transcription -/

section Model

open p3_binary_dft.mirror p3_binary_pcs.fold.mirror

variable {F EF : Type _} [Field F] [CharP F 2] [Field EF] [Algebra F EF]

omit [CharP F 2] in
/-- The pair fold panics exactly when the doubled index, wrapped at the word, leaves the alphabet's domain.

Otherwise it is f_0 + beta (f_0 + f_1), with f_1 = lo + hi and f_0 = lo + point(2 index) f_1. -/
theorem fold_pair_eq (L : Level F) (index : ℕ) (beta : EF) (lo hi : F) :
    fold_pair L index beta lo hi =
      if 2 * index % 2 ^ 64 < 2 ^ 2 ^ L.logBits then
        let x := point L.cantor (2 * index % 2 ^ 64)
        some (beta * algebraMap F EF ((lo + x * (lo + hi)) + (lo + hi)) +
          algebraMap F EF (lo + x * (lo + hi)))
      else none := by
  unfold fold_pair
  rw [domain_point_eq]
  split_ifs <;> rfl

/-- Fold the pair above point(j) of an honest codeword over S_(l+1).

The result is the honest codeword over S_l of the bound coefficients. -/
theorem fold_pair_ntt {L : Level F} (hL : Cantor L) {l : ℕ} (hl : l + 1 ≤ 2 ^ L.logBits) (hw : l < 64)
    (d : ℕ → F) {j : ℕ} (hj : j < 2 ^ l) (beta : EF) :
    fold_pair L j beta (ntt L.cantor (l + 1) 0 d (2 * j)) (ntt L.cantor (l + 1) 0 d (2 * j + 1)) =
      some (ntt (algebraMap F EF ∘ L.cantor) l 0
        (fun k => (1 - beta) * algebraMap F EF (d (2 * k)) + beta * algebraMap F EF (d (2 * k + 1))) j) := by
  have h2j : 2 * j < 2 ^ (l + 1) := by rw [pow_succ]; omega
  have hmod : 2 * j % 2 ^ 64 = 2 * j :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le h2j (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hin : 2 * j < 2 ^ 2 ^ L.logBits := lt_of_lt_of_le h2j (Nat.pow_le_pow_right (by norm_num) hl)
  simp only [fold_pair_eq, hmod, hin, ite_true]
  exact congrArg some (fold_ntt hL hl d hj beta)

end Model

/-! ## Several folds: the coset -/

section Coset

open p3_binary_dft.mirror p3_binary_pcs.fold.mirror

variable {F EF : Type _} [Field F] [CharP F 2] [Field EF] [Algebra F EF]

/-- Binding the lowest variable of the coefficients to beta. -/
def bind1 (beta : EF) (e : ℕ → EF) : ℕ → EF := fun k => (1 - beta) * e (2 * k) + beta * e (2 * k + 1)

/-- Binding the lowest variables to the challenges, first challenge first. -/
def bindAll (bs : List EF) (e : ℕ → EF) : ℕ → EF := bs.foldl (fun e b => bind1 b e) e

omit [CharP F 2] in
/-- Binding two runs of challenges in turn binds their concatenation. -/
theorem bindAll_append (bs cs : List EF) (e : ℕ → EF) : bindAll cs (bindAll bs e) = bindAll (bs ++ cs) e := by
  simp [bindAll, List.foldl_append]

omit [CharP F 2] in
theorem vanishing_congr {β β' : ℕ → F} {j : ℕ} (h : ∀ r < j, β r = β' r) (x : F) :
    vanishing β j x = vanishing β' j x :=
  prod_congr rfl fun m hm => by rw [point_congr (mem_range.mp hm) h]

omit [CharP F 2] in
/-- The transform over S_l reads only the first l basis vectors. -/
theorem ntt_congr_basis {β β' : ℕ → F} {l : ℕ} (h : ∀ r < l, β r = β' r) (shift : F) (d : ℕ → F)
    {i : ℕ} (hi : i < 2 ^ l) : ntt β l shift d i = ntt β' l shift d i := by
  simp only [ntt, novelEval, novel, normalized]
  rw [point_congr hi h]
  refine sum_congr rfl fun k _ => ?_
  congr 1
  refine prod_congr rfl fun j hj => ?_
  have hj' : ∀ r < j, β r = β' r := fun r hr => h r (by simp at hj; omega)
  rw [vanishing_congr hj', vanishing_congr hj', h j (by simpa using hj)]

/-- One in-place layer of the coset fold over honest values gives the honest values one level down. -/
theorem coset_layer_ntt {L : Level EF} [CharP EF 2] (hL : Cantor L) {l : ℕ} (hl : l + 1 ≤ 2 ^ L.logBits)
    (hw : l < 64) (e : ℕ → EF) (beta : EF) {c len : ℕ} (hlen : (c + 1) * len ≤ 2 ^ l)
    (scratch : List EF) (hs : ∀ i < 2 * len, scratch.getD i 0 = ntt L.cantor (l + 1) 0 e (c * (2 * len) + i)) :
    coset_layer L c len beta scratch =
      some ((List.range len).map fun i => ntt L.cantor l 0 (bind1 beta e) (c * len + i)) := by
  refine mapM_some _ _ _ fun i hi => ?_
  have hi' := mem_range.mp hi
  have hj : c * len + i < 2 ^ l := by nlinarith
  rw [hs _ (by omega), hs _ (by omega), show c * (2 * len) + 2 * i = 2 * (c * len + i) by ring,
    show c * (2 * len) + (2 * i + 1) = 2 * (c * len + i) + 1 by ring, fold_pair_ntt hL hl hw e hj beta]
  simp [Algebra.algebraMap_self]
  rfl

/-- Run the in-place layers of the coset fold over honest values of level l + m.

They end at the honest value of level l. -/
theorem coset_loop_ntt {L : Level EF} [CharP EF 2] (hL : Cantor L) {l : ℕ} (c : ℕ) (hc : c < 2 ^ l) :
    ∀ (rest : List EF) (e : ℕ → EF) (scratch : List EF),
      l + rest.length ≤ 2 ^ L.logBits → l + rest.length ≤ 64 → 2 ^ rest.length ≤ scratch.length →
      (∀ i < 2 ^ rest.length, scratch.getD i 0 = ntt L.cantor (l + rest.length) 0 e (c * 2 ^ rest.length + i)) →
      ∃ out, rest.foldlM (fun (acc : ℕ × List EF) beta => do
          let len := acc.1 / 2
          let layer ← coset_layer L c len beta acc.2
          pure (len, layer ++ acc.2.drop len)) (2 ^ rest.length, scratch) = some out ∧
        out.2.head? = some (ntt L.cantor l 0 (bindAll rest e) c) := by
  intro rest
  induction rest with
  | nil =>
    intro e scratch _ _ hlen hs
    refine ⟨_, rfl, ?_⟩
    have h0 := hs 0 (by simp)
    simp only [List.length_nil, add_zero, pow_zero, mul_one] at h0
    have hpos : 0 < scratch.length := by simp at hlen; omega
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos] at h0
    simpa [bindAll] using h0
  | cons b rest ih =>
    intro e scratch hl hw hlen hs
    simp only [List.length_cons] at hl hw hlen hs
    have hm : 2 ^ (rest.length + 1) / 2 = 2 ^ rest.length := by rw [pow_succ]; simp
    have hlay := coset_layer_ntt hL (l := l + rest.length) (by omega) (by omega) e b
      (c := c) (len := 2 ^ rest.length)
      (by rw [add_mul, one_mul]; have := Nat.mul_le_mul_right (2 ^ rest.length) (Nat.succ_le_of_lt hc)
          rw [pow_add]; nlinarith [Nat.two_pow_pos rest.length])
      scratch (fun i hi => by
        rw [hs i (by rw [pow_succ]; omega), show l + (rest.length + 1) = l + rest.length + 1 by ring,
          show c * 2 ^ (rest.length + 1) = c * (2 * 2 ^ rest.length) by ring])
    set layer := (List.range (2 ^ rest.length)).map
      fun i => ntt L.cantor (l + rest.length) 0 (bind1 b e) (c * 2 ^ rest.length + i)
    obtain ⟨out, hout, hhead⟩ := ih (bind1 b e) (layer ++ scratch.drop (2 ^ rest.length)) (by omega)
      (by omega) (by simp [layer]) (fun i hi => by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa [layer] using hi)]
        simp [layer, hi])
    refine ⟨out, ?_, by simpa [bindAll] using hhead⟩
    rw [List.foldlM_cons]
    simp only [List.length_cons, hm, hlay, Option.bind_eq_bind, Option.bind_some, pure]
    exact hout

/-- The coset fold of an honest coset is the honest value of the bound coefficients.

Each challenge moves it one level down.

The first fold reads the alphabet's codeword.

The alphabet's Cantor basis is the leading part of the field's. -/
theorem fold_coset_ntt {LF : Level F} {LE : Level EF} [CharP EF 2] (hF : Cantor LF) (hE : Cantor LE)
    (hpre : ∀ r < 2 ^ LF.logBits, LE.cantor r = algebraMap F EF (LF.cantor r)) {l a : ℕ} (ha : 0 < a)
    (hla : l + a ≤ 2 ^ LF.logBits) (hlaE : l + a ≤ 2 ^ LE.logBits) (hw : l + a ≤ 64) (d : ℕ → F)
    (bs : List EF) (hbs : bs.length = a) {c : ℕ} (hc : c < 2 ^ l) :
    fold_coset LF LE c ((List.range (2 ^ a)).map fun i => ntt LF.cantor (l + a) 0 d (c * 2 ^ a + i)) bs =
      some (ntt LE.cantor l 0 (bindAll bs (algebraMap F EF ∘ d)) c) := by
  obtain ⟨b, rest, rfl⟩ : ∃ b rest, bs = b :: rest := by
    cases bs with
    | nil => simp at hbs; omega
    | cons b rest => exact ⟨b, rest, rfl⟩
  simp only [List.length_cons] at hbs
  subst hbs
  have hm : 2 ^ (rest.length + 1) / 2 = 2 ^ rest.length := by rw [pow_succ]; simp
  have hfirst : ((List.range (2 ^ (rest.length + 1) / 2)).mapM fun i =>
      fold_pair LF (c * (2 ^ (rest.length + 1) / 2) + i) b
        ((((List.range (2 ^ (rest.length + 1))).map fun i =>
          ntt LF.cantor (l + (rest.length + 1)) 0 d (c * 2 ^ (rest.length + 1) + i))).getD (2 * i) 0)
        ((((List.range (2 ^ (rest.length + 1))).map fun i =>
          ntt LF.cantor (l + (rest.length + 1)) 0 d (c * 2 ^ (rest.length + 1) + i))).getD (2 * i + 1) 0)) =
      some ((List.range (2 ^ rest.length)).map fun i =>
        ntt LE.cantor (l + rest.length) 0 (bind1 b (algebraMap F EF ∘ d)) (c * 2 ^ rest.length + i)) := by
    rw [hm]
    refine mapM_some _ _ _ fun i hi => ?_
    have hi' := mem_range.mp hi
    have hj : c * 2 ^ rest.length + i < 2 ^ (l + rest.length) := by
      rw [pow_add]; nlinarith [Nat.two_pow_pos rest.length]
    have h20 : 2 * i < 2 ^ (rest.length + 1) := by rw [pow_succ]; omega
    have h21 : 2 * i + 1 < 2 ^ (rest.length + 1) := by rw [pow_succ]; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h20,
      List.getElem?_range h21, Option.map_some, Option.getD_some]
    rw [show c * 2 ^ (rest.length + 1) + 2 * i = 2 * (c * 2 ^ rest.length + i) by ring,
      show c * 2 ^ (rest.length + 1) + (2 * i + 1) = 2 * (c * 2 ^ rest.length + i) + 1 by ring,
      show l + (rest.length + 1) = l + rest.length + 1 by ring,
      fold_pair_ntt hF (by omega) (by omega) d hj b]
    refine congrArg some ((ntt_congr_basis (fun r hr => (hpre r (by omega)).symm) _ _ hj).trans ?_)
    rfl
  obtain ⟨out, hout, hhead⟩ := coset_loop_ntt hE c hc rest (bind1 b (algebraMap F EF ∘ d))
    ((List.range (2 ^ rest.length)).map fun i =>
      ntt LE.cantor (l + rest.length) 0 (bind1 b (algebraMap F EF ∘ d)) (c * 2 ^ rest.length + i))
    (by omega) (by omega) (by simp) (fun i hi => by simp [List.getD_eq_getElem?_getD, hi])
  unfold fold_coset
  simp only [List.length_map, List.length_range, List.length_cons, ne_eq, not_true_eq_false,
    ite_false, List.head?_cons, List.tail_cons, Option.bind_eq_bind, Option.bind_some, hfirst]
  rw [hm]
  refine (congrArg (fun o => Option.bind o fun x => x.2.head?) hout).trans ?_
  simpa [bindAll] using hhead

end Coset

/-! ## After every fold: the multilinear evaluation -/

section Final

variable {EF : Type _} [Field EF]

/-- The equality weight of hypercube point k at the challenges.

Bit i of k selects b_i when set, and 1 - b_i otherwise. -/
def eqWeight : List EF → ℕ → EF
  | [], _ => 1
  | b :: bs, k => (if k % 2 = 1 then b else 1 - b) * eqWeight bs (k / 2)

/-- Binding every variable leaves the multilinear extension of the coefficients at the challenges. -/
theorem bindAll_zero (bs : List EF) (e : ℕ → EF) :
    bindAll bs e 0 = ∑ k ∈ range (2 ^ bs.length), eqWeight bs k * e k := by
  induction bs generalizing e with
  | nil => simp [bindAll, eqWeight]
  | cons b bs ih =>
    rw [show bindAll (b :: bs) e = bindAll bs (bind1 b e) from rfl, ih, List.length_cons, pow_succ,
      mul_comm, sum_range_double]
    refine sum_congr rfl fun k _ => ?_
    simp only [bind1, eqWeight, Nat.mul_mod_right, Nat.mul_add_mod, show (2 * k) / 2 = k by omega,
      show (2 * k + 1) / 2 = k by omega]
    simp; ring

/-- Binding m variables of coefficients supported below 2^m leaves only the constant coefficient. -/
theorem bindAll_support (bs : List EF) (e : ℕ → EF) (he : ∀ k, 2 ^ bs.length ≤ k → e k = 0) :
    ∀ k, 1 ≤ k → bindAll bs e k = 0 := by
  induction bs generalizing e with
  | nil => simpa [bindAll] using he
  | cons b bs ih =>
    refine ih (bind1 b e) fun k hk => ?_
    simp only [List.length_cons, pow_succ] at he
    simp [bind1, he (2 * k) (by omega), he (2 * k + 1) (by omega)]

/-- After every fold, the honest codeword over S_r is uniform.

Each symbol is the multilinear evaluation at the challenges. -/
theorem ntt_bindAll {β : ℕ → EF} (r : ℕ) (bs : List EF) (e : ℕ → EF)
    (he : ∀ k, 2 ^ bs.length ≤ k → e k = 0) (i : ℕ) :
    ntt β r 0 (bindAll bs e) i = ∑ k ∈ range (2 ^ bs.length), eqWeight bs k * e k := by
  rw [ntt, novelEval, ← bindAll_zero, sum_eq_single 0]
  · simp [novel]
  · intro k _ hk; rw [bindAll_support bs e he k (by omega), smul_zero]
  · simp

end Final

end Plonky3Lean.Proofs.BinaryPcs
