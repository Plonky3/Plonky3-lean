module

public import Plonky3Lean.Proofs.Circle.Domain
public import Plonky3Lean.Proofs.Dft.Glue

@[expose] public section

/-!
# p3-circle: the circle FFT network computes the FFT-basis evaluation

The proof follows Theorem 2 of the paper, read backwards.

The first layer splits f = f_0 + v_(n-1) f_1 over the two halves of the domain.

There v_(n-1) is the constant plus or minus t.

The remaining layers are two independent transforms of half the size.

They run on the twin cosets S + <2 g> and S + g + <2 g>.

Row 2 b of the output holds the value at S + rev(b) g, and row 2 b + 1 the value at its conjugate:

```text
    row:     0      1       2          3          ...
    point:   S     -S     S + r(1) g  -(S + r(1) g)
```
-/

namespace Plonky3Lean.Proofs.Circle

open Plonky3Lean.Spec.Circle Plonky3Lean.Proofs.Dft Finset

set_option linter.unusedSectionVars false

local notation "rev" => Plonky3Lean.Spec.Matrix.bitRev

variable {K : Type _} [Field K] {V : Type _} [AddCommGroup V] [Module K V]

/-! ## The basis -/

theorem bit_add_two_pow {j n k : ℕ} (hk : k < n) : bit (j + 2 ^ n) k = bit j k := by
  unfold bit
  obtain ⟨d, hd⟩ : ∃ d, n = k + (d + 1) := ⟨n - k - 1, by omega⟩
  rw [hd, pow_add, Nat.add_mul_div_left _ _ (by positivity), pow_succ, mul_comm (2 ^ d) 2,
    Nat.add_mul_mod_self_left]

theorem bit_top {j n : ℕ} (hj : j < 2 ^ n) : bit j n = 0 := by
  unfold bit; rw [Nat.div_eq_of_lt hj]

theorem bit_top_add {j n : ℕ} (hj : j < 2 ^ n) : bit (j + 2 ^ n) n = 1 := by
  unfold bit
  rw [Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt hj]

/-- The basis of order n + 1 at j < 2^n is the basis of order n. -/
theorem basis_succ_low {n j : ℕ} (hn : 1 ≤ n) (hj : j < 2 ^ n) (P : C K) :
    basis (n + 1) j P = basis n j P := by
  unfold basis
  rw [prod_Ico_succ_top hn, bit_top hj, pow_zero, mul_one]

/-- The basis of order n + 1 at j + 2^n is the basis of order n at j times v_n. -/
theorem basis_succ_high {n j : ℕ} (hn : 1 ≤ n) (hj : j < 2 ^ n) (P : C K) :
    basis (n + 1) (j + 2 ^ n) P = basis n j P * vn n P := by
  unfold basis
  rw [prod_Ico_succ_top hn, bit_top_add hj, pow_one, bit_add_two_pow (by omega)]
  rw [prod_congr rfl fun k hk => by rw [bit_add_two_pow (by simp at hk; omega)]]
  ring

/-- The FFT-basis evaluation of order n + 1 splits into the low half plus v_n times the high half. -/
theorem fftEval_succ {n : ℕ} (hn : 1 ≤ n) (c : ℕ → V) (P : C K) :
    fftEval (n + 1) c P = fftEval n (fun j => c j + vn n P • c (j + 2 ^ n)) P := by
  unfold fftEval
  rw [pow_succ, mul_two, sum_range_add]
  simp only [smul_add, sum_add_distrib, smul_smul]
  congr 1
  · exact sum_congr rfl fun j hj => by rw [basis_succ_low hn (by simpa using hj)]
  · rw [sum_congr rfl fun j hj => by
      rw [add_comm (2 ^ n) j, basis_succ_high hn (by simpa using hj)]]

/-! ## The twiddles and the points of the output rows -/

/-- The twiddle of layer j, block b, on the twin coset S + <g> of size 2^n.

- layer 0 uses (S + rev(b) g).y
- layer j >= 1 uses (2^(j-1) (S + rev(b) g)).x

Here rev reverses n - 1 - j bits. -/
def twC (S g : C K) (n j b : ℕ) : K :=
  if j = 0 then (S + rev (n - 1) b • g).y else (2 ^ (j - 1) • (S + rev (n - 1 - j) b • g)).x

/-- The point of output row i: S + rev(i / 2) g for even i, its conjugate for odd i. -/
def ptAt (S g : C K) (n i : ℕ) : C K :=
  if i % 2 = 0 then S + rev (n - 1) (i / 2) • g else -(S + rev (n - 1) (i / 2) • g)

theorem twC_low (S g : C K) {n j b : ℕ} (hj : j < n) (hb : b < 2 ^ (n - 1 - j)) :
    twC S g (n + 1) j b = twC S (2 • g) n j b := by
  unfold twC
  split_ifs with h0
  · subst h0
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, rev_upper _ (by simpa using hb), smul_smul]
    simp only [Nat.mul_comm]
  · rw [show n + 1 - 1 - j = (n - 1 - j) + 1 by omega, rev_upper _ hb, smul_smul]
    simp only [Nat.mul_comm]

theorem twC_high (S g : C K) {n j b : ℕ} (hj : j < n) (hb : b < 2 ^ (n - 1 - j)) :
    twC S g (n + 1) j (2 ^ (n - 1 - j) + b) = twC (S + g) (2 • g) n j b := by
  unfold twC
  split_ifs with h0
  · subst h0
    simp only [Nat.sub_zero] at hb ⊢
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, rev_lower _ hb, add_nsmul, one_nsmul, smul_smul]
    simp only [Nat.mul_comm]
    congr 1; abel
  · rw [show n + 1 - 1 - j = (n - 1 - j) + 1 by omega, rev_lower _ hb, add_nsmul, one_nsmul,
      smul_smul]
    simp only [Nat.mul_comm]
    congr 2; abel

theorem ptAt_low (S g : C K) {n i : ℕ} (hn : 1 ≤ n) (hi : i < 2 ^ n) :
    ptAt S g (n + 1) i = ptAt S (2 • g) n i := by
  unfold ptAt
  have : i / 2 < 2 ^ (n - 1) := by
    rw [show 2 ^ n = 2 * 2 ^ (n - 1) by rw [← pow_succ']; congr 1; omega] at hi; omega
  rw [show n + 1 - 1 = (n - 1) + 1 by omega, rev_upper _ this, smul_smul]
  simp only [Nat.mul_comm]

theorem ptAt_high (S g : C K) {n i : ℕ} (hn : 1 ≤ n) (hi : i < 2 ^ n) :
    ptAt S g (n + 1) (2 ^ n + i) = ptAt (S + g) (2 • g) n i := by
  unfold ptAt
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : i / 2 < 2 ^ (n - 1) := by omega
  rw [show (2 ^ n + i) / 2 = 2 ^ (n - 1) + i / 2 by omega, show (2 ^ n + i) % 2 = i % 2 by omega,
    show n + 1 - 1 = (n - 1) + 1 by omega, rev_lower _ h1, add_nsmul, one_nsmul, smul_smul]
  have : S + ((2 * rev (n - 1) (i / 2)) • g + g) = S + g + (rev (n - 1) (i / 2) * 2) • g := by
    rw [Nat.mul_comm]; abel
  rw [this]


/-! ## Layers on halves -/

section halves

variable {W : Type _}

theorem layer_local (op : ℕ → ℕ → W → W → W × W) (m nb : ℕ) {x y : ℕ → W}
    (h : ∀ i < nb * (2 * m), x i = y i) : ∀ i < nb * (2 * m), layer op m nb x i = layer op m nb y i := by
  intro i hi
  have hb : i / (2 * m) < nb := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  have hd := Nat.div_add_mod i (2 * m)
  have hblk : (i / (2 * m) + 1) * (2 * m) ≤ nb * (2 * m) := Nat.mul_le_mul_right _ hb
  unfold layer
  simp only [hi, ↓reduceIte]
  split_ifs with hr
  · rw [h i hi, h (i + m) (by nlinarith)]
  · rw [h i hi, h (i - m) (by omega)]

/-- On the first half, a layer of 2 nb blocks is the layer of nb blocks. -/
theorem layer_top (op op' : ℕ → ℕ → W → W → W × W) (m nb : ℕ) (hop : ∀ b < nb, op b = op' b)
    (x : ℕ → W) : ∀ i < nb * (2 * m), layer op m (2 * nb) x i = layer op' m nb x i := by
  intro i hi
  have hb : i / (2 * m) < nb := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  unfold layer
  simp only [hi, ↓reduceIte, show i < 2 * nb * (2 * m) by nlinarith, hop _ hb]

/-- On the second half, a layer of 2 nb blocks is the layer of the upper nb blocks.

It acts on the shifted rows. -/
theorem layer_bot (op : ℕ → ℕ → W → W → W × W) (m nb : ℕ) (hm : 0 < m) (x : ℕ → W) :
    ∀ i < nb * (2 * m), layer op m (2 * nb) x (nb * (2 * m) + i) =
      layer (fun b => op (nb + b)) m nb (fun r => x (nb * (2 * m) + r)) i := by
  intro i hi
  have hm2 : 0 < 2 * m := by omega
  have hdiv : (nb * (2 * m) + i) / (2 * m) = nb + i / (2 * m) := by
    rw [Nat.mul_comm, Nat.mul_add_div hm2]
  have hmod : (nb * (2 * m) + i) % (2 * m) = i % (2 * m) := by
    rw [Nat.mul_comm, Nat.mul_add_mod]
  unfold layer
  simp only [hi, ↓reduceIte, show nb * (2 * m) + i < 2 * nb * (2 * m) by nlinarith, hdiv, hmod]
  split_ifs with hr
  · rw [add_assoc]
  · have : i % (2 * m) ≥ m := by omega
    have : i ≥ m := le_trans this (Nat.mod_le _ _)
    rw [show nb * (2 * m) + i - m = nb * (2 * m) + (i - m) by omega]

theorem layer_op_congr {op op' : ℕ → ℕ → W → W → W × W} {m nb : ℕ} (hop : ∀ b < nb, op b = op' b)
    (x : ℕ → W) : layer op m nb x = layer op' m nb x := by
  funext i
  unfold layer
  by_cases hi : i < nb * (2 * m)
  · rw [hop _ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi))]
  · simp [hi]

end halves

/-- The decimation-in-time layer j with block twiddles T, on nb blocks of 2^(j+1) rows. -/
def cl (T : ℕ → K) (j nb : ℕ) : (ℕ → V) → ℕ → V := layer (fun b _ => dit (T b)) (2 ^ j) nb

/-- A list of layers in order, each layer j with its own twiddles and block count. -/
def runCl (T : ℕ → ℕ → K) (nbf : ℕ → ℕ) (js : List ℕ) (x : ℕ → V) : ℕ → V :=
  js.foldl (fun acc j => cl (T j) j (nbf j) acc) x

/-- The evaluation network on 2^n rows: layers n - 1 down to 0. -/
def evalNet (T : ℕ → ℕ → K) (n : ℕ) (x : ℕ → V) : ℕ → V :=
  runCl T (fun j => 2 ^ (n - 1 - j)) (List.range n).reverse x

theorem runCl_local (T : ℕ → ℕ → K) (nbf : ℕ → ℕ) (H : ℕ) (js : List ℕ)
    (hH : ∀ j ∈ js, nbf j * (2 * 2 ^ j) = H) {x y : ℕ → V} (h : ∀ i < H, x i = y i) :
    ∀ i < H, runCl T nbf js x i = runCl T nbf js y i := by
  induction js generalizing x y with
  | nil => exact h
  | cons j js ih =>
    simp only [runCl, List.foldl_cons] at ih ⊢
    apply ih (fun j hj => hH j (by simp [hj]))
    intro i hi
    have := hH j (by simp)
    exact layer_local _ _ _ (by rw [this]; exact h) i (by rw [this]; exact hi)

/-- The layers below the top one, on the first half.

They form the network of half the size, on the first half's twiddles. -/
theorem runCl_top (T T' : ℕ → ℕ → K) (n : ℕ) (js : List ℕ) (hjs : ∀ j ∈ js, j < n)
    (hT : ∀ j ∈ js, ∀ b < 2 ^ (n - 1 - j), T j b = T' j b) (x : ℕ → V) :
    ∀ i < 2 ^ n, runCl T (fun j => 2 ^ (n - j)) js x i =
      runCl T' (fun j => 2 ^ (n - 1 - j)) js x i := by
  induction js generalizing x with
  | nil => intro i _; rfl
  | cons j js ih =>
    intro i hi
    simp only [runCl, List.foldl_cons] at ih ⊢
    have hj := hjs j (by simp)
    have hsz : ∀ k ∈ js, 2 ^ (n - 1 - k) * (2 * 2 ^ k) = 2 ^ n := fun k hk => by
      have := hjs k (by simp [hk]); rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [ih (fun k hk => hjs k (by simp [hk])) (fun k hk => hT k (by simp [hk])) _ i hi]
    refine runCl_local T' _ _ js hsz (fun i hi => ?_) i hi
    have e : 2 ^ (n - j) = 2 * 2 ^ (n - 1 - j) := by rw [← pow_succ']; congr 1; omega
    have e2 : 2 ^ (n - 1 - j) * (2 * 2 ^ j) = 2 ^ n := by rw [← pow_succ', ← pow_add]; congr 1; omega
    unfold cl
    rw [e]
    exact layer_top _ _ _ _ (fun b hb => by rw [hT j (by simp) b hb]) x i (by rw [e2]; exact hi)

/-- The layers below the top one, on the second half.

They form the network of half the size, on the second half's twiddles and rows. -/
theorem runCl_bot (T T' : ℕ → ℕ → K) (n : ℕ) (js : List ℕ) (hjs : ∀ j ∈ js, j < n)
    (hT : ∀ j ∈ js, ∀ b < 2 ^ (n - 1 - j), T j (2 ^ (n - 1 - j) + b) = T' j b) (x : ℕ → V) :
    ∀ i < 2 ^ n, runCl T (fun j => 2 ^ (n - j)) js x (2 ^ n + i) =
      runCl T' (fun j => 2 ^ (n - 1 - j)) js (fun r => x (2 ^ n + r)) i := by
  induction js generalizing x with
  | nil => intro i _; rfl
  | cons j js ih =>
    intro i hi
    simp only [runCl, List.foldl_cons] at ih ⊢
    have hj := hjs j (by simp)
    have hsz : ∀ k ∈ js, 2 ^ (n - 1 - k) * (2 * 2 ^ k) = 2 ^ n := fun k hk => by
      have := hjs k (by simp [hk]); rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [ih (fun k hk => hjs k (by simp [hk])) (fun k hk => hT k (by simp [hk])) _ i hi]
    refine runCl_local T' _ _ js hsz (fun i hi => ?_) i hi
    have e : 2 ^ (n - j) = 2 * 2 ^ (n - 1 - j) := by rw [← pow_succ']; congr 1; omega
    have e2 : 2 ^ (n - 1 - j) * (2 * 2 ^ j) = 2 ^ n := by rw [← pow_succ', ← pow_add]; congr 1; omega
    unfold cl
    rw [e]
    have := layer_bot (fun b _ => dit (T j b) (V := V)) (2 ^ j) (2 ^ (n - 1 - j)) (by positivity) x i
      (by rw [e2]; exact hi)
    rw [e2] at this
    rw [this]
    exact congrFun (layer_op_congr (fun b hb => by simp only [hT j (by simp) b hb]) _) i


/-! ## The network computes the evaluation -/

/-- The point (-1, 0) of order two. -/
def negOne : C K := C.mk (-1) 0 (by ring)

theorem cl_top (T : ℕ → K) (n : ℕ) (x : ℕ → V) {j : ℕ} (hj : j < 2 ^ n) :
    cl T n 1 x j = x j + T 0 • x (j + 2 ^ n) := by
  unfold cl layer
  simp only [one_mul, show j < 2 * 2 ^ n by omega, ↓reduceIte, Nat.mod_eq_of_lt (show j < 2 * 2 ^ n by omega),
    hj, Nat.div_eq_of_lt (show j < 2 * 2 ^ n by omega), dit]

theorem cl_bot (T : ℕ → K) (n : ℕ) (x : ℕ → V) {j : ℕ} (hj : j < 2 ^ n) :
    cl T n 1 x (2 ^ n + j) = x j - T 0 • x (2 ^ n + j) := by
  unfold cl layer
  have h1 : 2 ^ n + j < 1 * (2 * 2 ^ n) := by omega
  simp only [h1, ↓reduceIte, Nat.mod_eq_of_lt (show 2 ^ n + j < 2 * 2 ^ n by omega),
    show ¬ 2 ^ n + j < 2 ^ n by omega, Nat.div_eq_of_lt (show 2 ^ n + j < 2 * 2 ^ n by omega), dit,
    show 2 ^ n + j - 2 ^ n = j by omega]

theorem basis_one (j : ℕ) (P : C K) : basis 1 j P = P.y ^ bit j 0 := by
  simp [basis]

/-- The circle FFT network on 2^n rows evaluates the coefficients in the FFT basis.

It evaluates at the points of the output rows.

The step g must have order 2^(n - 1), with 2^(n - 2) g = (-1, 0) when n >= 2. -/
theorem evalNet_eq {n : ℕ} (hn : 1 ≤ n) (S g : C K) (hg : 2 ≤ n → 2 ^ (n - 2) • g = negOne)
    (x : ℕ → V) : ∀ i < 2 ^ n, evalNet (twC S g n) n x i = fftEval n x (ptAt S g n i) := by
  induction n, hn using Nat.le_induction generalizing S g x with
  | base =>
    intro i hi
    simp only [evalNet, runCl, List.range_one, List.reverse_singleton, List.foldl_cons,
      List.foldl_nil, fftEval, pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      basis_one]
    unfold cl layer
    interval_cases i <;> simp [twC, ptAt, bit, dit, Plonky3Lean.Spec.Matrix.bitRev, sub_eq_add_neg]
  | succ n hn ih =>
    intro i hi
    have hgn : 2 ^ (n - 1) • g = negOne := by
      have := hg (by omega); rwa [show n + 1 - 2 = n - 1 by omega] at this
    have hg0 : 2 ^ n • g = 0 := by
      rw [show 2 ^ n = 2 * 2 ^ (n - 1) by rw [← pow_succ']; congr 1; omega, mul_nsmul', hgn]
      ext <;> simp [negOne, two_nsmul]
    have hsub : 2 ≤ n → 2 ^ (n - 2) • (2 • g) = negOne := fun h => by
      rw [smul_smul, ← pow_succ, show n - 2 + 1 = n - 1 by omega, hgn]
    have hrev : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
      simp [List.range_succ]
    have hstep : evalNet (twC S g (n + 1)) (n + 1) x = runCl (twC S g (n + 1))
        (fun j => 2 ^ (n - j)) (List.range n).reverse (cl (twC S g (n + 1) n) n 1 x) := by
      simp only [evalNet, hrev, runCl, List.foldl_cons, Nat.add_sub_cancel, Nat.sub_self, pow_zero]
    rw [hstep]
    have ht : twC S g (n + 1) n 0 = (2 ^ (n - 1) • S).x := by
      simp [twC, show n ≠ 0 by omega, Plonky3Lean.Spec.Matrix.bitRev]
    have hv : ∀ (r : ℕ), vn n (S + r • 2 • g) = (2 ^ (n - 1) • S).x := fun r => by
      rw [vn, smul_add, smul_comm (2 ^ (n - 1)) r, smul_smul (2 ^ (n - 1)) 2 g, ← pow_succ,
        show n - 1 + 1 = n by omega, hg0, smul_zero, add_zero]
    have hv' : ∀ (r : ℕ), vn n (S + g + r • 2 • g) = -(2 ^ (n - 1) • S).x := fun r => by
      rw [vn, smul_add, smul_add, smul_comm (2 ^ (n - 1)) r, smul_smul (2 ^ (n - 1)) 2 g, ← pow_succ,
        show n - 1 + 1 = n by omega, hg0, smul_zero, add_zero, hgn]
      simp [negOne]
    rcases Nat.lt_or_ge i (2 ^ n) with hlo | hhi
    · rw [runCl_top _ (twC S (2 • g) n) n _ (by simp) (fun j hj b hb => twC_low S g (by simpa using hj) hb)
        _ i hlo]
      have e := ih S (2 • g) hsub (cl (twC S g (n + 1) n) n 1 x) i hlo
      unfold evalNet at e
      rw [e, ptAt_low S g hn hlo, fftEval_succ hn]
      unfold fftEval
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < 2 ^ n := by simpa using hj
      have hvP : vn n (ptAt S (2 • g) n i) = (2 ^ (n - 1) • S).x := by
        unfold ptAt; split_ifs
        · exact hv _
        · rw [vn_neg]; exact hv _
      rw [cl_top _ n x hj', ht, hvP]
    · obtain ⟨i', rfl⟩ : ∃ i', i = 2 ^ n + i' := ⟨i - 2 ^ n, by omega⟩
      have hi' : i' < 2 ^ n := by rw [pow_succ] at hi; omega
      rw [runCl_bot _ (twC (S + g) (2 • g) n) n _ (by simp)
        (fun j hj b hb => twC_high S g (by simpa using hj) hb) _ i' hi']
      have e := ih (S + g) (2 • g) hsub (fun r => cl (twC S g (n + 1) n) n 1 x (2 ^ n + r)) i' hi'
      unfold evalNet at e
      rw [e, ptAt_high S g hn hi', fftEval_succ hn]
      unfold fftEval
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < 2 ^ n := by simpa using hj
      have hvP : vn n (ptAt (S + g) (2 • g) n i') = -(2 ^ (n - 1) • S).x := by
        unfold ptAt; split_ifs
        · exact hv' _
        · rw [vn_neg]; exact hv' _
      simp only []
      rw [cl_bot _ n x hj', ht, hvP, add_comm j (2 ^ n), neg_smul, sub_eq_add_neg]

end Plonky3Lean.Proofs.Circle
