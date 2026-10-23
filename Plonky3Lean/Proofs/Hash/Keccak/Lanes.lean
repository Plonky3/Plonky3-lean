module

public import Plonky3Lean.Spec.Keccak
public import Mathlib.Data.Fin.Basic
public import Batteries.Data.BitVec
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Keccak-f[1600] on lanes

A lane is the 64-bit word `A[x, y, 0..63]`, with bit `z` of the lane at bit `z` of the word.

The 25 lanes are listed `x` fastest, as in the bit string of FIPS 202, 3.1.3.

```text
    lane x + 5 y  =  bits 64 (5 y + x) .. 64 (5 y + x) + 63 of S
```

Each step mapping of FIPS 202 is a word operation on lanes.

Theta and chi read neighbouring lanes, rho rotates each lane, and pi moves lanes.
-/

namespace Plonky3Lean.Proofs.Keccak

open Plonky3Lean.Spec.Keccak

/-- A lane. -/
abbrev Word := BitVec 64

/-- Lane `i`, or zero past the end. -/
def lane (L : List Word) (i : ℕ) : Word := L.getD i 0

/-- The state array whose lane `(x, y)` is word `x + 5 y`. -/
def ofLanes (L : List Word) : State := fun x y z => (lane L (x.val + 5 * y.val)).getLsbD z.val

/-- The column parity `C[x]`. -/
def parity (L : List Word) (x : ℕ) : Word :=
  lane L x ^^^ lane L (x + 5) ^^^ lane L (x + 10) ^^^ lane L (x + 15) ^^^ lane L (x + 20)

def thetaL (L : List Word) : List Word :=
  List.ofFn fun i : Fin 25 =>
    lane L i ^^^ (parity L ((i.val % 5 + 4) % 5) ^^^ (parity L ((i.val % 5 + 1) % 5)).rotateLeft 1)

/-- Lane `(x, y)` reached after `t` steps of Algorithm 2, as the index `x + 5 y`. -/
def walk (t : ℕ) : ℕ := let p := rhoStep^[t] (1, 0); p.1.val + 5 * p.2.val

/-- The rotation of lane `i` in rho: `(t + 1) (t + 2) / 2 mod 64` for the step `t` that reaches it. -/
def rhoOffset (i : ℕ) : ℕ :=
  (((List.range 24).find? fun t => walk t = i).map fun t => (t + 1) * (t + 2) / 2 % 64).getD 0

/-- The 25 rotations of rho, lane by lane. -/
def rhoOffsets : List ℕ := (List.range 25).map rhoOffset

def rhoL (L : List Word) : List Word :=
  List.ofFn fun i : Fin 25 => (lane L i).rotateLeft (rhoOffsets.getD i 0)

def piL (L : List Word) : List Word :=
  List.ofFn fun i : Fin 25 => lane L ((i.val % 5 + 3 * (i.val / 5)) % 5 + 5 * (i.val % 5))

def chiL (L : List Word) : List Word :=
  List.ofFn fun i : Fin 25 =>
    lane L i ^^^ (~~~lane L ((i.val % 5 + 1) % 5 + 5 * (i.val / 5)) &&&
      lane L ((i.val % 5 + 2) % 5 + 5 * (i.val / 5)))

/-- The round constant of round `i_r` as a word: bit `z` is `RC[z]`. -/
def rcWord (ir : ℕ) : Word := BitVec.ofFnLE (roundConstant ir)

def iotaL (L : List Word) (rc : Word) : List Word := L.set 0 (lane L 0 ^^^ rc)

/-- Theta, rho, pi and chi. -/
def stepsL (L : List Word) : List Word := chiL (piL (rhoL (thetaL L)))

def roundL (L : List Word) (ir : ℕ) : List Word := iotaL (stepsL L) (rcWord ir)

/-- The 24 rounds on lanes. -/
def keccakFL (L : List Word) : List Word := (List.range 24).foldl roundL L

/-! ## Each step on lanes is the step of FIPS 202 -/

theorem lane_ofFn (f : Fin 25 → Word) (i : ℕ) (h : i < 25) : lane (List.ofFn f) i = f ⟨i, h⟩ := by
  rw [lane, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [h]

/-- Bit `z` of a rotation by `r < 64` is bit `z - r` mod 64. -/
theorem getLsbD_rotateLeft' (w : Word) {r : ℕ} (hr : r < 64) (z : Fin 64) :
    (w.rotateLeft r).getLsbD z.val = w.getLsbD (z - Fin.ofNat 64 r).val := by
  rw [BitVec.getLsbD_rotateLeft]
  simp only [Fin.sub_def, Fin.ofNat, Nat.mod_eq_of_lt hr]
  split
  · congr 1; omega
  · simp only [z.isLt, decide_true, Bool.true_and]; congr 1; omega

theorem ofLanes_val (L : List Word) (x y : Fin 5) (z : Fin 64) :
    ofLanes L x y z = (lane L (x.val + 5 * y.val)).getLsbD z.val := rfl

theorem parity_bit (L : List Word) (x : Fin 5) (z : Fin 64) :
    (parity L x.val).getLsbD z.val =
      (ofLanes L x 0 z ^^ ofLanes L x 1 z ^^ ofLanes L x 2 z ^^ ofLanes L x 3 z ^^ ofLanes L x 4 z) := by
  simp [parity, ofLanes]

theorem theta_eq (L : List Word) : ofLanes (thetaL L) = theta (ofLanes L) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  rw [ofLanes_val, thetaL, lane_ofFn _ _ (by omega)]
  have h1 : (x.val + 5 * y.val) % 5 = x.val := by omega
  simp only [h1, BitVec.getLsbD_xor]
  have e4 : (x.val + 4) % 5 = (x - 1 : Fin 5).val := by simp [Fin.sub_def]; omega
  have e1 : (x.val + 1) % 5 = (x + 1 : Fin 5).val := by simp [Fin.val_add]
  rw [e4, e1, parity_bit, getLsbD_rotateLeft' _ (by decide : 1 < 64), parity_bit]
  simp only [theta, ofLanes_val]
  rfl

theorem pi_eq (L : List Word) : ofLanes (piL L) = pi (ofLanes L) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  rw [ofLanes_val, piL, lane_ofFn _ _ (by omega)]
  simp only [pi, ofLanes_val, Fin.val_add, Fin.val_mul]
  congr 3 <;> omega

theorem chi_eq (L : List Word) : ofLanes (chiL L) = chi (ofLanes L) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  rw [ofLanes_val, chiL, lane_ofFn _ _ (by omega)]
  simp only [chi, ofLanes_val, Fin.val_add, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, z.isLt,
    decide_true, Bool.true_and, Bool.xor_true]
  have e1 : ((x.val + 5 * y.val) % 5 + 1) % 5 + 5 * ((x.val + 5 * y.val) / 5) =
      (x.val + (1 : Fin 5).val) % 5 + 5 * y.val := by simp only [Fin.val_one]; omega
  have e2 : ((x.val + 5 * y.val) % 5 + 2) % 5 + 5 * ((x.val + 5 * y.val) / 5) =
      (x.val + (2 : Fin 5).val) % 5 + 5 * y.val := by simp only [Fin.val_two]; omega
  rw [e1, e2]

theorem getLsbD_rcWord (ir : ℕ) (z : Fin 64) : (rcWord ir).getLsbD z.val = roundConstant ir z := by
  exact BitVec.getLsb_ofFnLE (roundConstant ir) z

theorem iota_eq (L : List Word) (hL : L.length = 25) (ir : ℕ) :
    ofLanes (iotaL L (rcWord ir)) = iota (ofLanes L) ir := by
  funext x y z
  simp only [ofLanes_val, iotaL, iota, lane, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    simpa [hL] using getLsbD_rcWord ir z
  · have hne : ¬ 0 = x.val + 5 * y.val := fun e => h ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
    simp [hne, h]

/-- A map from each position of a state to the position it is read from. -/
abbrev Positions := Fin 5 → Fin 5 → Fin 64 → Fin 5 × Fin 5 × Fin 64

/-- The state `A` read at the positions `g`. -/
def readAt (A : State) (g : Positions) : State := fun x y z => let q := g x y z; A q.1 q.2.1 q.2.2

/-- Algorithm 2's step on positions instead of bits. -/
def rhoUpdatePos (acc : Positions × (Fin 5 × Fin 5)) (t : ℕ) : Positions × (Fin 5 × Fin 5) :=
  let (g, (x, y)) := acc
  (fun x' y' z => if x' = x ∧ y' = y then (x, y, z - Fin.ofNat 64 ((t + 1) * (t + 2) / 2)) else g x' y' z,
    rhoStep (x, y))

/-- Algorithm 2 only moves bits: it reads `A` at positions that do not depend on `A`. -/
theorem foldl_rhoUpdate (A : State) (ts : List ℕ) (g : Positions) (p : Fin 5 × Fin 5) :
    ts.foldl (rhoUpdate A) (readAt A g, p) =
      (readAt A (ts.foldl rhoUpdatePos (g, p)).1, (ts.foldl rhoUpdatePos (g, p)).2) := by
  induction ts generalizing g p with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    obtain ⟨x, y⟩ := p
    simp only [rhoUpdate, rhoUpdatePos]
    congr 2
    funext x' y' z
    simp only [readAt]
    split <;> rfl

/-- The positions rho reads, in closed form: lane `(x, y)` rotated by its offset, lane `(0, 0)` unchanged. -/
theorem rho_positions : ∀ x y z,
    ((List.range 24).foldl rhoUpdatePos (fun x y z => (x, y, z), (1, 0))).1 x y z =
      (x, y, z - Fin.ofNat 64 (rhoOffsets.getD (x.val + 5 * y.val) 0)) := by
  decide +kernel

theorem rhoOffsets_lt (i : ℕ) : rhoOffsets.getD i 0 < 64 := by
  have h : ∀ r ∈ rhoOffsets, r < 64 := by decide
  rw [List.getD_eq_getElem?_getD]
  cases e : rhoOffsets[i]? with
  | none => simp
  | some r => exact h r (List.mem_of_getElem? e)

theorem rho_eq (L : List Word) : ofLanes (rhoL L) = rho (ofLanes L) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have h := foldl_rhoUpdate (ofLanes L) (List.range 24) (fun x y z => (x, y, z)) (1, 0)
  rw [rho, show ((ofLanes L, (1, 0)) : State × (Fin 5 × Fin 5)) =
    (readAt (ofLanes L) fun x y z => (x, y, z), (1, 0)) from rfl, h]
  simp only [readAt, rho_positions]
  rw [ofLanes_val, rhoL, lane_ofFn _ _ (by omega), getLsbD_rotateLeft' _ (rhoOffsets_lt _)]
  rfl

/-! ## Rounds -/

theorem length_stepsL (L : List Word) : (stepsL L).length = 25 := by simp [stepsL, chiL]

theorem length_roundL (L : List Word) (ir : ℕ) : (roundL L ir).length = 25 := by
  simp [roundL, iotaL, length_stepsL]

theorem roundL_eq (L : List Word) (ir : ℕ) : ofLanes (roundL L ir) = rnd (ofLanes L) ir := by
  rw [roundL, iota_eq _ (length_stepsL L), stepsL, chi_eq, pi_eq, rho_eq, theta_eq, rnd]

theorem foldl_roundL (L : List Word) (ts : List ℕ) :
    ofLanes (ts.foldl roundL L) = ts.foldl (fun A k => rnd A k) (ofLanes L) := by
  induction ts generalizing L with
  | nil => rfl
  | cons t ts ih => simp only [List.foldl_cons, ih, roundL_eq]

/-- The 24 rounds on lanes are Keccak-p[1600, 24], whose rounds are numbered 0 to 23. -/
theorem keccakFL_eq (L : List Word) : ofLanes (keccakFL L) = keccakP 24 (ofLanes L) := by
  rw [keccakFL, foldl_roundL, keccakP]
  simp

/-! ## Bit strings -/

/-- The bit string of FIPS 202, 3.1.3, of a list of lanes: each lane's 64 bits, least significant first. -/
def toBits (L : List Word) : List Bool := L.flatMap fun w => (List.finRange 64).map fun z => w.getLsbD z

/-- Entry `k` of a concatenation of blocks of length `m` is entry `k % m` of block `k / m`. -/
theorem getD_flatMap_uniform {α β : Type} (l : List α) (f : α → List β) {m : ℕ} (hf : ∀ a, (f a).length = m)
    (d : β) (k : ℕ) (a₀ : α) (hk : k < m * l.length) :
    (l.flatMap f).getD k d = (f (l.getD (k / m) a₀)).getD (k % m) d := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · simp [h] at hk
      · exact h
    rw [List.flatMap_cons]
    by_cases hkm : k < m
    · rw [List.getD_append _ _ _ _ (by rw [hf]; exact hkm), Nat.div_eq_of_lt hkm, Nat.mod_eq_of_lt hkm]
      rfl
    · have hk' : k - m < m * l.length := by
        simp only [List.length_cons, Nat.mul_succ] at hk; omega
      have e1 : k / m = (k - m) / m + 1 := Nat.div_eq_sub_div hm (by omega)
      have e2 : k % m = (k - m) % m := Nat.mod_eq_sub_mod (by omega)
      rw [List.getD_append_right _ _ _ _ (by rw [hf]; omega), hf, ih _ hk', e1, e2]
      rfl

theorem length_toBits (L : List Word) : (toBits L).length = 64 * L.length := by
  simp [toBits, List.length_flatMap, Nat.mul_comm]

theorem ofString_toBits (L : List Word) (hL : L.length = 25) : stateOfString (toBits L) = ofLanes L := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  rw [stateOfString, toBits, getD_flatMap_uniform (m := 64) _ _ (fun _ => by simp) _ _ 0 (by rw [hL]; omega), ofLanes_val, lane]
  have e1 : (64 * (5 * y.val + x.val) + z.val) / 64 = x.val + 5 * y.val := by omega
  have e2 : (64 * (5 * y.val + x.val) + z.val) % 64 = z.val := by omega
  rw [e1, e2, List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [hz]

theorem getD_finRange {n : ℕ} (i : ℕ) (h : i < n) (d : Fin n) : (List.finRange n).getD i d = ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_finRange]
  rfl

theorem length_stringOfState (A : State) : (stringOfState A).length = 1600 := by
  simp [stringOfState, List.length_flatMap]

theorem stringOfState_ofLanes (L : List Word) (hL : L.length = 25) : stringOfState (ofLanes L) = toBits L := by
  apply List.ext_getElem (by rw [length_stringOfState, length_toBits, hL])
  intro k h1 h2
  rw [length_stringOfState] at h1
  rw [← List.getD_eq_getElem _ false, ← List.getD_eq_getElem _ false, stringOfState, toBits,
    getD_flatMap_uniform (m := 320) _ _ (fun _ => by simp [List.length_flatMap]) _ _ 0 (by simp; omega),
    getD_finRange _ (by omega),
    getD_flatMap_uniform (m := 64) _ _ (fun _ => by simp) _ _ 0 (by simp; omega),
    getD_finRange _ (by omega),
    getD_flatMap_uniform (m := 64) _ _ (fun _ => by simp) _ _ 0 (by rw [hL]; omega)]
  have e1 : k % 320 / 64 + 5 * (k / 320) = k / 64 := by omega
  have e2 : k % 320 % 64 = k % 64 := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, e2]
  simp only [List.getElem?_eq_getElem (show k % 64 < (List.finRange 64).length by simp; omega),
    List.getElem_finRange, Option.map_some, Option.getD_some]
  show (lane L (k % 320 / 64 + 5 * (k / 320))).getLsbD (k % 64) = _
  rw [e1, lane, List.getD_eq_getElem?_getD]
  rfl

theorem length_keccakFL (L : List Word) (hL : L.length = 25) : (keccakFL L).length = 25 := by
  rw [keccakFL]
  generalize List.range 24 = ts
  induction ts generalizing L with
  | nil => exact hL
  | cons t ts ih => exact ih _ (length_roundL _ _)

/-- Keccak-f[1600] on the bit string of 25 lanes is the bit string of the lanes after 24 rounds. -/
theorem keccakF_toBits (L : List Word) (hL : L.length = 25) : keccakF (toBits L) = toBits (keccakFL L) := by
  rw [keccakF, ofString_toBits _ hL, ← keccakFL_eq, stringOfState_ofLanes _ (length_keccakFL _ hL)]

end Plonky3Lean.Proofs.Keccak
