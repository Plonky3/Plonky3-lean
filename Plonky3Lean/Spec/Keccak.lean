module

public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Iterate
public import Batteries.Data.BitVec

@[expose] public section

/-!
# Keccak-f[1600], Keccak-256 and SHA3-256, from FIPS 202

Section and algorithm numbers are those of FIPS 202 (August 2015).

* **The state array** (3.1): A[x, y, z], with x, y < 5 and z < w = 64, and its bit string S.
* **The step mappings** (3.2): theta, rho, pi, chi and iota.
  The round constants come from the LFSR of Algorithm 5.
* **The permutation** (3.3, 3.4): 24 rounds, numbered 0 to 23.
* **The sponge** (4, 5.1): Algorithm 8 with the padding pad10*1.
* **The hashes** (6.1): SHA3-256 appends the two bits 01 before padding.

  Keccak-256, from the Keccak team's SHA-3 submission (version 3, 2011), appends nothing.

* **Bytes** (B.1): bit j of byte i is bit 8 i + j of the string.

Nothing here refers to the model.
-/

namespace Plonky3Lean.Spec.Keccak

/-! ## 3.1: the state array -/

/-- A state array A[x, y, z] of Keccak-f[1600]: b = 1600, w = 64, l = 6. -/
abbrev State := Fin 5 → Fin 5 → Fin 64 → Bool

/-- 3.1.2: A[x, y, z] = S[w (5 y + x) + z]. -/
def stateOfString (S : List Bool) : State := fun x y z => S.getD (64 * (5 * y.val + x.val) + z.val) false

/-- 3.1.3: the lanes A[x, y, 0..63], x fastest, concatenated plane by plane. -/
def stringOfState (A : State) : List Bool :=
  (List.finRange 5).flatMap fun y => (List.finRange 5).flatMap fun x => (List.finRange 64).map (A x y)

/-! ## 3.2: the step mappings -/

/-- 3.2.1, Algorithm 1. -/
def theta (A : State) : State :=
  let C : Fin 5 → Fin 64 → Bool := fun x z => A x 0 z ^^ A x 1 z ^^ A x 2 z ^^ A x 3 z ^^ A x 4 z
  let D : Fin 5 → Fin 64 → Bool := fun x z => C (x - 1) z ^^ C (x + 1) (z - 1)
  fun x y z => A x y z ^^ D x z

/-- The step (x, y) <- (y, (2 x + 3 y) mod 5) of Algorithm 2. -/
def rhoStep (p : Fin 5 × Fin 5) : Fin 5 × Fin 5 := (p.2, 2 * p.1 + 3 * p.2)

/-- Step t of Algorithm 2.

Lane (x, y) of A' becomes lane (x, y) of A, shifted by (t + 1) (t + 2) / 2. -/
def rhoUpdate (A : State) (acc : State × (Fin 5 × Fin 5)) (t : ℕ) : State × (Fin 5 × Fin 5) :=
  let (A', (x, y)) := acc
  (fun x' y' z => if x' = x ∧ y' = y then A x y (z - Fin.ofNat 64 ((t + 1) * (t + 2) / 2)) else A' x' y' z,
    rhoStep (x, y))

/-- 3.2.2, Algorithm 2.

A' starts as A, with (x, y) = (1, 0), and steps t = 0, ..., 23 follow. -/
def rho (A : State) : State := ((List.range 24).foldl (rhoUpdate A) (A, (1, 0))).1

/-- 3.2.3, Algorithm 3. -/
def pi (A : State) : State := fun x y z => A (x + 3 * y) x z

/-- 3.2.4, Algorithm 4. -/
def chi (A : State) : State := fun x y z => A x y z ^^ ((A (x + 1) y z ^^ true) && A (x + 2) y z)

/-- One step of the LFSR of Algorithm 5, on R = R[0] ... R[7]. -/
def lfsrStep (R : List Bool) : List Bool :=
  let R := false :: R
  let b := R.getD 8 false
  let R := (((R.modify 0 (· ^^ b)).modify 4 (· ^^ b)).modify 5 (· ^^ b)).modify 6 (· ^^ b)
  R.take 8

/-- 3.2.5, Algorithm 5: the bit rc(t). -/
def rc (t : ℕ) : Bool :=
  if t % 255 = 0 then true
  else (lfsrStep^[t % 255] [true, false, false, false, false, false, false, false]).getD 0 false

/-- Steps 2 and 3 of Algorithm 6: the round constant RC of round i_r. -/
def roundConstant (ir : ℕ) : Fin 64 → Bool :=
  (List.range 7).foldl (fun RC j => Function.update RC (Fin.ofNat 64 (2 ^ j - 1)) (rc (j + 7 * ir)))
    fun _ => false

/-- 3.2.5, Algorithm 6. -/
def iota (A : State) (ir : ℕ) : State :=
  fun x y z => if x = 0 ∧ y = 0 then A x y z ^^ roundConstant ir z else A x y z

/-! ## 3.3 and 3.4: the permutation -/

/-- 3.3: Rnd(A, i_r). -/
def rnd (A : State) (ir : ℕ) : State := iota (chi (pi (rho (theta A)))) ir

/-- 3.3, Algorithm 7, at b = 1600: rounds 12 + 2 l - n_r to 12 + 2 l - 1. -/
def keccakP (nr : ℕ) (A : State) : State :=
  (List.range nr).foldl (fun A k => rnd A (12 + 2 * 6 - nr + k)) A

/-- 3.4: Keccak-f[1600] = Keccak-p[1600, 24], on bit strings. -/
def keccakF (S : List Bool) : List Bool := stringOfState (keccakP 24 (stateOfString S))

/-! ## 4 and 5.1: the sponge -/

/-- 5.1, Algorithm 9: pad10*1(x, m) = 1 || 0^j || 1 with j = (-m - 2) mod x. -/
def pad101 (x m : ℕ) : List Bool :=
  true :: List.replicate ((x - (m + 2) % x) % x) false ++ [true]

/-- The k output blocks of steps 8 to 10 of Algorithm 8.

They are Trunc_r(S), Trunc_r(f(S)), and so on. -/
def squeeze (f : List Bool → List Bool) (r : ℕ) : ℕ → List Bool → List Bool
  | 0, _ => []
  | k + 1, S => S.take r ++ squeeze f r k (f S)

/-- 4, Algorithm 8: SPONGE[f, pad, r](N, d), with b = 1600. -/
def sponge (f : List Bool → List Bool) (pad : ℕ → ℕ → List Bool) (r : ℕ) (N : List Bool) (d : ℕ) :
    List Bool :=
  let P := N ++ pad r N.length
  let n := P.length / r
  let c := 1600 - r
  let S := (List.range n).foldl
    (fun S i => f (List.zipWith (· ^^ ·) S ((P.drop (i * r)).take r ++ List.replicate c false)))
    (List.replicate 1600 false)
  (squeeze f r (d / r + 1) S).take d

/-- 5.2: KECCAK[c](N, d). -/
def keccakC (c : ℕ) (N : List Bool) (d : ℕ) : List Bool := sponge keccakF pad101 (1600 - c) N d

/-! ## 6.1: the hashes -/

/-- 6.1: SHA3-256(M) = KECCAK[512](M || 01, 256). -/
def sha3_256Bits (M : List Bool) : List Bool := keccakC 512 (M ++ [false, true]) 256

/-- Keccak-256 of the SHA-3 submission: KECCAK[512](M, 256), with no suffix. -/
def keccak256Bits (M : List Bool) : List Bool := keccakC 512 M 256

/-! ## B.1: bytes -/

/-- A byte. -/
abbrev Byte := BitVec 8

/-- B.1: byte i gives bits 8 i to 8 i + 7, least significant bit first. -/
def bitsOfBytes (M : List Byte) : List Bool := M.flatMap fun b => List.ofFn fun j : Fin 8 => b.getLsbD j

/-- B.1: the bytes of a bit string.

Byte i holds bits 8 i to 8 i + 7, least significant first. -/
def bytesOfBits (S : List Bool) : List Byte :=
  (List.range (S.length / 8)).map fun i => BitVec.ofFnLE fun j : Fin 8 => S.getD (8 * i + j) false

/-- SHA3-256 of a byte string. -/
def sha3_256 (M : List Byte) : List Byte := bytesOfBits (sha3_256Bits (bitsOfBytes M))

/-- Keccak-256 of a byte string. -/
def keccak256 (M : List Byte) : List Byte := bytesOfBits (keccak256Bits (bitsOfBytes M))

end Plonky3Lean.Spec.Keccak
