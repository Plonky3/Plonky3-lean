module

public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Nat.Digits.Lemmas

@[expose] public section

/-!
# Reducing a uniform value to bits, an index or a smaller field

Every challenger turns a uniform value into a smaller one by one of three reductions.

* **Low bits.** Keep `x mod 2^b` of a canonical field element `x < p`.
* **Rejection.** Keep `x mod 2^k` of a value that passed a range test.
* **Modular reduction.** Keep `x mod p` of a uniform integer `x < N`.

For each, the exact number of preimages of every output is counted.

A uniform input gives an output whose probability is that count over the input range.

```text
    p = 7, b = 2:   x       0 1 2 3 4 5 6
                    x mod 4 0 1 2 3 0 1 2      counts 2 2 2 1
```
-/

namespace Plonky3Lean.Proofs.Challenger.Bits

/-! ## Counting residues -/

/-- Among `0, ..., n - 1`, the values with residue `v` modulo `r` number `n / r`, plus one when `v < n mod r`. -/
theorem count_mod_eq (n r v : ℕ) (hr : 0 < r) (hv : v < r) :
    Nat.count (fun x => x % r = v) n = n / r + if v < n % r then 1 else 0 := by
  have h := Nat.count_modEq_card n hr v
  rw [Nat.mod_eq_of_lt hv] at h
  rw [← h]
  congr 1
  funext x
  simp only [Nat.ModEq, Nat.mod_eq_of_lt hv]

/-- Each residue has `n / r` or `n / r + 1` preimages, so its probability is within `1 / n` of `1 / r`. -/
theorem count_mod_bounds (n r v : ℕ) (hr : 0 < r) (hv : v < r) :
    n < (Nat.count (fun x => x % r = v) n + 1) * r ∧ Nat.count (fun x => x % r = v) n * r < n + r := by
  rw [count_mod_eq n r v hr hv]
  have h1 := Nat.div_add_mod' n r
  have h2 := Nat.mod_lt n hr
  split_ifs with h <;> constructor <;> simp only [add_mul, one_mul, add_zero] <;> omega

/-- When `r` divides `n`, every residue has exactly `n / r` preimages: the output is uniform. -/
theorem count_mod_of_dvd (n r v : ℕ) (hr : 0 < r) (hv : v < r) (h : r ∣ n) :
    Nat.count (fun x => x % r = v) n = n / r := by
  rw [count_mod_eq n r v hr hv, Nat.mod_eq_zero_of_dvd h]
  simp

/-! ## The low bits of a field element -/

/-- The low `b` bits of a uniform canonical element of `F_p` take the value `v` for `p / 2^b` or `p / 2^b + 1` elements.

This is the distribution `sample_bits` returns. -/
theorem lowBits_count (p b v : ℕ) (hv : v < 2 ^ b) :
    Nat.count (fun x => x % 2 ^ b = v) p = p / 2 ^ b + if v < p % 2 ^ b then 1 else 0 :=
  count_mod_eq p (2 ^ b) v (Nat.two_pow_pos b) hv

/-- The probability of each `b`-bit value is within `1 / p` of `2^-b`, as the code's comment states. -/
theorem lowBits_bias (p b v : ℕ) (hv : v < 2 ^ b) :
    p < (Nat.count (fun x => x % 2 ^ b = v) p + 1) * 2 ^ b ∧
      Nat.count (fun x => x % 2 ^ b = v) p * 2 ^ b < p + 2 ^ b :=
  count_mod_bounds p (2 ^ b) v (Nat.two_pow_pos b) hv

/-- Proof of work accepts the elements whose low `b` bits are zero: there are `ceil(p / 2^b)` of them. -/
theorem pow_accept_count (p b : ℕ) :
    Nat.count (fun x => x % 2 ^ b = 0) p = p / 2 ^ b + if p % 2 ^ b = 0 then 0 else 1 := by
  rw [lowBits_count p b 0 (Nat.two_pow_pos b)]
  split_ifs <;> omega

/-- No low bit is fixed by the modulus: every pattern of `b` bits occurs once `2^b <= p`. -/

theorem every_pattern_occurs (p b v : ℕ) (hv : v < 2 ^ b) (hp : 2 ^ b ≤ p) :
    0 < Nat.count (fun x => x % 2 ^ b = v) p := by
  rw [lowBits_count p b v hv]
  have : 0 < p / 2 ^ b := Nat.div_pos hp (Nat.two_pow_pos b)
  omega

/-! ## Rejection to a multiple of `2^k` -/

/-- Below a multiple `m` of `2^k`, each `k`-bit value has `m / 2^k` preimages.

`sample_uniform_bits` rejects every canonical value at or above `m_k = floor(p / 2^k) 2^k`, so its bits are exactly uniform. -/
theorem uniform_below_multiple (p k v : ℕ) (hv : v < 2 ^ k) :
    Nat.count (fun x => x % 2 ^ k = v) (p / 2 ^ k * 2 ^ k) = p / 2 ^ k :=
  by rw [count_mod_of_dvd _ _ v (Nat.two_pow_pos k) hv (Nat.dvd_mul_left _ _),
    Nat.mul_div_cancel _ (Nat.two_pow_pos k)]

/-- The rejected canonical values number `p mod 2^k`. -/
theorem rejected_count (p k : ℕ) : p - p / 2 ^ k * 2 ^ k = p % 2 ^ k := by
  have := Nat.div_add_mod p (2 ^ k)
  rw [Nat.mul_comm] at this
  omega

/-! ## Rejection sampling from bytes -/

/-- An `n`-bit word masked to `k <= n` bits gives each `k`-bit value for `2^(n - k)` words.

The serializing challengers mask a uniform `u32` or `u64` and keep it if below `p`, so each accepted field element is equally likely, and `sample_bits` on bytes is exactly uniform. -/
theorem word_mask_count (n k v : ℕ) (hk : k ≤ n) (hv : v < 2 ^ k) :
    Nat.count (fun x => x % 2 ^ k = v) (2 ^ n) = 2 ^ (n - k) := by
  rw [count_mod_of_dvd _ _ v (Nat.two_pow_pos k) hv (Nat.pow_dvd_pow 2 hk),
    Nat.pow_div hk (by norm_num)]

/-! ## Modular reduction of a long integer -/

/-- Reducing a uniform integer below `N` modulo `p` gives each residue within `1 / N` of `1 / p`. -/
theorem modReduce_bias (N p v : ℕ) (hp : 0 < p) (hv : v < p) :
    N < (Nat.count (fun x => x % p = v) N + 1) * p ∧ Nat.count (fun x => x % p = v) N * p < N + p :=
  count_mod_bounds N p v hp hv

/-- The `Ns + 16` rule: with `ceil(bits / 8) + 16` bytes and `p < 2^bits`, the modulus is below `2^-128` of the input range. -/
theorem extraBytes_budget (p bits : ℕ) (hp : p < 2 ^ bits) :
    p * 2 ^ 128 < 256 ^ ((bits + 7) / 8 + 16) := by
  have h1 : 2 ^ bits ≤ 256 ^ ((bits + 7) / 8) := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc p * 2 ^ 128 < 2 ^ bits * 2 ^ 128 := by
        exact Nat.mul_lt_mul_of_pos_right hp (by positivity)
    _ ≤ 256 ^ ((bits + 7) / 8) * 256 ^ 16 := by
        exact Nat.mul_le_mul h1 (by norm_num)
    _ = 256 ^ ((bits + 7) / 8 + 16) := by rw [pow_add]

/-! ## Packing small field elements into a large one -/

/-- Base-`2^b` packing of digits below `2^b` is injective on lists of one length.

The multi-field challenger packs scalars this way.

While the packed value stays below the sponge field's order, no two pending runs share a rate cell. -/
theorem packing_injective (b : ℕ) (hb : 0 < b) (xs ys : List ℕ) (hl : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x < 2 ^ b) (hy : ∀ y ∈ ys, y < 2 ^ b)
    (h : Nat.ofDigits (2 ^ b) xs = Nat.ofDigits (2 ^ b) ys) : xs = ys :=
  Nat.ofDigits_inj_of_len_eq (Nat.one_lt_two_pow hb.ne') hl hx hy h

end Plonky3Lean.Proofs.Challenger.Bits
