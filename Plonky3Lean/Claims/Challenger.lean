module

public import Plonky3Lean.Proofs.Challenger.Duplex
public import Plonky3Lean.Proofs.Challenger.Grinding
public import Plonky3Lean.Proofs.Challenger.Fields
public import Plonky3Lean.Proofs.Challenger.Hash

@[expose] public section

/-!
# p3-challenger: claims

These claims hold at the Plonky3 commit pinned in `plonky3/`.

The model is the scoped extraction in `crates/challenger`.

It adds the transcriptions in `crates/challenger/extraction/P3Challenger/Mirror/`.

The field, the permutation and the hasher stay abstract.

A field enters through the trait-dictionary members the code calls.

Each member is assumed to compute what its name says.

The specification is the duplex construction of Bertoni, Daemen, Peeters and Van Assche.

It comes from "Duplexing the sponge" (SAC 2011).

It runs in overwrite mode, with the block length added to the first capacity cell.

## What the claims find

- every transcript of observations and samples returns the samples of the duplex construction
- the sample after an observation permutes a block ending with it, so no stale output survives
- the length tag separates blocks only when the characteristic q exceeds the rate r
- for q <= r, a block collides with its extension by q zeros
- the low bits of a canonical element are biased by at most 1 / p per value
- proof of work accepts ceil(p / 2^b) elements, and the modulus fixes no low bit
- the multi-field constructor accepts a BabyBear sampler over a KoalaBear sponge
- every sample of that challenger panics
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Plonky3Lean.Spec.Duplex Plonky3Lean.Proofs.Challenger Plonky3Lean.Proofs.Symmetric
open p3_challenger.mirror

namespace Plonky3Lean.Claims.P3Challenger

/-! ## The duplex challenger, as extracted -/

/-- With rate r and width w, the constructor panics exactly when 0 < r < w or r <= 255 fails.

Otherwise the sponge is w copies of the default value.

Both buffers start empty. -/
theorem duplex_challenger.DuplexChallenger.new.eq {F P : Type} {W : Std.Usize} (R : Std.Usize)
    (copyInst : core.marker.Copy F)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array F W))
    (defInst : core.default.Default F) (hcopy : CloneIsId copyInst) (z : F)
    (hz : defInst.default = .ok z) (p : P) :
    (¬ (0 < R.val ∧ R.val < W.val ∧ R.val ≤ 255) →
      p3_challenger.duplex_challenger.DuplexChallenger.new R copyInst permInst defInst p = .fail .panic) ∧
    (0 < R.val ∧ R.val < W.val ∧ R.val ≤ 255 →
      ∃ c, p3_challenger.duplex_challenger.DuplexChallenger.new R copyInst permInst defInst p = .ok c ∧
        toSt c = ⟨List.replicate W.val z, [], []⟩ ∧ c.permutation = p) :=
  new_eq R copyInst permInst defInst hcopy z hz p

/-- The duplexing step makes four moves:

- it overwrites the rate with the pending inputs, then zeros
- it adds the number of inputs to the first capacity cell
- it permutes the state
- it refills the outputs with the new rate

It never panics while at most r inputs are pending, for rate r. -/
theorem duplex_challenger.DuplexChallenger.duplexing.eq_spec {F P : Type} [AddMonoidWithOne F]
    {W R : Std.Usize} (copyInst : core.marker.Copy F)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array F W))
    (ringInst : p3_field.field.PrimeCharacteristicRing F)
    (hcopy : CloneIsId copyInst) (hring : RingComputes ringInst) (f : List F → List F)
    (c : p3_challenger.duplex_challenger.DuplexChallenger F P W R)
    (hf : PermComputes permInst c.permutation f) (hRW : R.val < W.val) (h255 : R.val ≤ 255)
    (hin : c.input_buffer.val.length ≤ R.val) :
    ∃ c', p3_challenger.duplex_challenger.DuplexChallenger.duplexing copyInst permInst ringInst c = .ok c' ∧
      toSt c' = ⟨f (pad R.val c.sponge_state.val c.input_buffer.val), [],
        (f (pad R.val c.sponge_state.val c.input_buffer.val)).take R.val⟩ ∧
      c'.permutation = c.permutation :=
  duplexing_eq copyInst permInst ringInst hcopy hring f c hf hRW h255 hin

/-- Observing clears the outputs, buffers the value, and duplexes once the pending inputs fill the rate. -/
theorem duplex_challenger.DuplexChallenger.observe.eq_spec {F P : Type} [AddMonoidWithOne F]
    {W R : Std.Usize} (copyInst : core.marker.Copy F)
    (ringInst : p3_field.field.PrimeCharacteristicRing F)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array F W))
    (hcopy : CloneIsId copyInst) (hring : RingComputes ringInst) (f : List F → List F)
    (c : p3_challenger.duplex_challenger.DuplexChallenger F P W R)
    (hf : PermComputes permInst c.permutation f) (hRW : R.val < W.val) (h255 : R.val ≤ 255)
    (hin : c.input_buffer.val.length < R.val) (x : F) :
    ∃ c', p3_challenger.duplex_challenger.DuplexChallenger.Insts.P3_challengerCanObserve.observe
        copyInst ringInst permInst c x = .ok c' ∧
      toSt c' = (toSt c).observe f R.val x ∧ c'.permutation = c.permutation :=
  observe_eq copyInst ringInst permInst hcopy hring f c hf hRW h255 hin x

/-- Sampling the base field pops the last output.

It first duplexes when inputs are pending or no output is left. -/
theorem duplex_challenger.DuplexChallenger.sample.eq_spec {F P : Type} [AddMonoidWithOne F]
    {W R : Std.Usize} (copyInst : core.marker.Copy F)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array F W))
    (ringInst : p3_field.field.PrimeCharacteristicRing F)
    (hcopy : CloneIsId copyInst) (hring : RingComputes ringInst) (f : List F → List F)
    (c : p3_challenger.duplex_challenger.DuplexChallenger F P W R)
    (hf : PermComputes permInst c.permutation f) (hR : 0 < R.val) (hRW : R.val < W.val)
    (h255 : R.val ≤ 255) (hin : c.input_buffer.val.length ≤ R.val) :
    ∃ y c', p3_challenger.duplex_challenger.mirror.sample copyInst permInst ringInst c = .ok (y, c') ∧
      (y, toSt c') = (toSt c).sample f R.val ∧ c'.permutation = c.permutation :=
  sample_eq copyInst permInst ringInst hcopy hring f c hf hR hRW h255 hin

/-- Finalizing duplexes once more and returns the rate part of the new state. -/
theorem duplex_challenger.DuplexChallenger.finalize.eq_spec {F P : Type} [AddMonoidWithOne F]
    [Inhabited F] {W R : Std.Usize} (copyInst : core.marker.Copy F)
    (ringInst : p3_field.field.PrimeCharacteristicRing F)
    (permInst : p3_symmetric.permutation.CryptographicPermutation P (Std.Array F W))
    (hcopy : CloneIsId copyInst) (hring : RingComputes ringInst) (f : List F → List F)
    (c : p3_challenger.duplex_challenger.DuplexChallenger F P W R)
    (hf : PermComputes permInst c.permutation f) (hRW : R.val < W.val) (h255 : R.val ≤ 255)
    (hin : c.input_buffer.val.length ≤ R.val) :
    ∃ out, p3_challenger.duplex_challenger.DuplexChallenger.Insts.P3_challengerCanFinalizeDigestArray.finalize
        copyInst ringInst permInst c = .ok out ∧
      out.val = (f (pad R.val c.sponge_state.val c.input_buffer.val)).take R.val :=
  finalize_eq copyInst ringInst permInst hcopy hring f c hf hRW h255 hin

/-! ## The hash challenger, as extracted -/

/-- A flush hashes the pending inputs.

The digest becomes both the only pending input and the outputs. -/
theorem hash_challenger.HashChallenger.flush.eq_spec {T Hs : Type} {N : Std.Usize}
    (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = .ok x)
    (hashInst : p3_symmetric.hasher.CryptographicHasher Hs T (Std.Array T N)) (H : List T → Std.Array T N)
    (c : p3_challenger.hash_challenger.HashChallenger T Hs N) (hH : HasherComputes hashInst c.hasher H) :
    ∃ c', p3_challenger.hash_challenger.HashChallenger.flush cl hashInst c = .ok c' ∧
      toHSt c' = ⟨(H c.input_buffer.val).val, (H c.input_buffer.val).val⟩ ∧ c'.hasher = c.hasher :=
  flush_eq cl hcl hashInst H c hH

/-- Observing appends the value to the pending inputs and clears the outputs. -/
theorem hash_challenger.HashChallenger.observe.eq_spec {T Hs : Type} {N : Std.Usize}
    (cl : core.clone.Clone T) (hashInst : p3_symmetric.hasher.CryptographicHasher Hs T (Std.Array T N))
    (c : p3_challenger.hash_challenger.HashChallenger T Hs N) (x : T)
    (hl : c.input_buffer.val.length + 1 ≤ Usize.max) :
    ∃ c', p3_challenger.hash_challenger.HashChallenger.Insts.P3_challengerCanObserve.observe cl hashInst c x =
      .ok c' ∧ toHSt c' = ⟨c.input_buffer.val ++ [x], []⟩ ∧ c'.hasher = c.hasher :=
  hash_observe_eq cl hashInst c x hl

/-- After an observation, the next sample is the last cell of a fresh digest.

That digest hashes the chaining value and every input since. -/
theorem hash_challenger.HashChallenger.sample_after_observe.fresh {T Hs : Type} [Inhabited T]
    {N : Std.Usize} (cl : core.clone.Clone T) (hcl : ∀ x, cl.clone x = .ok x)
    (hashInst : p3_symmetric.hasher.CryptographicHasher Hs T (Std.Array T N)) (H : List T → Std.Array T N)
    (c : p3_challenger.hash_challenger.HashChallenger T Hs N) (hH : HasherComputes hashInst c.hasher H)
    (x : T) (hl : c.input_buffer.val.length + 1 ≤ Usize.max) (hN : 0 < N.val) :
    ∃ c', (do
        let c1 ← p3_challenger.hash_challenger.HashChallenger.Insts.P3_challengerCanObserve.observe cl
          hashInst c x
        p3_challenger.hash_challenger.HashChallenger.Insts.P3_challengerCanSample.sample cl hashInst c1) =
      .ok ((H (c.input_buffer.val ++ [x])).val.getLastD default, c') ∧
      toHSt c' = ⟨(H (c.input_buffer.val ++ [x])).val, (H (c.input_buffer.val ++ [x])).val.dropLast⟩ :=
  hash_sample_after_observe cl hcl hashInst H c hH x hl hN

/-! ## The duplex construction -/

/-- Every well-formed transcript, from empty buffers, returns the samples of the duplex construction.

Each phase does two things:

- it observes a run of values in blocks of r, one absorbing call per block
- it reads rates from their last cell down, with a blank call each time a rate is used up. -/
theorem transcript.eq_spec {F : Type} [AddMonoidWithOne F] (f : List F → List F) (r w : ℕ)
    (hr : 0 < r) (hrw : r < w) (hf : ∀ s, s.length = w → (f s).length = w)
    (ps : List (List F × ℕ)) (st : St F) (hwf : WellFormed ps) (hs : st.s.length = w)
    (hinb : st.inb = []) (hout : st.outb = []) :
    st.transcript f r ps = transcript f r st.s ps :=
  transcript_eq hr hrw hf ps st hwf hs hinb hout

/-- The sample after observing x is the last rate cell of the permutation of a block that ends with x.

No output buffered before an observation is returned after it. -/
theorem sample_after_observe.fresh {F : Type} [AddMonoidWithOne F] (f : List F → List F) (r w : ℕ)
    (hr : 0 < r) (hrw : r < w) (hf : ∀ s, s.length = w → (f s).length = w)
    (st : St F) (hs : st.s.length = w) (hinb : st.inb.length < r) (x : F) :
    ((st.observe f r x).sample f r).1 = (f (pad r st.s (st.inb ++ [x]))).getD (r - 1) 0 :=
  sample_observe hr hrw hf st hs hinb x

/-- Fix the state, and assume no two lengths up to r are equal in the field.

Then the padded state determines the block.

A blank call and an absorbing call never give the same padded state. -/
theorem pad.injective {F : Type} [AddGroupWithOne F] (r : ℕ) (s : List F)
    (hchar : ∀ a b : ℕ, a ≤ r → b ≤ r → (a : F) = b → a = b)
    (σ τ : List F) (hσ : σ.length ≤ r) (hτ : τ.length ≤ r) (h : pad r s σ = pad r s τ) : σ = τ :=
  pad_injective r s hchar σ τ hσ hτ h

/-- Lengths up to r stay distinct in characteristic q > r. -/
theorem pad.lengths_distinct {F : Type} [AddGroupWithOne F] (q r : ℕ) [CharP F q] (hq : r < q) :
    ∀ a b : ℕ, a ≤ r → b ≤ r → (a : F) = b → a = b :=
  cast_inj_of_charP q r hq

/-- In characteristic q, a block collides with its extension by q zeros. -/
theorem pad.collision_of_charP {F : Type} [AddGroupWithOne F] (q r : ℕ) [CharP F q] (s σ : List F)
    (hσ : σ ≠ []) (hq : σ.length + q ≤ r) : pad r s σ = pad r s (σ ++ List.replicate q 0) :=
  pad_collision q r s σ hσ hq

/-! ## Proof of work -/

/-- The SIMD search tests a candidate exactly as the witness check does.

Both observe it, sample, and test the low bits. -/
theorem grinding.DuplexChallenger.grind.accepts_iff_check {F : Type} [AddMonoidWithOne F]
    (f : List F → List F) (r w : ℕ) (val : F → ℕ) (hr : 0 < r) (hrw : r < w)
    (hf : ∀ s, s.length = w → (f s).length = w) (st : St F) (hs : st.s.length = w)
    (hinb : st.inb.length < r) (bits : ℕ) (hb : 0 < bits) (x : F) :
    checkWitness f r val st bits x =
      decide (val ((f (grindState r w st.s st.inb x)).getD (r - 1) 0) % 2 ^ bits = 0) :=
  grind_accepts_iff_check f r w val hr hrw hf st hs hinb bits hb x

/-- Difficulty 0 accepts every witness. -/
theorem grinding.check_witness.zero {F : Type} [AddMonoidWithOne F] (f : List F → List F) (r : ℕ)
    (val : F → ℕ) (st : St F) (x : F) : checkWitness f r val st 0 x = true :=
  checkWitness_zero f r val st x

/-- Proof of work accepts ceil(p / 2^b) canonical elements. -/
theorem grinding.accept_count (p b : ℕ) :
    Nat.count (fun x => x % 2 ^ b = 0) p = p / 2 ^ b + if p % 2 ^ b = 0 then 0 else 1 :=
  Bits.pow_accept_count p b

/-- The modulus fixes no low bit.

Once 2^b <= p, every b-bit pattern occurs. -/
theorem grinding.no_fixed_low_bit (p b v : ℕ) (hv : v < 2 ^ b) (hp : 2 ^ b ≤ p) :
    0 < Nat.count (fun x => x % 2 ^ b = v) p :=
  Bits.every_pattern_occurs p b v hv hp

/-! ## Reductions to bits, indices and smaller fields -/

/-- When sampling b bits, each b-bit value comes from p / 2^b or p / 2^b + 1 canonical elements. -/
theorem sample_bits.count (p b v : ℕ) (hv : v < 2 ^ b) :
    Nat.count (fun x => x % 2 ^ b = v) p = p / 2 ^ b + if v < p % 2 ^ b then 1 else 0 :=
  Bits.lowBits_count p b v hv

/-- When sampling b bits, each value's probability is within 1 / p of 2^-b. -/
theorem sample_bits.bias (p b v : ℕ) (hv : v < 2 ^ b) :
    p < (Nat.count (fun x => x % 2 ^ b = v) p + 1) * 2 ^ b ∧
      Nat.count (fun x => x % 2 ^ b = v) p * 2 ^ b < p + 2 ^ b :=
  Bits.lowBits_bias p b v hv

/-- Below m_k = floor(p / 2^k) 2^k, each k-bit value has the same count.

Uniform bit sampling rejects every value from m_k on. -/
theorem sample_uniform_bits.uniform (p k v : ℕ) (hv : v < 2 ^ k) :
    Nat.count (fun x => x % 2 ^ k = v) (p / 2 ^ k * 2 ^ k) = p / 2 ^ k :=
  Bits.uniform_below_multiple p k v hv

/-- Uniform bit sampling rejects p mod 2^k of the p canonical values. -/
theorem sample_uniform_bits.rejected (p k : ℕ) : p - p / 2 ^ k * 2 ^ k = p % 2 ^ k :=
  Bits.rejected_count p k

/-- In the serializing challengers, a uniform n-bit word masked to k <= n bits is exactly uniform. -/
theorem serializing.mask_uniform (n k v : ℕ) (hk : k ≤ n) (hv : v < 2 ^ k) :
    Nat.count (fun x => x % 2 ^ k = v) (2 ^ n) = 2 ^ (n - k) :=
  Bits.word_mask_count n k v hk hv

/-- In the byte codec, a uniform integer below N reduced modulo p is within 1 / N of uniform per residue. -/
theorem bytes_to_field.bias (N p v : ℕ) (hp : 0 < p) (hv : v < p) :
    N < (Nat.count (fun x => x % p = v) N + 1) * p ∧ Nat.count (fun x => x % p = v) N * p < N + p :=
  Bits.modReduce_bias N p v hp hv

/-- The byte codec reads ceil(bits / 8) + 16 bytes, enough for p < 2^-128 N. -/
theorem bytes_to_field.budget (p bits : ℕ) (hp : p < 2 ^ bits) :
    p * 2 ^ 128 < 256 ^ ((bits + 7) / 8 + 16) :=
  Bits.extraBytes_budget p bits hp

/-- The multi-field packing is injective on runs of one length, with digits below 2^b. -/
theorem multi_field.packing_injective (b : ℕ) (hb : 0 < b) (xs ys : List ℕ) (hl : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x < 2 ^ b) (hy : ∀ y ∈ ys, y < 2 ^ b)
    (h : Nat.ofDigits (2 ^ b) xs = Nat.ofDigits (2 ^ b) ys) : xs = ys :=
  Bits.packing_injective b hb xs ys hl hx hy h

/-! ## The four fields -/

/-- For BabyBear, the uniform sampling bound for k bits is floor(p / 2^k) 2^k. -/
theorem uniform_sampling.m_babybear : ∀ k < 64, 0 < k → Fields.samplingM Fields.pBB k = Fields.pBB / 2 ^ k * 2 ^ k :=
  Fields.samplingM_eq_BB

/-- For KoalaBear, the uniform sampling bound for k bits is floor(p / 2^k) 2^k. -/
theorem uniform_sampling.m_koalabear : ∀ k < 64, 0 < k → Fields.samplingM Fields.pKB k = Fields.pKB / 2 ^ k * 2 ^ k :=
  Fields.samplingM_eq_KB

/-- For Goldilocks, the uniform sampling bound for k bits is floor(p / 2^k) 2^k. -/
theorem uniform_sampling.m_goldilocks : ∀ k < 64, 0 < k → Fields.samplingM Fields.pGL k = Fields.pGL / 2 ^ k * 2 ^ k :=
  Fields.samplingM_eq_GL

/-- For Mersenne31, the uniform sampling bound for k bits is floor(p / 2^k) 2^k. -/
theorem uniform_sampling.m_mersenne31 : ∀ k < 64, 0 < k → Fields.samplingM Fields.pM31 k = Fields.pM31 / 2 ^ k * 2 ^ k :=
  Fields.samplingM_eq_M31

/-- At the largest single-sample bit count, uniform sampling rejects few values:

- 1 value for BabyBear, KoalaBear and Goldilocks
- 2^16 - 1 values for Mersenne31. -/
theorem uniform_sampling.rejected_at_max :
    Fields.pBB % 2 ^ 27 = 1 ∧ Fields.pKB % 2 ^ 24 = 1 ∧ Fields.pGL % 2 ^ 32 = 1 ∧
      Fields.pM31 % 2 ^ 16 = 2 ^ 16 - 1 :=
  Fields.rejected_at_max

/-- Every accepted bit count above the single-sample maximum splits into two halves within it. -/
theorem uniform_sampling.halves_fit :
    (∀ b < 64, 2 ^ b < Fields.pBB → 27 < b → b - b / 2 ≤ 27) ∧
    (∀ b < 64, 2 ^ b < Fields.pKB → 24 < b → b - b / 2 ≤ 24) ∧
    (∀ b < 64, 2 ^ b < Fields.pGL → 32 < b → b - b / 2 ≤ 32) ∧
    (∀ b < 64, 2 ^ b < Fields.pM31 → 16 < b → b - b / 2 ≤ 16) :=
  Fields.halves_fit

/-- A Goldilocks sponge squeezes one near-uniform limb of BabyBear, KoalaBear or Mersenne31 per cell. -/
theorem multi_field.squeeze_limbs_goldilocks :
    squeeze_field_order_num_limbs Fields.pBB Fields.pGL = 1 ∧
      squeeze_field_order_num_limbs Fields.pKB Fields.pGL = 1 ∧
      squeeze_field_order_num_limbs Fields.pM31 Fields.pGL = 1 :=
  Fields.squeeze_limbs_goldilocks

/-- A 31-bit sponge squeezes no limb of a smaller 31-bit field. -/
theorem multi_field.squeeze_limbs_31 :
    squeeze_field_order_num_limbs Fields.pBB Fields.pKB = 0 ∧
      squeeze_field_order_num_limbs Fields.pBB Fields.pM31 = 0 ∧
      squeeze_field_order_num_limbs Fields.pKB Fields.pM31 = 0 :=
  Fields.squeeze_limbs_31

/-- The constructor accepts BabyBear over a KoalaBear sponge. -/
theorem multi_field.new_accepts_babybear_in_koalabear :
    MultiField32Challenger.new Fields.pBB Fields.pKB 4 = .ok () :=
  Fields.new_accepts_babybear_in_koalabear

/-- With no squeeze limb, every sample from an empty queue panics. -/
theorem multi_field.sample_panics_without_limbs (p : ℕ) (rate : List ℕ) :
    sampleFromQueue p 0 [] rate = none :=
  Fields.sample_panics_without_limbs p rate

end Plonky3Lean.Claims.P3Challenger
