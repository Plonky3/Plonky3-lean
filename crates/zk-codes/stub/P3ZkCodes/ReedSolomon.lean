/-
Transcriptions of the Reed-Solomon zero-knowledge encoding.

What a transcription abstracts, beyond the model of p3-dft:

* the field is a mathlib field K, and exp_u64 and the powers iterator yield powers of their base;
* the backend's forward transform is a parameter, of the shape p3-dft's transcriptions have;
* a codeword is the rows of the transform's output, a single column for one message;
* a random generator is the stream of its draws: the k-th call to random returns draw k;
* the configured lengths are words, and an addition that leaves the word panics, as in a debug build.

Loops, branches and the order of operations are kept.
-/
module

public import P3Dft

@[expose] public section

namespace p3_zk_codes.reed_solomon.mirror

open p3_dft.mirror

/-- The configuration: t masks, a message of msg_len coefficients, a codeword of m positions. -/
structure ReedSolomonZkEncoding where
  t : ℕ
  msg_len : ℕ
  m : ℕ

variable {K : Type _} [Field K]

/-- The constructor, which asserts that m is a power of two and msg_len + t <= m. -/
def ReedSolomonZkEncoding.new (t msg_len m : ℕ) : Option ReedSolomonZkEncoding :=
  if m ≠ 0 ∧ 2 ^ Nat.log 2 m = m then
    if msg_len + t < 2 ^ 64 then
      if msg_len + t ≤ m then some ⟨t, msg_len, m⟩ else none
    else none
  else none

/-- The evaluation point g^position, for g the generator of the subgroup of order m. -/
def ReedSolomonZkEncoding.evaluation_point (G : Gen K) (rs : ReedSolomonZkEncoding)
    (position : ℕ) : Option K := do
  let log2_m ← log2Strict rs.m
  let g ← G.get log2_m
  pure (g ^ position)

/-- The message row: the first msg_len powers of the evaluation point. -/
def ReedSolomonZkEncoding.message_row_iter (G : Gen K) (rs : ReedSolomonZkEncoding)
    (position : ℕ) : Option (List K) := do
  let x ← rs.evaluation_point G position
  pure (powersList x rs.msg_len)

/-- The first n values of the successors iterator: the seed, if any, then next applied repeatedly. -/
def successorsTake (next : K → K) : Option K → ℕ → List K
  | _, 0 => []
  | none, _ + 1 => []
  | some a, n + 1 => a :: successorsTake next (some (next a)) n

/-- The randomness row: t successive powers of the evaluation point, from x^msg_len.

The seed is absent when t is zero. -/
def ReedSolomonZkEncoding.randomness_row_iter (G : Gen K) (rs : ReedSolomonZkEncoding)
    (position : ℕ) : Option (List K) := do
  let x ← rs.evaluation_point G position
  let start := x ^ rs.msg_len
  let t := rs.t
  pure (successorsTake (· * x) (if t > 0 then some start else none) t)

/-- The message row, collected. -/
def ReedSolomonZkEncoding.message_row (G : Gen K) (rs : ReedSolomonZkEncoding) (position : ℕ) :
    Option (List K) :=
  rs.message_row_iter G position

/-- The randomness row, collected. -/
def ReedSolomonZkEncoding.randomness_row (G : Gen K) (rs : ReedSolomonZkEncoding)
    (position : ℕ) : Option (List K) :=
  rs.randomness_row_iter G position

/-- The accessors: message length, randomness length, query bound, codeword length. -/
def ReedSolomonZkEncoding.message_len (rs : ReedSolomonZkEncoding) : ℕ := rs.msg_len

def ReedSolomonZkEncoding.randomness_len (rs : ReedSolomonZkEncoding) : ℕ := rs.t

def ReedSolomonZkEncoding.query_bound (rs : ReedSolomonZkEncoding) : ℕ := rs.t

def ReedSolomonZkEncoding.codeword_len (rs : ReedSolomonZkEncoding) : ℕ := rs.m

/-- The statistical simulation error, which is zero. -/
def ReedSolomonZkEncoding.error (_rs : ReedSolomonZkEncoding) : ℚ := 0

/-- A uniform message: msg_len draws, in order. -/
def ReedSolomonZkEncoding.sample_message (rs : ReedSolomonZkEncoding) (draw : ℕ → K) : List K :=
  (List.range rs.msg_len).map draw

/-- Uniform randomness: t draws, in order. -/
def ReedSolomonZkEncoding.sample_randomness (rs : ReedSolomonZkEncoding) (draw : ℕ → K) :
    List K :=
  (List.range rs.t).map draw

/-- Resize a list to n entries: truncate, or append zeros. -/
def resize (l : List K) (n : ℕ) : List K := l.take n ++ List.replicate (n - l.length) 0

/-- Encode with explicit randomness.

The lengths are asserted.

The coefficients are the message, then the randomness, then zeros up to m; the codeword is their transform. -/
def ReedSolomonZkEncoding.encode_with_randomness (dft_batch : ℕ → (ℕ → K) → Option (ℕ → K))
    (rs : ReedSolomonZkEncoding) (msg randomness : List K) : Option (ℕ → K) :=
  if msg.length ≠ rs.msg_len then none
  else if randomness.length ≠ rs.t then none
  else
    let coeffs := resize (msg ++ randomness) rs.m
    dft_batch rs.m (fun i => coeffs.getD i 0)

/-- Encode with randomness drawn from the generator: t draws, then the explicit-randomness encoding. -/
def ReedSolomonZkEncoding.encode (dft_batch : ℕ → (ℕ → K) → Option (ℕ → K))
    (rs : ReedSolomonZkEncoding) (msg : List K) (draw : ℕ → K) : Option (ℕ → K) :=
  let randomness := (List.range rs.t).map draw
  rs.encode_with_randomness dft_batch msg randomness

/-- One step of the simulator: a cached position reuses its value, a new one takes the next draw. -/
def simStep (draw : ℕ → K) (st : List (ℕ × K) × List K) (p : ℕ) : List (ℕ × K) × List K :=
  match st.1.find? (fun q => q.1 == p) with
  | some (_, v) => (st.1, st.2 ++ [v])
  | none =>
    let v := draw st.1.length
    (st.1 ++ [(p, v)], st.2 ++ [v])

/-- The simulator.

Each new position takes one fresh draw, and a repeated position reuses its value.

It asserts, after the loop, that at most t distinct positions were seen. -/
def ReedSolomonZkEncoding.simulate (rs : ReedSolomonZkEncoding) (query_set : List ℕ)
    (draw : ℕ → K) : Option (List K) :=
  let st := query_set.foldl (simStep draw) ([], [])
  if st.1.length ≤ rs.t then some st.2 else none

/-- The batch encoding: w columns, packed into one matrix of m rows and transformed once.

The batch must be nonempty, its two counts must agree, and every member's lengths are asserted.

Row r of column c is entry r w + c of the flat buffer. -/
def ReedSolomonZkEncoding.encode_batch_with_randomness {w : ℕ}
    (dft_batch : ℕ → (ℕ → Fin w → K) → Option (ℕ → Fin w → K)) (rs : ReedSolomonZkEncoding)
    (messages randomness : List (List K)) : Option (ℕ → Fin w → K) := do
  if messages.isEmpty then none
  else if messages.length ≠ randomness.length then none
  else
    let width := messages.length
    let coeffs ← ((messages.zip randomness).zipIdx).foldlM (fun (coeffs : ℕ → K) mrc =>
      let ((msg, rnd), column) := mrc
      if msg.length ≠ rs.msg_len then none
      else if rnd.length ≠ rs.t then none
      else
        let coeffs := (List.range msg.length).foldl (fun acc row =>
          fun i => if i = row * width + column then msg.getD row 0 else acc i) coeffs
        some ((List.range rnd.length).foldl (fun acc row =>
          fun i => if i = (rs.msg_len + row) * width + column then rnd.getD row 0 else acc i)
          coeffs)) (fun _ => 0)
    dft_batch rs.m (fun r c => coeffs (r * width + c.val))

end p3_zk_codes.reed_solomon.mirror
