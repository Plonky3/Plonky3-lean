/-
Transcriptions of the query-index schedule of transcript/mod.rs.
-/
module

public import P3Whir.Model

@[expose] public section

namespace p3_whir.transcript.mirror

open p3_sumcheck.mirror p3_whir.mirror

variable {F EF : Type _}

/-- query_draws: num_queries draws, or none when every position opens. -/
def query_draws (folded_domain_size num_queries : ℕ) : ℕ :=
  if num_queries ≥ folded_domain_size then 0 else num_queries

/-- query_summand_depths: peel the highest power of two off the count until nothing remains. -/
def query_summand_depths (remaining : ℕ) : List ℕ :=
  if h : remaining = 0 then []
  else Nat.log 2 remaining :: query_summand_depths (remaining - 2 ^ Nat.log 2 remaining)
termination_by remaining
decreasing_by exact Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.two_pow_pos _)

/-- stratified_index: a low draw placed inside a stratum of the given number and depth. -/
def stratified_index (width depth stratum low : ℕ) : ℕ := (stratum <<< (width - depth)) ||| low

/-- One draw of a count of indices of the given width.

It returns the indices, and the history after the draw. -/
def draw (S : WSponge F EF) (h : List (Step F EF)) (bits count : ℕ) : List ℕ × List (Step F EF) :=
  (S.indices h bits count, h ++ [.challenge])

/-- assemble_query_indices played through the sponge:

- every position, when nothing is drawn
- one draw, when unstratified
- otherwise one draw per summand. -/
def play_query_indices (S : WSponge F EF) (h : List (Step F EF)) (width draws : ℕ) (stratified : Bool)
    (depths : List ℕ) : List ℕ × List (Step F EF) :=
  if draws = 0 then (List.range (2 ^ width), h)
  else if !stratified then draw S h width draws
  else depths.foldl (fun (acc : List ℕ × List (Step F EF)) depth =>
    let (lows, h') := draw S acc.2 (width - depth) (2 ^ depth)
    (acc.1 ++ (List.range lows.length).map fun s => stratified_index width depth s (lows.getD s 0), h'))
    ([], h)

end p3_whir.transcript.mirror
