module

public import Plonky3Lean.Proofs.Circle.Deep
public import Plonky3Lean.Proofs.Circle.Selectors
public import Plonky3Lean.Proofs.Circle.Query

@[expose] public section

/-!
# p3-circle: claims

The crate is transcribed over a field K, not extracted.

The specification is Haböck, Levit and Papini, "Circle STARKs", eprint 2024/278.

Each claim's statement is the proof's, recalled in its docstring.
-/

namespace Plonky3Lean.Claims.Circle

open Plonky3Lean.Proofs.Circle

/-- The squaring map of the code is P -> 2 P in the circle group. -/
theorem point.double : type_of% @Plonky3Lean.Proofs.Circle.double_ofC := @Plonky3Lean.Proofs.Circle.double_ofC

/-- Double-and-add scalar multiplication is n P. -/
theorem point.mul : type_of% @Plonky3Lean.Proofs.Circle.mul_ofC := @Plonky3Lean.Proofs.Circle.mul_ofC

/-- v_n is the x-coordinate of 2^(n-1) P for n >= 1, and panics at n = 0. -/
theorem point.v_n : type_of% @Plonky3Lean.Proofs.Circle.v_n_ofC := @Plonky3Lean.Proofs.Circle.v_n_ofC

/-- s_p_at_p is -2 v_n'(P_x) P_y, Remark 16, with v_n' = 4^(n-1) v_1 ... v_(n-1). -/
theorem point.s_p_at_p : type_of% @Plonky3Lean.Proofs.Circle.s_p_at_p_ofC := @Plonky3Lean.Proofs.Circle.s_p_at_p_ofC

/-- The point of the line panics exactly at t^2 = -1. -/
theorem point.from_projective_line : type_of% @Plonky3Lean.Proofs.Circle.from_projective_line_eq := @Plonky3Lean.Proofs.Circle.from_projective_line_eq

/-- Projecting the point of t gives back t, Lemma 1. -/
theorem point.projective_line_inverse : type_of% @Plonky3Lean.Proofs.Circle.to_from_projective_line := @Plonky3Lean.Proofs.Circle.to_from_projective_line

/-- v_p is the complex conjugate of the paper's v_P, equation (11). -/
theorem point.v_p : type_of% @Plonky3Lean.Proofs.Circle.v_p_ofC := @Plonky3Lean.Proofs.Circle.v_p_ofC

/-- Entry k of a valid generator table has order exactly 2^k. -/
theorem generator.order : type_of% @Plonky3Lean.Proofs.Circle.addOrderOf_genPt := @Plonky3Lean.Proofs.Circle.addOrderOf_genPt

/-- Mersenne31's circle generator table is valid up to 31. -/
theorem generator.m31_valid : type_of% @Plonky3Lean.Proofs.Circle.m31CircleGen_valid := @Plonky3Lean.Proofs.Circle.m31CircleGen_valid

/-- The circle group of Mersenne31 has 2^31 points. -/
theorem generator.m31_card : type_of% @Plonky3Lean.Proofs.Circle.card_circle := @Plonky3Lean.Proofs.Circle.card_circle

/-- The Rust circle generator of order 2^bits is table entry bits, and panics past 31. -/
theorem generator.m31_rust : type_of% @Plonky3Lean.Proofs.Circle.circle_two_adic_generator_eq := @Plonky3Lean.Proofs.Circle.circle_two_adic_generator_eq

/-- The standard domain of size 2^n lists (2k+1) Q, Q of order 2^(n+1). -/
theorem domain.standard_points : type_of% @Plonky3Lean.Proofs.Circle.standard_points := @Plonky3Lean.Proofs.Circle.standard_points

/-- The points of a standard domain are distinct. -/
theorem domain.standard_nodup : type_of% @Plonky3Lean.Proofs.Circle.standard_nodup := @Plonky3Lean.Proofs.Circle.standard_nodup

/-- Standard domains of different sizes are disjoint. -/
theorem domain.standard_disjoint : type_of% @Plonky3Lean.Proofs.Circle.standard_disjoint := @Plonky3Lean.Proofs.Circle.standard_disjoint

/-- Over any field with 2 nonzero, v_n vanishes exactly on the standard domain. -/
theorem domain.vanishing : type_of% @Plonky3Lean.Proofs.Circle.vn_eq_zero_iff := @Plonky3Lean.Proofs.Circle.vn_eq_zero_iff

/-- try_create_disjoint_domain returns the standard domain of the bumped size, or none past the adicity. -/
theorem domain.disjoint_domain : type_of% @Plonky3Lean.Proofs.Circle.try_create_disjoint_domain_eq := @Plonky3Lean.Proofs.Circle.try_create_disjoint_domain_eq

/-- The CFFT order is an involution of [0, 2^n). -/
theorem ordering.involutive : type_of% @Plonky3Lean.Proofs.Circle.cfft_permute_index_involutive := @Plonky3Lean.Proofs.Circle.cfft_permute_index_involutive

/-- The in-place chunk permutation reads row sigma(r) at row r. -/
theorem ordering.chunked : type_of% @Plonky3Lean.Proofs.Circle.cfft_permute_slice_chunked_in_place_eq := @Plonky3Lean.Proofs.Circle.cfft_permute_slice_chunked_in_place_eq

/-- Off the trace domain, selectors_at_point returns the selector polynomials and 1/v_n. -/
theorem selectors.at_point : type_of% @Plonky3Lean.Proofs.Circle.selectors_at_point_eq := @Plonky3Lean.Proofs.Circle.selectors_at_point_eq

/-- selectors_at_point panics on the trace domain. -/
theorem selectors.at_point_panics : type_of% @Plonky3Lean.Proofs.Circle.selectors_at_point_none := @Plonky3Lean.Proofs.Circle.selectors_at_point_none

/-- The selector polynomial of P vanishes at every other trace-domain point. -/
theorem selectors.on_domain : type_of% @Plonky3Lean.Proofs.Circle.selReg_on_domain := @Plonky3Lean.Proofs.Circle.selReg_on_domain

/-- selectors_on_coset lists the at-point selectors at each coset point. -/
theorem selectors.on_coset : type_of% @Plonky3Lean.Proofs.Circle.selectors_on_coset_eq := @Plonky3Lean.Proofs.Circle.selectors_on_coset_eq

/-- On the Mersenne31 trace domain of size 2^n the first-row selector is 2^n at the first row. -/
theorem selectors.m31_first_row : type_of% @Plonky3Lean.Proofs.Circle.m31_first_row_value := @Plonky3Lean.Proofs.Circle.m31_first_row_value

/-- On the Mersenne31 trace domain of size 2^n the last-row selector is -2^n at the last row. -/
theorem selectors.m31_last_row : type_of% @Plonky3Lean.Proofs.Circle.m31_last_row_value := @Plonky3Lean.Proofs.Circle.m31_last_row_value

/-- The twiddle tables are the half-coset coordinates in bit-reversed order. -/
theorem cfft.twiddles : type_of% @Plonky3Lean.Proofs.Circle.compute_twiddles_eq := @Plonky3Lean.Proofs.Circle.compute_twiddles_eq

/-- evaluate returns the FFT-basis polynomial's values at the natural points sigma(i). -/
theorem cfft.evaluate : type_of% @Plonky3Lean.Proofs.Circle.evaluate_standard := @Plonky3Lean.Proofs.Circle.evaluate_standard

/-- On a standard domain interpolate never panics and inverts evaluation, Theorem 2. -/
theorem cfft.interpolate : type_of% @Plonky3Lean.Proofs.Circle.interpolate_standard := @Plonky3Lean.Proofs.Circle.interpolate_standard

/-- circle_basis lists the basis of Definition 4. -/
theorem cfft.basis : type_of% @Plonky3Lean.Proofs.Circle.circle_basis_eq := @Plonky3Lean.Proofs.Circle.circle_basis_eq

/-- The first-layer fold is f_0 + beta f_1, equations (14) to (16). -/
theorem folding.fold_y : type_of% @Plonky3Lean.Proofs.Circle.fold_y_spec := @Plonky3Lean.Proofs.Circle.fold_y_spec

/-- The x-fold is g_0 + beta g_1 at pi(x), equations (17) to (19). -/
theorem folding.fold_x : type_of% @Plonky3Lean.Proofs.Circle.fold_x_spec := @Plonky3Lean.Proofs.Circle.fold_x_spec

/-- query_x_twiddles_inv returns every round's inverted twiddle and never panics. -/
theorem folding.query_twiddles : type_of% @Plonky3Lean.Proofs.Circle.query_x_twiddles_inv_eq := @Plonky3Lean.Proofs.Circle.query_x_twiddles_inv_eq

/-- The row reduction returns none exactly when the query point is the opening point. -/
theorem deep.reduce_row : type_of% @Plonky3Lean.Proofs.Circle.deep_quotient_reduce_row_eq := @Plonky3Lean.Proofs.Circle.deep_quotient_reduce_row_eq

/-- The row reduction is sum_j alpha^j Re(q_j) + alpha^(W+j) Im(q_j), Proposition 4. -/
theorem deep.re_im : type_of% @Plonky3Lean.Proofs.Circle.reduce_row_eq_re_im := @Plonky3Lean.Proofs.Circle.reduce_row_eq_re_im

/-- The prover's accumulated reduction equals offset times the verifier's row reduction. -/
theorem deep.prover_verifier : type_of% @Plonky3Lean.Proofs.Circle.accumulate_eq_reduce_row := @Plonky3Lean.Proofs.Circle.accumulate_eq_reduce_row

/-- extract_lambda returns <lde, v_d> / 2^(L-1) and the corrected LDE. -/
theorem deep.extract_lambda : type_of% @Plonky3Lean.Proofs.Circle.extract_lambda_eq := @Plonky3Lean.Proofs.Circle.extract_lambda_eq

/-- After the extraction the LDE is orthogonal to v_n on the LDE domain. -/
theorem deep.extract_lambda_orthogonal : type_of% @Plonky3Lean.Proofs.Circle.extract_lambda_orthogonal := @Plonky3Lean.Proofs.Circle.extract_lambda_orthogonal

/-! ## The PCS verifier -/

/-- The verifier never panics when:

- every claimed domain has at least 2 rows
- no opening point t has t^2 = -1. -/
theorem pcs.never_panics : type_of% @Plonky3Lean.Proofs.Circle.verify_total := @Plonky3Lean.Proofs.Circle.verify_total

/-- On claimed domains of at least 2 rows, the verifier panics exactly when:

- the checks before the transcript pass
- some opening point t has t^2 = -1. -/
theorem pcs.panics_iff : type_of% @Plonky3Lean.Proofs.Circle.verify_panics_iff :=
  @Plonky3Lean.Proofs.Circle.verify_panics_iff

/-- The lambda correction of a one-row claimed domain panics, since it reads v_0. -/
theorem pcs.one_row_panics : type_of% @Plonky3Lean.Proofs.Circle.firstLayerLeaf_one_row :=
  @Plonky3Lean.Proofs.Circle.firstLayerLeaf_one_row

/-- The verifier accepts when:

- the claims pass the checks before the transcript, and the transcript accepts
- the input checks return the honest inputs at the points each query reads
- the commit-phase siblings hold the honest layers, and the final value is the folded constant
- the commit-phase scheme accepts the honest codewords. -/
theorem pcs.complete : type_of% @Plonky3Lean.Proofs.Circle.verify_complete :=
  @Plonky3Lean.Proofs.Circle.verify_complete

/-! ## One query, against Sections 3 and 4 -/

/-- One matrix adds, at its height, each point's DEEP term of Proposition 4 times the running power of alpha. -/
theorem query.deep : type_of% @Plonky3Lean.Proofs.Circle.reduceMatrix_eq := @Plonky3Lean.Proofs.Circle.reduceMatrix_eq

/-- The query point at height h has x-coordinate sigma_r x_r, the point circle FRI reads at round H - h. -/
theorem query.first_layer_point : type_of% @Plonky3Lean.Proofs.Circle.firstLayer_point_x :=
  @Plonky3Lean.Proofs.Circle.firstLayer_point_x

/-- The first-layer fold of an honest pair is f_0 + beta f_1 at P.x, equations (14) to (16). -/
theorem query.first_layer_fold : type_of% @Plonky3Lean.Proofs.Circle.firstLayer_fold :=
  @Plonky3Lean.Proofs.Circle.firstLayer_fold

/-- An honest first-layer leaf folds to the input circle FRI rolls in at round H - h. -/
theorem query.first_layer : type_of% @Plonky3Lean.Proofs.Circle.firstLayer_honest :=
  @Plonky3Lean.Proofs.Circle.firstLayer_honest

/-- One round folds the honest row to g_0 + beta g_1 at pi(x_r), equations (17) to (19). -/
theorem query.fold_step : type_of% @Plonky3Lean.Proofs.Circle.foldStep_honest := @Plonky3Lean.Proofs.Circle.foldStep_honest

/-- Squaring round r's twiddle gives the point round r + 1 reads: pi(x_r) = sigma_(r+1) x_(r+1). -/
theorem query.next_point : type_of% @Plonky3Lean.Proofs.Circle.piX_Xq := @Plonky3Lean.Proofs.Circle.piX_Xq

/-- On honest data, a query's fold chain returns the folded constant and records every round's honest row. -/
theorem query.fold_chain : type_of% @Plonky3Lean.Proofs.Circle.fold_query_honest :=
  @Plonky3Lean.Proofs.Circle.fold_query_honest

/-- The query checks accept honest inputs, honest siblings, the folded constant and accepted codewords. -/
theorem query.complete : type_of% @Plonky3Lean.Proofs.Circle.verify_queries_complete :=
  @Plonky3Lean.Proofs.Circle.verify_queries_complete

end Plonky3Lean.Claims.Circle
