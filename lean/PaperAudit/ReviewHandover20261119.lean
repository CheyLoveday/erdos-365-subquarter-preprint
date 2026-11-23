import PaperProofs
import PaperAudit.ReviewSupplement

/-! Additional review corollaries, outside the maintained 151-module closure.
This is a local audit using existing compiled imports, not protected replay. -/
namespace P0365SecondReview
set_option autoImplicit false

/-- Rebalancing the chosen coarse and one-error constraints cannot beat theta.
This is a bound within those scalar constraints, not actual-source optimality. -/
theorem selected_seam_budget_lower_bound (m q : ℝ)
    (hcoarse : (9 / 50 : ℝ) ≤ m)
    (hminor : (32 / 5 : ℝ) - 1 - 21*m ≤ 28*q) :
    (333 / 1400 : ℝ) ≤ m+q := by
  linarith

/-- Make the manuscript's same-constant natural/real conclusion explicit.
No new external premise; the existing natural theorem supplies C. -/
theorem joint_natural_real_constant
    (hThue : P0365Subquarter.StewartPrimitiveThue) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (∀ N : ℕ, 1 ≤ N → (P0365Subquarter.PairCount N : ℝ) ≤
        C * (N : ℝ)^(P0365Subquarter.profileTheta+ε)) ∧
      (∀ X : ℝ, 1 ≤ X → (P0365Subquarter.PairCount (Nat.floor X) : ℝ) ≤
        C * X^(P0365Subquarter.profileTheta+ε)) := by
  obtain ⟨C, hC, hcount⟩ := P0365Subquarter.natural_pair_count hThue ε hε
  refine ⟨C, hC, hcount, ?_⟩
  intro X hX
  have hfloor : 1 ≤ Nat.floor X := Nat.le_floor (by exact_mod_cast hX)
  have hp : 0 ≤ P0365Subquarter.profileTheta+ε := by
    norm_num [P0365Subquarter.profileTheta]
    linarith
  exact (hcount (Nat.floor X) hfloor).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) hp) hC.le)

end P0365SecondReview

set_option pp.all true in
#print P0365Subquarter.CF09FiniteImplicitPolynomial

set_option pp.all true in
#print P0365Subquarter.CF10ActualSourceDeterminants

set_option pp.all true in
#print P0365Subquarter.CF12RoundedEntireClassRelation

set_option pp.all true in
#print P0365Subquarter.CF08RoundedShellSourceAssignment

set_option pp.all true in
#print P0365Subquarter.CF17ActualBoxSourceCount

set_option pp.all true in
#print P0365Subquarter.CF18NaturalPairCount

set_option pp.all true in
#print P0365Subquarter.CF18RealPairCount

set_option pp.all true in
#print P0365Subquarter.StewartPrimitiveThue

#print axioms P0365Subquarter.powerful_normal_form_exists
#print axioms P0365Subquarter.cube_square_powerful
#print axioms P0365Subquarter.normal_form_unique
#print axioms P0365Subquarter.normal_form
#print axioms P0365Subquarter.pair_source_equivalence
#print axioms P0365Subquarter.pair_source_unique
#print axioms P0365Subquarter.additive_and_integer_source
#print axioms P0365Subquarter.cross_endpoint_coprime
#print axioms P0365Subquarter.primitive_ratios
#print axioms P0365Subquarter.source_bounds
#print axioms P0365Subquarter.cutoff_source_bounds
#print axioms P0365Subquarter.source_ratio_coordinate_injection
#print axioms P0365Subquarter.source_ratio_injection
#print axioms P0365Subquarter.readback_prime_correspondence
#print axioms P0365Subquarter.readback_powerful_correspondence
#print axioms P0365Subquarter.readback_source_correspondence
#print axioms P0365Subquarter.readback_count_correspondence
#print axioms P0365Subquarter.count_source_correspondence
#print axioms P0365Subquarter.zero_not_powerful
#print axioms P0365Subquarter.one_powerful
#print axioms P0365Subquarter.two_not_powerful
#print axioms P0365Subquarter.count_empty_boundary
#print axioms P0365Subquarter.endpoint_overlap_controls
#print axioms P0365Subquarter.noncanonical_control
#print axioms P0365Subquarter.pell_pow_y_nonneg
#print axioms P0365Subquarter.two_pow_le_pell_x
#print axioms P0365Subquarter.pell_x_card_le_log_of_fundamental
#print axioms P0365Subquarter.pell_nontrivial_x_card_le_log
#print axioms P0365Subquarter.source_trace
#print axioms P0365Subquarter.fixed_kernel_product_count
#print axioms P0365Subquarter.small_kernel_product_count
#print axioms P0365Subquarter.original_small_kernel_count
#print axioms P0365Subquarter.original_small_kernel_subpower
#print axioms P0365Subquarter.dyadic_product_labels
#print axioms P0365Subquarter.small_multiplier_labels
#print axioms P0365Subquarter.original_small_multiplier_count
#print axioms P0365Subquarter.original_small_multiplier_subpower
#print axioms P0365Subquarter.profile_bounds
#print axioms P0365Subquarter.chart_branches
#print axioms P0365Subquarter.centre_values
#print axioms P0365Subquarter.profile_envelope
#print axioms P0365Subquarter.unrounded_slack
#print axioms P0365Subquarter.unrounded_strict_constraints
#print axioms P0365Subquarter.actual_box_product_bounds
#print axioms P0365Subquarter.residual_compact_profile
#print axioms P0365Subquarter.rounded_height_bounds
#print axioms P0365Subquarter.rounded_prime_scale
#print axioms P0365Subquarter.rounded_mixed_term_bound
#print axioms P0365Subquarter.rounded_error_absorption
#print axioms P0365Subquarter.cleared_identity
#print axioms P0365Subquarter.actual_source_witness
#print axioms P0365Subquarter.bertrand_list
#print axioms P0365Subquarter.first_good_assignment
#print axioms P0365Subquarter.smooth_label_budget
#print axioms P0365Subquarter.rounded_source_assignment
#print axioms P0365Subquarter.rounded_shell_source_assignment
#print axioms P0365Subquarter.polynomial_evaluation_determinant
#print axioms P0365Subquarter.finite_implicit_polynomial
#print axioms P0365Subquarter.actual_source_implicit_polynomial
#print axioms P0365Subquarter.source_row_identity
#print axioms P0365Subquarter.actual_source_determinants
#print axioms P0365Subquarter.actual_relative_errors
#print axioms P0365Subquarter.actual_normalized_error
#print axioms P0365Subquarter.actual_row_normalization
#print axioms P0365Subquarter.actual_minor_normalization
#print axioms P0365Subquarter.real_scale_cancellation
#print axioms P0365Subquarter.rounded_minor_vanishing
#print axioms P0365Subquarter.mixed_root_determinants
#print axioms P0365Subquarter.normalized_determinant_bound
#print axioms P0365Subquarter.actual_interval_nodes
#print axioms P0365Subquarter.actual_box_determinant_bound
#print axioms P0365Subquarter.rounded_actual_determinant_bound
#print axioms P0365Subquarter.rounded_actual_minor_vanishing
#print axioms P0365Subquarter.bounded_integer_relation
#print axioms P0365Subquarter.source_row_height
#print axioms P0365Subquarter.relation_polynomial
#print axioms P0365Subquarter.source_relation_evaluation
#print axioms P0365Subquarter.actual_class_relation
#print axioms P0365Subquarter.rounded_entire_class_relation
#print axioms P0365Subquarter.relation_sections
#print axioms P0365Subquarter.primitive_gcd_removal
#print axioms P0365Subquarter.integer_factor_height
#print axioms P0365Subquarter.graph_ruling_dispatch
#print axioms P0365Subquarter.actual_graph_ruling_decomposition
#print axioms P0365Subquarter.rounded_class_graph_rulings
#print axioms P0365Subquarter.multiplier_cubic_admissibility
#print axioms P0365Subquarter.fixed_multiplier_ratio_count
#print axioms P0365Subquarter.fixed_kernel_ratio_count
#print axioms P0365Subquarter.coordinate_ruling_count
#print axioms P0365Subquarter.ruling_log_subpower
#print axioms P0365Subquarter.coordinate_ruling_subpower
#print axioms P0365Subquarter.constant_graph_ruling
#print axioms P0365Subquarter.bounded_graph_ruling_class_subpower
#print axioms P0365Subquarter.rounded_class_source_subpower
#print axioms P0365Subquarter.irreducible_interval_source_count
#print axioms P0365Subquarter.coarse_interval_source_count
#print axioms P0365Subquarter.relative_interval_cover
#print axioms P0365Subquarter.actual_box_interval_cover
#print axioms P0365Subquarter.compact_box_source_count
#print axioms P0365Subquarter.residual_box_source_count
#print axioms P0365Subquarter.actual_box_source_count
#print axioms P0365Subquarter.original_shell_source_count
#print axioms P0365Subquarter.natural_pair_count
#print axioms P0365Subquarter.real_pair_count
#print axioms P0365SecondReview.selected_seam_budget_lower_bound
#print axioms P0365SecondReview.joint_natural_real_constant
