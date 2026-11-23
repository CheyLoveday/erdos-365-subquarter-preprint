import PaperProofs.AngularWitness

namespace P0365Subquarter.AngularWitness.Audit
noncomputable section
set_option autoImplicit false

/-- Seven ordered compact nodes, showing the witness hypotheses are satisfiable. -/
def sampleNodes (i : Fin 7) : ℝ := (i.val : ℝ)/6

theorem sampleNodes_injective : Function.Injective sampleNodes := by
  intro i j hij
  apply Fin.ext
  have h : (i.val : ℝ) = (j.val : ℝ) := by
    dsimp [sampleNodes] at hij
    linarith
  exact_mod_cast h

theorem sampleNodes_compact (i : Fin 7) : 0 ≤ sampleNodes i ∧ sampleNodes i ≤ 1 := by
  have hi : (i.val : ℝ) ≤ 6 := by
    exact_mod_cast (show i.val ≤ 6 by omega)
  dsimp [sampleNodes]
  constructor
  · positivity
  · linarith

theorem sample_both_charts (inverse : Bool) :
    (coefficientPolynomial inverse sampleNodes (sampleNodes 0)).coeff 21 ≠ 0 :=
  (section13_witness inverse sampleNodes (sampleNodes 0) sampleNodes_injective).2.2.2.1

/-- Every positive error cap admits the correct nonzero sign in either chart. -/
theorem sample_allowed_family (inverse : Bool) (L : ℝ) (hL : 0 < L) :
    ∃ lam : ℝ, lam ≠ 0 ∧ |lam| ≤ L ∧
      (if inverse then lam < 0 else 0 < lam) ∧
      lam * (vandermondeProduct sampleNodes * (if inverse then (393660 : ℝ) else 2240)) ≠ 0 := by
  obtain ⟨lam, hn, hcap, hsign⟩ := allowed_amplitude inverse L hL
  exact ⟨lam, hn, hcap, hsign, (realized_witness inverse sampleNodes lam sampleNodes_injective hn).2.2⟩

end
end P0365Subquarter.AngularWitness.Audit

set_option pp.all true
#check P0365Subquarter.AngularWitness.smooth_eq_power
#check P0365Subquarter.AngularWitness.jet_direct
#check P0365Subquarter.AngularWitness.jet_inverse
#check P0365Subquarter.AngularWitness.polynomial_remainder
#check P0365Subquarter.AngularWitness.coefficient_below
#check P0365Subquarter.AngularWitness.coefficient_at_21
#check P0365Subquarter.AngularWitness.remainder_isBigO
#check P0365Subquarter.AngularWitness.leading_ratio_limit
#check P0365Subquarter.AngularWitness.actual_determinant
#check P0365Subquarter.AngularWitness.smooth_repeated_node
#check P0365Subquarter.AngularWitness.actual_repeated_node
#check P0365Subquarter.AngularWitness.actual_repeated_node_ratio
#check P0365Subquarter.AngularWitness.exact_order
#check P0365Subquarter.AngularWitness.compact_node_range
#check P0365Subquarter.AngularWitness.scaled_nodes_injective
#check P0365Subquarter.AngularWitness.allowed_amplitude
#check P0365Subquarter.AngularWitness.jet_det
#check P0365Subquarter.AngularWitness.section13_witness
#check P0365Subquarter.AngularWitness.realized_witness
set_option pp.all false
#print axioms P0365Subquarter.AngularWitness.smooth_eq_power
#print axioms P0365Subquarter.AngularWitness.jet_direct
#print axioms P0365Subquarter.AngularWitness.jet_inverse
#print axioms P0365Subquarter.AngularWitness.polynomial_remainder
#print axioms P0365Subquarter.AngularWitness.coefficient_below
#print axioms P0365Subquarter.AngularWitness.coefficient_at_21
#print axioms P0365Subquarter.AngularWitness.remainder_isBigO
#print axioms P0365Subquarter.AngularWitness.leading_ratio_limit
#print axioms P0365Subquarter.AngularWitness.actual_determinant
#print axioms P0365Subquarter.AngularWitness.smooth_repeated_node
#print axioms P0365Subquarter.AngularWitness.actual_repeated_node
#print axioms P0365Subquarter.AngularWitness.actual_repeated_node_ratio
#print axioms P0365Subquarter.AngularWitness.exact_order
#print axioms P0365Subquarter.AngularWitness.compact_node_range
#print axioms P0365Subquarter.AngularWitness.scaled_nodes_injective
#print axioms P0365Subquarter.AngularWitness.allowed_amplitude
#print axioms P0365Subquarter.AngularWitness.jet_det
#print axioms P0365Subquarter.AngularWitness.section13_witness
#print axioms P0365Subquarter.AngularWitness.realized_witness
#print axioms P0365Subquarter.AngularWitness.Audit.sampleNodes_injective
#print axioms P0365Subquarter.AngularWitness.Audit.sampleNodes_compact
#print axioms P0365Subquarter.AngularWitness.Audit.sample_both_charts
#print axioms P0365Subquarter.AngularWitness.Audit.sample_allowed_family
