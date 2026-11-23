import PaperProofs.ExactProfiles

namespace P0365Subquarter

set_option pp.all true

#print profileTheta
#print profileRho
#print profileCentre
#print profileM0
#print profileW
#print profileErrorWeight
#print profileBranch
#print profileCentreValue
#print CF16ProfileBounds
#print CF16ChartBranches
#print CF16Envelope
#print CF16CentreValues
#print CF16UnroundedSlack
#print CF16UnroundedStrictConstraints

#check (profile_bounds : CF16ProfileBounds)
#check (chart_branches : CF16ChartBranches)
#check (centre_values : CF16CentreValues)
#check (profile_envelope : CF16Envelope)
#check (unrounded_slack : CF16UnroundedSlack)
#check (unrounded_strict_constraints : CF16UnroundedStrictConstraints)

#print axioms profile_bounds
#print axioms chart_branches
#print axioms centre_values
#print axioms profile_envelope
#print axioms unrounded_slack
#print axioms unrounded_strict_constraints

example : profileM0 0 = 0 ∧ profileM0 (2 / 3) = 0 ∧
    profileM0 (1 / 3) = 3 / 16 := by norm_num [profileM0]

example : profileW profileCentre = 4 + 6 * profileCentre ∧
    profileW profileCentre = 12 - 14 * profileCentre :=
  ⟨(chart_branches profileCentre).1 le_rfl, (chart_branches profileCentre).2 le_rfl⟩

example : profileBranch profileCentre 1 = profileTheta := centre_values.2.2.2

-- At zero slack the limiting determinant margin is exactly zero, not strict.
example : 28 * (profileTheta - profileM0 profileCentre) -
    (profileW profileCentre - 1 - 21 * profileM0 profileCentre) = 0 := by
  norm_num [profileTheta, profileM0, profileW, profileCentre]

-- The universal envelope cannot be made strict: k=1 attains the maximum.
example : ¬ (∀ ψ : ℝ, 0 ≤ ψ → ψ ≤ 2 / 3 →
    ∀ k : Fin 5, profileBranch ψ k < profileTheta) := by
  intro h
  have hh := h profileCentre (by norm_num [profileCentre])
    (by norm_num [profileCentre]) 1
  rw [centre_values.2.2.2] at hh
  exact (lt_irrefl _) hh

end P0365Subquarter
