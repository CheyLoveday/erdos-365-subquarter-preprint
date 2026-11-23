import PaperTargets.DividedMinors

/-! Geometric original-interval inventory. No polynomial cover or count is
supplied or concluded. One common family precedes every point/source. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- A compact positive ratio range has at most3M+1 original relative intervals,
including both endpoints. -/
def CF17RelativeIntervalCover : Prop :=
  ∀ a₀ : ℝ, 0<a₀ → ∀ M : ℕ, 1≤M → ∃ A : Finset ℝ,
    A.card≤3*M+1 ∧ (∀ a ∈ A, 0<a) ∧
    ∀ s : ℝ, a₀≤s → s≤4*a₀ →
      ∃ a ∈ A, a≤s ∧ s≤a*(1+1/(M:ℝ))

/-- The same finite family covers all actual ratios in one original box.
Neither a source-specific family nor a second inverse-chart inventory is used. -/
def CF17ActualBoxIntervalCover : Prop :=
  ∀ X B E : ℝ, 0<B → 0<E → ∀ M : ℕ, 1≤M → ∃ A : Finset ℝ,
    A.card≤3*M+1 ∧ (∀ a ∈ A, 0<a) ∧
    ∀ n b d : ℕ, actualRealBox X B E n b d →
      ∃ a ∈ A, actualDirectInterval a (M:ℝ) b d

end
end P0365Subquarter
