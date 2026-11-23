import PaperTargets.DividedMinors

/-! CF04 actual residual-box profile proposal. These targets produce no coarse
polynomial and assume no external inventory or counting result. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Original source equations and inclusive box bounds control both products
at the actual real shell scale, including kernels or multipliers equal to one. -/
def CF04ActualBoxProductBounds : Prop :=
  ∀ X B E : ℝ, 1≤X → 0<B → 0<E → ∀ n b d u v : ℕ,
    PairSource n b d u v → actualRealBox X B E n b d →
      (b*d:ℝ)≤4*(B*E) ∧ (u*v:ℝ)^2*(B*E)^3≤6*X^2

/-- Removing the two already-counted small-product populations puts every
remaining actual box in one fixed compact profile range. One threshold precedes
all boxes and sources; the positive lower determinant exponent is uniform. -/
def CF04ResidualCompactProfile : Prop :=
  ∃ X₀ : ℝ, 32≤X₀ ∧ ∀ X : ℝ, X₀≤X → ∀ B E : ℝ, 0<B → 0<E →
    ∀ n b d u v : ℕ, PairSource n b d u v → actualRealBox X B E n b d →
      X^profileTheta<(b*d:ℝ) → X^profileTheta<(u*v:ℝ) →
      ∃ ψ : ℝ, B*E=X^ψ ∧ profileTheta/2≤ψ ∧
        ψ≤(2/3)*(1-profileTheta/2) ∧
        profileTheta/2≤1-(3/2)*ψ ∧
        (9/32)*profileTheta^2≤profileM0 ψ

end
end P0365Subquarter
