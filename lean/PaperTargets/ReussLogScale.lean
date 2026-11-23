import PaperTargets.ResidualProfiles

/-! CF04 rounded logarithmic/source-scale application. No polynomial existence
or determinant extension is assumed here. The fixed nonnegative log perturbation
allows later upper-height/source adapters to pay their constant factors. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- The prescribed original multiplier scale, retaining its exact dependence
on X and the corresponding kernel-box scale. -/
def reussMultiplierScale (X B : ℝ) : ℝ := X^(1/2:ℝ)/B^(3/2:ℝ)

/-- Uniform rounded M satisfies both logarithmic size conditions and the
Reuss product budget at half the construction slack, including fixed errors. -/
def CF04RoundedLogSlack : Prop :=
  ∀ δ κ : ℝ, 0<δ → δ≤1 → 0≤κ → ∃ X₀ : ℝ, 32≤X₀ ∧
    ∀ X : ℝ, X₀≤X → ∀ ψ : ℝ,
      profileTheta/2≤ψ → ψ≤(2/3)*(1-profileTheta/2) →
      (9/32)*profileTheta^2*Real.log X≤Real.log (roundedHeight X ψ δ:ℝ) ∧
      Real.log (roundedHeight X ψ δ:ℝ)≤Real.log X ∧
      (9/8)*(1+δ/2)*((ψ*Real.log X+κ)*
        ((1-(3/2)*ψ)*Real.log X+κ)/Real.log X)≤
          Real.log (roundedHeight X ψ δ:ℝ)

/-- The same threshold and fixed-error budget apply to every actual residual
source at the prescribed coupled B,E,U,V scales, with all product logs comparable
to log X. The scale identity is exact, before any upper-height extension. -/
def CF04ActualReussLogScale : Prop :=
  ∀ δ κ : ℝ, 0<δ → δ≤1 → 0≤κ → ∃ X₀ : ℝ, 32≤X₀ ∧
    ∀ X : ℝ, X₀≤X → ∀ B E : ℝ, 0<B → 0<E →
    ∀ n b d u v : ℕ, PairSource n b d u v → actualRealBox X B E n b d →
      X^profileTheta<(b*d:ℝ) → X^profileTheta<(u*v:ℝ) →
      ∃ ψ : ℝ, B*E=X^ψ ∧ profileTheta/2≤ψ ∧
        ψ≤(2/3)*(1-profileTheta/2) ∧
        profileTheta/2*Real.log X≤Real.log (B*E) ∧
        Real.log (B*E)≤Real.log X ∧
        profileTheta/2*Real.log X≤
          Real.log (reussMultiplierScale X B*reussMultiplierScale X E) ∧
        Real.log (reussMultiplierScale X B*reussMultiplierScale X E)≤Real.log X ∧
        (9/32)*profileTheta^2*Real.log X≤Real.log (roundedHeight X ψ δ:ℝ) ∧
        Real.log (roundedHeight X ψ δ:ℝ)≤Real.log X ∧
        (9/8)*(1+δ/2)*((Real.log (B*E)+κ)*
          (Real.log (reussMultiplierScale X B*reussMultiplierScale X E)+κ)/Real.log X)≤
            Real.log (roundedHeight X ψ δ:ℝ)

end
end P0365Subquarter
