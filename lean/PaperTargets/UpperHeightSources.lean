import PaperTargets.ReussLogScale

/-! CF04 actual source ranges and a fixed-error budget for upper coordinate
heights. The scaled heights do not retain the literal prescribed U,V coupling;
the generic determinant extension remains a separate obligation. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Inclusive original source boxes give uniform multiplier ranges and positive
constant lower scales, including every kernel/multiplier equal to one. -/
def CF04ActualMultiplierRanges : Prop :=
  ∀ X B E : ℝ, 1≤X → 0<B → 0<E → ∀ n b d u v : ℕ,
    PairSource n b d u v → actualRealBox X B E n b d →
      1/2≤B ∧ 1/2≤E ∧ 1/2≤reussMultiplierScale X B ∧
      1/2≤reussMultiplierScale X E ∧
      reussMultiplierScale X B/4≤(u:ℝ) ∧ (u:ℝ)≤2*reussMultiplierScale X B ∧
      reussMultiplierScale X E/4≤(v:ℝ) ∧ (v:ℝ)≤2*reussMultiplierScale X E

/-- Four-times nominal scales bound every actual coordinate and are >=2.
The preceding fixed-error log theorem pays their product factors16 using the
same rounded M at one uniform threshold. It asserts no polynomial existence. -/
def CF04ActualUpperHeightLogBudget : Prop :=
  ∀ δ : ℝ, 0<δ → δ≤1 → ∃ X₀ : ℝ, 32≤X₀ ∧
    ∀ X : ℝ, X₀≤X → ∀ B E : ℝ, 0<B → 0<E →
    ∀ n b d u v : ℕ, PairSource n b d u v → actualRealBox X B E n b d →
      X^profileTheta<(b*d:ℝ) → X^profileTheta<(u*v:ℝ) →
      ∃ ψ : ℝ, B*E=X^ψ ∧ profileTheta/2≤ψ ∧
        ψ≤(2/3)*(1-profileTheta/2) ∧
        2≤4*B ∧ 2≤4*E ∧ 2≤4*reussMultiplierScale X B ∧
        2≤4*reussMultiplierScale X E ∧
        (b:ℝ)≤4*B ∧ (d:ℝ)≤4*E ∧
        (u:ℝ)≤4*reussMultiplierScale X B ∧
        (v:ℝ)≤4*reussMultiplierScale X E ∧
        (9/32)*profileTheta^2*Real.log X≤Real.log (roundedHeight X ψ δ:ℝ) ∧
        Real.log (roundedHeight X ψ δ:ℝ)≤Real.log X ∧
        (9/8)*(1+δ/2)*(Real.log ((4*B)*(4*E))*
          Real.log ((4*reussMultiplierScale X B)*(4*reussMultiplierScale X E))/
            Real.log X)≤Real.log (roundedHeight X ψ δ:ℝ)

end
end P0365Subquarter
