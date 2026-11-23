import PaperProofs.ReussLogScale

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04RoundedLogSlack
#print CF04ActualReussLogScale
#check (rounded_log_slack : CF04RoundedLogSlack)
#check (actual_reuss_log_scale : CF04ActualReussLogScale)
#print axioms rounded_log_slack
#print axioms actual_reuss_log_scale
set_option pp.all false

example : CF04RoundedLogSlack := by
  intro δ κ hδ hδ₁ hκ
  obtain ⟨X₀,hX₀,hslack⟩ := rounded_log_slack δ κ hδ hδ₁ hκ
  refine ⟨X₀,hX₀,?_⟩
  intro X hX ψ hlo hhi
  exact hslack X hX ψ hlo hhi
example : CF04ActualReussLogScale := by
  intro δ κ hδ hδ₁ hκ
  obtain ⟨X₀,hX₀,hactual⟩ := actual_reuss_log_scale δ κ hδ hδ₁ hκ
  refine ⟨X₀,hX₀,?_⟩
  intro X hX B E hB hE n b d u v hs hbox hbd hq
  exact hactual X hX B E hB hE n b d u v hs hbox hbd hq

-- The zero-error boundary gives an actual rounded integer 1<=M<=X,
-- retaining delta=1 and arbitrarily small positive delta in the quantifiers.
example (δ : ℝ) (hδ : 0<δ) (hδ₁ : δ≤1) :
    ∃ X₀ : ℝ, 32≤X₀ ∧ ∀ X : ℝ, X₀≤X → ∀ ψ : ℝ,
      profileTheta/2≤ψ → ψ≤(2/3)*(1-profileTheta/2) →
      1≤(roundedHeight X ψ δ:ℝ) ∧ (roundedHeight X ψ δ:ℝ)≤X := by
  obtain ⟨X₀,hX₀,hslack⟩ := rounded_log_slack δ 0 hδ hδ₁ (by norm_num)
  refine ⟨X₀,hX₀,?_⟩
  intro X hX ψ hlo hhi
  have ht : 0<profileTheta := by norm_num [profileTheta]
  have hψ₀ : 0≤ψ := by linarith
  have hψ₂ : ψ≤2/3 := by linarith
  have hX₁ : 1≤X := by linarith
  have hM₁ := (rounded_height_bounds X ψ δ hX₁ hψ₀ hψ₂ hδ.le).1
  have hMpos : (0:ℝ)<roundedHeight X ψ δ := by linarith
  have hXp : 0<X := by linarith
  exact ⟨hM₁,(Real.log_le_log_iff hMpos hXp).mp (hslack X hX ψ hlo hhi).2.1⟩

-- Exact coupling keeps both individual multiplier scales positive even when
-- an individual scale is <=1; no individual logarithm-growth premise is used.
example (X B : ℝ) (hX : 0<X) (hB : 0<B) : 0<reussMultiplierScale X B := by
  dsimp [reussMultiplierScale]
  positivity

end
end P0365Subquarter
