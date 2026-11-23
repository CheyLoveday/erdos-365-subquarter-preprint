import PaperProofs.ResidualProfiles

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04ActualBoxProductBounds
#print CF04ResidualCompactProfile
#check (actual_box_product_bounds : CF04ActualBoxProductBounds)
#check (residual_compact_profile : CF04ResidualCompactProfile)
#print axioms actual_box_product_bounds
#print axioms residual_compact_profile
set_option pp.all false

example : CF04ActualBoxProductBounds := by
  intro X B E hX hB hE n b d u v hs hbox
  exact actual_box_product_bounds X B E hX hB hE n b d u v hs hbox
example : CF04ResidualCompactProfile := by
  obtain ⟨X₀,hX₀,hprofile⟩ := residual_compact_profile
  refine ⟨X₀,hX₀,?_⟩
  intro X hX B E hB hE n b d u v hs hbox hbd hq
  exact hprofile X hX B E hB hE n b d u v hs hbox hbd hq

-- Actual 8/9 data include denominator kernel and first multiplier equal to one.
example : (2*1:ℝ)≤4*(2*1) ∧ (1*3:ℝ)^2*(2*1)^3≤6*(8:ℝ)^2 := by
  have hs : PairSource 8 2 1 1 3 :=
    ⟨by decide,by decide,by decide,by decide,Nat.squarefree_two,squarefree_one,by decide,by decide⟩
  simpa using actual_box_product_bounds 8 2 1 (by norm_num) (by norm_num) (by norm_num)
    8 2 1 1 3 hs (by norm_num [actualRealBox])

-- The compact range stays within the original CF16 domain with positive margin.
example (ψ : ℝ) (hlo : profileTheta/2≤ψ)
    (hhi : ψ≤(2/3)*(1-profileTheta/2))
    (hm : (9/32)*profileTheta^2≤profileM0 ψ) :
    0<ψ ∧ ψ<2/3 ∧ 0<profileM0 ψ := by
  have ht : 0<profileTheta := by norm_num [profileTheta]
  have hm₀ : 0<(9/32:ℝ)*profileTheta^2 := by positivity
  exact ⟨by linarith,by linarith,hm₀.trans_le hm⟩

-- A product at most one is outside either residual population at X>=32.
example (X z : ℝ) (hX : 32≤X) (hz : z≤1) : ¬X^profileTheta<z := by
  have ht : 0≤profileTheta := by norm_num [profileTheta]
  have hpow : 1≤X^profileTheta := Real.one_le_rpow (by linarith) ht
  exact not_lt_of_ge (hz.trans hpow)

end
end P0365Subquarter
