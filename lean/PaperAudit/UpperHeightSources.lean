import PaperProofs.UpperHeightSources

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04ActualMultiplierRanges
#print CF04ActualUpperHeightLogBudget
#check (actual_multiplier_ranges : CF04ActualMultiplierRanges)
#check (actual_upper_height_log_budget : CF04ActualUpperHeightLogBudget)
#print axioms actual_multiplier_ranges
#print axioms actual_upper_height_log_budget
set_option pp.all false

example : CF04ActualMultiplierRanges := by
  intro X B E hX hB hE n b d u v hs hbox
  exact actual_multiplier_ranges X B E hX hB hE n b d u v hs hbox
example : CF04ActualUpperHeightLogBudget := by
  intro δ hδ hδ₁
  obtain ⟨X₀,hX₀,hactual⟩ := actual_upper_height_log_budget δ hδ hδ₁
  refine ⟨X₀,hX₀,?_⟩
  intro X hX B E hB hE n b d u v hs hbox hbd hq
  exact hactual X hX B E hB hE n b d u v hs hbox hbd hq

-- Actual 8/9 source with d=u=1, both kernel-box upper endpoints, and E=1/2.
-- Thus the four-times E height equals2: the bound must include equality.
example : 2≤4*reussMultiplierScale 8 1 ∧
    (1:ℝ)≤4*reussMultiplierScale 8 1 ∧ (4*(1/2:ℝ))=2 := by
  have hs : PairSource 8 2 1 1 3 :=
    ⟨by decide,by decide,by decide,by decide,Nat.squarefree_two,squarefree_one,by decide,by decide⟩
  obtain ⟨_,_,hU,_,_,hu,_,_⟩ := actual_multiplier_ranges 8 1 (1/2)
    (by norm_num) (by norm_num) (by norm_num) 8 2 1 1 3 hs
    (by norm_num [actualRealBox])
  have hu' : (1:ℝ)≤2*reussMultiplierScale 8 1 := by simpa using hu
  exact ⟨by linarith,by linarith,by norm_num⟩

-- Both enlarged product logs have a positive domain at the proved lower2 bound.
example (D E U V : ℝ) (hD : 2≤D) (hE : 2≤E) (hU : 2≤U) (hV : 2≤V) :
    0<Real.log (D*E) ∧ 0<Real.log (U*V) := by
  constructor <;> apply Real.log_pos
  · nlinarith [mul_le_mul hD hE (by norm_num : (0:ℝ)≤2) (by linarith : 0≤D)]
  · nlinarith [mul_le_mul hU hV (by norm_num : (0:ℝ)≤2) (by linarith : 0≤U)]

end
end P0365Subquarter
