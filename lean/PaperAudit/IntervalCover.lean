import PaperProofs.IntervalCover

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF17RelativeIntervalCover
#print CF17ActualBoxIntervalCover
#check (relative_interval_cover : CF17RelativeIntervalCover)
#check (actual_box_interval_cover : CF17ActualBoxIntervalCover)
#print axioms relative_interval_cover
#print axioms actual_box_interval_cover
set_option pp.all false

example : CF17RelativeIntervalCover := by
  intro a₀ ha₀ M hM
  exact relative_interval_cover a₀ ha₀ M hM
example : CF17ActualBoxIntervalCover := by
  intro X B E hB hE M hM
  exact actual_box_interval_cover X B E hB hE M hM

-- Both endpoints belong to the same family, including M=1.
example (a₀ : ℝ) (ha₀ : 0<a₀) (M : ℕ) (hM : 1≤M) :
    ∃ A : Finset ℝ, A.card≤3*M+1 ∧
      (∃ a ∈ A, a≤a₀ ∧ a₀≤a*(1+1/(M:ℝ))) ∧
      (∃ a ∈ A, a≤4*a₀ ∧ 4*a₀≤a*(1+1/(M:ℝ))) := by
  obtain ⟨A,hcard,_,hcover⟩ := relative_interval_cover a₀ ha₀ M hM
  exact ⟨A,hcard,hcover a₀ le_rfl (by linarith),hcover (4*a₀) (by linarith) le_rfl⟩

-- The geometry needs neither a positive shell nor a PairSource premise.
-- This zero-shell box is nonempty and its kernel-one ratio is still covered.
example : ∃ A : Finset ℝ, A.card≤4 ∧ ∃ a ∈ A, actualDirectInterval a 1 1 1 := by
  obtain ⟨A,hcard,_,hcover⟩ := actual_box_interval_cover 0 1 1
    (by norm_num) (by norm_num) 1 (by norm_num)
  refine ⟨A,by simpa using hcard,?_⟩
  simpa using hcover 0 1 1 (by norm_num [actualRealBox])

end
end P0365Subquarter
