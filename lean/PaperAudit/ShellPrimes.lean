import PaperProofs.ShellPrimes
import PaperTargets.DividedMinors

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF08RoundedShellSourceAssignment
#check (rounded_shell_source_assignment : CF08RoundedShellSourceAssignment)
#print axioms rounded_shell_source_assignment
set_option pp.all false

example : CF08RoundedShellSourceAssignment := by
  intro D H C δ hH hC hδ
  exact rounded_shell_source_assignment D H C δ hH hC hδ

-- The actual box supplies exactly the enlarged shell cutoff.
example (X B E : ℝ) (n b d : ℕ) (h : actualRealBox X B E n b d) :
    (n:ℝ)≤2*X := h.2.1
-- The rounded-height endpoints are retained, including their constant ceiling.
example (X δ : ℝ) : roundedHeight X 0 δ=1 := by
  simp [roundedHeight,profileM0]
example (X δ : ℝ) : roundedHeight X (2/3) δ=1 := by
  norm_num [roundedHeight,profileM0]
-- A zero polynomial has no nonsingular source, including zero coefficient-height data.
example (b d u v : ℕ) : ¬nonsingularSource 0 b d u v := by
  simp [nonsingularSource,polynomialValue]
-- A toy ceiling-normalized scale can fall even with positive unrounded growth.
-- This arithmetic control is separate from the actual profile definition.
example : (32:ℝ)^2/(Nat.ceil (32:ℝ):ℝ)>
    ((129:ℝ)/4)^2/(Nat.ceil ((129:ℝ)/4):ℝ) := by
  have hc : Nat.ceil ((129:ℝ)/4)=33 :=
    (Nat.ceil_eq_iff (by decide)).2 (by norm_num)
  rw [hc]
  norm_num

end
end P0365Subquarter
