import PaperProofs.RootColumns

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF04RootColumnSupport
#print CF04RootColumnCoefficientBound
#print CF04ActualRectangularRootColumns
#check (root_column_support : CF04RootColumnSupport)
#check (root_column_coefficient_bound : CF04RootColumnCoefficientBound)
#check (actual_rectangular_root_columns : CF04ActualRectangularRootColumns)
#print axioms root_column_support
#print axioms root_column_coefficient_bound
#print axioms actual_rectangular_root_columns
set_option pp.all false

example : CF04RootColumnSupport := by
  intro i j e he
  exact root_column_support i j e he
example : CF04RootColumnCoefficientBound := by
  intro A C
  exact root_column_coefficient_bound A C
example : CF04ActualRectangularRootColumns := by
  intro n b d u v hs X M a hX hn hM hMX ha hint
  exact actual_rectangular_root_columns n b d u v hs X M a hX hn hM hMX ha hint

-- The actual 8/9 source is at the upper closed endpoint for a=M=1.
-- One common pair controls degrees beyond the previous eight columns and zero.
example : ∃ α β : ℝ, 0≤α ∧ α≤3 ∧ |β|≤1 ∧
    (rectangularIntegerEntry 8 9 2 1 1 3 8 9:ℝ)=
      (1:ℝ)^8*1^9*1^8*((1:ℝ)^(3/2:ℝ))^9*rootColumnValue 8 9 α β ∧
    (rectangularIntegerEntry 0 0 2 1 1 3 0 0:ℝ)=
      (1:ℝ)^0*1^0*1^0*((1:ℝ)^(3/2:ℝ))^0*rootColumnValue 0 0 α β := by
  have hs : PairSource 8 2 1 1 3 :=
    ⟨by decide,by decide,by decide,by decide,Nat.squarefree_two,squarefree_one,by decide,by decide⟩
  obtain ⟨α,β,hα,hα',hβ,hcol⟩ := actual_rectangular_root_columns
    8 2 1 1 3 hs 8 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [actualDirectInterval])
  exact ⟨α,β,hα,by simpa using hα',by simpa using hβ,
    by simpa only [Nat.cast_one] using hcol 8 9 8 9 (by omega) (by omega),
    by simpa only [Nat.cast_one] using hcol 0 0 0 0 (by omega) (by omega)⟩

-- Support is checked at large degrees; exponent zero is included in the bounds.
example (e : Fin 2 →₀ ℕ) (he : e ∈ (rootColumnPolynomial 8 9).support) :
    e 0≤2*8+3*9 ∧ e 1≤9 := root_column_support 8 9 e he
example (e : Fin 2 →₀ ℕ) (he : e ∈ (rootColumnPolynomial 0 0).support) :
    e 0≤0 ∧ e 1≤0 := root_column_support 0 0 e he

end
end P0365Subquarter
