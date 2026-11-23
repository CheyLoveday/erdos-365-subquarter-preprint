import PaperProofs.DivisorGrowth

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print CF15PolynomialExponentialBound
#print CF15DivisorPowerGrowth
#print CF15DivisorSubpower
#print CF15PolynomialHeightDivisorGrowth
#print CF15ActualGraphDivisorGrowth
#check (polynomial_exponential_bound : CF15PolynomialExponentialBound)
#check (divisor_power_growth : CF15DivisorPowerGrowth)
#check (divisor_subpower : CF15DivisorSubpower)
#check (polynomial_height_divisor_growth : CF15PolynomialHeightDivisorGrowth)
#check (actual_graph_divisor_growth : CF15ActualGraphDivisorGrowth)
#print axioms polynomial_exponential_bound
#print axioms divisor_power_growth
#print axioms divisor_subpower
#print axioms polynomial_height_divisor_growth
#print axioms actual_graph_divisor_growth
set_option pp.all false

example : CF15PolynomialExponentialBound := by
  intro k
  exact polynomial_exponential_bound k
example : CF15DivisorPowerGrowth := by
  intro k
  exact divisor_power_growth k
example : CF15DivisorSubpower := by
  intro ε hε
  exact divisor_subpower ε hε
example : CF15PolynomialHeightDivisorGrowth := by
  intro ε hε
  exact polynomial_height_divisor_growth ε hε
example : CF15ActualGraphDivisorGrowth := by
  intro ε hε
  exact actual_graph_divisor_growth ε hε

-- The reciprocal-root step must choose a positive k, even though the integer
-- estimate itself correctly includes k0 and the unit n1.
example : ∃ C : ℕ, 1≤C ∧ ∀ n : ℕ, n≠0 → (divisorCount n)^0≤C*n := divisor_power_growth 0
example (k : ℕ) : (divisorCount 1)^k=1 := by simp [divisorCount]
example (C : ℕ) : ¬ (divisorCount 0)^0≤C*0 := by simp [divisorCount]
example (ε : ℝ) : (divisorCount 1:ℝ)^ε=1 := by simp [divisorCount]
-- Exact exponent allocation pays both the eighth power and height exponent90.
example (ε : ℝ) : (ε/720)*(8:ℝ)*(90:ℝ)=ε := by ring
example : ((1:ℝ)/720)*(8:ℝ)*(90:ℝ)=1 := by norm_num
example : ((1:ℝ)/8)*(8:ℝ)*(90:ℝ) ≠ 1 := by norm_num
-- Unit resultants and the first allowed scale remain in the real estimate.
example : ∃ C : ℝ, 0<C ∧ ∀ X : ℝ, 32≤X →
    (divisorCount 1:ℝ)^8≤C*X^((1:ℝ)/1000) := by
  obtain ⟨C,hC,h⟩ := polynomial_height_divisor_growth ((1:ℝ)/1000) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro X hX
  apply h X hX 1 (by decide)
  have hpow : (1:ℝ)≤X^(90:ℕ) := one_le_pow₀ (by linarith)
  norm_num
  nlinarith

end
end P0365Subquarter
