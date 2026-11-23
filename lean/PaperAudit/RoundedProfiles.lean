import PaperProofs.RoundedProfiles

namespace P0365Subquarter

set_option pp.all true

#print roundedHeight
#print roundedScale
#print roundedMixedTerm
#print CF16RoundedHeightBounds
#print CF17RoundedPrimeScale
#print CF17RoundedMixedTermBound
#print CF17RoundedErrorAbsorption
#check (rounded_height_bounds : CF16RoundedHeightBounds)
#check (rounded_prime_scale : CF17RoundedPrimeScale)
#check (rounded_mixed_term_bound : CF17RoundedMixedTermBound)
#check (rounded_error_absorption : CF17RoundedErrorAbsorption)
#print axioms rounded_height_bounds
#print axioms rounded_prime_scale
#print axioms rounded_mixed_term_bound
#print axioms rounded_error_absorption

-- No extra source/population assumptions at endpoint profiles or x=1.
example (x δ : ℝ) : roundedHeight x 0 δ = 1 := by simp [roundedHeight, profileM0]
example (x δ : ℝ) : roundedHeight x (2 / 3) δ = 1 := by
  norm_num [roundedHeight, profileM0]
example (ψ δ : ℝ) : roundedHeight 1 ψ δ = 1 ∧ roundedScale 1 ψ δ = 1 := by
  simp [roundedHeight, roundedScale]

-- Integral powers agree with the real-exponent presentation of each error term.
example (x ψ δ : ℝ) (k : Fin 5) : roundedMixedTerm x ψ δ k =
    x ^ (profileW ψ - (k.val : ℝ)) /
      (roundedHeight x ψ δ : ℝ) ^ (profileErrorWeight k : ℕ) := by
  unfold roundedMixedTerm
  rw [Real.rpow_natCast]

-- Ceil is not an exact real identity, and x=1 cannot absorb an arbitrary constant.
example : (Nat.ceil (3 / 2 : ℝ) : ℝ) ≠ 3 / 2 := by
  have h : Nat.ceil (3 / 2 : ℝ) = 2 := (Nat.ceil_eq_iff (by decide)).2 (by norm_num)
  rw [h]
  norm_num
example (ψ δ : ℝ) : ¬ ((∑ k : Fin 5, roundedMixedTerm 1 ψ δ k) <
    roundedScale 1 ψ δ ^ (28 : ℕ)) := by
  simp [roundedMixedTerm, roundedScale, roundedHeight]

end P0365Subquarter
