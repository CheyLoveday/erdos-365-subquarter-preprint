import PaperProofs.LowFactorLevels

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print primitiveBinaryPoint
#print rationalBinary
#print binaryNonproportional
#print lowBinaryFactorPair
#print CF15SignedPrimitiveParallel
#print CF15PrimitiveRatioFiber
#print CF15HomogeneousPrimitiveZeros
#print CF15TwoLinearLevels
#print CF15LinearQuadraticLevels
#print CF15TwoQuadraticLevels
#print CF15LowFactorDivisorBudget
#check (signed_primitive_parallel : CF15SignedPrimitiveParallel)
#check (primitive_ratio_fiber : CF15PrimitiveRatioFiber)
#check (homogeneous_primitive_zeros : CF15HomogeneousPrimitiveZeros)
#check (two_linear_levels : CF15TwoLinearLevels)
#check (linear_quadratic_levels : CF15LinearQuadraticLevels)
#check (two_quadratic_levels : CF15TwoQuadraticLevels)
#check (low_factor_divisor_budget : CF15LowFactorDivisorBudget)
#print axioms signed_primitive_parallel
#print axioms primitive_ratio_fiber
#print axioms homogeneous_primitive_zeros
#print axioms two_linear_levels
#print axioms linear_quadratic_levels
#print axioms two_quadratic_levels
#print axioms low_factor_divisor_budget
set_option pp.all false

-- Complete typed applications of the seven frozen targets.
example : CF15SignedPrimitiveParallel := by
  intro z w hz hw he
  exact signed_primitive_parallel z w hz hw he
example : CF15PrimitiveRatioFiber := by
  intro r S hS
  exact primitive_ratio_fiber r S hS
example : CF15HomogeneousPrimitiveZeros := by
  intro K d hK hhom S hS
  exact homogeneous_primitive_zeros K d hK hhom S hS
example : CF15TwoLinearLevels := by
  intro L₁ L₂ hL₁ hL₂ hn h₁ h₂ hh₁ hh₂ S hS
  exact two_linear_levels L₁ L₂ hL₁ hL₂ hn h₁ h₂ hh₁ hh₂ S hS
example : CF15LinearQuadraticLevels := by
  intro L G hL hG hn a b ha hb S hS
  exact linear_quadratic_levels L G hL hG hn a b ha hb S hS
example : CF15TwoQuadraticLevels := by
  intro G H hG hH hn a b ha hb S hS
  exact two_quadratic_levels G H hG hH hn a b ha hb S hS
example : CF15LowFactorDivisorBudget := by
  intro Q G H hp hG hH h hh S hS
  exact low_factor_divisor_budget Q G H hp hG hH h hh S hS

private def infinityPoint : Fin 2 → ℤ := ![1,0]
private theorem infinity_primitive : primitiveBinaryPoint infinityPoint := ⟨1,0,by simp [infinityPoint]⟩
-- Both signed points at infinity are real primitive roots of Y. The affine
-- polynomial is constant1, so omitting infinity would incorrectly count zero.
example : binaryDehomogenize (MvPolynomial.X 1)=1 := by simp [binaryDehomogenize]
example : ({infinityPoint,-infinityPoint} : Finset (Fin 2 → ℤ)).card=2 := by
  apply Finset.card_pair
  intro he
  have h := congrArg (fun z : Fin 2 → ℤ => z 0) he
  norm_num [infinityPoint] at h
example : ({infinityPoint,-infinityPoint} : Finset (Fin 2 → ℤ)).card ≤ 2 := by
  apply homogeneous_primitive_zeros (MvPolynomial.X 1) 1 (by simp) (MvPolynomial.isHomogeneous_X ℤ 1)
  intro z hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact ⟨infinity_primitive,by simp [infinityPoint]⟩
  · refine ⟨⟨-1,0,by simp [infinityPoint]⟩,?_⟩
    simp [infinityPoint]
-- Zero polynomial guard is necessary even in homogeneous degree zero.
example : (0:SourcePolynomial).IsHomogeneous 0 ∧
    MvPolynomial.eval infinityPoint (0:SourcePolynomial)=0 ∧
    ({infinityPoint} : Finset (Fin 2 → ℤ)).card>2*0 := by
  exact ⟨MvPolynomial.isHomogeneous_zero (Fin 2) ℤ 0,by simp,by simp⟩
-- Nonprimitive multiples would violate the two-representative conclusion.
example : ¬ primitiveBinaryPoint (![2,0] : Fin 2 → ℤ) := by
  intro h
  have hu : IsUnit (2:ℤ) := isCoprime_zero_right.mp (by simpa [primitiveBinaryPoint] using h)
  rcases Int.isUnit_eq_one_or hu with h | h <;> norm_num at h

private theorem coordinate_nonproportional : binaryNonproportional (MvPolynomial.X 0) (MvPolynomial.X 1) := by
  rintro ⟨q,he⟩
  have h := congrArg (MvPolynomial.eval (![1,0] : Fin 2 → ℚ)) he
  norm_num [rationalBinary] at h
private theorem coordinate_pair : lowBinaryFactorPair (MvPolynomial.X 0) (MvPolynomial.X 1) :=
  ⟨by simp,by simp,Or.inl ⟨MvPolynomial.isHomogeneous_X ℤ 0,MvPolynomial.isHomogeneous_X ℤ 1,
    coordinate_nonproportional⟩⟩
-- Negative admitted levels and both signs are part of the divisor budget.
example (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, primitiveBinaryPoint z ∧ z 0*z 1=(-1:ℤ)) : S.card ≤ 16 := by
  have h := low_factor_divisor_budget (MvPolynomial.X 0*MvPolynomial.X 1)
    (MvPolynomial.X 0) (MvPolynomial.X 1) coordinate_pair ⟨_,rfl⟩ ⟨_,mul_comm _ _⟩ (-1) (by decide) S (by
      intro z hz
      exact ⟨(hS z hz).1,by simpa using (hS z hz).2⟩)
  simpa using h
-- At level0 the claimed divisor ceiling would be0, yet there is a primitive
-- point and both coordinate factors divide Q=0. Nonzero h cannot be dropped.
example : lowBinaryFactorPair (MvPolynomial.X 0) (MvPolynomial.X 1) ∧
    (MvPolynomial.X 0:SourcePolynomial) ∣ 0 ∧ (MvPolynomial.X 1:SourcePolynomial) ∣ 0 ∧
    MvPolynomial.eval infinityPoint (0:SourcePolynomial)=0 ∧
    16*((0:ℤ).natAbs.divisors.card)^2=0 := by
  exact ⟨coordinate_pair,dvd_zero _,dvd_zero _,by simp,by simp⟩

private def pellQuadratic : SourcePolynomial := MvPolynomial.X 0^2-MvPolynomial.C 2*MvPolynomial.X 1^2
private def pellFive : Finset (Fin 2 → ℤ) :=
  {![1,0],![-1,0],![3,2],![-3,-2],![17,12]}
-- Proportional quadratic levels can contain more than four primitive points;
-- this explicit fifth point already refutes the uniform four-point shortcut.
example : pellFive.card=5 := by
  norm_num [pellFive,Finset.card_insert_of_notMem,funext_iff,Fin.forall_fin_two]
example : ∀ z ∈ pellFive, primitiveBinaryPoint z ∧ MvPolynomial.eval z pellQuadratic=1 := by
  intro z hz
  simp only [pellFive,Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨1,0,by norm_num⟩,by norm_num [pellQuadratic]⟩
  · exact ⟨⟨-1,0,by norm_num⟩,by norm_num [pellQuadratic]⟩
  · exact ⟨⟨1,-1,by norm_num⟩,by norm_num [pellQuadratic]⟩
  · exact ⟨⟨-1,1,by norm_num⟩,by norm_num [pellQuadratic]⟩
  · exact ⟨⟨5,-7,by norm_num⟩,by norm_num [pellQuadratic]⟩
example : ¬ binaryNonproportional pellQuadratic pellQuadratic := by
  intro h
  exact h ⟨1,by simp⟩

end
end P0365Subquarter
