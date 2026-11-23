import PaperProofs.PrimitiveFactors

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print CF15HomogeneousScalarCancellation
#print CF15PrimitiveDehomogenization
#print CF15HomogenizationPadding
#print CF15HomogeneousFactorLift
#print CF15PrimitiveSmallPowerTransfer
#print CF15ActualPrimitiveGraphFactors
#check (homogeneous_scalar_cancellation : CF15HomogeneousScalarCancellation)
#check (primitive_dehomogenization : CF15PrimitiveDehomogenization)
#check (homogenization_padding : CF15HomogenizationPadding)
#check (homogeneous_factor_lift : CF15HomogeneousFactorLift)
#check (primitive_small_power_transfer : CF15PrimitiveSmallPowerTransfer)
#check (actual_primitive_graph_factors : CF15ActualPrimitiveGraphFactors)
#print axioms homogeneous_scalar_cancellation
#print axioms primitive_dehomogenization
#print axioms homogenization_padding
#print axioms homogeneous_factor_lift
#print axioms primitive_small_power_transfer
#print axioms actual_primitive_graph_factors
set_option pp.all false

example : CF15HomogeneousScalarCancellation := by
  intro H Q c N hc he hh
  exact homogeneous_scalar_cancellation H Q c N hc he hh
example : CF15PrimitiveDehomogenization := by
  intro Q N hh hc
  exact primitive_dehomogenization Q N hh hc
example : CF15HomogenizationPadding := by
  intro P N hN
  exact homogenization_padding P N hN
example : CF15HomogeneousFactorLift := by
  intro P f N hp hf hN
  exact homogeneous_factor_lift P f N hp hf hN
example : CF15PrimitiveSmallPowerTransfer := by
  intro H Q c he hn G d k a hh hd
  exact primitive_small_power_transfer H Q c he hn G d k a hh hd
example : CF15ActualPrimitiveGraphFactors := by
  intro X D A B hX hg hr inverse
  exact actual_primitive_graph_factors X D A B hX hg hr inverse

-- Repeated factors at infinity survive reconstruction, including unit sections.
example : (1:Polynomial ℤ).homogenize 7=MvPolynomial.X 1^7 := by simp
example : binaryDehomogenize (MvPolynomial.X 1^7)=1 := by simp [binaryDehomogenize]
example : (0:Polynomial ℤ).homogenize 7=
    (0:Polynomial ℤ).homogenize 0*MvPolynomial.X 1^7 := by simp
example : (Polynomial.X:Polynomial ℤ).homogenize 7=
    MvPolynomial.X 0*MvPolynomial.X 1^6 := by
  simp
-- Every unit factor is retained; degree zero is not silently filtered away.
example : (-1:Polynomial ℤ).IsPrimitive ∧ (-1:Polynomial ℤ) ≠ 0 ∧
    (-1:Polynomial ℤ).natDegree ≤ 7 ∧
    ((-1:Polynomial ℤ).homogenize (-1:Polynomial ℤ).natDegree).IsHomogeneous (-1:Polynomial ℤ).natDegree ∧
    (-1:Polynomial ℤ).homogenize (-1:Polynomial ℤ).natDegree ∣ (1:Polynomial ℤ).homogenize 7 := by
  apply homogeneous_factor_lift 1 (-1) 7 Polynomial.isPrimitive_one
    (by exact isUnit_neg_one.dvd) (by simp)
-- Without a nonzero scalar, homogeneity of the product conveys no degree.
example : (0:SourcePolynomial).IsHomogeneous 1 ∧
    (0:SourcePolynomial)=MvPolynomial.C (0:ℤ)*(1:SourcePolynomial) ∧
    ¬ (1:SourcePolynomial).IsHomogeneous 1 := by
  refine ⟨MvPolynomial.isHomogeneous_zero (Fin 2) ℤ 1,by simp,?_⟩
  intro hh
  have h := hh (d := 0) (by simp)
  norm_num [Finsupp.weight_apply] at h
-- A scalar factor2 cannot divide an affine primitive section.
example : ¬ Polynomial.C (2:ℤ) ∣ (Polynomial.X:Polynomial ℤ) := by
  intro hd
  have hu := Polynomial.monic_X.isPrimitive 2 hd
  rcases Int.isUnit_eq_one_or hu with h | h <;> norm_num at h

end
end P0365Subquarter
