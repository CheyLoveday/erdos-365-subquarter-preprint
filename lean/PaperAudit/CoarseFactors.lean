import PaperProofs.CoarseFactors

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print coarseKronecker
#print CF05KroneckerControl
#print CF05IntegerCoarseFactorHeight
#print CF05UniformCoarseFactorHeight
#check (kronecker_control : CF05KroneckerControl)
#check (integer_coarse_factor_height : CF05IntegerCoarseFactorHeight)
#check (uniform_coarse_factor_height : CF05UniformCoarseFactorHeight)
#print axioms kronecker_control
#print axioms integer_coarse_factor_height
#print axioms uniform_coarse_factor_height
set_option pp.all false

example : CF05KroneckerControl := by
  intro D F hD
  exact kronecker_control D F hD
example : CF05IntegerCoarseFactorHeight := by
  intro D H hH F hF hD hcoeff A hdiv
  exact integer_coarse_factor_height D H hH F hF hD hcoeff A hdiv
example : CF05UniformCoarseFactorHeight := by
  intro D H C hH hC
  exact uniform_coarse_factor_height D H C hH hC

-- Degree zero has only constant monomials, despite the base being one.
example : coarseKronecker 0 (MvPolynomial.C (7:ℤ))=Polynomial.C 7 := by
  simp [coarseKronecker]
-- Degree-one labels are distinct and preserve both coefficients.
example : coarseKronecker 1 ((MvPolynomial.X 0+MvPolynomial.X 1):SourcePolynomial)=
    Polynomial.X+Polynomial.X^2 := by
  simp [coarseKronecker]
-- Outside the degree ball the encoding can collide; its hypothesis is essential.
example : coarseKronecker 1 (((MvPolynomial.X 0)^2-MvPolynomial.X 1):SourcePolynomial)=0 := by
  simp [coarseKronecker]
example : (((MvPolynomial.X 0)^2-MvPolynomial.X 1):SourcePolynomial).coeff
    (Finsupp.single 0 2)=1 := by
  norm_num [MvPolynomial.coeff_sub,MvPolynomial.coeff_X_pow,MvPolynomial.coeff_X,
    Finsupp.single_eq_single_iff]
-- Nonzero constant factors obey the exact degree-zero height bound.
example (H : ℝ) (hH : 1≤H) (F A : SourcePolynomial) (hF : F≠0)
    (hD : F.totalDegree=0) (hcoeff : ∀ e, |(F.coeff e:ℝ)|≤H) (hdiv : A∣F) :
    A.totalDegree=0 ∧ ∀ e, |(A.coeff e:ℝ)|≤H := by
  obtain ⟨ha,hb⟩ := integer_coarse_factor_height 0 H hH F hF hD.le hcoeff A hdiv
  exact ⟨by omega,by simpa using hb⟩
-- Zero coefficient height forces the zero polynomial, so C0 is handled faithfully.
example (F : SourcePolynomial) (hcoeff : ∀ e, |(F.coeff e:ℝ)|≤0) : F=0 := by
  ext e
  change F.coeff e=0
  have hz : (F.coeff e:ℝ)=0 := abs_eq_zero.mp (le_antisymm (hcoeff e) (abs_nonneg _))
  exact_mod_cast hz

end
end P0365Subquarter
