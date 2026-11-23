import PaperProofs.SingularCounts

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
set_option pp.all true
#print CF06SingularRationalPointCount
#print CF06ActualSingularSourceCount
#check (singular_rational_point_count : CF06SingularRationalPointCount)
#check (actual_singular_source_count : CF06ActualSingularSourceCount)
#print axioms singular_rational_point_count
#print axioms actual_singular_source_count
set_option pp.all false

example : CF06SingularRationalPointCount := by
  intro D F hD hir S hS
  exact singular_rational_point_count D F hD hir S hS
example : CF06ActualSingularSourceCount := by
  intro D F hD hir S hS
  exact actual_singular_source_count D F hD hir S hS

-- Degree-zero specialization gives an empty original-source population.
example (F : SourcePolynomial) (hD : F.totalDegree≤0)
    (hir : Irreducible (rationalSourcePolynomial F)) (S : Finset ℕ)
    (hS : ∀ n ∈ S, ∃ b d u v : ℕ, PairSource n b d u v ∧
      singularRationalPoint F (sourcePoint b d u v)) : S=∅ := by
  apply Finset.card_eq_zero.mp
  have h := actual_singular_source_count 0 F hD hir S hS
  simpa using h

-- Nonzero constants have no zero, hence no singular point.
example (z : Fin 2 → ℚ) :
    ¬singularRationalPoint (MvPolynomial.C (6:ℤ)) z := by
  intro h
  norm_num [singularRationalPoint,polynomialValue] at h

-- The vertical coordinate line is covered by the nonzero-fiber argument.
example (z : Fin 2 → ℚ) :
    ¬singularRationalPoint (MvPolynomial.X 0-MvPolynomial.C (1:ℤ)) z := by
  intro h
  have hh := h.2 0
  norm_num [polynomialValue] at hh

-- A rational singular point need not have a real branch through it.
-- This control asserts singularity, not rational irreducibility.
example : singularRationalPoint
    ((MvPolynomial.X 0:SourcePolynomial)^2+MvPolynomial.X 1^2) (fun _ => 0) := by
  constructor
  · simp [polynomialValue]
  · intro i
    fin_cases i <;> simp [polynomialValue]

-- Padding both actual degrees can destroy a nonzero resultant.
example : Polynomial.resultant (Polynomial.X+1 : Polynomial ℚ) 1 2 1=0 := by
  simp [Polynomial.coeff_X,Polynomial.coeff_one]
example : Polynomial.resultant (Polynomial.X+1 : Polynomial ℚ) 1 1 0=1 := by
  simp

-- At s=0 this cubic in t drops to the nonzero fiber t^2.
-- The origin is singular, so projection must survive this degree drop.
example : singularRationalPoint
    ((MvPolynomial.X 0:SourcePolynomial)*MvPolynomial.X 1^3+
      MvPolynomial.X 1^2+MvPolynomial.X 0^2) (fun _ => 0) := by
  constructor
  · simp [polynomialValue]
  · intro i
    fin_cases i <;> simp [polynomialValue]
example : ((Polynomial.C Polynomial.X*Polynomial.X^3+Polynomial.X^2+
    Polynomial.C (Polynomial.X^2) : Polynomial (Polynomial ℚ)).map
      (Polynomial.evalRingHom 0))=Polynomial.X^2 := by
  simp

end
end P0365Subquarter
