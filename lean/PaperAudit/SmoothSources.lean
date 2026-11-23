import PaperProofs.SmoothSources

namespace P0365Subquarter
open MvPolynomial
set_option pp.all true

#print SmoothRing
#print smoothReduction
#print otherCoordinate
#print sourceLift
#print chartMonomial
#print sourceIntegerRow
#print sourceRowDenominator
#print CF09FiniteImplicitPolynomial
#print CF09ActualSourceImplicitPolynomial
#print CF10PolynomialEvaluationDeterminant
#print CF10SourceRowIdentity
#print CF10ActualSourceDeterminants
#check (finite_implicit_polynomial : CF09FiniteImplicitPolynomial)
#check (actual_source_implicit_polynomial : CF09ActualSourceImplicitPolynomial)
#check (polynomial_evaluation_determinant : CF10PolynomialEvaluationDeterminant)
#check (source_row_identity : CF10SourceRowIdentity)
#check (actual_source_determinants : CF10ActualSourceDeterminants)
#print axioms finite_implicit_polynomial
#print axioms actual_source_implicit_polynomial
#print axioms polynomial_evaluation_determinant
#print axioms source_row_identity
#print axioms actual_source_determinants

set_option pp.all false

-- Exact original R31 and R13 rows, all eight columns and both denominators.
example (b d u v : ℕ) : (fun j => sourceIntegerRow false b d u v j) =
    ![(d:ℤ)^3*u, (b:ℤ)*d^2*u, (b:ℤ)^2*d*u, (b:ℤ)^3*u,
      (d:ℤ)^3*v, (b:ℤ)*d^2*v, (b:ℤ)^2*d*v, (b:ℤ)^3*v] := by
  ext j; fin_cases j <;> norm_num [sourceIntegerRow]
example (b d u v : ℕ) : (fun j => sourceIntegerRow true b d u v j) =
    ![(d:ℤ)*u^3, (d:ℤ)*u^2*v, (d:ℤ)*u*v^2, (d:ℤ)*v^3,
      (b:ℤ)*u^3, (b:ℤ)*u^2*v, (b:ℤ)*u*v^2, (b:ℤ)*v^3] := by
  ext j; fin_cases j <;> norm_num [sourceIntegerRow] <;> ring

-- The first partial may vanish: F=t is smooth through the second partial.
example (p : ℕ) (hp : p.Prime) :
    ∃ (i : Fin 2) (q : Polynomial (SmoothRing p)),
      smoothReduction p (polynomialValue (pderiv i (X 1)) (fun _ => (0:SmoothRing p))) ≠ 0 ∧
      q.eval 0 = 0 ∧ ∀ z : Fin 2 → SmoothRing p, polynomialValue (X 1) z = 0 →
        (∀ j, smoothReduction p (z j) = 0) →
        z i = q.eval (z (otherCoordinate i)) := by
  have hn : (0 : ZMod p) ≠ 1 := by
    let : Fact p.Prime := ⟨hp⟩
    exact zero_ne_one
  obtain ⟨i,q,hi,hq0,hq⟩ := finite_implicit_polynomial (X 1) p hp (fun _ => 0)
    (by simp [polynomialValue])
    ⟨1, by simpa [polynomialValue, pderiv_X_self] using hn.symm⟩
  refine ⟨i,q,hi,hq0,?_⟩
  intro z hz hres
  simpa using hq z hz (by simpa using hres)

-- A singular polynomial has no unit partial at its singular origin.
example (p : ℕ) : ¬ ∃ i : Fin 2,
    smoothReduction p (polynomialValue (pderiv i ((X 0)^2)) (fun _ => (0:SmoothRing p))) ≠ 0 := by
  rintro ⟨i,hi⟩
  simp [polynomialValue] at hi

-- Actual canonical 8/9 centre, with no artificial row or population premise.
example : ∃ (i : Fin 2) (q : Polynomial (SmoothRing 2)), q.eval 0 = 0 ∧
    ∀ n b d u v : ℕ, PairSource n b d u v →
      polynomialValue (X 0 - C 2) (sourcePoint b d u v) = 0 →
      goodSourcePrime (X 0 - C 2) b d u v 2 →
      sourceReduction b d u v 2 = sourceReduction 2 1 1 3 2 →
      sourceLift b d u v 2 i = sourceLift 2 1 1 3 2 i +
        q.eval (sourceLift b d u v 2 (otherCoordinate i) - sourceLift 2 1 1 3 2 (otherCoordinate i)) := by
  apply actual_source_implicit_polynomial (X 0 - C 2) 2 8 2 1 1 3 (by decide)
  · norm_num [PairSource]; exact Nat.prime_two.squarefree
  · norm_num [polynomialValue, sourcePoint, eval₂_sub]
  · refine ⟨by decide, ?_, 0, ?_⟩
    · norm_num [polynomialValue, sourceReduction, eval₂_sub]
    · simp only [map_sub, pderiv_X_self, pderiv_C]
      norm_num [polynomialValue]

-- End-to-end original integer minors at a genuine, repeated canonical source.
example (inverse : Bool) : (2:ℤ)^28 ∣ Matrix.det
    (fun _i : Fin 8 => sourceIntegerRow inverse 2 1 1 3) := by
  apply actual_source_determinants (X 0 - C 2) 2
    (fun _ => 8) (fun _ => 2) (fun _ => 1) (fun _ => 1) (fun _ => 3) (by decide)
  · intro i; norm_num [PairSource]; exact Nat.prime_two.squarefree
  · intro i; norm_num [polynomialValue, sourcePoint, eval₂_sub]
  · intro i; refine ⟨by decide, ?_, 0, ?_⟩
    · norm_num [polynomialValue, sourceReduction, eval₂_sub]
    · simp only [map_sub, pderiv_X_self, pderiv_C]
      norm_num [polynomialValue]
  · intro i; rfl

-- Nilpotent and duplicate-node cases are included in the universal determinant lemma.
example (p : ℕ) (f : Fin 8 → Polynomial (SmoothRing p)) :
    Matrix.det (fun _i : Fin 8 => fun j => (f j).eval 0) = 0 := by
  apply polynomial_evaluation_determinant (SmoothRing p) (p : SmoothRing p)
  · rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  · intro i; exact dvd_zero _

-- The exponent 28 cannot generally be raised to 29 even for integral series.
-- Vandermonde on z_i=11*i has exactly the 28 prime factors when p=11.
example : ¬ (11:ℤ)^29 ∣ (Matrix.vandermonde (fun i : Fin 8 => (11:ℤ)*i.val)).det := by
  rw [Matrix.det_vandermonde]
  decide

end P0365Subquarter
