import PaperProofs.FactorDispatch

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print binaryFactorDispatch
#print CF15PrimitiveIrreducibleFactor
#print CF15DistinctLowFactorPair
#print CF15InfinityLowFactorPair
#print CF15PrimitiveFactorDispatch
#print CF15ActualGraphFactorDispatch
#check (primitive_irreducible_factor : CF15PrimitiveIrreducibleFactor)
#check (distinct_low_factor_pair : CF15DistinctLowFactorPair)
#check (infinity_low_factor_pair : CF15InfinityLowFactorPair)
#check (primitive_factor_dispatch : CF15PrimitiveFactorDispatch)
#check (actual_graph_factor_dispatch : CF15ActualGraphFactorDispatch)
#print axioms primitive_irreducible_factor
#print axioms distinct_low_factor_pair
#print axioms infinity_low_factor_pair
#print axioms primitive_factor_dispatch
#print axioms actual_graph_factor_dispatch
set_option pp.all false

example : CF15PrimitiveIrreducibleFactor := by
  intro P f hp hi hf
  exact primitive_irreducible_factor P f hp hi hf
example : CF15DistinctLowFactorPair := by
  intro f g hf hg hif hig hna hdf hdg
  exact distinct_low_factor_pair f g hf hg hif hig hna hdf hdg
example : CF15InfinityLowFactorPair := by
  intro f hd
  exact infinity_low_factor_pair f hd
example : CF15PrimitiveFactorDispatch := by
  intro Q N hh hc hN hn
  exact primitive_factor_dispatch Q N hh hc hN hn
example : CF15ActualGraphFactorDispatch := by
  intro X D A B hX hg hr inverse
  exact actual_graph_factor_dispatch X D A B hX hg hr inverse

-- The infinity comparison needs full degree, not content one: even2X works.
example : lowBinaryFactorPair (MvPolynomial.X 1)
    ((Polynomial.C 2*Polynomial.X : Polynomial ℤ).homogenize
      (Polynomial.C 2*Polynomial.X : Polynomial ℤ).natDegree) := by
  apply infinity_low_factor_pair
  left
  rw [Polynomial.natDegree_C_mul (by decide : (2:ℤ) ≠ 0),Polynomial.natDegree_X]

-- Repeated infinity factors are retained and can join one fixed affine factor.
example : binaryFactorDispatch (MvPolynomial.X 0*MvPolynomial.X 1^3) := by
  left
  have hp : lowBinaryFactorPair (MvPolynomial.X 1) (MvPolynomial.X 0) := by
    simpa using infinity_low_factor_pair (Polynomial.X:Polynomial ℤ) (Or.inl Polynomial.natDegree_X)
  refine ⟨MvPolynomial.X 1,MvPolynomial.X 0,hp,?_,dvd_mul_right _ _⟩
  exact (dvd_pow_self (MvPolynomial.X 1 : SourcePolynomial) (by decide : (3:ℕ) ≠ 0)).trans (dvd_mul_left _ _)

-- A single repeated small factor is exactly the excluded alternative; both
-- scalar signs and exponent0 are visible rather than silently discarded.
example : ¬ (∀ (G : SourcePolynomial) (d k : ℕ) (a : ℤ), G.IsHomogeneous d →
    (d=1 ∨ d=2) → (MvPolynomial.X 0:SourcePolynomial)^2 ≠ MvPolynomial.C a*G^k) := by
  intro h
  exact h (MvPolynomial.X 0) 1 2 1 (MvPolynomial.isHomogeneous_X ℤ 0) (Or.inl rfl) (by simp)
example : ¬ (∀ (G : SourcePolynomial) (d k : ℕ) (a : ℤ), G.IsHomogeneous d →
    (d=1 ∨ d=2) → -(MvPolynomial.X 1:SourcePolynomial)^7 ≠ MvPolynomial.C a*G^k) := by
  intro h
  exact h (MvPolynomial.X 1) 1 7 (-1) (MvPolynomial.isHomogeneous_X ℤ 1) (Or.inl rfl) (by simp)
example : ¬ (∀ (G : SourcePolynomial) (d k : ℕ) (a : ℤ), G.IsHomogeneous d →
    (d=1 ∨ d=2) → (1:SourcePolynomial) ≠ MvPolynomial.C a*G^k) := by
  intro h
  exact h (MvPolynomial.X 1) 1 0 1 (MvPolynomial.isHomogeneous_X ℤ 1) (Or.inl rfl) (by simp)

end
end P0365Subquarter
