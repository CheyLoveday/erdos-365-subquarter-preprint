import PaperTargets.PrimeAssignment

/-! CF05 actual primitive rational irreducible-factor inventory. Constant
integer-content factors are excluded by positive degree, not counted as curves.
No factor list or source-cover conclusion is assumed. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def coarseRationalPolynomial (F : SourcePolynomial) : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ) F

def coarseIntegralPrimitive (F : SourcePolynomial) : Prop :=
  ∀ a : ℤ, (∀ e, a∣F.coeff e) → IsUnit a

/-- Produce boundedly many actual integral divisors which are primitive and
irreducible over Q, covering every rational zero of the nonzero coarse curve. -/
def CF05PrimitiveFactorInventory : Prop :=
  ∀ (D : ℕ) (F : SourcePolynomial), F≠0 → F.totalDegree≤D →
    ∃ s : Finset SourcePolynomial, s.card≤D ∧
      (∀ A ∈ s, A∣F ∧ 0<A.totalDegree ∧ A.totalDegree≤D ∧
        Irreducible A ∧ coarseIntegralPrimitive A ∧ Irreducible (coarseRationalPolynomial A)) ∧
      (∀ z : Fin 2 → ℚ, polynomialValue F z=0 → ∃ A ∈ s, polynomialValue A z=0)

/-- One polynomial-height constant precedes the coarse polynomial and all
selected factors. Every original rational source is covered by the actual list. -/
def CF05UniformPrimitiveFactorCover : Prop :=
  ∀ (D : ℕ) (H C : ℝ), 0≤H → 0≤C → ∃ K : ℝ, 0<K ∧
    ∀ X : ℝ, 1≤X → ∀ F : SourcePolynomial, F≠0 → F.totalDegree≤D →
      (∀ e, |(F.coeff e:ℝ)|≤C*X^H) →
      ∃ s : Finset SourcePolynomial, s.card≤D ∧
        (∀ A ∈ s, A∣F ∧ 0<A.totalDegree ∧ A.totalDegree≤D ∧
          coarseIntegralPrimitive A ∧ Irreducible (coarseRationalPolynomial A) ∧
          ∀ e, |(A.coeff e:ℝ)|≤K*X^H) ∧
        (∀ z : Fin 2 → ℚ, polynomialValue F z=0 → ∃ A ∈ s, polynomialValue A z=0)

end
end P0365Subquarter
