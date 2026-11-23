import PaperTargets.PrimeAssignment

/-! CF06 singular rational sources. The coarser degree-only bound2D^3 suffices
for the frozen O_D(1) inventory and does not assert the sharper Bezout constant.
Rational irreducible-factor production remains a separate coarse-cover task. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def rationalSourcePolynomial (F : SourcePolynomial) : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ) F

def singularRationalPoint (F : SourcePolynomial) (z : Fin 2 → ℚ) : Prop :=
  polynomialValue F z=0 ∧ ∀ i : Fin 2, polynomialValue (MvPolynomial.pderiv i F) z=0

/-- Actual rational singular points on a rationally irreducible plane curve;
no absolute irreducibility or supplied finite singular inventory is assumed. -/
def CF06SingularRationalPointCount : Prop :=
  ∀ (D : ℕ) (F : SourcePolynomial), F.totalDegree≤D →
    Irreducible (rationalSourcePolynomial F) → ∀ S : Finset (Fin 2 → ℚ),
      (∀ z ∈ S, singularRationalPoint F z) → S.card≤2*D^3

/-- Count original starts through actual canonical ratios; tuple allocations
and unproved source-count hypotheses do not enter the bound. -/
def CF06ActualSingularSourceCount : Prop :=
  ∀ (D : ℕ) (F : SourcePolynomial), F.totalDegree≤D →
    Irreducible (rationalSourcePolynomial F) → ∀ S : Finset ℕ,
      (∀ n ∈ S, ∃ b d u v : ℕ, PairSource n b d u v ∧
        singularRationalPoint F (sourcePoint b d u v)) → S.card≤2*D^3

end
end P0365Subquarter
