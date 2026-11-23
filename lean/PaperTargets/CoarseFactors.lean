import PaperTargets.PrimeAssignment
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! CF05 integral coarse-factor height. A bounded-degree Kronecker substitution
reduces coefficient control to the already proved integer univariate factor
height theorem. Coarse-cover existence and irreducible-factor inventory remain
separate. The degree-dependent constant need not be sharp. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def coarseKronecker (D : ℕ) (F : SourcePolynomial) : Polynomial ℤ :=
  F.eval₂ Polynomial.C ![Polynomial.X,Polynomial.X^(D+1)]

/-- Total degree <=D gives unique base(D+1) monomial labels, degree <=D(D+1),
and nonvanishing of the actual substituted polynomial. -/
def CF05KroneckerControl : Prop :=
  ∀ (D : ℕ) (F : SourcePolynomial), F.totalDegree≤D →
    (∀ e : Fin 2 →₀ ℕ, e 0+e 1≤D →
      (coarseKronecker D F).coeff (e 0+(D+1)*e 1)=F.coeff e) ∧
    (coarseKronecker D F).natDegree≤D*(D+1) ∧
    (F≠0 → coarseKronecker D F≠0)

/-- The divisor's degree and every coefficient are derived, not supplied as
factor hypotheses. Nonzero F is essential; degree zero is included. -/
def CF05IntegerCoarseFactorHeight : Prop :=
  ∀ (D : ℕ) (H : ℝ), 1≤H → ∀ F : SourcePolynomial, F≠0 →
    F.totalDegree≤D → (∀ e, |(F.coeff e:ℝ)|≤H) →
    ∀ A : SourcePolynomial, A∣F → A.totalDegree≤D ∧
      ∀ e, |(A.coeff e:ℝ)|≤(2:ℝ)^(D*(D+1))*(D*(D+1)+1)*H

/-- Preserve one polynomial-height exponent uniformly for every actual
integral factor, with the coefficient constant chosen before X/F/A. -/
def CF05UniformCoarseFactorHeight : Prop :=
  ∀ (D : ℕ) (H C : ℝ), 0≤H → 0≤C → ∃ K : ℝ, 0<K ∧
    ∀ X : ℝ, 1≤X → ∀ F : SourcePolynomial, F≠0 → F.totalDegree≤D →
      (∀ e, |(F.coeff e:ℝ)|≤C*X^H) → ∀ A : SourcePolynomial, A∣F →
        A.totalDegree≤D ∧ ∀ e, |(A.coeff e:ℝ)|≤K*X^H

end
end P0365Subquarter
