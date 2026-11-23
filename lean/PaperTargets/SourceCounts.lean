import PaperTargets.ThueLevels

/-! CF15 fixed-content aggregation and actual mixed-graph source counts.
Corrected ALGEBRA AR05–10: c*h=±g^ell, g divides the one full resultant.
The content c is fixed before all gcd/sign labels, and need not divide R. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- One fixed (g,sign) fiber has one reduced level because c is nonzero.
No enumeration of all divisors of g^ell is used in the low-factor branch. -/
def CF15FixedContentLevelBound : Prop :=
  StewartPrimitiveThue → ∀ (Q : SourcePolynomial) (c R g ell : ℕ) (σ : ℤ),
    binaryFactorDispatch Q → 0<c → R≠0 → g∣R → ell≤3 → (σ=1 ∨ σ= -1) →
    ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, primitiveBinaryPoint z ∧
        (c:ℤ)*MvPolynomial.eval z Q=σ*(g:ℤ)^ell) →
      S.card≤61616*(divisorCount R)^7

/-- There are at most 2*tau(R) gcd/sign labels, with c fixed throughout. -/
def CF15FixedContentDivisorCount : Prop :=
  StewartPrimitiveThue → ∀ (Q : SourcePolynomial) (c R ell : ℕ),
    binaryFactorDispatch Q → 0<c → R≠0 → ell≤3 →
    ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, primitiveBinaryPoint z ∧ ∃ (g : ℕ) (σ : ℤ),
        g∣R ∧ (σ=1 ∨ σ= -1) ∧ (c:ℤ)*MvPolynomial.eval z Q=σ*(g:ℤ)^ell) →
      S.card≤123232*(divisorCount R)^8

/-- Every point here must be an actual source parameter on the fixed graph.
Its primitive coordinates, signed level and evaluated-gcd divisibility are derived. -/
def CF15ActualGraphParameterCount : Prop :=
  StewartPrimitiveThue → ∀ (X : ℝ) (D A B : Polynomial ℤ), 32≤X →
    boundedGraphData X D A B → 1≤graphDegree A B → ∀ inverse : Bool,
    ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, ∃ n b d u v : ℕ, PairSource n b d u v ∧
        sourceGraphBranch inverse A B b d u v ∧ graphParameter inverse b d u v=z) →
      S.card≤123232*(divisorCount (fullGraphResultant A B).natAbs)^8

/-- On a fixed graph branch the parameter determines both rational ratios,
and hence the original start. Positivity and primitivity come from PairSource. -/
def CF15GraphParameterInjection : Prop :=
  ∀ (inverse : Bool) (A B : Polynomial ℤ) (n m b d u v b' d' u' v' : ℕ),
    PairSource n b d u v → PairSource m b' d' u' v' →
    sourceGraphBranch inverse A B b d u v → sourceGraphBranch inverse A B b' d' u' v' →
    graphParameter inverse b d u v=graphParameter inverse b' d' u' v' → n=m

/-- Count original starts, choosing actual canonical sources and deriving
injectivity of their parameter image. No source-count conclusion is assumed. -/
def CF15ActualGraphSourceCount : Prop :=
  StewartPrimitiveThue → ∀ (X : ℝ) (D A B : Polynomial ℤ), 32≤X →
    boundedGraphData X D A B → 1≤graphDegree A B → ∀ inverse : Bool,
    ∀ S : Finset ℕ,
      (∀ n ∈ S, ∃ b d u v : ℕ, PairSource n b d u v ∧ sourceGraphBranch inverse A B b d u v) →
      S.card≤123232*(divisorCount (fullGraphResultant A B).natAbs)^8

/-- The constant precedes X and every actual graph, chart and finite source
class. The precise external Thue input remains explicit. -/
def CF15ActualGraphSourceSubpower : Prop :=
  StewartPrimitiveThue → ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ (X : ℝ) (D A B : Polynomial ℤ), 32≤X → boundedGraphData X D A B →
      1≤graphDegree A B → ∀ inverse : Bool, ∀ S : Finset ℕ,
        (∀ n ∈ S, ∃ b d u v : ℕ, PairSource n b d u v ∧ sourceGraphBranch inverse A B b d u v) →
        (S.card:ℝ)≤C*X^ε

end
end P0365Subquarter
