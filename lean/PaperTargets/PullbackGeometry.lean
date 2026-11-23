import PaperTargets.SourceRecovery
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! First CF14 stage: exact mixed-graph pullback degree and both axis orders.
The adopted contract is ALGEBRA AR09. Pure non-axis factor exclusion by proved
polynomial abc is the next stage; degree-zero graphs remain CF13 rulings. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def graphPullbackDegree (inverse : Bool) (r : ℕ) : ℕ :=
  if inverse then 3*r+2 else 2*r+3

def affineGraphPullback (inverse : Bool) (A B : Polynomial ℤ) : Polynomial ℤ :=
  if inverse then Polynomial.X^2*B^3-A^3 else A^2-Polynomial.X^3*B^2

def pullbackAxisGeometry (inverse : Bool) (A B : Polynomial ℤ) : Prop :=
  let N := graphPullbackDegree inverse (graphDegree A B)
  let F := affineGraphPullback inverse A B
  graphPullback inverse A B ≠ 0 ∧
    (graphPullback inverse A B).IsHomogeneous N ∧
    (graphPullback inverse A B).totalDegree = N ∧
    F.natTrailingDegree ≤ (if inverse then 2 else 3) ∧
    N-F.natDegree ≤ (if inverse then 2 else 3) ∧
    ∀ c : ℤ, ∀ i : Fin 2,
      graphPullback inverse A B ≠ MvPolynomial.C c*MvPolynomial.X i^N

/-- Rational coprimality and actual positive maximum degree exclude either
zero section. Integer contents need not be units. -/
def CF14MixedSectionsNonzero : Prop :=
  ∀ A B : Polynomial ℤ, 1 ≤ graphDegree A B →
    IsCoprime (rationalPolynomial A) (rationalPolynomial B) → A ≠ 0 ∧ B ≠ 0

/-- Degree parity in the direct chart and residues modulo three in the inverse
chart prevent cancellation of the two leading terms. -/
def CF14AffinePullbackDegrees : Prop :=
  ∀ A B : Polynomial ℤ, A ≠ 0 → B ≠ 0 →
    ∀ inverse : Bool, affineGraphPullback inverse A B ≠ 0 ∧
      (affineGraphPullback inverse A B).natDegree =
        (if inverse then max (2+3*B.natDegree) (3*A.natDegree)
         else max (2*A.natDegree) (3+2*B.natDegree))

/-- The polynomial used at actual source levels is exactly the homogenization
at N, even when its affine degree is smaller than N. -/
def CF14HomogeneousPullback : Prop :=
  ∀ (inverse : Bool) (A B : Polynomial ℤ),
    let N := graphPullbackDegree inverse (graphDegree A B)
    (affineGraphPullback inverse A B).natDegree ≤ N ∧
    (affineGraphPullback inverse A B).homogenize N = graphPullback inverse A B ∧
    (graphPullback inverse A B).IsHomogeneous N ∧
    (A ≠ 0 → B ≠ 0 → graphPullback inverse A B ≠ 0 ∧
      (graphPullback inverse A B).totalDegree = N)

/-- Exact x-order (the affine trailing degree) and y-order (N minus affine
degree). Positive direct orders are at most three; inverse orders are zero or
two. The two original sections may contain an axis factor individually. -/
def CF14AxisOrders : Prop :=
  ∀ A B : Polynomial ℤ, 1 ≤ graphDegree A B →
    IsCoprime (rationalPolynomial A) (rationalPolynomial B) →
    ∀ inverse : Bool,
      (affineGraphPullback inverse A B).natTrailingDegree =
        (if inverse then min (2+3*B.natTrailingDegree) (3*A.natTrailingDegree)
         else min (2*A.natTrailingDegree) (3+2*B.natTrailingDegree)) ∧
      (affineGraphPullback inverse A B).natTrailingDegree ≤ (if inverse then 2 else 3) ∧
      graphPullbackDegree inverse (graphDegree A B)-
        (affineGraphPullback inverse A B).natDegree ≤ (if inverse then 2 else 3) ∧
      (inverse = true →
        ((affineGraphPullback inverse A B).natTrailingDegree = 0 ∨
          (affineGraphPullback inverse A B).natTrailingDegree = 2) ∧
        (graphPullbackDegree inverse (graphDegree A B)-
          (affineGraphPullback inverse A B).natDegree = 0 ∨
        graphPullbackDegree inverse (graphDegree A B)-
          (affineGraphPullback inverse A B).natDegree = 2))

def CF14AxisPowerExclusion : Prop :=
  ∀ A B : Polynomial ℤ, 1 ≤ graphDegree A B →
    IsCoprime (rationalPolynomial A) (rationalPolynomial B) →
    ∀ (inverse : Bool) (c : ℤ) (i : Fin 2),
      graphPullback inverse A B ≠ MvPolynomial.C c*
        MvPolynomial.X i^(graphPullbackDegree inverse (graphDegree A B))

/-- Connect the exact geometry to each bounded actual CF13 mixed graph. This
is uniform before all sources and retains both charts, integer contents and
all r=1,2,3. The non-axis pure-power and counting conclusions are not premises. -/
def CF14ActualMixedPullback : Prop :=
  ∀ (X : ℝ) (D A B : Polynomial ℤ), 32 ≤ X → boundedGraphData X D A B →
    1 ≤ graphDegree A B → ∀ inverse : Bool,
      5 ≤ graphPullbackDegree inverse (graphDegree A B) ∧
      graphPullbackDegree inverse (graphDegree A B) ≤ (if inverse then 11 else 9) ∧
      pullbackAxisGeometry inverse A B

end
end P0365Subquarter
