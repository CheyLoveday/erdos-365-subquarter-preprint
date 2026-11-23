import PaperTargets.SmoothSources
import PaperTargets.RoundedProfiles

/-! CF11 actual-source real normalization and its downstream same-minor
consumer. Source: corrected v3 MATHEMATICS §4 and review/ANALYTIC A07–A08.
The divided-difference determinant estimate remains an explicit open step;
no target below assumes that estimate as an already proved theorem. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Direct free ratio s=b/d, or inverse free ratio t=v/u. -/
def realSourceCoordinate (inverse : Bool) (b d u v : ℕ) : ℝ :=
  if inverse then (v : ℝ) / u else (b : ℝ) / d

def realSourcePartner (inverse : Bool) (b d u v : ℕ) : ℝ :=
  realSourceCoordinate (!inverse) b d u v

def realChartExponent (inverse : Bool) : ℝ :=
  if inverse then 2 / 3 else 3 / 2

/-- The exact multiplicative source error, before normalization by the interval. -/
def realSourceError (inverse : Bool) (b d u v : ℕ) : ℝ :=
  realSourcePartner inverse b d u v /
    realSourceCoordinate inverse b d u v ^ realChartExponent inverse - 1

/-- The additive normalized error. It need not have bounded derivatives. -/
def realNormalizedError (inverse : Bool) (a : ℝ) (b d u v : ℕ) : ℝ :=
  (realSourceCoordinate inverse b d u v / a) ^ realChartExponent inverse *
    realSourceError inverse b d u v

def realNormalizedRow (inverse : Bool) (z β : ℝ) (j : Fin 8) : ℝ :=
  z ^ (j.val % 4) *
    (if j.val < 4 then 1 else z ^ realChartExponent inverse + β)

def realColumnScale (inverse : Bool) (a : ℝ) (j : Fin 8) : ℝ :=
  a ^ (j.val % 4) * (if j.val < 4 then 1 else a ^ realChartExponent inverse)

/-- Original positive sources, including n=8 and a kernel equal to one.
Direct errors are nonnegative, inverse errors nonpositive. -/
def CF11ActualRelativeErrors : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v →
    (0 ≤ realSourceError false b d u v ∧
      realSourceError false b d u v ≤ 1 / (n : ℝ)) ∧
    (-(1 / (n : ℝ)) ≤ realSourceError true b d u v ∧
      realSourceError true b d u v ≤ 0)

/-- Uniform beta bound on either compact normalized chart, without any
assumption about the coarse polynomial or the derivatives of beta. -/
def CF11ActualNormalizedError : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v →
    ∀ (inverse : Bool) (a X : ℝ), 0 < a → 0 < X → X ≤ (n : ℝ) →
      1 ≤ realSourceCoordinate inverse b d u v / a →
      realSourceCoordinate inverse b d u v / a ≤ 2 →
      |realNormalizedError inverse a b d u v| ≤ 4 / X

/-- Exact original integer rows after positive real row and column scaling. -/
def CF11ActualRowNormalization : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v →
    ∀ (inverse : Bool) (a : ℝ), 0 < a → ∀ j : Fin 8,
      (sourceIntegerRow inverse b d u v j : ℝ) =
        (sourceRowDenominator inverse d u : ℝ) * realColumnScale inverse a j *
          realNormalizedRow inverse (realSourceCoordinate inverse b d u v / a)
            (realNormalizedError inverse a b d u v) j

/-- All eight rows use the same interval scale; the determinant on the left
is the very same original integer minor as in CF10. -/
def CF11ActualMinorNormalization : Prop :=
  ∀ (n b d u v : Fin 8 → ℕ), (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
    ∀ (inverse : Bool) (a : ℝ), 0 < a →
      (Matrix.det (fun i j => sourceIntegerRow inverse (b i) (d i) (u i) (v i) j) : ℝ) =
        (∏ i : Fin 8, (sourceRowDenominator inverse (d i) (u i) : ℝ)) *
          (∏ j : Fin 8, realColumnScale inverse a j) *
          Matrix.det (fun i j => realNormalizedRow inverse
            (realSourceCoordinate inverse (b i) (d i) (u i) (v i) / a)
            (realNormalizedError inverse a (b i) (d i) (u i) (v i)) j)

/-- Both source scale cancellations, with no bounded-skew condition on B/E.
U^2 B^3=X is the nominal multiplier scale definition. -/
def CF11RealScaleCancellation : Prop :=
  ∀ B E U X : ℝ, 0 < B → 0 < E → U ^ 2 * B ^ 3 = X →
    (E ^ 3 * U) ^ 8 * (B / E) ^ 18 = X ^ 4 * (B * E) ^ 6 ∧
    (E * U ^ 3) ^ 8 * (B / E) ^ 22 = X ^ 12 / (B * E) ^ 14

/-- Once the still-open analytic estimate is supplied explicitly for the SAME
integer minor, rounded absorption and the proved CF10 force that minor to zero.
The fixed starting height precedes profiles, sources, primes and chart choice. -/
def CF11RoundedMinorVanishing : Prop :=
  ∀ δ C : ℝ, 0 < δ → 0 ≤ C → ∃ X₀ : ℝ, 1 ≤ X₀ ∧
    ∀ X ψ : ℝ, X₀ ≤ X → 0 ≤ ψ → ψ ≤ 2 / 3 →
      ∀ (F : SourcePolynomial) (p : ℕ) (n b d u v : Fin 8 → ℕ), Nat.Prime p →
        roundedScale X ψ δ ≤ (p : ℝ) →
        (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
        (∀ i, polynomialValue F (sourcePoint (b i) (d i) (u i) (v i)) = 0) →
        (∀ i, goodSourcePrime F (b i) (d i) (u i) (v i) p) →
        (∀ i, sourceReduction (b i) (d i) (u i) (v i) p =
          sourceReduction (b 0) (d 0) (u 0) (v 0) p) →
        ∀ inverse : Bool,
          |(Matrix.det (fun i j => sourceIntegerRow inverse
            (b i) (d i) (u i) (v i) j) : ℝ)| ≤
              C * (∑ k : Fin 5, roundedMixedTerm X ψ δ k) →
          Matrix.det (fun i j => sourceIntegerRow inverse
            (b i) (d i) (u i) (v i) j) = 0

end
end P0365Subquarter
