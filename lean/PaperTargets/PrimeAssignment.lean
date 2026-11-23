import PaperTargets.CanonicalSource
import PaperTargets.RoundedProfiles
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.ZMod.Basic

/-! CF07–08, corrected v3 MATHEMATICS §3 and addendum C, ANALYTIC A06.
Actual integral polynomials and canonical sources. Coarse-factor production,
singular-source counting, determinant valuation and final counting stay separate.
The coarser exponent H+2D+3 suffices for a bounded list; it is not the sharp
H+5(D+1)/6+1 estimate in the source. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

abbrev SourcePolynomial := MvPolynomial (Fin 2) ℤ

def sourcePoint (b d u v : ℕ) : Fin 2 → ℚ :=
  ![(b : ℚ) / d, (v : ℚ) / u]

def sourceReduction (b d u v p : ℕ) : Fin 2 → ZMod p :=
  ![(b : ZMod p) * (d : ZMod p)⁻¹, (v : ZMod p) * (u : ZMod p)⁻¹]

def polynomialValue {k : Type*} [CommRing k] (F : SourcePolynomial)
    (z : Fin 2 → k) : k := F.eval₂ (Int.castRingHom k) z

def nonsingularSource (F : SourcePolynomial) (b d u v : ℕ) : Prop :=
  polynomialValue F (sourcePoint b d u v) = 0 ∧
    ∃ i : Fin 2, polynomialValue (MvPolynomial.pderiv i F) (sourcePoint b d u v) ≠ 0

/-- Integral double homogenisation, not a supplied witness parameter. -/
def clearedValue (G : SourcePolynomial) (D b d u v : ℕ) : ℤ :=
  ∑ e ∈ G.support, G.coeff e * (b : ℤ) ^ e 0 * (d : ℤ) ^ (D - e 0) *
    (v : ℤ) ^ e 1 * (u : ℤ) ^ (D - e 1)

def clearedPartial (F : SourcePolynomial) (D b d u v : ℕ) (i : Fin 2) : ℤ :=
  clearedValue (MvPolynomial.pderiv i F) D b d u v

def selectedPartial (F : SourcePolynomial) (D b d u v : ℕ) : ℤ :=
  if clearedPartial F D b d u v 0 ≠ 0 then clearedPartial F D b d u v 0
  else clearedPartial F D b d u v 1

def sourceWitness (F : SourcePolynomial) (D b d u v : ℕ) : ℤ :=
  (d : ℤ) * u * selectedPartial F D b d u v

/-- Genuine good reduction at this source, with both denominator units. -/
def goodSourcePrime (F : SourcePolynomial) (b d u v p : ℕ) : Prop :=
  ¬ p ∣ d * u ∧ polynomialValue F (sourceReduction b d u v p) = 0 ∧
    ∃ i : Fin 2,
      polynomialValue (MvPolynomial.pderiv i F) (sourceReduction b d u v p) ≠ 0

def smoothResidues (F : SourcePolynomial) (p : ℕ) : Finset (Fin 2 → ZMod p) := by
  classical
  exact if hp : p = 0 then ∅ else
    letI : NeZero p := ⟨hp⟩
    Finset.univ.filter (fun z => polynomialValue F z = 0 ∧
      ∃ i : Fin 2, polynomialValue (MvPolynomial.pderiv i F) z ≠ 0)

def firstGoodPrime (F : SourcePolynomial) (b d u v : ℕ) (s : Finset ℕ) : ℕ := by
  classical
  exact if h : (s.filter (goodSourcePrime F b d u v)).Nonempty
    then (s.filter (goodSourcePrime F b d u v)).min' h else 0

def CF07ClearedIdentity : Prop :=
  ∀ (G : SourcePolynomial) (D b d u v : ℕ), G.totalDegree ≤ D → 0 < d → 0 < u →
    (clearedValue G D b d u v : ℚ) =
      (d : ℚ)^D * (u : ℚ)^D * polynomialValue G (sourcePoint b d u v)

/-- Uniformity is before F and all canonical sources, not just one witness.
The coefficient and degree hypotheses are the still-open CF04/05 consumer. -/
def CF07ActualSourceWitness : Prop :=
  ∀ (D : ℕ) (H C : ℝ), 0 ≤ H → 0 ≤ C →
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ F : SourcePolynomial, F.totalDegree ≤ D →
      (∀ e, |(F.coeff e : ℝ)| ≤ C * x ^ H) →
      ∀ n b d u v : ℕ, PairSource n b d u v → (n : ℝ) ≤ x →
        nonsingularSource F b d u v →
        sourceWitness F D b d u v ≠ 0 ∧
        |(sourceWitness F D b d u v : ℝ)| < x ^ (H + 2 * (D : ℝ) + 3) ∧
        ∀ p : ℕ, Nat.Prime p → ¬ goodSourcePrime F b d u v p →
          (p : ℤ) ∣ sourceWitness F D b d u v

def CF08BertrandList : Prop :=
  ∀ (L : ℕ) (R : ℝ), 1 ≤ R → ∃ s : Finset ℕ, s.card = L ∧
    ∀ p ∈ s, Nat.Prime p ∧ R ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2^(L+1) * R

/-- Arbitrary actual witness height and list; no globally common good prime. -/
def CF08FirstGoodAssignment : Prop :=
  ∀ (F : SourcePolynomial) (D n b d u v : ℕ) (s : Finset ℕ),
    PairSource n b d u v → nonsingularSource F b d u v → F.totalDegree ≤ D →
    (∀ p ∈ s, Nat.Prime p) →
    (sourceWitness F D b d u v).natAbs < ∏ p ∈ s, p →
    firstGoodPrime F b d u v s ∈ s ∧
      goodSourcePrime F b d u v (firstGoodPrime F b d u v s) ∧
      ∀ p ∈ s, goodSourcePrime F b d u v p → firstGoodPrime F b d u v s ≤ p

def CF08SmoothLabelBudget : Prop :=
  ∀ (F : SourcePolynomial) (D L : ℕ) (R : ℝ) (s : Finset ℕ),
    F.totalDegree ≤ D → s.card = L → 0 ≤ R →
    (∀ p ∈ s, Nat.Prime p ∧ (p : ℝ) ≤ 2^(L+1) * R) →
    (∑ p ∈ s, ((smoothResidues F p).card : ℝ)) ≤
      (L : ℝ) * D * 2^(L+1) * R

/-- Connected consumer: rounded scale, one list for every nonsingular source,
least good prime, actual smooth residue, and the linear-in-scale label budget. -/
def CF08RoundedSourceAssignment : Prop :=
  ∀ (D : ℕ) (H C δ : ℝ), 0 ≤ H → 0 ≤ C → 0 < δ →
    ∃ (L : ℕ) (x₀ : ℝ), 0 < L ∧ 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ ψ : ℝ, 0 ≤ ψ → ψ ≤ 2/3 →
      ∃ s : Finset ℕ, s.card = L ∧
        (∀ p ∈ s, Nat.Prime p ∧ roundedScale x ψ δ ≤ (p : ℝ) ∧
          (p : ℝ) ≤ 2^(L+1) * roundedScale x ψ δ) ∧
        (∀ F : SourcePolynomial, F.totalDegree ≤ D →
          (∀ e, |(F.coeff e : ℝ)| ≤ C * x ^ H) →
          ∀ n b d u v : ℕ, PairSource n b d u v → (n : ℝ) ≤ x →
            nonsingularSource F b d u v →
            firstGoodPrime F b d u v s ∈ s ∧
            goodSourcePrime F b d u v (firstGoodPrime F b d u v s) ∧
            sourceReduction b d u v (firstGoodPrime F b d u v s) ∈
              smoothResidues F (firstGoodPrime F b d u v s)) ∧
        (∀ F : SourcePolynomial, F.totalDegree ≤ D →
          (∑ p ∈ s, ((smoothResidues F p).card : ℝ)) ≤
            (L : ℝ) * D * 2^(L+1) * roundedScale x ψ δ)

end
end P0365Subquarter
