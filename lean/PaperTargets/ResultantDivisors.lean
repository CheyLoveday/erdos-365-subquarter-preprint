import PaperTargets.LowFactorLevels
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! CF15 divisor/prime-support arithmetic, ALGEBRA AR10. The integer polynomial
content never divides the resultant here. Actual levels divide g^ell, g divides
|R|, ell≤3. The precise Thue/factor selection and subpower growth remain later. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def divisorCount (n : ℕ) : ℕ := n.divisors.card

def primeSupportCount (n : ℕ) : ℕ := n.primeFactors.card

def thueDivisorInventory (R ℓ d : ℕ) : ℕ :=
  ∑ g ∈ R.divisors, ∑ h ∈ (g^ℓ).divisors, d^(primeSupportCount h)

def CF15DivisorCardMul : Prop :=
  ∀ m n : ℕ, divisorCount (m*n) ≤ divisorCount m*divisorCount n

def CF15DivisorCardPow : Prop :=
  ∀ n k : ℕ, divisorCount (n^k) ≤ (divisorCount n)^k

def CF15DivisorCardDvd : Prop :=
  ∀ m n : ℕ, n ≠ 0 → m ∣ n → divisorCount m ≤ divisorCount n

/-- Prime support transfers through a power-divisor, even though the level
itself need not divide R. Exponent zero and R=1 are retained. -/
def CF15PrimeSupportLevel : Prop :=
  ∀ R g h ℓ : ℕ, R ≠ 0 → g ∣ R → h ∣ g^ℓ →
    g ≠ 0 ∧ h ≠ 0 ∧ h.primeFactors ⊆ R.primeFactors

def CF15SupportDivisorLower : Prop :=
  ∀ R : ℕ, R ≠ 0 → 2^(primeSupportCount R) ≤ divisorCount R

/-- Derive both charges used for actual admitted levels: tau(h)≤tau(R)^3
and d^omega(h)≤tau(R)^4 for degrees at most11, hence the low-factor budget. -/
def CF15ResultantLevelCharges : Prop :=
  ∀ R g h ℓ : ℕ, R ≠ 0 → g ∣ R → h ∣ g^ℓ → ℓ ≤ 3 →
    divisorCount h ≤ (divisorCount R)^3 ∧
    (∀ d : ℕ, d ≤ 11 → d^(primeSupportCount h) ≤ (divisorCount R)^4) ∧
    16*(divisorCount h)^2 ≤ 16*(divisorCount R)^6

/-- Sum the actual positive factor-level divisor labels at all evaluated gcd
labels. Signed levels and the external degree constant cost a fixed multiplier
later. There is no assumed source-count or label-budget premise. -/
def CF15ThueDivisorInventory : Prop :=
  ∀ R ℓ d : ℕ, R ≠ 0 → ℓ ≤ 3 → d ≤ 11 →
    thueDivisorInventory R ℓ d ≤ (divisorCount R)^8

/-- The integer is the one ACTUAL full homogeneous resultant, uniformly fixed
before divisor/degree labels. Nonvanishing and polynomial height are derived
from the proved bounded graph, not supplied as resultant hypotheses. -/
def CF15ActualGraphDivisorInventory : Prop :=
  ∀ (X : ℝ) (D A B : Polynomial ℤ), 32 ≤ X → boundedGraphData X D A B →
    1 ≤ graphDegree A B →
      let R := (fullGraphResultant A B).natAbs
      R ≠ 0 ∧ (R:ℝ) ≤ 720*X^(90:ℕ) ∧
        ∀ ℓ d : ℕ, ℓ ≤ 3 → d ≤ 11 → thueDivisorInventory R ℓ d ≤ (divisorCount R)^8

end
end P0365Subquarter
