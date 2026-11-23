import PaperTargets.HomogeneousResultants
import Mathlib.Algebra.GCDMonoid.Finset

/-! Final adopted CF13 stage: actual signed source recovery and the corrected
admitted-level content statement, ALGEBRA AR05/AR08 and MATHEMATICS §6.
Polynomial content divides the admitted level; no content-divides-resultant
claim is made. Both inverse signs and all earlier ruling branches remain. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def binaryContent (H : SourcePolynomial) : ℕ := H.support.gcd (fun e => (H.coeff e).natAbs)

def binaryPrimitivePart (H : SourcePolynomial) : SourcePolynomial :=
  ∑ e ∈ H.support, MvPolynomial.monomial e (H.coeff e/(binaryContent H : ℤ))

def graphParameter (inverse : Bool) (b d u v : ℕ) : Fin 2 → ℤ :=
  if inverse then ![(v:ℤ),u] else ![(b:ℤ),d]

def graphPartner (inverse : Bool) (b d u v : ℕ) : Fin 2 → ℕ :=
  if inverse then ![b,d] else ![v,u]

def graphLevelPower (inverse : Bool) : ℕ := if inverse then 3 else 2

def graphPullback (inverse : Bool) (A B : Polynomial ℤ) : SourcePolynomial :=
  let r := graphDegree A B
  if inverse then MvPolynomial.X 0^2*(B.homogenize r)^3-MvPolynomial.X 1^2*(A.homogenize r)^3
  else MvPolynomial.X 1^3*(A.homogenize r)^2-MvPolynomial.X 0^3*(B.homogenize r)^2

def sourceGraphGCD (inverse : Bool) (A B : Polynomial ℤ) (b d u v : ℕ) : ℕ :=
  let xy := graphParameter inverse b d u v
  Int.gcd (homogeneousGraphValue A (graphDegree A B) (xy 0) (xy 1))
    (homogeneousGraphValue B (graphDegree A B) (xy 0) (xy 1))

def sourceGraphBranch (inverse : Bool) (A B : Polynomial ℤ) (b d u v : ℕ) : Prop :=
  let z := sourcePoint b d u v
  let s := z (if inverse then 1 else 0)
  let t := z (if inverse then 0 else 1)
  integerPolynomialValue B s ≠ 0 ∧ integerPolynomialValue A s ≠ 0 ∧
    t = integerPolynomialValue A s/integerPolynomialValue B s

def signedGraphRecovery (inverse : Bool) (A B : Polynomial ℤ) (b d u v : ℕ) : Prop :=
  let xy := graphParameter inverse b d u v
  let r := graphDegree A B
  let av := homogeneousGraphValue A r (xy 0) (xy 1)
  let bv := homogeneousGraphValue B r (xy 0) (xy 1)
  let g := sourceGraphGCD inverse A B b d u v
  ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ 0 < g ∧
    (graphPartner inverse b d u v 0 : ℤ) = σ*av/(g:ℤ) ∧
    (graphPartner inverse b d u v 1 : ℤ) = σ*bv/(g:ℤ) ∧
    MvPolynomial.eval xy (graphPullback inverse A B) =
      (if inverse then σ else 1)*(g:ℤ)^graphLevelPower inverse

def reducedGraphLevel (inverse : Bool) (A B : Polynomial ℤ) (b d u v : ℕ) : Prop :=
  let H := graphPullback inverse A B
  let Q := binaryPrimitivePart H
  let c := binaryContent H
  let xy := graphParameter inverse b d u v
  let g := sourceGraphGCD inverse A B b d u v
  0 < c ∧ binaryContent Q = 1 ∧ H = MvPolynomial.C (c:ℤ)*Q ∧
    c ∣ g^graphLevelPower inverse ∧ ∃ h : ℤ, h ≠ 0 ∧ MvPolynomial.eval xy Q = h ∧
      (c:ℤ)*h = MvPolynomial.eval xy H ∧ h.natAbs ∣ g^graphLevelPower inverse

def CF13PrimitiveSignedRecovery : Prop :=
  ∀ v u : ℕ, 0 < v → 0 < u → Nat.Coprime v u → ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
    (v:ℚ)/(u:ℚ) = (a:ℚ)/(b:ℚ) →
    let g := Int.gcd a b
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ 0 < g ∧
      a = σ*(g:ℤ)*(v:ℤ) ∧ b = σ*(g:ℤ)*(u:ℤ) ∧
      (v:ℤ) = σ*a/(g:ℤ) ∧ (u:ℤ) = σ*b/(g:ℤ)

def CF13DirectSourceRecovery : Prop :=
  ∀ (A B : Polynomial ℤ) (n b d u v : ℕ), PairSource n b d u v →
    sourceGraphBranch false A B b d u v → signedGraphRecovery false A B b d u v

def CF13InverseSourceRecovery : Prop :=
  ∀ (A B : Polynomial ℤ) (n b d u v : ℕ), PairSource n b d u v →
    sourceGraphBranch true A B b d u v → signedGraphRecovery true A B b d u v

def CF13BinaryContentRemoval : Prop :=
  ∀ H : SourcePolynomial, H ≠ 0 →
    let c := binaryContent H
    let Q := binaryPrimitivePart H
    0 < c ∧ binaryContent Q = 1 ∧ H = MvPolynomial.C (c:ℤ)*Q ∧
      ∀ z : Fin 2 → ℤ, MvPolynomial.eval z H = (c:ℤ)*MvPolynomial.eval z Q

/-- Exact corrected content route at an admitted NONZERO signed level.
The primitive polynomial is constructed, not supplied as a premise. -/
def CF13AdmittedContentLevel : Prop :=
  ∀ (H : SourcePolynomial) (z : Fin 2 → ℤ) (g ℓ : ℕ) (σ : ℤ),
    0 < g → (σ = 1 ∨ σ = -1) → MvPolynomial.eval z H = σ*(g:ℤ)^ℓ →
    let c := binaryContent H
    let Q := binaryPrimitivePart H
    0 < c ∧ binaryContent Q = 1 ∧ H = MvPolynomial.C (c:ℤ)*Q ∧
      c ∣ g^ℓ ∧ ∃ h : ℤ, h ≠ 0 ∧ MvPolynomial.eval z Q = h ∧
        (c:ℤ)*h = σ*(g:ℤ)^ℓ ∧ h.natAbs ∣ g^ℓ

def CF13ActualSourceResultantLevel : Prop :=
  ∀ (X : ℝ) (D A B : Polynomial ℤ), 32 ≤ X → boundedGraphData X D A B →
    1 ≤ graphDegree A B → fullGraphResultant A B ≠ 0 ∧
      |(fullGraphResultant A B : ℝ)| ≤ 720*X^(90:ℕ) ∧
      ∀ (inverse : Bool) (n b d u v : ℕ), PairSource n b d u v →
        sourceGraphBranch inverse A B b d u v →
          sourceGraphGCD inverse A B b d u v ∣ (fullGraphResultant A B).natAbs ∧
          signedGraphRecovery inverse A B b d u v ∧ reducedGraphLevel inverse A B b d u v

/-- One graph/resultant/content polynomial before the entire actual class.
Common-factor rulings and actual degree-zero graphs remain explicit. -/
def CF13RoundedClassResultantLevels : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ X₀ : ℝ, 32 ≤ X₀ ∧
    ∀ X ψ B E a : ℝ, X₀ ≤ X → 0 ≤ ψ → ψ ≤ 2/3 →
      0 < B → 0 < E → 0 < a → B*E = X^ψ →
      ∀ (F : SourcePolynomial) (p : ℕ) (z₀ : Fin 2 → ZMod p)
        (ι : Type) (n b d u v : ι → ℕ), Nat.Prime p → roundedScale X ψ δ ≤ (p:ℝ) →
        (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
        (∀ i, actualRealBox X B E (n i) (b i) (d i)) →
        (∀ i, actualDirectInterval a (roundedHeight X ψ δ : ℝ) (b i) (d i)) →
        (∀ i, polynomialValue F (sourcePoint (b i) (d i) (u i) (v i)) = 0) →
        (∀ i, goodSourcePrime F (b i) (d i) (u i) (v i) p) →
        (∀ i, sourceReduction (b i) (d i) (u i) (v i) p = z₀) →
        ∃ D A C : Polynomial ℤ, boundedGraphData X D A C ∧ (rulingRoots D).card ≤ 3 ∧
          (∀ i, graphRulingCase (selectedRealChart ψ) D A C (sourcePoint (b i) (d i) (u i) (v i))) ∧
          (graphDegree A C = 0 ∨ (fullGraphResultant A C ≠ 0 ∧
            |(fullGraphResultant A C : ℝ)| ≤ 720*X^(90:ℕ) ∧
            ∀ i : ι, (sourcePoint (b i) (d i) (u i) (v i)) (if selectedRealChart ψ then 1 else 0) ∈ rulingRoots D ∨
              (sourceGraphGCD (selectedRealChart ψ) A C (b i) (d i) (u i) (v i) ∣ (fullGraphResultant A C).natAbs ∧
                signedGraphRecovery (selectedRealChart ψ) A C (b i) (d i) (u i) (v i) ∧
                reducedGraphLevel (selectedRealChart ψ) A C (b i) (d i) (u i) (v i))))

end
end P0365Subquarter
