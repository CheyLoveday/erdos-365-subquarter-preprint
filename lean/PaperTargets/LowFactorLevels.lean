import PaperTargets.PullbackNonpowers
import Mathlib.NumberTheory.Divisors

/-! CF15 first counting stage, ALGEBRA AR10. Count fixed low-degree factor
levels through primitive rational directions, retaining both axes and signs.
The uniform four-point budget suffices for the source's divisor-pair bound;
the sharper one/two intersection constants are unnecessary here. Factor
selection, the precise external Thue application and tau(R)^8 follow later. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

def primitiveBinaryPoint (z : Fin 2 → ℤ) : Prop := IsCoprime (z 0) (z 1)

abbrev rationalBinary (G : SourcePolynomial) : MvPolynomial (Fin 2) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ) G

def binaryNonproportional (G H : SourcePolynomial) : Prop :=
  ¬ ∃ q : ℚ, rationalBinary G=MvPolynomial.C q*rationalBinary H

/-- The four cases for two fixed distinct low-degree factors. The subsequent
factor-selection stage must derive these nonproportionality conditions. -/
def lowBinaryFactorPair (G H : SourcePolynomial) : Prop :=
  G ≠ 0 ∧ H ≠ 0 ∧
  ((G.IsHomogeneous 1 ∧ H.IsHomogeneous 1 ∧ binaryNonproportional G H) ∨
   (G.IsHomogeneous 1 ∧ H.IsHomogeneous 2 ∧ binaryNonproportional H (G^2)) ∨
   (G.IsHomogeneous 2 ∧ H.IsHomogeneous 1 ∧ binaryNonproportional G (H^2)) ∨
   (G.IsHomogeneous 2 ∧ H.IsHomogeneous 2 ∧ binaryNonproportional G H))

/-- Every primitive integer projective direction has just its two signed
primitive representatives. Neither coordinate is divided in this lemma. -/
def CF15SignedPrimitiveParallel : Prop :=
  ∀ z w : Fin 2 → ℤ, primitiveBinaryPoint z → primitiveBinaryPoint w →
    z 0*w 1=w 0*z 1 → w=z ∨ w=-z

def CF15PrimitiveRatioFiber : Prop :=
  ∀ (r : ℚ) (S : Finset (Fin 2 → ℤ)),
    (∀ z ∈ S, primitiveBinaryPoint z ∧ z 1 ≠ 0 ∧ (z 0:ℚ)/(z 1:ℚ)=r) → S.card ≤ 2

/-- At most d rational projective roots, each with at most two primitive
signed representatives. The point at infinity is included in the degree cost. -/
def CF15HomogeneousPrimitiveZeros : Prop :=
  ∀ (K : SourcePolynomial) (d : ℕ), K ≠ 0 → K.IsHomogeneous d →
    ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z K=0) → S.card ≤ 2*d

/-- A deliberately uniform primitive-direction bound (two suffices); the
sharper one-point affine intersection bound is not needed for CF15. -/
def CF15TwoLinearLevels : Prop :=
  ∀ L₁ L₂ : SourcePolynomial, L₁.IsHomogeneous 1 → L₂.IsHomogeneous 1 →
    binaryNonproportional L₁ L₂ → ∀ h₁ h₂ : ℤ, h₁ ≠ 0 → h₂ ≠ 0 →
      ∀ S : Finset (Fin 2 → ℤ), (∀ z ∈ S, primitiveBinaryPoint z ∧
        MvPolynomial.eval z L₁=h₁ ∧ MvPolynomial.eval z L₂=h₂) → S.card ≤ 2

def CF15LinearQuadraticLevels : Prop :=
  ∀ L G : SourcePolynomial, L.IsHomogeneous 1 → G.IsHomogeneous 2 →
    binaryNonproportional G (L^2) → ∀ hL hG : ℤ, hL ≠ 0 → hG ≠ 0 →
      ∀ S : Finset (Fin 2 → ℤ), (∀ z ∈ S, primitiveBinaryPoint z ∧
        MvPolynomial.eval z L=hL ∧ MvPolynomial.eval z G=hG) → S.card ≤ 4

def CF15TwoQuadraticLevels : Prop :=
  ∀ G₁ G₂ : SourcePolynomial, G₁.IsHomogeneous 2 → G₂.IsHomogeneous 2 →
    binaryNonproportional G₁ G₂ → ∀ h₁ h₂ : ℤ, h₁ ≠ 0 → h₂ ≠ 0 →
      ∀ S : Finset (Fin 2 → ℤ), (∀ z ∈ S, primitiveBinaryPoint z ∧
        MvPolynomial.eval z G₁=h₁ ∧ MvPolynomial.eval z G₂=h₂) → S.card ≤ 4

/-- Fixed factors, not an enumeration of coefficient families. Nonzero source
levels force both factor values into the signed divisors of |h|. The proved
four-point fiber budget gives16*tau(|h|)^2. No intersection-count premise is
supplied. Actual irreducible-factor selection remains a subsequent obligation. -/
def CF15LowFactorDivisorBudget : Prop :=
  ∀ Q G H : SourcePolynomial, lowBinaryFactorPair G H → G ∣ Q → H ∣ Q →
    ∀ h : ℤ, h ≠ 0 → ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, primitiveBinaryPoint z ∧ MvPolynomial.eval z Q=h) →
      S.card ≤ 16*((h.natAbs.divisors).card)^2

end
end P0365Subquarter
