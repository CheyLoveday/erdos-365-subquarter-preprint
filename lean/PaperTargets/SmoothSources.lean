import PaperTargets.PrimeAssignment
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! CF09–10 finite implicit-series form explicitly permitted by corrected v3
MATHEMATICS §4 and ALGEBRA AR03–04. Work modulo p^28: no claim about infinite
p-adic convergence. All final determinants are the original integer rows. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

abbrev SmoothRing (p : ℕ) := ZMod (p^28)

def smoothReduction (p : ℕ) : SmoothRing p →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : (28:ℕ) ≠ 0)) (ZMod p)

def otherCoordinate (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

def sourceLift (b d u v p : ℕ) : Fin 2 → SmoothRing p :=
  sourceReduction b d u v (p^28)

/-- The eight unscaled rational monomials, with the two chart choices. -/
def chartMonomial {R : Type*} [CommRing R] (inverse : Bool)
    (z : Fin 2 → R) (j : Fin 8) : R :=
  z (if inverse then 1 else 0) ^ (j.val % 4) *
    (if j.val < 4 then 1 else z (if inverse then 0 else 1))

/-- Exactly R31 or R13 of MATHEMATICS §4, in the original column order. -/
def sourceIntegerRow (inverse : Bool) (b d u v : ℕ) (j : Fin 8) : ℤ :=
  if inverse then
    (u : ℤ)^(3-j.val%4) * (v : ℤ)^(j.val%4) * (if j.val < 4 then d else b)
  else
    (b : ℤ)^(j.val%4) * (d : ℤ)^(3-j.val%4) * (if j.val < 4 then u else v)

def sourceRowDenominator (inverse : Bool) (d u : ℕ) : ℤ :=
  if inverse then (d : ℤ)*u^3 else (d : ℤ)^3*u

/-- One polynomial for the entire smooth fibre, chosen from either unit partial.
It is an integral finite implicit series; no supplied-series premise occurs. -/
def CF09FiniteImplicitPolynomial : Prop :=
  ∀ (F : SourcePolynomial) (p : ℕ), Nat.Prime p →
    ∀ z₀ : Fin 2 → SmoothRing p, polynomialValue F z₀ = 0 →
      (∃ i : Fin 2, smoothReduction p (polynomialValue (MvPolynomial.pderiv i F) z₀) ≠ 0) →
      ∃ (i : Fin 2) (q : Polynomial (SmoothRing p)),
        smoothReduction p (polynomialValue (MvPolynomial.pderiv i F) z₀) ≠ 0 ∧
        q.eval 0 = 0 ∧ ∀ z : Fin 2 → SmoothRing p, polynomialValue F z = 0 →
          (∀ j, smoothReduction p (z j) = smoothReduction p (z₀ j)) →
          z i = z₀ i + q.eval (z (otherCoordinate i) - z₀ (otherCoordinate i))

/-- Actual canonical source centre and actual ratio denominators. One q and
coordinate precede every source in the selected common residue class. -/
def CF09ActualSourceImplicitPolynomial : Prop :=
  ∀ (F : SourcePolynomial) (p n₀ b₀ d₀ u₀ v₀ : ℕ), Nat.Prime p →
    PairSource n₀ b₀ d₀ u₀ v₀ → polynomialValue F (sourcePoint b₀ d₀ u₀ v₀) = 0 →
    goodSourcePrime F b₀ d₀ u₀ v₀ p →
    ∃ (i : Fin 2) (q : Polynomial (SmoothRing p)), q.eval 0 = 0 ∧
      ∀ n b d u v : ℕ, PairSource n b d u v →
        polynomialValue F (sourcePoint b d u v) = 0 → goodSourcePrime F b d u v p →
        sourceReduction b d u v p = sourceReduction b₀ d₀ u₀ v₀ p →
        sourceLift b d u v p i = sourceLift b₀ d₀ u₀ v₀ p i +
          q.eval (sourceLift b d u v p (otherCoordinate i) -
            sourceLift b₀ d₀ u₀ v₀ p (otherCoordinate i))

/-- Universal finite-series determinant lemma over any commutative ring.
A degree<8 remainder at the eight nodes gives Vandermonde factorization;
duplicate nodes and zero-divisors require no extra hypotheses. -/
def CF10PolynomialEvaluationDeterminant : Prop :=
  ∀ (R : Type) [CommRing R] (a : R), a^28 = 0 →
    ∀ (z : Fin 8 → R), (∀ i, a ∣ z i) →
      ∀ f : Fin 8 → Polynomial R, Matrix.det (fun i j => (f j).eval (z i)) = 0

def CF10SourceRowIdentity : Prop :=
  ∀ (p b d u v : ℕ), Nat.Prime p → ¬ p ∣ d*u → ∀ inverse : Bool,
    IsUnit (sourceRowDenominator inverse d u : SmoothRing p) ∧
      ∀ j : Fin 8, (sourceIntegerRow inverse b d u v j : SmoothRing p) =
        (sourceRowDenominator inverse d u : SmoothRing p) *
          chartMonomial inverse (sourceLift b d u v p) j

/-- Same actual polynomial and common smooth residue for all eight canonical
sources. This proves divisibility of both ORIGINAL integer minors, not of a
real-normalised or arbitrary two-parameter matrix. -/
def CF10ActualSourceDeterminants : Prop :=
  ∀ (F : SourcePolynomial) (p : ℕ) (n b d u v : Fin 8 → ℕ), Nat.Prime p →
    (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
    (∀ i, polynomialValue F (sourcePoint (b i) (d i) (u i) (v i)) = 0) →
    (∀ i, goodSourcePrime F (b i) (d i) (u i) (v i) p) →
    (∀ i, sourceReduction (b i) (d i) (u i) (v i) p =
      sourceReduction (b 0) (d 0) (u 0) (v 0) p) →
    ∀ inverse : Bool, (p : ℤ)^28 ∣ Matrix.det
      (fun i j => sourceIntegerRow inverse (b i) (d i) (u i) (v i) j)

end
end P0365Subquarter
