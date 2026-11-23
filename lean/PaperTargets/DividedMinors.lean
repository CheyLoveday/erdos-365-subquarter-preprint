import PaperTargets.RealSources

/-! CF11: exact polynomial divided differences in root chart coordinates,
followed by the actual positive-source box/original-interval application.
Source: corrected v3 MATHEMATICS §4, review/ANALYTIC A04 and A07–A08.
No determinant-size, derivative, or interval-transfer theorem is a premise. -/
namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Square-root coordinate in the direct chart, cube-root in the inverse. -/
def realRootOrder (inverse : Bool) : ℕ := if inverse then 3 else 2
def realRootPartnerOrder (inverse : Bool) : ℕ := if inverse then 2 else 3

def rootSmoothRow {R : Type*} [CommRing R] (inverse : Bool) (w : R) (j : Fin 8) : R :=
  w ^ (realRootOrder inverse * (j.val % 4)) *
    (if j.val < 4 then 1 else w ^ realRootPartnerOrder inverse)

def rootErrorRow {R : Type*} [CommRing R] (inverse : Bool) (w : R) (j : Fin 8) : R :=
  if j.val < 4 then 0 else w ^ (realRootOrder inverse * (j.val % 4))

def rootNormalizedRow (inverse : Bool) (w β : ℝ) (j : Fin 8) : ℝ :=
  rootSmoothRow inverse w j + β * rootErrorRow inverse w j

/-- One original direct interval supplies BOTH real chart scales. -/
def realIntervalScale (inverse : Bool) (a : ℝ) : ℝ :=
  if inverse then a ^ (3 / 2 : ℝ) else a

def realIntervalNode (inverse : Bool) (a : ℝ) (b d u v : ℕ) : ℝ :=
  (realSourceCoordinate inverse b d u v / realIntervalScale inverse a) ^
    (1 / (realRootOrder inverse : ℝ))

def actualDirectInterval (a M : ℝ) (b d : ℕ) : Prop :=
  a ≤ (b : ℝ) / d ∧ (b : ℝ) / d ≤ a * (1 + 1 / M)

def actualRealBox (X B E : ℝ) (n b d : ℕ) : Prop :=
  X ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * X ∧
    B ≤ (b : ℝ) ∧ (b : ℝ) ≤ 2 * B ∧ E ≤ (d : ℝ) ∧ (d : ℝ) ≤ 2 * E

def realBoxScale (inverse : Bool) (X B E : ℝ) : ℝ :=
  if inverse then X ^ (12 : ℕ) / (B * E) ^ (14 : ℕ)
  else X ^ (4 : ℕ) * (B * E) ^ (6 : ℕ)

def realErrorSum (X M : ℝ) : ℝ :=
  ∑ k : Fin 5, 1 / (X ^ k.val * M ^ profileErrorWeight k)

def selectedRealChart (ψ : ℝ) : Bool := if ψ ≤ profileCentre then false else true

/-- Same-group polynomial divided differences give all five angular powers.
Repeated nodes are included, and five perturbation rows force zero. -/
def CF11MixedRootDeterminants : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (inverse : Bool) (S : Finset (Fin 8)) (w : Fin 8 → ℝ)
    (h : ℝ), 0 ≤ h → (∀ i, 1 ≤ w i ∧ w i ≤ 2) →
      (∀ i j, |w i - w j| ≤ h) →
      let D := Matrix.det (fun i j => if i ∈ S then rootErrorRow inverse (w i) j
        else rootSmoothRow inverse (w i) j)
      (4 < S.card → D = 0) ∧
        (∀ k : Fin 5, S.card = k.val → |D| ≤ C * h ^ profileErrorWeight k)

/-- Row multilinearity keeps every mixed error, with fixed uniform constants. -/
def CF11NormalizedDeterminantBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (inverse : Bool) (X M : ℝ) (w β : Fin 8 → ℝ),
    1 ≤ X → 1 ≤ M → (∀ i, 1 ≤ w i ∧ w i ≤ 2) →
      (∀ i j, |w i - w j| ≤ 3 / M) → (∀ i, |β i| ≤ 8 / X) →
      |Matrix.det (fun i j => rootNormalizedRow inverse (w i) (β i) j)| ≤
        C * realErrorSum X M

/-- The actual additive source equation transfers one original interval to
both root charts. The normalized error and row identity are derived here. -/
def CF11ActualIntervalNodes : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v → ∀ X M a : ℝ,
    1 ≤ X → X ≤ (n : ℝ) → 1 ≤ M → M ≤ X → 0 < a →
      actualDirectInterval a M b d → ∀ inverse : Bool,
        1 ≤ realIntervalNode inverse a b d u v ∧
        realIntervalNode inverse a b d u v ≤ 2 ∧
        realIntervalNode inverse a b d u v ≤ 1 + 3 / M ∧
        |realNormalizedError inverse (realIntervalScale inverse a) b d u v| ≤ 8 / X ∧
        ∀ j : Fin 8, realNormalizedRow inverse
          (realSourceCoordinate inverse b d u v / realIntervalScale inverse a)
          (realNormalizedError inverse (realIntervalScale inverse a) b d u v) j =
            rootNormalizedRow inverse (realIntervalNode inverse a b d u v)
              (realNormalizedError inverse (realIntervalScale inverse a) b d u v) j

/-- Actual canonical rows, literal shell and arbitrary positive kernel skew.
The original direct interval is the only interval-localization assumption. -/
def CF11ActualBoxDeterminantBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X M B E a : ℝ,
    1 ≤ X → 1 ≤ M → M ≤ X → 0 < B → 0 < E → 0 < a →
      ∀ n b d u v : Fin 8 → ℕ, (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
        (∀ i, actualRealBox X B E (n i) (b i) (d i)) →
        (∀ i, actualDirectInterval a M (b i) (d i)) → ∀ inverse : Bool,
          |(Matrix.det (fun i j => sourceIntegerRow inverse
            (b i) (d i) (u i) (v i) j) : ℝ)| ≤
              C * realBoxScale inverse X B E * realErrorSum X M

/-- The real size bound is now a conclusion, for the chosen profile chart and
actual rounded height, rather than an assumed analytic antecedent. -/
def CF11RoundedActualDeterminantBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X ψ δ B E a : ℝ,
    4 ≤ X → 0 ≤ ψ → ψ ≤ 2 / 3 → 0 ≤ δ → δ ≤ 1 →
      0 < B → 0 < E → 0 < a → B * E = X ^ ψ →
      ∀ n b d u v : Fin 8 → ℕ, (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
        (∀ i, actualRealBox X B E (n i) (b i) (d i)) →
        (∀ i, actualDirectInterval a (roundedHeight X ψ δ : ℝ) (b i) (d i)) →
        |(Matrix.det (fun i j => sourceIntegerRow (selectedRealChart ψ)
          (b i) (d i) (u i) (v i) j) : ℝ)| ≤
            C * (∑ k : Fin 5, roundedMixedTerm X ψ δ k)

/-- Actual localized smooth-source minors vanish, without a supplied size bound.
The coarse box/interval cover and later relation/count inventory are separate. -/
def CF11RoundedActualMinorVanishing : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ X₀ : ℝ, 4 ≤ X₀ ∧
    ∀ X ψ B E a : ℝ, X₀ ≤ X → 0 ≤ ψ → ψ ≤ 2 / 3 →
      0 < B → 0 < E → 0 < a → B * E = X ^ ψ →
      ∀ (F : SourcePolynomial) (p : ℕ) (n b d u v : Fin 8 → ℕ), Nat.Prime p →
        roundedScale X ψ δ ≤ (p : ℝ) →
        (∀ i, PairSource (n i) (b i) (d i) (u i) (v i)) →
        (∀ i, actualRealBox X B E (n i) (b i) (d i)) →
        (∀ i, actualDirectInterval a (roundedHeight X ψ δ : ℝ) (b i) (d i)) →
        (∀ i, polynomialValue F (sourcePoint (b i) (d i) (u i) (v i)) = 0) →
        (∀ i, goodSourcePrime F (b i) (d i) (u i) (v i) p) →
        (∀ i, sourceReduction (b i) (d i) (u i) (v i) p =
          sourceReduction (b 0) (d 0) (u 0) (v 0) p) →
        Matrix.det (fun i j => sourceIntegerRow (selectedRealChart ψ)
          (b i) (d i) (u i) (v i) j) = 0

end
end P0365Subquarter
