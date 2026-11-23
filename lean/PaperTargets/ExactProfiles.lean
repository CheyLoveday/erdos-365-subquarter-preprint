import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation

/-! CF16 numerical specification over the reals, frozen before proof authoring.
Source: corrected v3 review/ANALYTIC.md A08 and formal/CF_OBLIGATIONS.md CF16.
No proof-module, Pell, source-count or external-input imports. Rounding,
determinant constants and source-specific applications are separate obligations. -/

namespace P0365Subquarter

noncomputable section

set_option autoImplicit false

def profileTheta : ℝ := 333 / 1400
def profileRho : ℝ := 141 / 2800
def profileCentre : ℝ := 2 / 5
def profileM0 (ψ : ℝ) : ℝ := (9 / 8) * ψ * (1 - (3 / 2) * ψ)
def profileW (ψ : ℝ) : ℝ := min (4 + 6 * ψ) (12 - 14 * ψ)

/-- The five integral exponents in the actual mixed-error inventory. -/
def profileErrorWeight : Fin 5 → ℕ := ![28, 21, 16, 13, 12]

def profileBranch (ψ : ℝ) (k : Fin 5) : ℝ :=
  (profileW ψ - (k.val : ℝ) +
    (28 - (profileErrorWeight k : ℝ)) * profileM0 ψ) / 28

def profileCentreValue : Fin 5 → ℝ :=
  ![8 / 35, 333 / 1400, 41 / 175, 61 / 280, 33 / 175]

def CF16ProfileBounds : Prop :=
  ∀ ψ : ℝ, 0 ≤ ψ → ψ ≤ 2 / 3 →
    0 ≤ profileM0 ψ ∧ profileM0 ψ ≤ 3 / 16 ∧ profileM0 ψ < profileTheta

def CF16ChartBranches : Prop :=
  ∀ ψ : ℝ, (ψ ≤ profileCentre → profileW ψ = 4 + 6 * ψ) ∧
    (profileCentre ≤ ψ → profileW ψ = 12 - 14 * ψ)

def CF16Envelope : Prop :=
  ∀ ψ : ℝ, 0 ≤ ψ → ψ ≤ 2 / 3 →
    ∀ k : Fin 5, profileBranch ψ k ≤ profileTheta

def CF16CentreValues : Prop :=
  profileM0 profileCentre = 9 / 50 ∧ profileW profileCentre = 32 / 5 ∧
    (∀ k : Fin 5, profileBranch profileCentre k = profileCentreValue k) ∧
    profileBranch profileCentre 1 = profileTheta

def CF16UnroundedSlack : Prop :=
  ∀ ψ δ : ℝ, 0 ≤ ψ → ψ ≤ 2 / 3 → 0 < δ →
    let m := (1 + δ) * profileM0 ψ
    let q := profileTheta + δ - m
    profileRho + (13 / 16) * δ ≤ q ∧ 0 < q ∧ 0 < 25 * δ ∧
      (∀ k : Fin 5,
        25 * δ ≤ 28 * q - (profileW ψ - (k.val : ℝ) -
          (profileErrorWeight k : ℝ) * m) ∧
        0 < 28 * q - (profileW ψ - (k.val : ℝ) -
          (profileErrorWeight k : ℝ) * m)) ∧
      m + q = profileTheta + δ

/-- Immediate numerical consumer only: not the rounded determinant argument. -/
def CF16UnroundedStrictConstraints : Prop :=
  ∀ ψ δ : ℝ, 0 ≤ ψ → ψ ≤ 2 / 3 → 0 < δ →
    let m := (1 + δ) * profileM0 ψ
    let q := profileTheta + δ - m
    0 ≤ m ∧ profileRho < q ∧ m + q = profileTheta + δ ∧
      ∀ k : Fin 5,
        profileW ψ - (k.val : ℝ) - (profileErrorWeight k : ℝ) * m < 28 * q

end

end P0365Subquarter
