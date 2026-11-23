import PaperTargets.Definitions
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

/-!
CF01 target proposal, not compiled or accepted formal coverage.
Definitions are independently frozen before proof construction. There are no
solution imports. Historical scratch proofs must not be imported into targets.
-/

namespace P0365Subquarter

set_option autoImplicit false

/-- All positive canonical sources for the original consecutive-pair problem.
Cross-endpoint coprimality is to be derived, not imposed. Same-endpoint
coprimality is deliberately absent. -/
def PairSource (n b d u v : ℕ) : Prop :=
  0 < b ∧ 0 < d ∧ 0 < u ∧ 0 < v ∧ Squarefree b ∧ Squarefree d ∧
    n = b ^ 3 * u ^ 2 ∧ d ^ 3 * v ^ 2 = b ^ 3 * u ^ 2 + 1

/-- Original natural-cutoff count; zero is excluded by `Powerful` itself. -/
noncomputable def PairCount (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range (N + 1)).filter
    (fun n => Powerful n ∧ Powerful (n + 1))).card

/-- Ordered primitive rational ratios, retaining the orientation in the source. -/
def SourceRatios (b d u v : ℕ) : ℚ × ℚ :=
  ((b : ℚ) / (d : ℚ), (v : ℚ) / (u : ℚ))

def CF01NormalForm : Prop :=
  ∀ n : ℕ, Powerful n ↔ ∃! bu : ℕ × ℕ,
    0 < bu.1 ∧ 0 < bu.2 ∧ Squarefree bu.1 ∧ n = bu.1 ^ 3 * bu.2 ^ 2

def CF01NormalFormUnique : Prop :=
  ∀ b u c v : ℕ, Squarefree b → Squarefree c → 0 < u → 0 < v →
    b ^ 3 * u ^ 2 = c ^ 3 * v ^ 2 → b = c ∧ u = v

def CF01CubeSquarePowerful : Prop :=
  ∀ b u : ℕ, 0 < b → 0 < u → Powerful (b ^ 3 * u ^ 2)

def CF01PairSourceEquivalence : Prop :=
  ∀ n : ℕ, (Powerful n ∧ Powerful (n + 1)) ↔
    ∃ b d u v : ℕ, PairSource n b d u v

def CF01PairSourceUnique : Prop :=
  ∀ n b d u v b' d' u' v' : ℕ,
    PairSource n b d u v → PairSource n b' d' u' v' →
      b = b' ∧ d = d' ∧ u = u' ∧ v = v'

def CF01AdditiveAndIntegerSource : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v →
    0 < n ∧ n + 1 = d ^ 3 * v ^ 2 ∧
      (d : ℤ) ^ 3 * (v : ℤ) ^ 2 - (b : ℤ) ^ 3 * (u : ℤ) ^ 2 = 1

def CF01CrossEndpointCoprime : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v →
    Nat.Coprime (b * u) (d * v)

def CF01PrimitiveRatios : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v →
    Nat.Coprime b d ∧ Nat.Coprime v u ∧ Squarefree (b * d)

def CF01SourceBounds : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v →
    b ^ 3 ≤ n ∧ u ^ 2 ≤ n ∧ d ^ 3 ≤ n + 1 ∧ v ^ 2 ≤ n + 1

def CF01CutoffSourceBounds : Prop :=
  ∀ N n b d u v : ℕ, PairSource n b d u v → n ≤ N →
    0 < n ∧ n ≤ N ∧ b ≤ N + 1 ∧ d ≤ N + 1 ∧
      u ≤ N + 1 ∧ v ≤ N + 1

/-- A primitive rational ratio pair determines at most one original start. -/
def CF01SourceRatioInjection : Prop :=
  ∀ n m b d u v b' d' u' v' : ℕ,
    PairSource n b d u v → PairSource m b' d' u' v' →
    SourceRatios b d u v = SourceRatios b' d' u' v' → n = m

def CF01SourceRatioCoordinateInjection : Prop :=
  ∀ n m b d u v b' d' u' v' : ℕ,
    PairSource n b d u v → PairSource m b' d' u' v' →
    SourceRatios b d u v = SourceRatios b' d' u' v' →
      n = m ∧ b = b' ∧ d = d' ∧ u = u' ∧ v = v'

/- Literal, source-bound readback only, not an imported historical definition.
The actual `P365Bound` declaration adapters remain an independent open gate. -/
namespace LegacyReadback

def IsPrime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ d : ℕ, d ∣ p → d = 1 ∨ d = p

def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, IsPrime p → p ∣ n → p ^ 2 ∣ n

noncomputable def pairCount (N : ℕ) : ℕ := by
  classical
  exact ((List.range (N + 1)).filter
    (fun n => decide (Powerful n ∧ Powerful (n + 1)))).length

def PairSource (n b d u v : ℕ) : Prop :=
  0 < b ∧ 0 < d ∧ 0 < u ∧ 0 < v ∧ Squarefree b ∧ Squarefree d ∧
    n = b ^ 3 * u ^ 2 ∧ n + 1 = d ^ 3 * v ^ 2

end LegacyReadback

def CF01ReadbackPrimeCorrespondence : Prop :=
  ∀ p : ℕ, LegacyReadback.IsPrime p ↔ Nat.Prime p

def CF01ReadbackPowerfulCorrespondence : Prop :=
  ∀ n : ℕ, LegacyReadback.Powerful n ↔ Powerful n

def CF01ReadbackSourceCorrespondence : Prop :=
  ∀ n b d u v : ℕ, LegacyReadback.PairSource n b d u v ↔ PairSource n b d u v

def CF01ReadbackCountCorrespondence : Prop :=
  ∀ N : ℕ, LegacyReadback.pairCount N = PairCount N

def CF01CountSourceCorrespondence : Prop := by
  classical
  exact ∀ N : ℕ, PairCount N =
    ((Finset.range (N + 1)).filter
      (fun n => ∃ b d u v : ℕ, PairSource n b d u v)).card

def CF01CountEmptyBoundary : Prop :=
  PairCount 0 = 0 ∧ PairCount 1 = 0

def CF01EndpointAndOverlapControls : Prop :=
  ¬ Powerful 0 ∧ Powerful 1 ∧ Powerful 16 ∧ Powerful 81 ∧
    Powerful 32 ∧ 32 = (2 : ℕ) ^ 3 * 2 ^ 2 ∧ ¬ Nat.Coprime 2 2 ∧
    PairSource 8 2 1 1 3 ∧ PairSource 288 2 1 6 17 ∧
    ¬ Nat.Coprime 2 6 ∧ PairSource 12167 23 2 1 39

def CF01NoncanonicalControl : Prop :=
  (64 : ℕ) = 1 ^ 3 * 8 ^ 2 ∧ (64 : ℕ) = 4 ^ 3 * 1 ^ 2 ∧
    ¬ Squarefree (4 : ℕ)

end P0365Subquarter
