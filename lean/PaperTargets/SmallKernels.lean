import PaperTargets.CanonicalSource
import Mathlib.Data.Nat.Log

/-!
CF02 finite counting targets. The retained source's Mathlib-Pell route gives
the stronger Y*log bound, not merely Y*log^2. No Pell count or classification
is an external premise of these targets. Fraction-spacing for later rulings
is not claimed here. Boundary Y=0/N=0 and kernel-one sources are retained.
-/

namespace P0365Subquarter

set_option autoImplicit false

def CF02SourceTrace : Prop :=
  ∀ n b d u v : ℕ, PairSource n b d u v →
    (2 * (n : ℤ) + 1) ^ 2 - (b : ℤ) * (d : ℤ) *
      (2 * (b : ℤ) * (d : ℤ) * (u : ℤ) * (v : ℤ)) ^ 2 = 1

/-- Counts original starts, not allocations among two kernels. -/
def CF02FixedKernelProductCount : Prop :=
  ∀ D N : ℕ, ∀ S : Finset ℕ,
    (∀ n ∈ S, n ≤ N ∧ ∃ b d u v : ℕ, PairSource n b d u v ∧ b * d = D) →
    S.card ≤ Nat.log 2 (2 * N + 1) + 1

def CF02SmallKernelProductCount : Prop :=
  ∀ Y N : ℕ, ∀ S : Finset ℕ,
    (∀ n ∈ S, n ≤ N ∧ ∃ b d u v : ℕ, PairSource n b d u v ∧ b * d ≤ Y) →
    S.card ≤ Y * (Nat.log 2 (2 * N + 1) + 1)

noncomputable def SmallKernelCount (Y N : ℕ) : ℕ := by
  classical
  exact ((Finset.range (N + 1)).filter
    (fun n => ∃ b d u v : ℕ, PairSource n b d u v ∧ b * d ≤ Y)).card

def CF02OriginalSmallKernelCount : Prop :=
  ∀ Y N : ℕ, SmallKernelCount Y N ≤ Y * (Nat.log 2 (2 * N + 1) + 1)

end P0365Subquarter
