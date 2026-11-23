import Mathlib.Data.Nat.Prime.Defs

/-!
Source-faithful definitions for the maintained P0365 consumer.
The P1b checker pilot uses only `Powerful`; it proves no CF01 obligation.
-/

namespace P0365Subquarter

set_option autoImplicit false

/-- Positive natural numbers whose every prime divisor divides to order at least two.
There is no squarefree restriction and no endpoint-overlap restriction. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

end P0365Subquarter
