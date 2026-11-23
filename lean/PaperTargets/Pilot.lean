import PaperTargets.Definitions
import Mathlib.Algebra.Order.Field.Rat

/-!
Independently frozen P1b checker challenges, not proof declarations.
Rational arithmetic below tests the checker pipeline, not the continuous CF16 claim.
This module must never import PaperProofs or a candidate solution module.
-/

namespace P0365Subquarter

set_option autoImplicit false

/-- Minimal native/export/checker positive control. -/
def PilotEquality : Prop :=
  (1 : ℕ) + 1 = 2

/-- Exact arithmetic at the central k=1 profile, not a profile maximum theorem. -/
def PilotCentralExponent : Prop :=
  ((32 : ℚ) / 5 - 1 + 7 * ((9 : ℚ) / 50)) / 28 = (333 : ℚ) / 1400

/-- The proposed exact exponent is strictly less than one quarter. -/
def PilotBelowQuarter : Prop :=
  (333 : ℚ) / 1400 < (1 : ℚ) / 4

/-- Positivity is essential: zero is excluded despite every square dividing zero. -/
def PilotPowerfulZero : Prop :=
  ¬ Powerful 0

/-- One is included: it has no prime divisors. -/
def PilotPowerfulOne : Prop :=
  Powerful 1

end P0365Subquarter
