import PaperTargets.Pilot
import Mathlib.Tactic.NormNum

/-! Elementary native checks, not CF01 or CF16 coverage.
Originally selected for P1b; full-checker assurance remains deferred.
The protected challenge is independently authored and is never imported here. -/

namespace P0365Subquarter.PilotVerified

set_option autoImplicit false

theorem equality : P0365Subquarter.PilotEquality := rfl

theorem centralExponent : P0365Subquarter.PilotCentralExponent := by
  norm_num [P0365Subquarter.PilotCentralExponent]

theorem belowQuarter : P0365Subquarter.PilotBelowQuarter := by
  norm_num [P0365Subquarter.PilotBelowQuarter]

theorem powerfulZero : P0365Subquarter.PilotPowerfulZero := by
  intro h
  exact Nat.lt_irrefl 0 h.1

theorem powerfulOne : P0365Subquarter.PilotPowerfulOne := by
  constructor
  · exact Nat.zero_lt_one
  · intro p hp hd
    exact False.elim (hp.not_dvd_one hd)

end P0365Subquarter.PilotVerified
