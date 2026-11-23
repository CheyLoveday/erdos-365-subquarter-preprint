import PaperProofs.Pilot

-- Native development readback of the frozen definition bodies, not external
-- comparison or independent assurance.
#print P0365Subquarter.Powerful
#print P0365Subquarter.PilotEquality
#print P0365Subquarter.PilotCentralExponent
#print P0365Subquarter.PilotBelowQuarter
#print P0365Subquarter.PilotPowerfulZero
#print P0365Subquarter.PilotPowerfulOne

#check (P0365Subquarter.PilotVerified.equality : P0365Subquarter.PilotEquality)
#check (P0365Subquarter.PilotVerified.centralExponent : P0365Subquarter.PilotCentralExponent)
#check (P0365Subquarter.PilotVerified.belowQuarter : P0365Subquarter.PilotBelowQuarter)
#check (P0365Subquarter.PilotVerified.powerfulZero : P0365Subquarter.PilotPowerfulZero)
#check (P0365Subquarter.PilotVerified.powerfulOne : P0365Subquarter.PilotPowerfulOne)

set_option pp.all true in
#check P0365Subquarter.PilotVerified.equality
set_option pp.all true in
#check P0365Subquarter.PilotVerified.centralExponent
set_option pp.all true in
#check P0365Subquarter.PilotVerified.belowQuarter
set_option pp.all true in
#check P0365Subquarter.PilotVerified.powerfulZero
set_option pp.all true in
#check P0365Subquarter.PilotVerified.powerfulOne

#print axioms P0365Subquarter.PilotVerified.equality
#print axioms P0365Subquarter.PilotVerified.centralExponent
#print axioms P0365Subquarter.PilotVerified.belowQuarter
#print axioms P0365Subquarter.PilotVerified.powerfulZero
#print axioms P0365Subquarter.PilotVerified.powerfulOne
