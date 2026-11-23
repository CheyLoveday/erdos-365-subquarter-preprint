import PaperTargets.CanonicalSource

/-! Additional independently reviewed CF01 cutoff controls. The cutoff bounds
the starting integer, not both endpoints. Existing frozen targets are unchanged. -/

namespace P0365Subquarter

set_option autoImplicit false

def CF01FirstCutoffs : Prop :=
  PairCount 7 = 0 ∧ PairCount 8 = 1

end P0365Subquarter
