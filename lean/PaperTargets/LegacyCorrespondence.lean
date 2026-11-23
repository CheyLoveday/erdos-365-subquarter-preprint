import PaperTargets.CanonicalSource
import PaperTargets.LegacyDefinitions

/-! Four source-identity adapters; target definitions precede their proofs.
These refer to the requalified source-exact P365Bound declarations, not only
the earlier LegacyReadback namespace. No donor proof or final bound is assumed.
-/

namespace P0365Subquarter

set_option autoImplicit false

def CF01LegacyPrimeCorrespondence : Prop :=
  ∀ p : ℕ, P365Bound.IsPrime p ↔ Nat.Prime p

def CF01LegacyPowerfulCorrespondence : Prop :=
  ∀ n : ℕ, P365Bound.Powerful n ↔ Powerful n

def CF01LegacySourceCorrespondence : Prop :=
  ∀ n b d u v : ℕ, P365Bound.PairSource n b d u v ↔ PairSource n b d u v

def CF01LegacyCountCorrespondence : Prop :=
  ∀ N : ℕ, P365Bound.pairCount N = PairCount N

end P0365Subquarter
