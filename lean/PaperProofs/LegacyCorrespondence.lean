import PaperTargets.LegacyCorrespondence
import PaperProofs.CanonicalSource

/-! Exact legacy-declaration adapters. Each `change` is kernel-checked
definitional equality with the earlier readback, not an extra assumption.
Source-block identity is separately tested against the pinned historical files.
-/

namespace P0365Subquarter

set_option autoImplicit false

theorem legacy_prime_correspondence : CF01LegacyPrimeCorrespondence := by
  intro p
  change LegacyReadback.IsPrime p ↔ Nat.Prime p
  exact readback_prime_correspondence p

theorem legacy_powerful_correspondence : CF01LegacyPowerfulCorrespondence := by
  intro n
  change LegacyReadback.Powerful n ↔ Powerful n
  exact readback_powerful_correspondence n

theorem legacy_source_correspondence : CF01LegacySourceCorrespondence := by
  intro n b d u v
  change LegacyReadback.PairSource n b d u v ↔ PairSource n b d u v
  exact readback_source_correspondence n b d u v

theorem legacy_count_correspondence : CF01LegacyCountCorrespondence := by
  intro N
  change LegacyReadback.pairCount N = PairCount N
  exact readback_count_correspondence N

end P0365Subquarter
