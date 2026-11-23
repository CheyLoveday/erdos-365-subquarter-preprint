import PaperTargets.CutoffControls
import PaperProofs.CanonicalSource

namespace P0365Subquarter

set_option autoImplicit false

private theorem bad_prime_excludes {n p : ℕ} (hp : Nat.Prime p)
    (hd : p ∣ n) (hbad : ¬ p ^ 2 ∣ n) : ¬ Powerful n :=
  fun h => hbad (h.2 p hp hd)

theorem first_cutoffs : CF01FirstCutoffs := by
  classical
  have h3 : ¬ Powerful 3 := bad_prime_excludes (by decide : Nat.Prime 3)
    (by decide) (by decide)
  have h5 : ¬ Powerful 5 := bad_prime_excludes (by decide : Nat.Prime 5)
    (by decide) (by decide)
  have h6 : ¬ Powerful 6 := bad_prime_excludes Nat.prime_two (by decide) (by decide)
  have h7 : ¬ Powerful 7 := bad_prime_excludes (by decide : Nat.Prime 7)
    (by decide) (by decide)
  have h8 : Powerful 8 := by
    simpa using cube_square_powerful 2 1 (by decide) (by decide)
  have h9 : Powerful 9 := by
    simpa using cube_square_powerful 1 3 (by decide) (by decide)
  norm_num [CF01FirstCutoffs, PairCount, Finset.range_add_one,
    zero_not_powerful, one_powerful, two_not_powerful, h3, h5, h6, h7, h8, h9]
  simp [Finset.filter_insert, zero_not_powerful, one_powerful,
    two_not_powerful, h3, h5, h6, h7, h8, h9]

end P0365Subquarter
