import PaperTargets.ResultantDivisors
import PaperProofs.LowFactorLevels

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Every divisor of a product is a product of one divisor of each factor.
The surjection, rather than uniqueness of such a decomposition, suffices. -/
theorem divisor_card_mul : CF15DivisorCardMul := by
  classical
  intro m n
  by_cases hm : m=0
  · simp [hm,divisorCount]
  by_cases hn : n=0
  · simp [hn,divisorCount]
  have hsub : (m*n).divisors ⊆ (m.divisors.product n.divisors).image (fun p : ℕ×ℕ => p.1*p.2) := by
    intro a ha
    obtain ⟨b,c,hb,hc,he⟩ := exists_dvd_and_dvd_of_dvd_mul (Nat.dvd_of_mem_divisors ha)
    exact Finset.mem_image.mpr ⟨(b,c),Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hb,hm⟩,Nat.mem_divisors.mpr ⟨hc,hn⟩⟩,he.symm⟩
  have hc : (m.divisors.product n.divisors).card=m.divisors.card*n.divisors.card :=
    Finset.card_product _ _
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans_eq hc)

/-- Includes exponent zero and base zero, with the usual natural 0^0=1. -/
theorem divisor_card_pow : CF15DivisorCardPow := by
  intro n k
  induction k with
  | zero => simp [divisorCount]
  | succ k ih =>
    calc
      divisorCount (n^(k+1))=divisorCount (n^k*n) := by rw [pow_succ]
      _ ≤ divisorCount (n^k)*divisorCount n := divisor_card_mul _ _
      _ ≤ (divisorCount n)^k*divisorCount n := Nat.mul_le_mul_right _ ih
      _ = _ := (pow_succ _ _).symm

/-- The upper modulus must be nonzero because divisors0 is empty. -/
theorem divisor_card_dvd : CF15DivisorCardDvd := by
  intro m n hn hmn
  apply Finset.card_le_card
  intro a ha
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors ha).trans hmn,hn⟩

/-- Passing through g^ell changes valuations, but introduces no new primes. -/
theorem prime_support_level : CF15PrimeSupportLevel := by
  intro R g h ℓ hR hg hh
  have hgn : g ≠ 0 := by intro hz; exact hR (zero_dvd_iff.mp (by simpa [hz] using hg))
  have hgp : g^ℓ ≠ 0 := pow_ne_zero _ hgn
  have hhn : h ≠ 0 := by intro hz; exact hgp (zero_dvd_iff.mp (by simpa [hz] using hh))
  refine ⟨hgn,hhn,?_⟩
  by_cases he : ℓ=0
  · have hh1 : h=1 := Nat.dvd_one.mp (by simpa [he] using hh)
    simp [hh1]
  · have hs := Nat.primeFactors_mono (hh.trans (pow_dvd_pow_of_dvd hg ℓ)) (pow_ne_zero ℓ hR)
    simpa only [Nat.primeFactors_pow R he] using hs

/-- Each distinct prime contributes at least two divisors. -/
theorem support_divisor_lower : CF15SupportDivisorLower := by
  intro R hR
  change 2^R.primeFactors.card ≤ R.divisors.card
  rw [Nat.card_divisors hR]
  calc
    _ = ∏ p ∈ R.primeFactors, 2 := by simp
    _ ≤ _ := Finset.prod_le_prod (fun p hp => by
      have hpos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hR (Nat.dvd_of_mem_primeFactors hp)
      omega)

private theorem divisor_count_one_le (R : ℕ) (hR : R ≠ 0) : 1 ≤ divisorCount R := by
  exact Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hR⟩

/-- All degree/level charges come from the one actual resultant support. -/
theorem resultant_level_charges : CF15ResultantLevelCharges := by
  intro R g h ℓ hR hg hh he
  obtain ⟨hgn,hhn,hs⟩ := prime_support_level R g h ℓ hR hg hh
  have hτR := divisor_count_one_le R hR
  have hτg := divisor_card_dvd g R hR hg
  have hτh : divisorCount h ≤ (divisorCount R)^3 := by
    calc
      _ ≤ divisorCount (g^ℓ) := divisor_card_dvd h (g^ℓ) (pow_ne_zero _ hgn) hh
      _ ≤ (divisorCount g)^ℓ := divisor_card_pow g ℓ
      _ ≤ (divisorCount R)^ℓ := Nat.pow_le_pow_left hτg ℓ
      _ ≤ _ := pow_le_pow_right₀ hτR he
  refine ⟨hτh,?_,?_⟩
  · intro d hd
    have hw : primeSupportCount h ≤ primeSupportCount R := Finset.card_le_card hs
    calc
      _ ≤ 16^(primeSupportCount h) := Nat.pow_le_pow_left (by omega) _
      _ ≤ 16^(primeSupportCount R) := pow_le_pow_right₀ (by decide) hw
      _ = (2^(primeSupportCount R))^4 := by
        change (2^4)^(primeSupportCount R)=(2^(primeSupportCount R))^4
        rw [← pow_mul,← pow_mul,Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_left (support_divisor_lower R hR) 4
  · calc
      _ ≤ 16*((divisorCount R)^3)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hτh 2)
      _ = _ := by rw [← pow_mul]

/-- The positive gcd/divisor inventory costs powers1+3+4 of tau(R).
Signs and the fixed coefficient in the precise Thue input are charged later. -/
theorem thue_divisor_inventory : CF15ThueDivisorInventory := by
  classical
  intro R ℓ d hR he hd
  have hinner (g : ℕ) (hg : g ∈ R.divisors) :
      (∑ h ∈ (g^ℓ).divisors, d^(primeSupportCount h)) ≤ (divisorCount R)^7 := by
    have hgR := Nat.dvd_of_mem_divisors hg
    have hc := (resultant_level_charges R g (g^ℓ) ℓ hR hgR dvd_rfl he).1
    calc
      _ ≤ ∑ _h ∈ (g^ℓ).divisors, (divisorCount R)^4 := by
        apply Finset.sum_le_sum
        intro h hh
        exact (resultant_level_charges R g h ℓ hR hgR (Nat.dvd_of_mem_divisors hh) he).2.1 d hd
      _ = divisorCount (g^ℓ)*(divisorCount R)^4 := by simp [divisorCount]
      _ ≤ (divisorCount R)^3*(divisorCount R)^4 := Nat.mul_le_mul_right _ hc
      _ = _ := (pow_add _ 3 4).symm
  calc
    thueDivisorInventory R ℓ d ≤ ∑ _g ∈ R.divisors, (divisorCount R)^7 := Finset.sum_le_sum hinner
    _ = divisorCount R*(divisorCount R)^7 := by simp [divisorCount]
    _ = (divisorCount R)^8 := by rw [show 8=1+7 by rfl,pow_add,pow_one]

/-- Instantiate the whole inventory using the full, padded homogeneous
resultant of the actual bounded graph, before choosing any level labels. -/
theorem actual_graph_divisor_inventory : CF15ActualGraphDivisorInventory := by
  intro X D A B hX hgraph hr
  obtain ⟨hR,hheight,_⟩ := actual_mixed_resultant X D A B hX hgraph hr
  have hn : (fullGraphResultant A B).natAbs ≠ 0 := by
    intro hz
    exact hR (Int.natAbs_eq_zero.mp hz)
  refine ⟨hn,?_,?_⟩
  · rw [Nat.cast_natAbs,Int.cast_abs]
    exact hheight
  · intro ℓ d he hd
    exact thue_divisor_inventory _ ℓ d hn he hd

end
end P0365Subquarter
