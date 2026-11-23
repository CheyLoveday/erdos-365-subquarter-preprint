import PaperTargets.CanonicalSource
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Native-development port of canonical-source arithmetic. Normalisation and
uniqueness adapt `docs/research/2026-10-13-p0365-bound/CanonicalSources.lean`
(SHA-256 a03481f8a3dceb42eb478e2f274454dde4acd1a7fbf241922f2339fa87ca2f60).
The donor is not imported or modified. Standard Nat.Prime and the frozen
additive PairSource replace the old interface; no asymptotic claim is proved.
-/

namespace P0365Subquarter

set_option autoImplicit false

private theorem squarefree_dvd_square_base {b s : ℕ} (hb : Squarefree b) (hs : 0 < s)
    (hpow : Powerful (s ^ 2 * b)) : b ∣ s := by
  apply (Nat.factorization_le_iff_dvd hb.ne_zero hs.ne').mp
  intro p
  by_cases hp : p.Prime
  · by_cases hz : b.factorization p = 0
    · simp [hz]
    · have hpb : p ∣ b := (hp.dvd_iff_one_le_factorization hb.ne_zero).mpr (by omega)
      have hb1 := Nat.factorization_eq_one_of_squarefree hb hp hpb
      have hp2 := hpow.2 p hp (dvd_mul_of_dvd_right hpb (s ^ 2))
      have hh := (hp.pow_dvd_iff_le_factorization hpow.1.ne').mp hp2
      simp only [Nat.factorization_mul (pow_ne_zero 2 hs.ne') hb.ne_zero,
        Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hh
      omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem powerful_normal_form_exists {n : ℕ} (hn : Powerful n) :
    ∃ b u : ℕ, 0 < b ∧ 0 < u ∧ Squarefree b ∧ n = b ^ 3 * u ^ 2 := by
  obtain ⟨b, s, hb, hs, heq, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn.1
  have hdiv : b ∣ s := squarefree_dvd_square_base hsq hs (heq ▸ hn)
  obtain ⟨u, hu⟩ := hdiv
  refine ⟨b, u, hb, ?_, hsq, ?_⟩
  · by_contra h
    have : u = 0 := by omega
    simp [this] at hu
    omega
  · rw [← heq, hu]
    ring

theorem cube_square_powerful : CF01CubeSquarePowerful := by
  intro b u hb hu
  refine ⟨mul_pos (pow_pos hb 3) (pow_pos hu 2), ?_⟩
  intro p hp hdiv
  rcases hp.dvd_mul.mp hdiv with hbdiv | hudiv
  · obtain ⟨w, rfl⟩ := hp.dvd_of_dvd_pow hbdiv
    exact ⟨p * w ^ 3 * u ^ 2, by ring⟩
  · obtain ⟨w, rfl⟩ := hp.dvd_of_dvd_pow hudiv
    exact ⟨b ^ 3 * w ^ 2, by ring⟩

theorem normal_form_unique : CF01NormalFormUnique := by
  intro b u c v hb hc hu hv h
  have hcoords (p : ℕ) :
      b.factorization p = c.factorization p ∧ u.factorization p = v.factorization p := by
    have he := congrArg (fun n : ℕ => n.factorization p) h
    simp only [Nat.factorization_mul (pow_ne_zero 3 hb.ne_zero) (pow_ne_zero 2 hu.ne'),
      Nat.factorization_mul (pow_ne_zero 3 hc.ne_zero) (pow_ne_zero 2 hv.ne'),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he
    have hb1 := hb.natFactorization_le_one p
    have hc1 := hc.natFactorization_le_one p
    omega
  exact ⟨Nat.eq_of_factorization_eq hb.ne_zero hc.ne_zero (fun p => (hcoords p).1),
    Nat.eq_of_factorization_eq hu.ne' hv.ne' (fun p => (hcoords p).2)⟩

theorem normal_form : CF01NormalForm := by
  intro n
  constructor
  · intro hn
    obtain ⟨b, u, hb, hu, hsq, heq⟩ := powerful_normal_form_exists hn
    refine ⟨(b, u), ⟨hb, hu, hsq, heq⟩, ?_⟩
    rintro ⟨c, v⟩ ⟨_, hv, hc, heq'⟩
    obtain ⟨hbc, huv⟩ := normal_form_unique c v b u hc hsq hv hu (heq'.symm.trans heq)
    exact Prod.ext hbc huv
  · rintro ⟨⟨b, u⟩, ⟨hb, hu, _, heq⟩, _⟩
    rw [heq]
    exact cube_square_powerful b u hb hu

theorem pair_source_equivalence : CF01PairSourceEquivalence := by
  intro n
  constructor
  · rintro ⟨hn, hn1⟩
    obtain ⟨b, u, hb, hu, hsb, heq⟩ := powerful_normal_form_exists hn
    obtain ⟨d, v, hd, hv, hsd, heq'⟩ := powerful_normal_form_exists hn1
    exact ⟨b, d, u, v, hb, hd, hu, hv, hsb, hsd, heq, by omega⟩
  · rintro ⟨b, d, u, v, hb, hd, hu, hv, _, _, heq, heq'⟩
    refine ⟨heq ▸ cube_square_powerful b u hb hu, ?_⟩
    have hn : n + 1 = d ^ 3 * v ^ 2 := by omega
    exact hn ▸ cube_square_powerful d v hd hv

theorem pair_source_unique : CF01PairSourceUnique := by
  intro n b d u v b' d' u' v' h h'
  rcases h with ⟨_, _, hu, hv, hb, hd, heq, heq1⟩
  rcases h' with ⟨_, _, hu', hv', hb', hd', heq', heq1'⟩
  obtain ⟨hbb, huu⟩ := normal_form_unique b u b' u' hb hb' hu hu'
    (heq.symm.trans heq')
  obtain ⟨hdd, hvv⟩ := normal_form_unique d v d' v' hd hd' hv hv' (by omega)
  exact ⟨hbb, hdd, huu, hvv⟩

theorem additive_and_integer_source : CF01AdditiveAndIntegerSource := by
  intro n b d u v h
  rcases h with ⟨hb, hd, hu, hv, hsb, hsd, heq, hs⟩
  refine ⟨heq ▸ mul_pos (pow_pos hb 3) (pow_pos hu 2), by omega, ?_⟩
  have hi : (d : ℤ) ^ 3 * (v : ℤ) ^ 2 = (b : ℤ) ^ 3 * (u : ℤ) ^ 2 + 1 := by
    exact_mod_cast hs
  omega

theorem cross_endpoint_coprime : CF01CrossEndpointCoprime := by
  intro n b d u v h
  rcases h with ⟨_, _, _, _, _, _, heq, hs⟩
  have hn : n + 1 = d ^ 3 * v ^ 2 := by omega
  apply Nat.Coprime.of_dvd
    (heq ▸ (show b * u ∣ b ^ 3 * u ^ 2 from ⟨b ^ 2 * u, by ring⟩))
    (hn ▸ (show d * v ∣ d ^ 3 * v ^ 2 from ⟨d ^ 2 * v, by ring⟩))
  simp

theorem primitive_ratios : CF01PrimitiveRatios := by
  intro n b d u v h
  have hcross := cross_endpoint_coprime n b d u v h
  have hbd : Nat.Coprime b d := Nat.Coprime.of_dvd (dvd_mul_right b u)
    (dvd_mul_right d v) hcross
  have huv : Nat.Coprime u v := Nat.Coprime.of_dvd (dvd_mul_left u b)
    (dvd_mul_left v d) hcross
  exact ⟨hbd, huv.symm, Nat.squarefree_mul_iff.mpr ⟨hbd, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩

theorem source_bounds : CF01SourceBounds := by
  intro n b d u v h
  rcases h with ⟨hb, hd, hu, hv, _, _, heq, hs⟩
  have hn : n + 1 = d ^ 3 * v ^ 2 := by omega
  have bound (a c : ℕ) (hc : 0 < c) : a ≤ a * c := by
    calc a = a * 1 := by simp
         _ ≤ a * c := Nat.mul_le_mul_left _ hc
  refine ⟨heq ▸ bound (b ^ 3) (u ^ 2) (pow_pos hu 2), ?_,
    hn ▸ bound (d ^ 3) (v ^ 2) (pow_pos hv 2), ?_⟩
  · rw [heq, mul_comm]
    exact bound (u ^ 2) (b ^ 3) (pow_pos hb 3)
  · rw [hn, mul_comm]
    exact bound (v ^ 2) (d ^ 3) (pow_pos hd 3)

theorem cutoff_source_bounds : CF01CutoffSourceBounds := by
  intro N n b d u v h hN
  have hs := source_bounds n b d u v h
  have hb := Nat.le_self_pow (by decide : 3 ≠ 0) b
  have hd := Nat.le_self_pow (by decide : 3 ≠ 0) d
  have hu := Nat.le_self_pow (by decide : 2 ≠ 0) u
  have hv := Nat.le_self_pow (by decide : 2 ≠ 0) v
  exact ⟨(additive_and_integer_source n b d u v h).1, hN, by omega, by omega,
    by omega, by omega⟩

private theorem primitive_ratio_injective {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d)
    (hr : (a : ℚ) / b = (c : ℚ) / d) : a = c ∧ b = d := by
  have hi := Rat.div_int_inj (by exact_mod_cast hb : (0 : ℤ) < b)
    (by exact_mod_cast hd : (0 : ℤ) < d)
    (by simpa using hab : Nat.Coprime (a : ℤ).natAbs (b : ℤ).natAbs)
    (by simpa using hcd : Nat.Coprime (c : ℤ).natAbs (d : ℤ).natAbs)
    (by simpa using hr : ((a : ℤ) : ℚ) / (b : ℤ) = ((c : ℤ) : ℚ) / (d : ℤ))
  exact ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩

theorem source_ratio_coordinate_injection : CF01SourceRatioCoordinateInjection := by
  intro n m b d u v b' d' u' v' h h' hr
  have hp := primitive_ratios n b d u v h
  have hp' := primitive_ratios m b' d' u' v' h'
  have hbd := primitive_ratio_injective h.2.1 h'.2.1 hp.1 hp'.1
    (congrArg Prod.fst hr)
  have hvu := primitive_ratio_injective h.2.2.1 h'.2.2.1 hp.2.1 hp'.2.1
    (congrArg Prod.snd hr)
  have heq := h.2.2.2.2.2.2.1
  have heq' := h'.2.2.2.2.2.2.1
  refine ⟨?_, hbd.1, hbd.2, hvu.2, hvu.1⟩
  calc n = b ^ 3 * u ^ 2 := heq
       _ = b' ^ 3 * u' ^ 2 := by rw [hbd.1, hvu.2]
       _ = m := heq'.symm

theorem source_ratio_injection : CF01SourceRatioInjection := by
  intro n m b d u v b' d' u' v' h h' hr
  exact (source_ratio_coordinate_injection n m b d u v b' d' u' v' h h' hr).1

theorem readback_prime_correspondence : CF01ReadbackPrimeCorrespondence := by
  intro p
  exact Nat.prime_def.symm

theorem readback_powerful_correspondence : CF01ReadbackPowerfulCorrespondence := by
  intro n
  constructor
  · rintro ⟨hn, hp⟩
    exact ⟨hn, fun p hprime hd => hp p ((readback_prime_correspondence p).mpr hprime) hd⟩
  · rintro ⟨hn, hp⟩
    exact ⟨hn, fun p hprime hd => hp p ((readback_prime_correspondence p).mp hprime) hd⟩

theorem readback_source_correspondence : CF01ReadbackSourceCorrespondence := by
  intro n b d u v
  constructor
  · rintro ⟨hb, hd, hu, hv, hsb, hsd, hn, hs⟩
    exact ⟨hb, hd, hu, hv, hsb, hsd, hn, by omega⟩
  · rintro ⟨hb, hd, hu, hv, hsb, hsd, hn, hs⟩
    exact ⟨hb, hd, hu, hv, hsb, hsd, hn, by omega⟩

theorem readback_count_correspondence : CF01ReadbackCountCorrespondence := by
  classical
  intro N
  unfold LegacyReadback.pairCount PairCount
  have hp (n : ℕ) : LegacyReadback.Powerful n ↔ Powerful n :=
    readback_powerful_correspondence n
  simp_rw [hp]
  rw [← List.toFinset_card_of_nodup
    ((show (List.range (N + 1)).Nodup from List.nodup_range).filter _)]
  congr 1
  ext n
  simp

theorem count_source_correspondence : CF01CountSourceCorrespondence := by
  classical
  intro N
  unfold PairCount
  congr 1
  apply Finset.filter_congr
  intro n hn
  exact pair_source_equivalence n

theorem zero_not_powerful : ¬ Powerful 0 := by
  intro h
  exact Nat.not_lt_zero 0 h.1

theorem one_powerful : Powerful 1 := by
  simpa using cube_square_powerful 1 1 (by decide) (by decide)

theorem two_not_powerful : ¬ Powerful 2 := by
  intro h
  have hh := h.2 2 Nat.prime_two (dvd_refl 2)
  norm_num at hh

theorem count_empty_boundary : CF01CountEmptyBoundary := by
  classical
  simp [CF01CountEmptyBoundary, PairCount, Finset.range_add_one,
    zero_not_powerful, one_powerful, two_not_powerful]

theorem endpoint_overlap_controls : CF01EndpointAndOverlapControls := by
  refine ⟨zero_not_powerful, one_powerful, ?_, ?_, ?_, by decide, by decide,
    ?_, ?_, by decide, ?_⟩
  · simpa using cube_square_powerful 1 4 (by decide) (by decide)
  · simpa using cube_square_powerful 1 9 (by decide) (by decide)
  · simpa using cube_square_powerful 2 2 (by decide) (by decide)
  · norm_num [PairSource, Nat.prime_two.squarefree]
  · norm_num [PairSource, Nat.prime_two.squarefree]
  · have hp : Squarefree (23 : ℕ) := (by decide : Nat.Prime 23).squarefree
    norm_num [PairSource, hp, Nat.prime_two.squarefree]

theorem noncanonical_control : CF01NoncanonicalControl := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact (Nat.squarefree_iff_prime_squarefree.mp h) 2 Nat.prime_two (by decide)

end P0365Subquarter
