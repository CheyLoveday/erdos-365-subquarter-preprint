import PaperTargets.PrimeAssignment
import PaperProofs.CanonicalSource
import PaperProofs.RoundedProfiles
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Floor.Semifield

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
open MvPolynomial

private theorem exponent_le (G : SourcePolynomial) (D : ℕ) (hD : G.totalDegree ≤ D)
    (e : Fin 2 →₀ ℕ) (he : e ∈ G.support) (i : Fin 2) : e i ≤ D :=
  (monomial_le_degreeOf i he).trans ((degreeOf_le_totalDegree G i).trans hD)

private theorem clear_power {k : Type*} [Field k] (b d : k) (D a : ℕ)
    (hd : d ≠ 0) (ha : a ≤ D) :
    b ^ a * d ^ (D-a) = d^D * (b/d)^a := by
  have hp : d^D = d^a * d^(D-a) := by rw [← pow_add, Nat.add_sub_of_le ha]
  rw [hp, div_pow]
  field_simp

private theorem cleared_field {k : Type*} [Field k] (G : SourcePolynomial)
    (D b d u v : ℕ) (hD : G.totalDegree ≤ D)
    (hd : (d : k) ≠ 0) (hu : (u : k) ≠ 0) :
    (clearedValue G D b d u v : k) =
      (d : k)^D * (u : k)^D * polynomialValue G (![(b : k)/d, (v : k)/u]) := by
  classical
  simp only [clearedValue, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    polynomialValue, eval₂_eq', Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Int.coe_castRingHom]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have h0 := clear_power (b : k) d D (e 0) hd (exponent_le G D hD e he 0)
  have h1 := clear_power (v : k) u D (e 1) hu (exponent_le G D hD e he 1)
  calc
    _ = (G.coeff e : k) * ((b : k)^e 0 * d^(D-e 0)) *
      ((v : k)^e 1 * u^(D-e 1)) := by ring
    _ = _ := by rw [h0, h1]; ring

theorem cleared_identity : CF07ClearedIdentity := by
  intro G D b d u v hD hd hu
  exact cleared_field G D b d u v hD (by exact_mod_cast hd.ne') (by exact_mod_cast hu.ne')

private theorem partial_degree (F : SourcePolynomial) (D : ℕ)
    (hD : F.totalDegree ≤ D) (i : Fin 2) : (pderiv i F).totalDegree ≤ D := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro e he
  have hc : F.coeff (e + Finsupp.single i 1) ≠ 0 := by
    have hh := mem_support_iff.mp he
    rw [coeff_pderiv] at hh
    exact (mul_ne_zero_iff.mp hh).1
  have h := le_totalDegree (mem_support_iff.mpr hc)
  have hle : e.sum (fun _ a => a) ≤ (e + Finsupp.single i 1).sum (fun _ a => a) := by
    rw [Finsupp.sum_fintype e (fun _ a => a) (fun _ => rfl),
      Finsupp.sum_fintype (e + Finsupp.single i 1) (fun _ a => a) (fun _ => rfl)]
    simp only [Finsupp.add_apply]
    exact Finset.sum_le_sum (fun j _ => Nat.le_add_right _ _)
  exact hle.trans (h.trans hD)

private theorem support_card (G : SourcePolynomial) (D : ℕ) (hD : G.totalDegree ≤ D) :
    G.support.card ≤ (D+1)^2 := by
  classical
  have h := Finset.card_le_card_of_injOn (fun e : Fin 2 →₀ ℕ => (e 0, e 1))
    (s := G.support) (t := (Finset.range (D+1)) ×ˢ (Finset.range (D+1)))
    (by
      intro e he
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (exponent_le G D hD e he 0)),
        Finset.mem_range.mpr (Nat.lt_succ_of_le (exponent_le G D hD e he 1))⟩)
    (by
      intro e he f hf hef
      ext i
      fin_cases i
      · exact congrArg Prod.fst hef
      · exact congrArg Prod.snd hef)
  simpa [pow_two] using h

private theorem partial_coefficient (F : SourcePolynomial) (D : ℕ) (B : ℝ)
    (hD : F.totalDegree ≤ D) (hB : ∀ e, |(F.coeff e : ℝ)| ≤ B)
    (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    |((pderiv i F).coeff e : ℝ)| ≤ (D+1) * B := by
  have hB0 : 0 ≤ B := (abs_nonneg (F.coeff 0 : ℝ)).trans (hB 0)
  by_cases hc : F.coeff (e + Finsupp.single i 1) = 0
  · simp [coeff_pderiv, hc, mul_nonneg (show (0:ℝ) ≤ D+1 by positivity) hB0]
  have he := exponent_le F D hD (e + Finsupp.single i 1) (mem_support_iff.mpr hc) i
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at he
  rw [coeff_pderiv]
  push_cast
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (e i : ℝ)+1 by positivity)]
  calc
    _ ≤ B * (D+1) := mul_le_mul (hB _) (by exact_mod_cast (he.trans (Nat.le_succ D)))
      (by positivity) hB0
    _ = _ := by ring

private theorem cleared_bound (G : SourcePolynomial) (D b d u v : ℕ) (B Y : ℝ)
    (hD : G.totalDegree ≤ D) (hB : ∀ e, |(G.coeff e : ℝ)| ≤ B)
    (hY : 1 ≤ Y) (hb : (b : ℝ) ≤ Y) (hd : (d : ℝ) ≤ Y)
    (hu : (u : ℝ) ≤ Y) (hv : (v : ℝ) ≤ Y) :
    |(clearedValue G D b d u v : ℝ)| ≤ (D+1)^2 * B * Y^(2*D) := by
  classical
  have hB0 : 0 ≤ B := (abs_nonneg (G.coeff 0 : ℝ)).trans (hB 0)
  have hY0 : 0 ≤ Y := by linarith
  simp only [clearedValue, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  calc
    _ ≤ ∑ e ∈ G.support, |(G.coeff e : ℝ) * b^e 0 * d^(D-e 0) * v^e 1 * u^(D-e 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ G.support, B * Y^(2*D) := by
      apply Finset.sum_le_sum
      intro e he
      have h0 : (b : ℝ)^e 0 * d^(D-e 0) ≤ Y^D := by
        calc
          _ ≤ Y^e 0 * Y^(D-e 0) := by gcongr
          _ = _ := by rw [← pow_add, Nat.add_sub_of_le (exponent_le G D hD e he 0)]
      have h1 : (v : ℝ)^e 1 * u^(D-e 1) ≤ Y^D := by
        calc
          _ ≤ Y^e 1 * Y^(D-e 1) := by gcongr
          _ = _ := by rw [← pow_add, Nat.add_sub_of_le (exponent_le G D hD e he 1)]
      rw [show (G.coeff e : ℝ) * b^e 0 * d^(D-e 0) * v^e 1 * u^(D-e 1) =
        (G.coeff e : ℝ) * ((b : ℝ)^e 0 * d^(D-e 0)) * ((v : ℝ)^e 1 * u^(D-e 1)) by ring]
      rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ (b : ℝ)^e 0 * d^(D-e 0) by positivity),
        abs_of_nonneg (show 0 ≤ (v : ℝ)^e 1 * u^(D-e 1) by positivity)]
      calc
        _ ≤ B * Y^D * Y^D := by gcongr; exact hB e
        _ = _ := by rw [mul_assoc, ← pow_add]; congr 2; omega
    _ = (G.support.card : ℝ) * (B * Y^(2*D)) := by simp
    _ ≤ _ := by
      have hc : (G.support.card : ℝ) ≤ ((D+1 : ℕ)^2 : ℝ) := by exact_mod_cast support_card G D hD
      push_cast at hc
      calc
        _ ≤ (D+1)^2 * (B * Y^(2*D)) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := by ring

private theorem selected_nonzero (F : SourcePolynomial) (D b d u v : ℕ)
    (hD : F.totalDegree ≤ D) (hd : 0 < d) (hu : 0 < u)
    (hns : nonsingularSource F b d u v) : selectedPartial F D b d u v ≠ 0 := by
  have hex : ∃ i : Fin 2, clearedPartial F D b d u v i ≠ 0 := by
    obtain ⟨i, hi⟩ := hns.2
    refine ⟨i, ?_⟩
    intro hc
    have hh := cleared_identity (pderiv i F) D b d u v (partial_degree F D hD i) hd hu
    change (clearedPartial F D b d u v i : ℚ) = _ at hh
    rw [hc, Int.cast_zero] at hh
    have hdu : (d : ℚ)^D * (u : ℚ)^D ≠ 0 := by positivity
    exact hi ((mul_eq_zero.mp hh.symm).resolve_left hdu)
  by_cases h0 : clearedPartial F D b d u v 0 ≠ 0
  · simp [selectedPartial, h0]
  · obtain ⟨i, hi⟩ := hex
    fin_cases i
    · exact (hi (not_ne_iff.mp h0)).elim
    · simpa [selectedPartial, h0] using hi

private theorem witness_nonzero (F : SourcePolynomial) (D b d u v : ℕ)
    (hD : F.totalDegree ≤ D) (hd : 0 < d) (hu : 0 < u)
    (hns : nonsingularSource F b d u v) : sourceWitness F D b d u v ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hd.ne') (by exact_mod_cast hu.ne'))
    (selected_nonzero F D b d u v hD hd hu hns)

private theorem bad_prime_divides (F : SourcePolynomial) (D b d u v p : ℕ)
    (hD : F.totalDegree ≤ D) (hd : 0 < d) (hu : 0 < u)
    (hcurve : polynomialValue F (sourcePoint b d u v) = 0) (hp : p.Prime) :
    ¬ goodSourcePrime F b d u v p → (p : ℤ) ∣ sourceWitness F D b d u v := by
  classical
  contrapose!
  intro hn
  let : Fact p.Prime := ⟨hp⟩
  have hN : (sourceWitness F D b d u v : ZMod p) ≠ 0 := by
    exact fun hz => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  have hdp : (d : ZMod p) ≠ 0 := fun hz => hN (by simp [sourceWitness, hz])
  have hup : (u : ZMod p) ≠ 0 := fun hz => hN (by simp [sourceWitness, hz])
  have hvp : (selectedPartial F D b d u v : ZMod p) ≠ 0 :=
    fun hz => hN (by simp [sourceWitness, hz])
  have hden : ¬ p ∣ d*u := by
    intro h
    have hz := (ZMod.natCast_eq_zero_iff (d*u) p).mpr h
    rw [Nat.cast_mul] at hz
    exact (mul_ne_zero hdp hup) hz
  have hclear0 : clearedValue F D b d u v = 0 := by
    have hh := cleared_identity F D b d u v hD hd hu
    rw [hcurve, mul_zero] at hh
    exact_mod_cast hh
  have hF : polynomialValue F (sourceReduction b d u v p) = 0 := by
    have hh := cleared_field (k := ZMod p) F D b d u v hD hdp hup
    rw [hclear0, Int.cast_zero] at hh
    have hdu : (d : ZMod p)^D * (u : ZMod p)^D ≠ 0 := by positivity
    have hz := (mul_eq_zero.mp hh.symm).resolve_left hdu
    simpa only [sourceReduction, div_eq_mul_inv] using hz
  have hex : ∃ i : Fin 2, (clearedPartial F D b d u v i : ZMod p) ≠ 0 := by
    by_cases h0 : clearedPartial F D b d u v 0 ≠ 0
    · exact ⟨0, by simpa [selectedPartial, h0] using hvp⟩
    · exact ⟨1, by simpa [selectedPartial, h0] using hvp⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨hden, hF, i, ?_⟩
  intro hz
  have hh := cleared_field (k := ZMod p) (pderiv i F) D b d u v
    (partial_degree F D hD i) hdp hup
  change (clearedPartial F D b d u v i : ZMod p) = _ at hh
  simp only [div_eq_mul_inv] at hh
  change (clearedPartial F D b d u v i : ZMod p) =
    (d : ZMod p)^D * (u : ZMod p)^D * polynomialValue (pderiv i F)
      (sourceReduction b d u v p) at hh
  rw [hz, mul_zero] at hh
  exact hi hh

private theorem witness_bound (F : SourcePolynomial) (D n b d u v : ℕ) (x B : ℝ)
    (hD : F.totalDegree ≤ D) (hB : ∀ e, |(F.coeff e : ℝ)| ≤ B)
    (hs : PairSource n b d u v) (hn : (n : ℝ) ≤ x) (hx : 1 ≤ x) :
    |(sourceWitness F D b d u v : ℝ)| ≤
      (D+1)^3 * B * (2*x)^(2*D+2) := by
  have hB0 : 0 ≤ B := (abs_nonneg (F.coeff 0 : ℝ)).trans (hB 0)
  obtain ⟨_, _, hb, hd, hu, hv⟩ := cutoff_source_bounds n n b d u v hs le_rfl
  have hcoords : (b : ℝ) ≤ 2*x ∧ (d : ℝ) ≤ 2*x ∧
      (u : ℝ) ≤ 2*x ∧ (v : ℝ) ≤ 2*x := by
    have hb' : (b : ℝ) ≤ n+1 := by exact_mod_cast hb
    have hd' : (d : ℝ) ≤ n+1 := by exact_mod_cast hd
    have hu' : (u : ℝ) ≤ n+1 := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ n+1 := by exact_mod_cast hv
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hpart : ∀ i, |(clearedPartial F D b d u v i : ℝ)| ≤
      (D+1)^2 * ((D+1)*B) * (2*x)^(2*D) := by
    intro i
    exact cleared_bound (pderiv i F) D b d u v ((D+1)*B) (2*x)
      (partial_degree F D hD i) (partial_coefficient F D B hD hB i)
      (by linarith) hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2
  have hsel : |(selectedPartial F D b d u v : ℝ)| ≤
      (D+1)^2 * ((D+1)*B) * (2*x)^(2*D) := by
    unfold selectedPartial
    split_ifs <;> exact hpart _
  simp only [sourceWitness, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg d : (0:ℝ) ≤ d), abs_of_nonneg (Nat.cast_nonneg u : (0:ℝ) ≤ u)]
  calc
    _ ≤ (2*x) * (2*x) * ((D+1)^2 * ((D+1)*B) * (2*x)^(2*D)) := by
      gcongr
      · exact hcoords.2.1
      · exact hcoords.2.2.1
    _ = _ := by rw [pow_add, pow_two]; ring

theorem actual_source_witness : CF07ActualSourceWitness := by
  intro D H C hH hC
  let A : ℝ := (D+1)^3 * C * 2^(2*D+2)
  refine ⟨max 2 (A+1), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x hx F hD hcoeff n b d u v hs hn hns
  have hx1 : 1 ≤ x := by have := (le_max_left 2 (A+1)).trans hx; linarith
  have hAx : A < x := by have := (le_max_right 2 (A+1)).trans hx; linarith
  have hpositive : 0 < x := by linarith
  have hpow : 0 < x^(H + 2*(D : ℝ)+2) := Real.rpow_pos_of_pos hpositive _
  refine ⟨witness_nonzero F D b d u v hD hs.2.1 hs.2.2.1 hns, ?_, ?_⟩
  · calc
      _ ≤ (D+1)^3 * (C*x^H) * (2*x)^(2*D+2) :=
        witness_bound F D n b d u v x (C*x^H) hD hcoeff hs hn hx1
      _ = A * x^(H + 2*(D : ℝ)+2) := by
        dsimp [A]
        have he : H + 2*(D : ℝ)+2 = H + ((2*D+2 : ℕ) : ℝ) := by push_cast; ring
        rw [mul_pow, he, Real.rpow_add hpositive, Real.rpow_natCast]
        ring
      _ < x * x^(H + 2*(D : ℝ)+2) := mul_lt_mul_of_pos_right hAx hpow
      _ = x^(H + 2*(D : ℝ)+3) := by
        have he : H + 2*(D : ℝ)+3 = 1 + (H + 2*(D : ℝ)+2) := by ring
        conv_rhs => rw [he, Real.rpow_add hpositive, Real.rpow_one]
  · intro p hp hbad
    exact bad_prime_divides F D b d u v p hD hs.2.1 hs.2.2.1 hns.1 hp hbad

private theorem natural_prime_list (L a : ℕ) (ha : 0 < a) :
    ∃ s : Finset ℕ, s.card = L ∧
      ∀ p ∈ s, Nat.Prime p ∧ a < p ∧ p ≤ 2^L * a := by
  classical
  induction L with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ L ih =>
    obtain ⟨s, hc, hs⟩ := ih
    obtain ⟨p, hp, hlo, hup⟩ := Nat.exists_prime_lt_and_le_two_mul (2^L*a) (by positivity)
    have hn : p ∉ s := by intro h; exact (hs p h).2.2.not_gt hlo
    refine ⟨insert p s, by simp [hn, hc], ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · refine ⟨hp, lt_of_le_of_lt ?_ hlo, ?_⟩
      · nlinarith [(Nat.one_le_two_pow (n := L))]
      · simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hup
    · obtain ⟨hqprime, hqa, hqhi⟩ := hs q hq
      refine ⟨hqprime, hqa, hqhi.trans ?_⟩
      rw [pow_succ]
      nlinarith [Nat.zero_le (2^L*a)]

theorem bertrand_list : CF08BertrandList := by
  intro L R hR
  have ha : 0 < Nat.ceil R := by
    have : 0 < R := by linarith
    exact Nat.ceil_pos.mpr this
  obtain ⟨s, hc, hs⟩ := natural_prime_list L (Nat.ceil R) ha
  refine ⟨s, hc, ?_⟩
  intro p hp
  obtain ⟨hprime, hlo, hup⟩ := hs p hp
  refine ⟨hprime, (Nat.le_ceil R).trans (by exact_mod_cast hlo.le), ?_⟩
  calc
    (p : ℝ) ≤ (2 : ℝ)^L * (Nat.ceil R : ℝ) := by exact_mod_cast hup
    _ ≤ 2^L * (2*R) := mul_le_mul_of_nonneg_left (Nat.ceil_le_two_mul (by linarith)) (by positivity)
    _ = _ := by rw [pow_succ]; ring

private theorem first_assignment (F : SourcePolynomial) (D n b d u v : ℕ) (s : Finset ℕ)
    (hs : PairSource n b d u v) (hns : nonsingularSource F b d u v) (hD : F.totalDegree ≤ D)
    (hp : ∀ p ∈ s, Nat.Prime p)
    (hsize : (sourceWitness F D b d u v).natAbs < ∏ p ∈ s, p) :
    firstGoodPrime F b d u v s ∈ s ∧
      goodSourcePrime F b d u v (firstGoodPrime F b d u v s) ∧
      ∀ p ∈ s, goodSourcePrime F b d u v p → firstGoodPrime F b d u v s ≤ p := by
  classical
  have hex : (s.filter (goodSourcePrime F b d u v)).Nonempty := by
    by_contra! hempty
    have hall : ∀ p ∈ s, ¬ goodSourcePrime F b d u v p := by simpa using hempty
    have hdiv : (∏ p ∈ s, p) ∣ (sourceWitness F D b d u v).natAbs := by
      apply Finset.prod_dvd_of_isRelPrime
      · intro p hps q hqs hpq
        exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp p hps) (hp q hqs)).mpr hpq)
      · intro p hps
        exact Int.natCast_dvd.mp (bad_prime_divides F D b d u v p hD hs.2.1 hs.2.2.1 hns.1
          (hp p hps) (hall p hps))
    have hNpos : 0 < (sourceWitness F D b d u v).natAbs := by
      exact Int.natAbs_pos.mpr (witness_nonzero F D b d u v hD hs.2.1 hs.2.2.1 hns)
    exact (Nat.le_of_dvd hNpos hdiv).not_gt hsize
  have hmem := Finset.min'_mem _ hex
  have hgood := (Finset.mem_filter.mp hmem).2
  have hmins := (Finset.mem_filter.mp hmem).1
  simp only [firstGoodPrime, dite_eq_left hex]
  exact ⟨hmins, hgood, fun p hps hpg => Finset.min'_le _ p (Finset.mem_filter.mpr ⟨hps, hpg⟩)⟩

theorem first_good_assignment : CF08FirstGoodAssignment := first_assignment

private theorem smooth_card_bound (F : SourcePolynomial) (D p : ℕ)
    (hD : F.totalDegree ≤ D) (hp : Nat.Prime p) :
    (smoothResidues F p).card ≤ D*p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let G : MvPolynomial (Fin 2) (ZMod p) := MvPolynomial.map (Int.castRingHom (ZMod p)) F
  have hde : G.totalDegree ≤ D := by
    unfold totalDegree
    apply Finset.sup_le
    intro e he
    exact (le_totalDegree ((support_map_subset _ F) he)).trans hD
  have heval (z : Fin 2 → ZMod p) : polynomialValue F z = MvPolynomial.eval z G := by
    exact eval₂_eq_eval_map _ _ _
  by_cases hG : G = 0
  · have hempty : smoothResidues F p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      simp only [smoothResidues, dite_eq_right hp.ne_zero, Finset.mem_filter, Finset.mem_univ,
        true_and] at hz
      obtain ⟨i, hi⟩ := hz.2
      have hgder : MvPolynomial.map (Int.castRingHom (ZMod p)) (pderiv i F) = 0 := by
        rw [← pderiv_map]
        change pderiv i G = 0
        rw [hG]
        exact (pderiv i).map_zero
      apply hi
      rw [polynomialValue, eval₂_eq_eval_map, hgder]
      simp
    simp [hempty]
  · let Z : Finset (Fin 2 → ZMod p) := Finset.univ.filter (fun z => eval z G = 0)
    have hsub : smoothResidues F p ⊆ Z := by
      intro z hz
      simp only [smoothResidues, dite_eq_right hp.ne_zero, Finset.mem_filter, Finset.mem_univ,
        true_and] at hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (heval z) ▸ hz.1⟩
    have hsz := MvPolynomial.schwartz_zippel_totalDegree hG (Finset.univ : Finset (ZMod p))
    have hpi : (Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (ZMod p)))) = Finset.univ := by
      ext z
      simp
    rw [hpi] at hsz
    change (Z.card : ℚ≥0) / (Fintype.card (ZMod p) : ℚ≥0)^2 ≤
      (G.totalDegree : ℚ≥0) / Fintype.card (ZMod p) at hsz
    rw [ZMod.card p] at hsz
    have hp0 : (0 : ℚ≥0) < p := by exact_mod_cast hp.pos
    have hbound : (Z.card : ℚ≥0) ≤ (D*p : ℕ) := by
      have h1 := (div_le_div_iff₀ (pow_pos hp0 2) hp0).mp hsz
      have h2 : (Z.card : ℚ≥0) ≤ G.totalDegree * (p : ℚ≥0) := by
        apply (mul_le_mul_iff_right₀ hp0).mp
        calc
          (p : ℚ≥0) * Z.card = (Z.card : ℚ≥0) * p := by ring
          _ ≤ (G.totalDegree : ℚ≥0) * (p : ℚ≥0)^2 := h1
          _ = _ := by ring
      have hd' : (G.totalDegree : ℚ≥0) ≤ D := by exact_mod_cast hde
      calc
        _ ≤ G.totalDegree * (p : ℚ≥0) := h2
        _ ≤ (D : ℚ≥0) * p := mul_le_mul_of_nonneg_right hd' hp0.le
        _ = _ := by push_cast; rfl
    exact (Finset.card_le_card hsub).trans (by exact_mod_cast hbound)

theorem smooth_label_budget : CF08SmoothLabelBudget := by
  intro F D L R s hD hc hR hp
  calc
    _ ≤ ∑ p ∈ s, (D : ℝ) * (2^(L+1)*R) := by
      apply Finset.sum_le_sum
      intro p hps
      have hcard : ((smoothResidues F p).card : ℝ) ≤ (D : ℝ)*p := by
        exact_mod_cast smooth_card_bound F D p hD (hp p hps).1
      exact hcard.trans (mul_le_mul_of_nonneg_left (hp p hps).2 (Nat.cast_nonneg D))
    _ = _ := by simp [hc]; ring

theorem rounded_source_assignment : CF08RoundedSourceAssignment := by
  intro D H C δ hH hC hδ
  let K : ℝ := H + 2*(D : ℝ)+3
  have hrho : 0 < profileRho := by norm_num [profileRho]
  obtain ⟨L, hL⟩ := exists_nat_gt (K / profileRho)
  have hLK : K < profileRho * (L : ℝ) := by
    have h := (div_lt_iff₀ hrho).mp hL
    nlinarith
  have hLpos : 0 < L := by
    have hK : 0 ≤ K := by dsimp [K]; positivity
    by_contra h
    have : L = 0 := by omega
    simp [this] at hLK
    linarith
  obtain ⟨xw, hxw, hw⟩ := actual_source_witness D H C hH hC
  obtain ⟨xr, hxr, hr⟩ := rounded_prime_scale δ hδ
  refine ⟨L, max xw (max xr 2), hLpos, hxw.trans_le (le_max_left _ _), ?_⟩
  intro x hx ψ hψ0 hψ2
  have hxw' : xw ≤ x := (le_max_left _ _).trans hx
  have hxr' : xr ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx1 : 1 < x := hxw.trans_le hxw'
  have hx0 : 0 < x := by linarith
  have hrscale : x^profileRho ≤ roundedScale x ψ δ := hr x hxr' ψ hψ0 hψ2
  have hR : 1 ≤ roundedScale x ψ δ :=
    (Real.one_le_rpow hx1.le hrho.le).trans hrscale
  obtain ⟨s, hc, hs⟩ := bertrand_list L (roundedScale x ψ δ) hR
  refine ⟨s, hc, hs, ?_, ?_⟩
  · intro F hD hcoeff n b d u v hsource hn hns
    obtain ⟨hN, hNb, hbad⟩ := hw x hxw' F hD hcoeff n b d u v hsource hn hns
    have hprod : (x^profileRho)^L ≤ ∏ p ∈ s, (p : ℝ) := by
      rw [← hc, ← Finset.prod_const]
      apply Finset.prod_le_prod₀
      · intro p hp
        exact Real.rpow_nonneg hx0.le _
      · intro p hp
        exact hrscale.trans (hs p hp).2.1
    have hstrict : x^K < (x^profileRho)^L := by
      rw [← Real.rpow_mul_natCast hx0.le]
      exact Real.rpow_lt_rpow_of_exponent_lt hx1 hLK
    have hsize : (sourceWitness F D b d u v).natAbs < ∏ p ∈ s, p := by
      have hh : ((sourceWitness F D b d u v).natAbs : ℝ) < ∏ p ∈ s, (p : ℝ) := by
        simp only [Nat.cast_natAbs, Int.cast_abs]
        exact hNb.trans (hstrict.trans_le hprod)
      have hcast : ((sourceWitness F D b d u v).natAbs : ℝ) < ((∏ p ∈ s, p : ℕ) : ℝ) := by
        simpa only [Nat.cast_prod] using hh
      exact_mod_cast hcast
    obtain ⟨hmem, hgood, hfirst⟩ := first_good_assignment F D n b d u v s
      hsource hns hD (fun p hp => (hs p hp).1) hsize
    refine ⟨hmem, hgood, ?_⟩
    have hp := (hs _ hmem).1
    simp only [smoothResidues, dite_eq_right hp.ne_zero, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hgood.2
  · intro F hD
    exact smooth_label_budget F D L (roundedScale x ψ δ) s hD hc (by linarith)
      (fun p hp => ⟨(hs p hp).1, (hs p hp).2.2⟩)

end
end P0365Subquarter
