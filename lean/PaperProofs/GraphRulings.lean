import PaperTargets.GraphRulings
import PaperProofs.ClassRelations
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Analysis.Polynomial.MahlerMeasure

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false
open scoped nonZeroDivisors

private theorem exponent_cover (inverse : Bool) (e : Fin 2 →₀ ℕ)
    (hf : e (if inverse then 1 else 0) ≤ 3)
    (ht : e (if inverse then 0 else 1) ≤ 1) :
    ∃ j : Fin 8, e = relationExponent inverse j := by
  let j : Fin 8 := ⟨e (if inverse then 1 else 0)+4*e (if inverse then 0 else 1),by omega⟩
  refine ⟨j,?_⟩
  ext i
  cases inverse <;> dsimp at hf ht <;> fin_cases i <;>
    simp [relationExponent,j] <;> try split_ifs
  all_goals omega

private theorem section_coeff (inverse : Bool) (G : SourcePolynomial) (t : Fin 2) (k : ℕ) :
    (graphSection inverse G t).coeff k =
      if hk : k < 4 then G.coeff (relationExponent inverse ⟨k+4*t.val,by omega⟩) else 0 := by
  classical
  simp only [graphSection,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  split_ifs with hk
  · rw [Finset.sum_eq_single (⟨k,hk⟩ : Fin 4)]
    · simp
    · intro b hb hbk
      exact ite_eq_right (fun h => hbk (Fin.ext h))
    · simp
  · apply Finset.sum_eq_zero
    intro b hb
    exact ite_eq_right (by intro h; have := b.isLt; omega)

private theorem section_degree (inverse : Bool) (G : SourcePolynomial) (t : Fin 2) :
    (graphSection inverse G t).natDegree ≤ 3 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [section_coeff, dite_eq_right (by omega)]

/-- Both chart sections retain every original coefficient and every source point. -/
theorem relation_sections : CF13RelationSections := by
  classical
  intro inverse X G hG
  let c : Fin 8 → ℤ := fun j => G.coeff (relationExponent inverse j)
  have hrec : G = relationPolynomial inverse c := by
    ext e
    by_cases he : e ∈ G.support
    · obtain ⟨j,rfl⟩ := exponent_cover inverse e (hG.2.2 e he).1 (hG.2.2 e he).2
      exact ((relation_polynomial inverse c).1 j).symm
    · rw [MvPolynomial.notMem_support_iff.mp he]
      obtain hz | ⟨j,hj,hc⟩ := (relation_polynomial inverse c).2.2.1 e
      · exact hz.symm
      · rw [hc]
        exact (show c j = 0 by simpa only [c,← hj] using MvPolynomial.notMem_support_iff.mp he).symm
  have heval (z : Fin 2 → ℚ) : polynomialValue G z =
      integerPolynomialValue (graphSection inverse G 0) (z (if inverse then 1 else 0)) +
      z (if inverse then 0 else 1)*integerPolynomialValue (graphSection inverse G 1) (z (if inverse then 1 else 0)) := by
    rw [hrec,(relation_polynomial inverse c).2.2.2.2]
    simp only [integerPolynomialValue,rationalPolynomial,graphSection,Polynomial.map_sum,
      Polynomial.map_monomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,(relation_polynomial inverse c).1]
    cases inverse <;> simp [chartMonomial,Fin.sum_univ_succ] <;> ring
  refine ⟨?_,section_degree inverse G 0,section_degree inverse G 1,?_,heval⟩
  · by_contra h
    push Not at h
    apply hG.1
    rw [hrec]
    apply (relation_polynomial inverse c).2.1.mpr
    ext j
    have hj (t : Fin 2) (k : Fin 4) :
        G.coeff (relationExponent inverse ⟨k.val+4*t.val,by omega⟩) = 0 := by
      fin_cases t
      · simpa [section_coeff] using congrArg (fun P : Polynomial ℤ => P.coeff k.val) h.1
      · simpa [section_coeff] using congrArg (fun P : Polynomial ℤ => P.coeff k.val) h.2
    fin_cases j
    · exact hj 0 0
    · exact hj 0 1
    · exact hj 0 2
    · exact hj 0 3
    · exact hj 1 0
    · exact hj 1 1
    · exact hj 1 2
    · exact hj 1 3
  · intro t k
    rw [section_coeff]
    split_ifs
    · exact hG.2.1 _
    · simp only [Int.cast_zero,abs_zero]
      positivity

/-- Clear the rational gcd, then use Gauss's lemma to obtain integral
quotients. Scalar contents remain in the quotient pair. -/
theorem primitive_gcd_removal : CF13PrimitiveGCDRemoval := by
  classical
  intro P Q hPQ
  let f := rationalPolynomial P
  let g := rationalPolynomial Q
  let h := GCDMonoid.gcd f g
  have h0 : h ≠ 0 := by
    rcases hPQ with hp | hq
    · exact gcd_ne_zero_of_left ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp)
    · exact gcd_ne_zero_of_right ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hq)
  let W : Polynomial ℤ := IsLocalization.integerNormalization ℤ⁰ h
  let D := W.primPart
  obtain ⟨c,hc,hw⟩ := IsLocalization.integerNormalization_spec ℤ⁰ h
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
  have hW0 : W ≠ 0 := by
    intro hz
    have hh : (c:ℚ) • h = 0 := by simpa [W,hz] using hw.symm
    exact (smul_ne_zero hcQ h0) hh
  have hw0 : W.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hW0
  have hwQ : (W.content : ℚ) ≠ 0 := by exact_mod_cast hw0
  let μ : ℚ := (W.content : ℚ)/(c:ℚ)
  have hμ : μ ≠ 0 := div_ne_zero hwQ hcQ
  have hscale : h = Polynomial.C μ * rationalPolynomial D := by
    have hh : Polynomial.C (W.content : ℚ)*rationalPolynomial D = Polynomial.C (c:ℚ)*h := by
      calc
        _ = rationalPolynomial W := by
          simpa only [rationalPolynomial,Polynomial.map_mul,Polynomial.map_C,Int.coe_castRingHom,D] using
            (congrArg (fun Z : Polynomial ℤ => rationalPolynomial Z) W.eq_C_content_mul_primPart).symm
        _ = _ := by simpa [W,Algebra.smul_def,Polynomial.algebraMap_apply] using hw
    ext k
    have hk := congrArg (fun Z : Polynomial ℚ => Z.coeff k) hh
    simp only [Polynomial.coeff_C_mul] at hk ⊢
    dsimp [μ]
    field_simp
    nlinarith [hk]
  have hD0 : D ≠ 0 := W.primPart_ne_zero
  have hDm : rationalPolynomial D ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hD0
  have hpf : h*(f/h) = f := EuclideanDomain.mul_div_cancel' h0 (gcd_dvd_left f g)
  have hqf : h*(g/h) = g := EuclideanDomain.mul_div_cancel' h0 (gcd_dvd_right f g)
  have hDP : rationalPolynomial D ∣ f := ⟨Polynomial.C μ*(f/h),by
    calc
      f = h*(f/h) := hpf.symm
      _ = _ := by rw [hscale]; ring⟩
  have hDQ : rationalPolynomial D ∣ g := ⟨Polynomial.C μ*(g/h),by
    calc
      g = h*(g/h) := hqf.symm
      _ = _ := by rw [hscale]; ring⟩
  obtain ⟨P₁,hP₁⟩ := W.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (K := ℚ) hDP
  obtain ⟨Q₁,hQ₁⟩ := W.isPrimitive_primPart.dvd_of_fraction_map_dvd_fraction_map (K := ℚ) hDQ
  have hpmap : rationalPolynomial P₁ = Polynomial.C μ*(f/h) := by
    apply mul_left_cancel₀ hDm
    calc
      _ = f := by simp [f,rationalPolynomial,hP₁,D]
      _ = h*(f/h) := hpf.symm
      _ = _ := by rw [hscale]; ring
  have hqmap : rationalPolynomial Q₁ = Polynomial.C μ*(g/h) := by
    apply mul_left_cancel₀ hDm
    calc
      _ = g := by simp [g,rationalPolynomial,hQ₁,D]
      _ = h*(g/h) := hqf.symm
      _ = _ := by rw [hscale]; ring
  have hcop : IsCoprime (rationalPolynomial P₁) (rationalPolynomial Q₁) := by
    rw [hpmap,hqmap]
    exact (isCoprime_mul_units_left
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hμ))
      (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hμ)) _ _).mpr
        (isCoprime_div_gcd_div_gcd_of_gcd_ne_zero h0)
  have hdegP : P₁.natDegree ≤ P.natDegree := by
    by_cases hp : P = 0
    · have hp1 : P₁ = 0 := (mul_eq_zero.mp (hP₁.symm.trans hp)).resolve_left hD0
      simp [hp1]
    · exact Polynomial.natDegree_le_of_dvd ⟨D,by rw [hP₁]; ring⟩ hp
  have hdegQ : Q₁.natDegree ≤ Q.natDegree := by
    by_cases hq : Q = 0
    · have hq1 : Q₁ = 0 := (mul_eq_zero.mp (hQ₁.symm.trans hq)).resolve_left hD0
      simp [hq1]
    · exact Polynomial.natDegree_le_of_dvd ⟨D,by rw [hQ₁]; ring⟩ hq
  refine ⟨D,-P₁,Q₁,hD0,W.isPrimitive_primPart,by simpa using hP₁,hQ₁,?_,?_,by simpa using hdegP,hdegQ⟩
  · simpa [rationalPolynomial] using hcop.neg_left
  · rcases hPQ with hp | hq
    · exact (Polynomial.natDegree_le_of_dvd ⟨P₁,hP₁⟩ hp).trans (le_max_left _ _)
    · exact (Polynomial.natDegree_le_of_dvd ⟨Q₁,hQ₁⟩ hq).trans (le_max_right _ _)

/-- Mignotte's coefficient inequality, with the integral complementary factor
providing Mahler measure at least one. -/
theorem integer_factor_height : CF13IntegerFactorHeight := by
  classical
  intro d H hH P hP hd hcoeff A hdiv k
  obtain ⟨T,hT⟩ := hdiv
  have hT0 : T ≠ 0 := by intro h; simp [h] at hT; exact hP hT
  let PC := P.map (Int.castRingHom ℂ)
  let AC := A.map (Int.castRingHom ℂ)
  let TC := T.map (Int.castRingHom ℂ)
  have hnorm (Z : Polynomial ℤ) (i : ℕ) :
      ‖(Z.map (Int.castRingHom ℂ)).coeff i‖ = |(Z.coeff i : ℝ)| := by
    simp [Complex.norm_intCast]
  have hTC : 1 ≤ TC.mahlerMeasure := by
    apply Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
    dsimp [TC]
    rw [Polynomial.leadingCoeff_map_of_injective (Int.cast_injective)]
    change 1 ≤ ‖(T.leadingCoeff:ℂ)‖
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hT0)
  have hsum : PC.mahlerMeasure ≤ (d+1)*H := by
    calc
      _ ≤ PC.sum (fun _ a => ‖a‖) := Polynomial.mahlerMeasure_le_sum_norm_coeff PC
      _ ≤ (PC.support.card : ℝ)*H := by
        rw [Polynomial.sum_def]
        calc
          _ ≤ ∑ _i ∈ PC.support, H := Finset.sum_le_sum (fun i _ => by simpa only [PC,hnorm] using hcoeff i)
          _ = _ := by simp
      _ ≤ (d+1)*H := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        have hcard := PC.card_supp_le_succ_natDegree
        have hdeg : PC.natDegree ≤ d := by
          simpa [PC,Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective] using hd
        exact_mod_cast hcard.trans (Nat.add_le_add_right hdeg 1)
  have hchoose : (AC.natDegree.choose k : ℝ) ≤ (2:ℝ)^d := by
    have hdeg : AC.natDegree ≤ d := by
      simpa [AC,Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective] using
        (Polynomial.natDegree_le_of_dvd (show A ∣ P from ⟨T,hT⟩) hP).trans hd
    calc
      _ ≤ (2:ℝ)^AC.natDegree := by exact_mod_cast Nat.choose_le_two_pow AC.natDegree k
      _ ≤ (2:ℝ)^d := pow_le_pow_right₀ (by norm_num) hdeg
  have hprod : AC*TC = PC := by simp [AC,TC,PC,hT]
  calc
    _ = ‖AC.coeff k‖ := (hnorm A k).symm
    _ ≤ (AC.natDegree.choose k : ℝ)*PC.mahlerMeasure := by
      simpa [hprod] using Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure k AC TC hTC
    _ ≤ (2:ℝ)^d*((d+1)*H) := mul_le_mul hchoose hsum PC.mahlerMeasure_nonneg (by positivity)
    _ = _ := by ring

@[simp] private theorem value_zero (s : ℚ) : integerPolynomialValue 0 s = 0 := by
  simp [integerPolynomialValue,rationalPolynomial]
@[simp] private theorem value_mul (A B : Polynomial ℤ) (s : ℚ) :
    integerPolynomialValue (A*B) s = integerPolynomialValue A s*integerPolynomialValue B s := by
  simp [integerPolynomialValue,rationalPolynomial]
@[simp] private theorem value_neg (A : Polynomial ℤ) (s : ℚ) :
    integerPolynomialValue (-A) s = -integerPolynomialValue A s := by
  simp [integerPolynomialValue,rationalPolynomial]

/-- Off the primitive common factor, Bezout excludes a simultaneous zero;
positive-partner sources therefore lie on the exact rational graph. -/
theorem graph_ruling_dispatch : CF13GraphRulingDispatch := by
  classical
  intro P Q D A B hD hP hQ hcop hdeg
  have hDm : rationalPolynomial D ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hD
  have hroot (s : ℚ) : s ∈ rulingRoots D ↔ integerPolynomialValue D s = 0 := by
    simp [rulingRoots,Polynomial.mem_roots hDm,Polynomial.IsRoot,integerPolynomialValue]
  have hcard : (rulingRoots D).card ≤ 3 := by
    calc
      _ ≤ (rationalPolynomial D).roots.card := Multiset.toFinset_card_le _
      _ ≤ (rationalPolynomial D).natDegree := Polynomial.card_roots' _
      _ = D.natDegree := Polynomial.natDegree_map_eq_of_injective Int.cast_injective D
      _ ≤ 3 := hdeg
  have hno (s : ℚ) : ¬ (integerPolynomialValue A s = 0 ∧ integerPolynomialValue B s = 0) := by
    rintro ⟨ha,hb⟩
    obtain ⟨u,v,huv⟩ := hcop
    have hh := congrArg (Polynomial.eval s) huv
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one] at hh
    change _*integerPolynomialValue A s+_*integerPolynomialValue B s=1 at hh
    rw [ha,hb] at hh
    norm_num at hh
  have hiff (s t : ℚ) (ht : t ≠ 0) :
      integerPolynomialValue P s+t*integerPolynomialValue Q s = 0 ↔
        s ∈ rulingRoots D ∨ (integerPolynomialValue B s ≠ 0 ∧
          integerPolynomialValue A s ≠ 0 ∧ t = integerPolynomialValue A s/integerPolynomialValue B s) := by
    rw [hP,hQ,value_mul,value_mul,value_neg]
    constructor
    · intro hh
      by_cases hs : s ∈ rulingRoots D
      · exact Or.inl hs
      · right
        have hd : integerPolynomialValue D s ≠ 0 := mt (hroot s).mpr hs
        have he : -integerPolynomialValue A s+t*integerPolynomialValue B s=0 := by
          apply (mul_eq_zero.mp (show integerPolynomialValue D s *
            (-integerPolynomialValue A s+t*integerPolynomialValue B s)=0 by nlinarith [hh])).resolve_left hd
        have hb : integerPolynomialValue B s ≠ 0 := by
          intro hb
          exact hno s ⟨by rw [hb] at he; linarith,hb⟩
        have ha : integerPolynomialValue A s ≠ 0 := by
          intro ha
          rw [ha] at he
          exact (mul_ne_zero ht hb) (by linarith)
        exact ⟨hb,ha,(eq_div_iff hb).mpr (by linarith)⟩
    · rintro (hs | ⟨hb,ha,ht⟩)
      · rw [(hroot s).mp hs]; ring
      · rw [ht]; field_simp; ring
  refine ⟨hcard,hiff,?_,?_⟩
  · intro hz s t ht he
    rcases (hiff s t ht).mp he with hs | ⟨hb,ha,he⟩
    · exact hs
    · rcases hz with rfl | rfl <;> simp at *
  · intro hzero s t ht he
    rcases (hiff s t ht).mp he with hs | ⟨hb,ha,he⟩
    · exact Or.inl hs
    · right
      have ha0 := Polynomial.eq_C_of_natDegree_le_zero (show A.natDegree ≤ 0 by omega)
      have hb0 := Polynomial.eq_C_of_natDegree_le_zero (show B.natDegree ≤ 0 by omega)
      have va : integerPolynomialValue A s = (A.coeff 0 : ℚ) := by
        simpa [integerPolynomialValue,rationalPolynomial] using
          congrArg (fun Z : Polynomial ℤ => integerPolynomialValue Z s) ha0
      have vb : integerPolynomialValue B s = (B.coeff 0 : ℚ) := by
        simpa [integerPolynomialValue,rationalPolynomial] using
          congrArg (fun Z : Polynomial ℤ => integerPolynomialValue Z s) hb0
      rwa [va,vb] at he

/-- The bounded relation supplies a single bounded graph/ruling decomposition
before quantifying over actual sources in either original chart. -/
theorem actual_graph_ruling_decomposition : CF13ActualGraphRulingDecomposition := by
  classical
  intro inverse X G hX hG
  obtain ⟨hne,hPdeg,hQdeg,hcoeff,heval⟩ := relation_sections inverse X G hG
  let P := graphSection inverse G 0
  let Q := graphSection inverse G 1
  obtain ⟨D,A,B,hD,hprim,hP,hQ,hcop,hdegD,hdegA,hdegB⟩ := primitive_gcd_removal P Q hne
  have hDdeg : D.natDegree ≤ 3 := hdegD.trans (max_le hPdeg hQdeg)
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hH : 1 ≤ X^(14:ℕ) := one_le_pow₀ hX1
  have hfactor (Z R : Polynomial ℤ) (hR : R ≠ 0) (hdeg : R.natDegree ≤ 3)
      (hc : ∀ k, |(R.coeff k : ℝ)| ≤ X^(14:ℕ)) (hdv : Z ∣ R) :
      ∀ k, |(Z.coeff k : ℝ)| ≤ X^(15:ℕ) := by
    intro k
    calc
      _ ≤ (2:ℝ)^3*(3+1)*X^(14:ℕ) := integer_factor_height 3 _ hH R hR hdeg hc Z hdv k
      _ = 32*X^(14:ℕ) := by norm_num
      _ ≤ X*X^(14:ℕ) := mul_le_mul_of_nonneg_right hX (pow_nonneg hX0 _)
      _ = _ := by ring
  have hdheight : ∀ k, |(D.coeff k : ℝ)| ≤ X^(15:ℕ) := by
    rcases hne with hp | hq
    · exact hfactor D P hp hPdeg (hcoeff 0) ⟨-A,hP⟩
    · exact hfactor D Q hq hQdeg (hcoeff 1) ⟨B,hQ⟩
  have haheight : ∀ k, |(A.coeff k : ℝ)| ≤ X^(15:ℕ) := by
    by_cases hp : P = 0
    · have ha : A = 0 := neg_eq_zero.mp ((mul_eq_zero.mp (hP.symm.trans hp)).resolve_left hD)
      simp [ha,pow_nonneg hX0]
    · exact hfactor A P hp hPdeg (hcoeff 0) ⟨-D,by rw [hP]; ring⟩
  have hbheight : ∀ k, |(B.coeff k : ℝ)| ≤ X^(15:ℕ) := by
    by_cases hq : Q = 0
    · have hb : B = 0 := (mul_eq_zero.mp (hQ.symm.trans hq)).resolve_left hD
      simp [hb,pow_nonneg hX0]
    · exact hfactor B Q hq hQdeg (hcoeff 1) ⟨D,by rw [hQ]; ring⟩
  obtain ⟨hcard,hdispatch,hdegenerate,hconstant⟩ := graph_ruling_dispatch P Q D A B hD hP hQ hcop hDdeg
  refine ⟨D,A,B,⟨hD,hprim,hcop,hDdeg,hdegA.trans hPdeg,hdegB.trans hQdeg,?_⟩,hcard,?_⟩
  · intro R hR k
    simp only [Finset.mem_insert,Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact hdheight k
    · exact haheight k
    · exact hbheight k
  · intro n b d u v hs hz
    have hb0 : (b:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs.1
    have hd0 : (d:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs.2.1
    have hu0 : (u:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs.2.2.1
    have hv0 : (v:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs.2.2.2.1
    apply (hdispatch _ _ ?_).mp
    · rw [← heval]; exact hz
    · cases inverse <;> simp [sourcePoint,hb0,hd0,hu0,hv0]

/-- Compose the proved actual CF11/CF12 class relation with its graph/ruling
decomposition; the polynomial and decomposition precede every class member. -/
theorem rounded_class_graph_rulings : CF13RoundedClassGraphRulings := by
  intro δ hδ hδ1
  obtain ⟨X₁,hX₁,hclass⟩ := rounded_entire_class_relation δ hδ hδ1
  refine ⟨max X₁ 32,le_max_right _ _,?_⟩
  intro X ψ B E a hX hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  obtain ⟨G,hG,hzero⟩ := hclass X ψ B E a ((le_max_left _ _).trans hX)
    hψ0 hψ2 hB hE ha hBE F p z₀ ι n b d u v hp hscale hs hb hi hf hg hz
  obtain ⟨D,A,C,hdata,hcard,hpoints⟩ := actual_graph_ruling_decomposition
    (selectedRealChart ψ) X G ((le_max_right _ _).trans hX) hG
  exact ⟨D,A,C,hdata,hcard,fun i => hpoints _ _ _ _ _ (hs i) (hzero i)⟩

end
end P0365Subquarter
