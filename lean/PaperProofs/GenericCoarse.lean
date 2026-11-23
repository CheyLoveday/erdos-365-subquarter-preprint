import PaperTargets.GenericCoarse
import PaperProofs.UniformRectangles
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Nat.Find

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem determinant_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (L : ℝ) (_hL : 0≤L) (hA : ∀ i j, |(A i j:ℝ)|≤L) :
    |(A.det:ℝ)|≤(n.factorial:ℝ)*L^n := by
  rw [Int.cast_det,Matrix.det_apply']
  calc
    _≤∑ σ : Equiv.Perm (Fin n),
        |((Equiv.Perm.sign σ:ℤ):ℝ)*∏ i,(A (σ i) i:ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _=∑ σ : Equiv.Perm (Fin n),∏ i,|(A (σ i) i:ℝ)| := by
      simp only [abs_mul,abs_unit_intCast,one_mul,Finset.abs_prod]
    _≤∑ _σ : Equiv.Perm (Fin n), L^n := by
      apply Finset.sum_le_sum
      intro σ hσ
      calc
        _≤∏ _i : Fin n,L := Finset.prod_le_prod₀
          (fun _ _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _=L^n := by simp
    _=_ := by simp [Fintype.card_perm]

private def genericCompletion {H : ℕ} {ι : Type} (A : ι → Fin H → ℤ)
    (k : ℕ) : Prop :=
  ∃ (S : Finset (Fin H)) (B : Matrix (Fin H) (Fin H) ℤ),
    S.card=k ∧ B.det≠0 ∧ (∀ i∈S,∃ x : ι,B i=A x) ∧
      ∀ i∉S,∃ j : Fin H,B i=Pi.single j 1

private theorem completion_zero {H : ℕ} {ι : Type} (A : ι → Fin H → ℤ) :
    genericCompletion A 0 := by
  refine ⟨∅,1,by simp,by simp,by simp,?_⟩
  intro i hi
  refine ⟨i,?_⟩
  ext j
  simp [Matrix.one_apply,Pi.single_apply,eq_comm]

/-- The maximal actual/unit completion gives one bounded cofactor relation
at every rank, including H=1 and empty populations. -/
theorem generic_bounded_integer_relation : CF04GenericBoundedIntegerRelation := by
  classical
  intro H hH
  cases H with
  | zero => omega
  | succ n =>
    intro ι A L hL hA hzero
    let q := Nat.findGreatest (genericCompletion A) (n+1)
    obtain ⟨S,B,hcard,hdet,hrows,hunits⟩ :=
      Nat.findGreatest_spec (by omega : 0≤n+1) (completion_zero A)
    have hq : q≤n+1 := Nat.findGreatest_le (n+1)
    have hqn : q<n+1 := by
      by_contra hh
      have hS : S=Finset.univ := Finset.eq_univ_of_card S
        (by simpa [hcard] using (show q=n+1 by omega))
      have hx (i : Fin (n+1)) : ∃ x : ι,B i=A x := hrows i (by simp [hS])
      choose f hf using hx
      apply hdet
      have he : B=Matrix.of (fun i j => A (f i) j) := by
        ext i j
        exact congrFun (hf i) j
      rw [he]
      exact hzero f
    obtain ⟨r,hr⟩ : ∃ r : Fin (n+1),r∉S := by
      obtain ⟨r,_,hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (show S.card<(Finset.univ:Finset (Fin (n+1))).card by simpa [hcard] using hqn)
      exact ⟨r,hr⟩
    let c : Fin (n+1) → ℤ := fun j => B.adjugate j r
    have hc : c≠0 := by
      intro hz
      apply hdet
      rw [Matrix.det_eq_sum_mul_adjugate_row B r]
      have hz' (j : Fin (n+1)) : B.adjugate j r=0 := congrFun hz j
      simp [hz']
    have hBL (i j : Fin (n+1)) : |(B i j:ℝ)|≤L := by
      by_cases hi : i∈S
      · obtain ⟨x,hx⟩ := hrows i hi
        rw [congrFun hx j]
        exact hA x j
      · obtain ⟨k,hk⟩ := hunits i hi
        rw [congrFun hk j]
        by_cases hj : j=k <;>
          simp [hj,hL,le_trans (by norm_num : (0:ℝ)≤1) hL]
    refine ⟨c,hc,?_,?_⟩
    · intro j
      dsimp [c]
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      simp only [Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,
        abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      simpa using determinant_bound (B.submatrix r.succAbove j.succAbove) L
        (by linarith) (fun i k => hBL _ _)
    · intro x
      have hz : (B.updateRow r (A x)).det=0 := by
        by_contra hn
        have hp : genericCompletion A (q+1) := by
          refine ⟨insert r S,B.updateRow r (A x),?_,hn,?_,?_⟩
          · rw [Finset.card_insert_of_notMem hr,hcard]
          · intro i hi
            by_cases hir : i=r
            · subst i; exact ⟨x,Matrix.updateRow_self⟩
            · rw [Matrix.updateRow_ne hir]
              exact hrows i ((Finset.mem_insert.mp hi).resolve_left hir)
          · intro i hi
            have hir : i≠r := fun h => hi (by simp [h])
            rw [Matrix.updateRow_ne hir]
            exact hunits i (fun h => hi (Finset.mem_insert_of_mem h))
        exact Nat.findGreatest_is_greatest (show q<q+1 by omega)
          (show q+1≤n+1 by omega) hp
      have hadj (j : Fin (n+1)) : (B.updateRow r (A x)).adjugate j r=B.adjugate j r := by
        simp only [Matrix.adjugate_apply,Matrix.updateRow_idem]
      rw [Matrix.det_eq_sum_mul_adjugate_row _ r] at hz
      simpa only [Matrix.updateRow_self,hadj] using hz

private def rectangleExponent {A C : ℕ} (j : RectangularIndex A C) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j.1.val+Finsupp.single 1 j.2.val

private def rectanglePolynomial (A C : ℕ) (c : RectangularIndex A C → ℤ) :
    SourcePolynomial :=
  ∑ j : RectangularIndex A C,MvPolynomial.monomial (rectangleExponent j) (c j)

private theorem rectangle_exponent_injective {A C : ℕ} :
    Function.Injective (@rectangleExponent A C) := by
  intro j k h
  have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  apply Prod.ext <;> apply Fin.ext
  · simpa [rectangleExponent] using h0
  · simpa [rectangleExponent] using h1

private theorem rectangle_coefficient {A C : ℕ} (c : RectangularIndex A C → ℤ)
    (j : RectangularIndex A C) :
    (rectanglePolynomial A C c).coeff (rectangleExponent j)=c j := by
  classical
  unfold rectanglePolynomial
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    rw [ite_eq_right (fun h => hkj (rectangle_exponent_injective h))]
  · simp

private theorem rectangle_other_coefficient {A C : ℕ}
    (c : RectangularIndex A C → ℤ) (e : Fin 2 →₀ ℕ) :
    (rectanglePolynomial A C c).coeff e=0 ∨
      ∃ j : RectangularIndex A C,
        (rectanglePolynomial A C c).coeff e=c j := by
  classical
  by_cases he : ∃ j : RectangularIndex A C,e=rectangleExponent j
  · obtain ⟨j,rfl⟩ := he
    exact Or.inr ⟨j,rectangle_coefficient c j⟩
  · left
    unfold rectanglePolynomial
    simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h => he ⟨j,h.symm⟩)

private theorem rectangle_nonzero {A C : ℕ} (c : RectangularIndex A C → ℤ)
    (hc : c≠0) : rectanglePolynomial A C c≠0 := by
  intro hz
  apply hc
  ext j
  have hj := rectangle_coefficient c j
  rw [hz] at hj
  simpa using hj.symm

private theorem rectangle_degree {A C : ℕ} (c : RectangularIndex A C → ℤ) :
    (rectanglePolynomial A C c).totalDegree≤A+C := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  have hdeg := MvPolynomial.totalDegree_monomial_le (rectangleExponent j) (c j)
  have he : (rectangleExponent j).sum (fun _ => id)=j.1.val+j.2.val := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp [rectangleExponent,Fin.sum_univ_succ]
  exact hdeg.trans (he ▸ Nat.add_le_add (Nat.le_of_lt_succ j.1.is_lt)
    (Nat.le_of_lt_succ j.2.is_lt))

private theorem rectangle_value {A C : ℕ} (c : RectangularIndex A C → ℤ)
    (z : Fin 2 → ℚ) :
    polynomialValue (rectanglePolynomial A C c) z=
      ∑ j : RectangularIndex A C,(c j:ℚ)*z 0^j.1.val*z 1^j.2.val := by
  classical
  unfold rectanglePolynomial polynomialValue
  rw [MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MvPolynomial.eval₂_monomial,Finsupp.prod_pow]
  simp [rectangleExponent,Fin.prod_univ_succ,mul_assoc]

private theorem rectangle_entry_rational {A C : ℕ} (b d u v : ℕ)
    (hd : 0<d) (hu : 0<u) (j : RectangularIndex A C) :
    (rectangularIntegerEntry A C b d u v j.1.val j.2.val:ℚ)=
      ((d:ℚ)^A*(u:ℚ)^C)*(((b:ℚ)/d)^j.1.val*((v:ℚ)/u)^j.2.val) := by
  have hd' : (d:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hu' : (u:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have hda : (d:ℚ)^A=(d:ℚ)^j.1.val*(d:ℚ)^(A-j.1.val) := by
    rw [←pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ j.1.is_lt)]
  have huc : (u:ℚ)^C=(u:ℚ)^j.2.val*(u:ℚ)^(C-j.2.val) := by
    rw [←pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ j.2.is_lt)]
  simp only [rectangularIntegerEntry,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
  rw [div_pow,div_pow,hda,huc]
  field_simp [hd',hu']

private theorem rectangle_evaluation {A C : ℕ} (n b d u v : ℕ)
    (hs : PairSource n b d u v) (c : RectangularIndex A C → ℤ)
    (hz : ∑ j : RectangularIndex A C,
      rectangularIntegerEntry A C b d u v j.1.val j.2.val*c j=0) :
    polynomialValue (rectanglePolynomial A C c) (sourcePoint b d u v)=0 := by
  have hd : (d:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hs.2.1)
  have hu : (u:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hs.2.2.1)
  have hden : (d:ℚ)^A*(u:ℚ)^C≠0 := by positivity
  have heq : ((∑ j : RectangularIndex A C,
      rectangularIntegerEntry A C b d u v j.1.val j.2.val*c j:ℤ):ℚ)=
      ((d:ℚ)^A*(u:ℚ)^C)*polynomialValue
        (rectanglePolynomial A C c) (sourcePoint b d u v) := by
    rw [rectangle_value]
    simp only [Int.cast_sum,Int.cast_mul,Finset.mul_sum,sourcePoint,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    apply Finset.sum_congr rfl
    intro j hj
    rw [rectangle_entry_rational b d u v hs.2.1 hs.2.2.1 j]
    ring
  have hp : ((d:ℚ)^A*(u:ℚ)^C)*polynomialValue
      (rectanglePolynomial A C c) (sourcePoint b d u v)=0 := by
    rw [←heq,hz]; norm_num
  exact (mul_eq_zero.mp hp).resolve_left hden

private theorem source_coordinate_bounds (X : ℝ) (hX : 1≤X) (n b d u v : ℕ)
    (hs : PairSource n b d u v) (hn : (n:ℝ)≤2*X) :
    (b:ℝ)≤3*X ∧ (d:ℝ)≤3*X ∧ (u:ℝ)≤3*X ∧ (v:ℝ)≤3*X := by
  obtain ⟨hb3,hu2,hd3,hv2⟩ := source_bounds n b d u v hs
  have bound (q k : ℕ) (hq : 0<q) (hk : k≠0) (hp : q^k≤n+1) :
      (q:ℝ)≤3*X := by
    have hq₁ : (1:ℝ)≤q := by exact_mod_cast hq
    have hp' : (q:ℝ)^k≤(n:ℝ)+1 := by exact_mod_cast hp
    exact (le_self_pow₀ hq₁ hk).trans (hp'.trans (by linarith))
  exact ⟨bound b 3 hs.1 (by decide) (by omega),
    bound d 3 hs.2.1 (by decide) hd3,
    bound u 2 hs.2.2.1 (by decide) (by omega),
    bound v 2 hs.2.2.2.1 (by decide) hv2⟩

private theorem mixed_bound (a b Y : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hY : 0≤Y) (haY : a≤Y) (hbY : b≤Y) (k N : ℕ) (hk : k≤N) :
    a^k*b^(N-k)≤Y^N := by
  calc
    _≤Y^k*Y^(N-k) := mul_le_mul (pow_le_pow_left₀ ha haY _)
      (pow_le_pow_left₀ hb hbY _) (pow_nonneg hb _) (pow_nonneg hY _)
    _=Y^N := by rw [←pow_add,Nat.add_sub_of_le hk]

private theorem rectangle_entry_bound (X : ℝ) (hX : 1≤X)
    (n b d u v A C D : ℕ) (hs : PairSource n b d u v)
    (hn : (n:ℝ)≤2*X) (hD : A+C≤D) (j : RectangularIndex A C) :
    |(rectangularIntegerEntry A C b d u v j.1.val j.2.val:ℝ)|≤(3*X)^D := by
  obtain ⟨hb,hd,hu,hv⟩ := source_coordinate_bounds X hX n b d u v hs hn
  have hY : (1:ℝ)≤3*X := by linarith
  simp only [rectangularIntegerEntry,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
  rw [abs_of_nonneg (by positivity)]
  have hbd := mixed_bound (b:ℝ) (d:ℝ) (3*X) (by positivity) (by positivity)
    (by linarith) hb hd _ A (Nat.le_of_lt_succ j.1.is_lt)
  have hvu := mixed_bound (v:ℝ) (u:ℝ) (3*X) (by positivity) (by positivity)
    (by linarith) hv hu _ C (Nat.le_of_lt_succ j.2.is_lt)
  calc
    _=((b:ℝ)^j.1.val*(d:ℝ)^(A-j.1.val))*
        ((v:ℝ)^j.2.val*(u:ℝ)^(C-j.2.val)) := by ring
    _≤(3*X)^A*(3*X)^C := mul_le_mul hbd hvu (by positivity) (by positivity)
    _=(3*X)^(A+C) := (pow_add _ _ _).symm
    _≤(3*X)^D := pow_le_pow_right₀ hY hD

/-- Uniform original integer-minor vanishing constructs the actual polynomial;
degree, coefficient exponent and constant all precede every source population. -/
theorem actual_uniform_coarse_polynomial : CF04ActualUniformCoarsePolynomial := by
  classical
  intro δ hδ hδ₁
  obtain ⟨C,Amax,hC,X₀,hX₀,hminors⟩ := actual_uniform_minor_vanishing δ hδ hδ₁
  let D := Amax+C
  let Hmax := (Amax+1)*(C+1)
  let N := D*(Hmax-1)
  let K : ℝ := ((Hmax-1).factorial:ℝ)*(3:ℝ)^N
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨D,N,by dsimp [D]; omega,K,X₀,hK,hX₀,?_⟩
  intro X ψ B E t hX hψlo hψhi hB hE ht hBE S b d u v hs hbox hint
  have hX₁ : 1≤X := by linarith
  obtain ⟨A,hA,hzero⟩ := hminors X ψ B E t hX hψlo hψhi hB hE ht hBE
  let H := Fintype.card (RectangularIndex A C)
  let e : RectangularIndex A C ≃ Fin H := Fintype.equivFin _
  let rows (i : S) (j : Fin H) : ℤ :=
    rectangularIntegerEntry A C (b i.val) (d i.val) (u i.val) (v i.val)
      (e.symm j).1.val (e.symm j).2.val
  have hH : 1≤H := by
    dsimp [H]
    simp only [Fintype.card_prod,Fintype.card_fin]
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos A) (Nat.succ_pos C))
  have hD : A+C≤D := by dsimp [D]; omega
  have hHmax : H≤Hmax := by
    dsimp [H,Hmax]
    simpa using Nat.mul_le_mul_right (C+1) (Nat.add_le_add_right hA 1)
  have hentry (i : S) (j : Fin H) : |(rows i j:ℝ)|≤(3*X)^D :=
    rectangle_entry_bound X hX₁ i.val (b i.val) (d i.val) (u i.val) (v i.val)
      A C D (hs i.val i.property) (hbox i.val i.property).2.1 hD (e.symm j)
  have hzero' (f : Fin H → S) : (Matrix.of (fun i j => rows (f i) j)).det=0 := by
    let nr : RectangularIndex A C → ℕ := fun j => (f (e j)).val
    have hm := hzero nr (fun j => b (nr j)) (fun j => d (nr j))
      (fun j => u (nr j)) (fun j => v (nr j))
      (fun j => hs _ (f (e j)).property)
      (fun j => hbox _ (f (e j)).property)
      (fun j => hint _ (f (e j)).property)
    have heq : Matrix.reindex e e (rectangularSourceMatrix A C
        (fun j => b (nr j)) (fun j => d (nr j))
        (fun j => u (nr j)) (fun j => v (nr j)))=
        Matrix.of (fun i j => rows (f i) j) := by
      ext i j
      simp [Matrix.reindex_apply,rectangularSourceMatrix,rows,nr]
    rw [←heq,Matrix.det_reindex_self]
    exact hm
  obtain ⟨c,hc,hcL,hrel⟩ := generic_bounded_integer_relation H hH S rows ((3*X)^D)
    (one_le_pow₀ (by linarith : (1:ℝ)≤3*X)) hentry hzero'
  let cr : RectangularIndex A C → ℤ := fun j => c (e j)
  have hcr : cr≠0 := by
    intro hz
    apply hc
    ext j
    have hh := congrFun hz (e.symm j)
    simpa [cr] using hh
  have hcoeff (j : RectangularIndex A C) : |(cr j:ℝ)|≤K*X^N := by
    calc
      _≤((H-1).factorial:ℝ)*((3*X)^D)^(H-1) := hcL (e j)
      _=((H-1).factorial:ℝ)*(3*X)^(D*(H-1)) := by rw [pow_mul]
      _≤((Hmax-1).factorial:ℝ)*(3*X)^N := by
        apply mul_le_mul
        · exact_mod_cast Nat.factorial_le (Nat.sub_le_sub_right hHmax 1)
        · exact pow_le_pow_right₀ (by linarith : (1:ℝ)≤3*X)
            (Nat.mul_le_mul_left D (Nat.sub_le_sub_right hHmax 1))
        · positivity
        · positivity
      _=K*X^N := by dsimp [K]; rw [mul_pow]; ring
  refine ⟨rectanglePolynomial A C cr,rectangle_nonzero cr hcr,
    (rectangle_degree cr).trans hD,?_,?_⟩
  · intro z
    obtain hz | ⟨j,hj⟩ := rectangle_other_coefficient cr z
    · rw [hz]; simp only [Int.cast_zero,abs_zero]
      exact le_of_lt (mul_pos hK (pow_pos (by linarith : 0<X) _))
    · rw [hj]
      exact hcoeff j
  · intro n hn
    have heq : ∑ j : RectangularIndex A C,
        rectangularIntegerEntry A C (b n) (d n) (u n) (v n) j.1.val j.2.val*cr j=0 := by
      have hh := hrel (⟨n,hn⟩:S)
      rw [←e.sum_comp] at hh
      simpa [rows,cr] using hh
    exact rectangle_evaluation n (b n) (d n) (u n) (v n) (hs n hn) cr heq

end
end P0365Subquarter
