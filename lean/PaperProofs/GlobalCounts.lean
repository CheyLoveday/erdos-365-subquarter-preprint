import PaperTargets.GlobalCounts
import PaperProofs.BoxCounts
import PaperProofs.RulingCounts

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem real_cover_card {ι α : Type} [DecidableEq α] (S : Finset α) (I : Finset ι)
    (A : ι → Finset α) (f : ι → ℝ) (hcover : S⊆I.biUnion A)
    (hA : ∀ i∈I,((A i).card:ℝ)≤f i) :
    (S.card:ℝ)≤∑ i∈I,f i := by
  classical
  have hc : S.card≤∑ i∈I,(A i).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcast : (S.card:ℝ)≤∑ i∈I,((A i).card:ℝ) := by exact_mod_cast hc
  exact hcast.trans (Finset.sum_le_sum hA)

private theorem dyadic_real_bounds (q k : ℕ) (hq : 0<q) (hk : Nat.log 2 q=k) :
    (2:ℝ)^k≤(q:ℝ) ∧ (q:ℝ)≤2*(2:ℝ)^k := by
  have hl : 2^k≤q := by simpa only [hk] using Nat.pow_log_le_self 2 hq.ne'
  have hu : q<2^(k+1) := by
    simpa only [hk] using Nat.lt_pow_succ_log_self (by decide : 1<2) q
  refine ⟨by exact_mod_cast hl,?_⟩
  have hu' : (q:ℝ)≤(2:ℝ)^(k+1) := by exact_mod_cast hu.le
  simpa only [pow_succ,mul_comm] using hu'

private theorem log_count_bound (e : ℝ) (he : 0<e) :
    ∃ C : ℝ,0<C ∧ ∀ X : ℝ,32≤X → ∀ N : ℕ,(N:ℝ)≤2*X →
      ((Nat.log 2 N+1:ℕ):ℝ)≤C*X^e := by
  obtain ⟨C,hC,hbound⟩ := ruling_log_subpower e he
  refine ⟨C,hC,?_⟩
  intro X hX N hN
  have hl : Nat.log 2 N+1≤8401+Nat.log 2 (2*N+1) := by
    have hh := Nat.log_mono_right (b:=2) (show N≤2*N+1 by omega)
    omega
  have hl' : ((Nat.log 2 N+1:ℕ):ℝ)≤(8401:ℝ)+(Nat.log 2 (2*N+1):ℝ) := by
    exact_mod_cast hl
  exact hl'.trans (hbound X hX N hN)

private theorem kernel_coordinate_bounds (X : ℝ) (hX : 1≤X) (n b d u v : ℕ)
    (hs : PairSource n b d u v) (hn : (n:ℝ)≤2*X) :
    (b:ℝ)≤3*X ∧ (d:ℝ)≤3*X := by
  obtain ⟨hb3,_,hd3,_⟩ := source_bounds n b d u v hs
  have bound (q : ℕ) (hq : 0<q) (hp : q^3≤n+1) : (q:ℝ)≤3*X := by
    have hq₁ : (1:ℝ)≤q := by exact_mod_cast hq
    have hp' : (q:ℝ)^3≤(n:ℝ)+1 := by exact_mod_cast hp
    exact (le_self_pow₀ hq₁ (by decide : 3≠0)).trans (hp'.trans (by linarith))
  exact ⟨bound b hs.1 (by omega),bound d hs.2.1 hd3⟩

/-- Sum all actual dyadic kernel boxes; both logarithmic costs are paid. -/
theorem original_shell_source_count : CF18OriginalShellSourceCount := by
  classical
  intro hThue ε hε
  have he : 0<ε/2 := by linarith
  let η : ℝ := ε/4
  have hη : 0<η := by dsimp [η]; linarith
  obtain ⟨X₀,Kb,hX₀,hKb,hbox⟩ := actual_box_source_count hThue (ε/2) he
  obtain ⟨Cl,hCl,hlog⟩ := log_count_bound η hη
  let A : ℝ := Cl*3^η
  refine ⟨X₀,Kb*A^2,hX₀,by dsimp [A]; positivity,?_⟩
  intro X hX S b d u v hs hn
  have hX₃₂ : 32≤X := hX₀.trans hX
  have hX₁ : 1≤X := by linarith
  have hXp : 0<X := by linarith
  let N := Nat.floor (3*X)
  let L := Nat.log 2 N+1
  let I := (Finset.range L).product (Finset.range L)
  let T : ℕ×ℕ → Finset ℕ := fun j => S.filter
    (fun n => Nat.log 2 (b n)=j.1 ∧ Nat.log 2 (d n)=j.2)
  have hcoord (n : ℕ) (hnS : n∈S) : b n≤N ∧ d n≤N := by
    obtain ⟨hb,hd⟩ := kernel_coordinate_bounds X hX₁ n (b n) (d n) (u n) (v n)
      (hs n hnS) (hn n hnS).2
    exact ⟨Nat.le_floor hb,Nat.le_floor hd⟩
  have hcover : S⊆I.biUnion T := by
    intro n hnS
    obtain ⟨hb,hd⟩ := hcoord n hnS
    have hbL : Nat.log 2 (b n)<L := by
      dsimp [L]; have hh := Nat.log_mono_right (b:=2) hb; omega
    have hdL : Nat.log 2 (d n)<L := by
      dsimp [L]; have hh := Nat.log_mono_right (b:=2) hd; omega
    apply Finset.mem_biUnion.mpr
    refine ⟨(Nat.log 2 (b n),Nat.log 2 (d n)),?_,?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hbL,Finset.mem_range.mpr hdL⟩
    · exact Finset.mem_filter.mpr ⟨hnS,rfl,rfl⟩
  have hT (j : ℕ×ℕ) (_hj : j∈I) :
      ((T j).card:ℝ)≤Kb*X^(profileTheta+ε/2) := by
    have hTS : T j⊆S := Finset.filter_subset _ _
    apply hbox X ((2:ℝ)^j.1) ((2:ℝ)^j.2) hX (by positivity) (by positivity)
      (T j) b d u v (fun n hnT => hs n (hTS hnT))
    intro n hnT
    obtain ⟨_,hb,hd⟩ := Finset.mem_filter.mp hnT
    have hbb := dyadic_real_bounds (b n) j.1 (hs n (hTS hnT)).1 hb
    have hdd := dyadic_real_bounds (d n) j.2 (hs n (hTS hnT)).2.1 hd
    exact ⟨(hn n (hTS hnT)).1,(hn n (hTS hnT)).2,hbb.1,hbb.2,hdd.1,hdd.2⟩
  have hL : (L:ℝ)≤A*X^η := by
    have hh := hlog (3*X) (by linarith) N
      ((Nat.floor_le (by positivity : 0≤3*X)).trans (by linarith))
    dsimp [A,L,N] at *
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3) hXp.le] at hh
    simpa only [mul_assoc] using hh
  have hL₂ : (L:ℝ)^2≤A^2*(X^η)^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg L) hL 2
  have hexp : (X^η)^2*X^(profileTheta+ε/2)=X^(profileTheta+ε) := by
    rw [pow_two,←Real.rpow_add hXp η η,←Real.rpow_add hXp (η+η) (profileTheta+ε/2)]
    congr 1
    dsimp [η]
    ring
  calc
    (S.card:ℝ)≤∑ j∈I,Kb*X^(profileTheta+ε/2) := real_cover_card S I T _ hcover hT
    _=(L:ℝ)^2*(Kb*X^(profileTheta+ε/2)) := by simp [I,pow_two]
    _≤(A^2*(X^η)^2)*(Kb*X^(profileTheta+ε/2)) :=
      mul_le_mul_of_nonneg_right hL₂ (by positivity)
    _=(Kb*A^2)*((X^η)^2*X^(profileTheta+ε/2)) := by ring
    _=(Kb*A^2)*X^(profileTheta+ε) := by rw [hexp]

/-- Sum every original-start shell and a bounded finite head, uniformly in N. -/
theorem natural_pair_count : CF18NaturalPairCount := by
  classical
  intro hThue ε hε
  let e : ℝ := ε/2
  have he : 0<e := by dsimp [e]; linarith
  obtain ⟨X₀,Cs,hX₀,hCs,hshell⟩ := original_shell_source_count hThue e he
  obtain ⟨Cl,hCl,hlog⟩ := log_count_bound e he
  let Hn := Nat.ceil (2*X₀)+1
  let H : ℝ := Hn
  let α : ℝ := profileTheta+e
  have hα : 0≤α := by dsimp [α]; norm_num [profileTheta] at *; linarith
  have hH : 0<H := by dsimp [H,Hn]; positivity
  let A : ℝ := Cl*32^e
  refine ⟨(Cs+H)*A,by dsimp [A]; positivity,?_⟩
  intro N hN
  let S := (Finset.range (N+1)).filter (fun n => ∃ b d u v,PairSource n b d u v)
  have hex : ∀ n : ℕ,∃ b d u v : ℕ,n∈S → PairSource n b d u v := by
    intro n
    by_cases hn : n∈S
    · obtain ⟨b,d,u,v,hs⟩ := (Finset.mem_filter.mp hn).2
      exact ⟨b,d,u,v,fun _ => hs⟩
    · exact ⟨1,1,1,1,fun h => False.elim (hn h)⟩
  choose b d u v hs using hex
  have hnN (n : ℕ) (hn : n∈S) : n≤N := by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    omega
  have hnpos (n : ℕ) (hn : n∈S) : 0<n :=
    (additive_and_integer_source n (b n) (d n) (u n) (v n) (hs n hn)).1
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith
  have hpower : 1≤(N:ℝ)^α := Real.one_le_rpow hNr hα
  let J := Finset.range (Nat.log 2 N+1)
  let T : ℕ → Finset ℕ := fun j => S.filter (fun n => Nat.log 2 n=j)
  have hcover : S⊆J.biUnion T := by
    intro n hn
    have hh := Nat.log_mono_right (b:=2) (hnN n hn)
    exact Finset.mem_biUnion.mpr ⟨Nat.log 2 n,Finset.mem_range.mpr (by omega),
      Finset.mem_filter.mpr ⟨hn,rfl⟩⟩
  have hT (j : ℕ) (hj : j∈J) : ((T j).card:ℝ)≤(Cs+H)*(N:ℝ)^α := by
    have hTS : T j⊆S := Finset.filter_subset _ _
    have hjlog : j≤Nat.log 2 N := by have hh := Finset.mem_range.mp hj; omega
    have hXjN : (2:ℝ)^j≤(N:ℝ) := by
      have hh : (2:ℕ)^j≤N := (pow_le_pow_right₀ (by decide : 1≤(2:ℕ)) hjlog).trans
        (Nat.pow_log_le_self 2 (by omega : N≠0))
      exact_mod_cast hh
    have hbounds (n : ℕ) (hn : n∈T j) : (2:ℝ)^j≤(n:ℝ) ∧ (n:ℝ)≤2*(2:ℝ)^j :=
      dyadic_real_bounds n j (hnpos n (hTS hn)) (Finset.mem_filter.mp hn).2
    by_cases hlarge : X₀≤(2:ℝ)^j
    · calc
        ((T j).card:ℝ)≤Cs*((2:ℝ)^j)^α :=
          hshell ((2:ℝ)^j) hlarge (T j) b d u v (fun n hn => hs n (hTS hn)) hbounds
        _≤Cs*(N:ℝ)^α := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hXjN hα) hCs.le
        _≤(Cs+H)*(N:ℝ)^α := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · have hsmall : (2:ℝ)^j<X₀ := lt_of_not_ge hlarge
      have hsub : T j⊆Finset.range Hn := by
        intro n hn
        have hnreal : (n:ℝ)≤(Nat.ceil (2*X₀):ℝ) :=
          (hbounds n hn).2.trans ((by linarith : 2*(2:ℝ)^j≤2*X₀).trans (Nat.le_ceil _))
        have hnceil : n≤Nat.ceil (2*X₀) := by exact_mod_cast hnreal
        exact Finset.mem_range.mpr (by dsimp [Hn]; omega)
      have hc : ((T j).card:ℝ)≤H := by
        have hh : (T j).card≤Hn := by simpa only [Finset.card_range] using Finset.card_le_card hsub
        change ((T j).card:ℝ)≤(Hn:ℝ)
        exact_mod_cast hh
      calc
        ((T j).card:ℝ)≤H := hc
        _≤H*(N:ℝ)^α := le_mul_of_one_le_right hH.le hpower
        _≤(Cs+H)*(N:ℝ)^α := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hJ : (J.card:ℝ)≤A*(N:ℝ)^e := by
    have hh := hlog (32*(N:ℝ)) (by nlinarith) N (by nlinarith)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤32) hNp.le] at hh
    simpa only [J,Finset.card_range,A,mul_assoc] using hh
  have hexp : (N:ℝ)^e*(N:ℝ)^α=(N:ℝ)^(profileTheta+ε) := by
    rw [←Real.rpow_add hNp e α]
    congr 1
    dsimp [e,α]
    ring
  have hcard : (S.card:ℝ)≤((Cs+H)*A)*(N:ℝ)^(profileTheta+ε) := by
    calc
      (S.card:ℝ)≤∑ j∈J,(Cs+H)*(N:ℝ)^α := real_cover_card S J T _ hcover hT
      _=(J.card:ℝ)*((Cs+H)*(N:ℝ)^α) := by simp
      _≤(A*(N:ℝ)^e)*((Cs+H)*(N:ℝ)^α) :=
        mul_le_mul_of_nonneg_right hJ (by positivity)
      _=((Cs+H)*A)*((N:ℝ)^e*(N:ℝ)^α) := by ring
      _=((Cs+H)*A)*(N:ℝ)^(profileTheta+ε) := by rw [hexp]
  simpa only [count_source_correspondence N] using hcard

/-- Preserve the original real cutoff by the natural floor adapter. -/
theorem real_pair_count : CF18RealPairCount := by
  intro hThue ε hε
  obtain ⟨C,hC,hcount⟩ := natural_pair_count hThue ε hε
  refine ⟨C,hC,?_⟩
  intro X hX
  have hfloor : 1≤Nat.floor X := Nat.le_floor (by exact_mod_cast hX)
  have hX₀ : 0≤X := by linarith
  have hp : 0≤profileTheta+ε := by norm_num [profileTheta]; linarith
  exact (hcount (Nat.floor X) hfloor).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hX₀) hp) hC.le)

end
end P0365Subquarter
