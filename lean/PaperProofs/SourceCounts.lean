import PaperTargets.SourceCounts
import PaperProofs.ThueLevels

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Fixed nonzero content gives one level, rather than a divisor inventory. -/
theorem fixed_content_level_bound : CF15FixedContentLevelBound := by
  classical
  intro hThue Q c R g ell σ hdispatch hc hR hg hell hσ S hS
  by_cases hempty : S=∅
  · simp [hempty]
  obtain ⟨z₀,hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  let h := MvPolynomial.eval z₀ Q
  have heq : (c:ℤ)*h=σ*(g:ℤ)^ell := (hS z₀ hz₀).2
  have hcZ : (c:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hc
  have hg₀ : g≠0 := by
    intro hz
    exact hR (zero_dvd_iff.mp (by simpa [hz] using hg))
  have hgZ : (g:ℤ)≠0 := by exact_mod_cast hg₀
  have hσ₀ : σ≠0 := by rcases hσ with rfl | rfl <;> norm_num
  have hnonzero : σ*(g:ℤ)^ell≠0 := mul_ne_zero hσ₀ (pow_ne_zero _ hgZ)
  have hh : h≠0 := by intro hz; rw [hz,mul_zero] at heq; exact hnonzero heq.symm
  have habs : c*h.natAbs=g^ell := by
    have ha := congrArg Int.natAbs heq
    rcases hσ with rfl | rfl <;> simpa [Int.natAbs_mul] using ha
  have hdiv : h.natAbs ∣ g^ell := by rw [←habs]; exact dvd_mul_left _ _
  have hlevel := selected_factor_level_budget hThue Q hdispatch h hh S (by
    intro z hz
    exact ⟨(hS z hz).1,mul_left_cancel₀ hcZ ((hS z hz).2.trans heq.symm)⟩)
  obtain ⟨htau,hpow,hlow⟩ := resultant_level_charges R g h.natAbs ell hR hg hdiv hell
  have htauR : 1≤divisorCount R := by
    exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,hR⟩⟩)
  have hp67 : (divisorCount R)^6≤(divisorCount R)^7 := pow_le_pow_right₀ htauR (by decide : 6≤7)
  have hhigh : 61600*divisorCount h.natAbs*11^(primeSupportCount h.natAbs)≤
      61600*(divisorCount R)^7 := by
    calc
      _ ≤ (61600*(divisorCount R)^3)*(divisorCount R)^4 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ htau) (hpow 11 le_rfl)
      _ = _ := by ring
  calc
    S.card ≤ 16*(divisorCount h.natAbs)^2+
        61600*divisorCount h.natAbs*11^(primeSupportCount h.natAbs) := hlevel
    _ ≤ 16*(divisorCount R)^6+61600*(divisorCount R)^7 := add_le_add hlow hhigh
    _ ≤ 16*(divisorCount R)^7+61600*(divisorCount R)^7 :=
      add_le_add (Nat.mul_le_mul_left 16 hp67) le_rfl
    _ = _ := by ring

private theorem finite_fiber_bound {α β : Type} [DecidableEq β] (S : Finset α) (T : Finset β)
    (f : α → β) (k : ℕ) (hmap : ∀ z ∈ S, f z ∈ T)
    (hfib : ∀ r ∈ T, (S.filter (fun z => f z=r)).card ≤ k) : S.card ≤ T.card*k := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := T) (fun z hz => hmap z hz)]
  calc
    _ ≤ ∑ r ∈ T, k := Finset.sum_le_sum hfib
    _ = _ := by simp

/-- Assign each point one evaluated gcd and sign. The content stays fixed. -/
theorem fixed_content_divisor_count : CF15FixedContentDivisorCount := by
  classical
  intro hThue Q c R ell hdispatch hc hR hell S hS
  let T := R.divisors.product ({1,-1}:Finset ℤ)
  have hchoose : ∀ z : Fin 2 → ℤ, ∃ l : ℕ × ℤ, z∈S →
      l∈T ∧ (c:ℤ)*MvPolynomial.eval z Q=l.2*(l.1:ℤ)^ell := by
    intro z
    by_cases hz : z∈S
    · obtain ⟨g,σ,hg,hσ,he⟩ := (hS z hz).2
      refine ⟨(g,σ),fun _ => ⟨?_,he⟩⟩
      exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hg,hR⟩,by simpa using hσ⟩
    · exact ⟨(1,1),fun h => False.elim (hz h)⟩
  choose label hlabel using hchoose
  have hmap (z : Fin 2 → ℤ) (hz : z∈S) : label z∈T := (hlabel z hz).1
  have hfib (l : ℕ × ℤ) (hl : l∈T) :
      (S.filter (fun z => label z=l)).card≤61616*(divisorCount R)^7 := by
    have hmem := Finset.mem_product.mp hl
    have hsign : l.2=1 ∨ l.2= -1 := by simpa using hmem.2
    apply fixed_content_level_bound hThue Q c R l.1 ell l.2 hdispatch hc hR
      (Nat.dvd_of_mem_divisors hmem.1) hell hsign
    intro z hz
    obtain ⟨hzS,he⟩ := Finset.mem_filter.mp hz
    refine ⟨(hS z hzS).1,?_⟩
    simpa only [he] using (hlabel z hzS).2
  have hcard : T.card≤2*divisorCount R := by
    dsimp [T]
    rw [Finset.card_product]
    have hs : ({1,-1}:Finset ℤ).card=2 := by decide
    rw [hs]
    dsimp [divisorCount]
    omega
  calc
    S.card ≤ T.card*(61616*(divisorCount R)^7) := finite_fiber_bound S T label _ hmap hfib
    _ ≤ (2*divisorCount R)*(61616*(divisorCount R)^7) := Nat.mul_le_mul_right _ hcard
    _ = _ := by ring

/-- The actual source supplies its primitive parameter, gcd and sign. -/
theorem actual_graph_parameter_count : CF15ActualGraphParameterCount := by
  intro hThue X D A B hX hg hr inverse S hS
  let H := graphPullback inverse A B
  let Q := binaryPrimitivePart H
  let c := binaryContent H
  let R := (fullGraphResultant A B).natAbs
  have hH : H≠0 := (actual_mixed_pullback X D A B hX hg hr inverse).2.2.1
  obtain ⟨hc,_,_,heval⟩ := binary_content_removal H hH
  obtain ⟨hR,_,hactual⟩ := actual_source_resultant_level X D A B hX hg hr
  have hRn : R≠0 := by intro hz; exact hR (Int.natAbs_eq_zero.mp hz)
  have hdispatch : binaryFactorDispatch Q := actual_graph_factor_dispatch X D A B hX hg hr inverse
  apply fixed_content_divisor_count hThue Q c R (graphLevelPower inverse) hdispatch hc hRn
    (by cases inverse <;> norm_num [graphLevelPower]) S
  intro z hz
  obtain ⟨n,b,d,u,v,hs,hbranch,hparam⟩ := hS z hz
  have hprimitive : primitiveBinaryPoint z := by
    rw [←hparam]
    cases inverse
    · simpa [primitiveBinaryPoint,graphParameter] using (primitive_ratios n b d u v hs).1.isCoprime
    · simpa [primitiveBinaryPoint,graphParameter] using (primitive_ratios n b d u v hs).2.1.isCoprime
  obtain ⟨hdiv,hrec,_⟩ := hactual inverse n b d u v hs hbranch
  obtain ⟨σ,hσ,_,_,_,hlevel⟩ := hrec
  refine ⟨hprimitive,sourceGraphGCD inverse A B b d u v,(if inverse then σ else 1),hdiv,?_,?_⟩
  · cases inverse
    · exact Or.inl rfl
    · exact hσ
  · rw [←hparam]
    exact (heval _).symm.trans hlevel

/-- A graph parameter fixes the partner ratio, hence the original start. -/
theorem graph_parameter_injection : CF15GraphParameterInjection := by
  intro inverse A B n m b d u v b' d' u' v' hs hs' hbranch hbranch' hparam
  cases inverse
  · have hb : b=b' := by have h := congrFun hparam 0; simpa [graphParameter] using h
    have hd : d=d' := by have h := congrFun hparam 1; simpa [graphParameter] using h
    subst b'
    subst d'
    have ht : (v:ℚ)/u=(v':ℚ)/u' := hbranch.2.2.trans hbranch'.2.2.symm
    apply source_ratio_injection n m b d u v b d u' v' hs hs'
    exact Prod.ext rfl ht
  · have hv : v=v' := by have h := congrFun hparam 0; simpa [graphParameter] using h
    have hu : u=u' := by have h := congrFun hparam 1; simpa [graphParameter] using h
    subst v'
    subst u'
    have ht : (b:ℚ)/d=(b':ℚ)/d' := hbranch.2.2.trans hbranch'.2.2.symm
    apply source_ratio_injection n m b d u v b' d' u v hs hs'
    exact Prod.ext ht rfl

/-- Choose canonical witnesses; injectivity preserves the original cardinal. -/
theorem actual_graph_source_count : CF15ActualGraphSourceCount := by
  classical
  intro hThue X D A B hX hg hr inverse S hS
  have hw : ∀ n : ℕ, ∃ b d u v : ℕ, n∈S →
      PairSource n b d u v ∧ sourceGraphBranch inverse A B b d u v := by
    intro n
    by_cases hn : n∈S
    · obtain ⟨b,d,u,v,hs,hbranch⟩ := hS n hn
      exact ⟨b,d,u,v,fun _ => ⟨hs,hbranch⟩⟩
    · exact ⟨0,0,0,0,fun h => False.elim (hn h)⟩
  choose b d u v hsource using hw
  let z : ℕ → Fin 2 → ℤ := fun n => graphParameter inverse (b n) (d n) (u n) (v n)
  have hinj : Set.InjOn z (↑S:Set ℕ) := by
    intro n hn m hm he
    exact graph_parameter_injection inverse A B n m (b n) (d n) (u n) (v n)
      (b m) (d m) (u m) (v m) (hsource n hn).1 (hsource m hm).1
      (hsource n hn).2 (hsource m hm).2 he
  have hcard : (S.image z).card=S.card := Finset.card_image_of_injOn hinj
  calc
    S.card=(S.image z).card := hcard.symm
    _ ≤ _ := actual_graph_parameter_count hThue X D A B hX hg hr inverse (S.image z) (by
      intro y hy
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hy
      exact ⟨n,b n,d n,u n,v n,(hsource n hn).1,(hsource n hn).2,rfl⟩)

/-- The actual full resultant's uniform subpower growth pays the full budget. -/
theorem actual_graph_source_subpower : CF15ActualGraphSourceSubpower := by
  intro hThue ε hε
  obtain ⟨C,hC,hbound⟩ := actual_graph_divisor_growth ε hε
  refine ⟨123232*C,by positivity,?_⟩
  intro X D A B hX hg hr inverse S hS
  calc
    (S.card:ℝ)≤123232*(divisorCount (fullGraphResultant A B).natAbs:ℝ)^8 := by
      exact_mod_cast actual_graph_source_count hThue X D A B hX hg hr inverse S hS
    _ ≤ 123232*(C*X^ε) := mul_le_mul_of_nonneg_left (hbound X D A B hX hg hr).2 (by norm_num)
    _ = _ := by ring

end
end P0365Subquarter
