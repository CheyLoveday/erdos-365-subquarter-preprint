import PaperTargets.WeightedMonomials
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

private theorem positive_square_step (h x : ℝ) (hh : 0<h) :
    2*h*max 0 x≤(max 0 (x+h))^2-(max 0 x)^2 := by
  by_cases hx : 0≤x
  · rw [max_eq_right hx,max_eq_right (by linarith : 0≤x+h)]
    nlinarith only [sq_nonneg h]
  · rw [max_eq_left (le_of_not_ge hx)]
    simp

private theorem positive_cube_step (h x : ℝ) (hh : 0<h) :
    3*h*(max 0 x)^2≤(max 0 (x+h))^3-(max 0 x)^3 := by
  by_cases hx : 0≤x
  · rw [max_eq_right hx,max_eq_right (by linarith : 0≤x+h)]
    nlinarith only [mul_nonneg (sq_nonneg h) hx,pow_nonneg hh.le 3]
  · rw [max_eq_left (le_of_not_ge hx)]
    simp

private theorem positive_sum (a T : ℝ) (ha : 0<a) (N : ℕ) :
    2*a*(∑ i ∈ Finset.range N, max 0 (T-a*(i:ℝ)))≤(max 0 (T+a))^2 := by
  let f : ℕ → ℝ := fun i => (max 0 (T+a-a*(i:ℝ)))^2
  have hstep (i : ℕ) : 2*a*max 0 (T-a*(i:ℝ))≤f i-f (i+1) := by
    have he₀ : T+a-a*(i:ℝ)=(T-a*(i:ℝ))+a := by ring
    have he₁ : T+a-a*((i+1:ℕ):ℝ)=T-a*(i:ℝ) := by push_cast; ring
    dsimp [f]
    rw [he₀,he₁]
    exact positive_square_step a _ ha
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range N) => hstep i)
  rw [←Finset.mul_sum,Finset.sum_range_sub'] at hh
  have hf : 0≤f N := sq_nonneg _
  have he : f 0=(max 0 (T+a))^2 := by simp [f]
  linarith

private theorem positive_square_sum (a T : ℝ) (ha : 0<a) (N : ℕ) :
    3*a*(∑ i ∈ Finset.range N, (max 0 (T-a*(i:ℝ)))^2)≤(max 0 (T+a))^3 := by
  let f : ℕ → ℝ := fun i => (max 0 (T+a-a*(i:ℝ)))^3
  have hstep (i : ℕ) : 3*a*(max 0 (T-a*(i:ℝ)))^2≤f i-f (i+1) := by
    have he₀ : T+a-a*(i:ℝ)=(T-a*(i:ℝ))+a := by ring
    have he₁ : T+a-a*((i+1:ℕ):ℝ)=T-a*(i:ℝ) := by push_cast; ring
    dsimp [f]
    rw [he₀,he₁]
    exact positive_cube_step a _ ha
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range N) => hstep i)
  rw [←Finset.mul_sum,Finset.sum_range_sub'] at hh
  have hf : 0≤f N := pow_nonneg (le_max_left _ _) _
  have he : f 0=(max 0 (T+a))^3 := by simp [f]
  linarith

/-- Finite telescoping twice gives the cubic lattice bound, with every terminal
positive-part term retained as nonnegative before discarding it. -/
theorem positive_part_rectangle : CF04PositivePartRectangle := by
  intro a b T ha hb hT N M
  let f : ℕ → ℝ := fun i => ∑ j ∈ Finset.range M, max 0 (T-a*(i:ℝ)-b*(j:ℝ))
  let g : ℕ → ℝ := fun i => (max 0 (T+b-a*(i:ℝ)))^2
  have hinner (i : ℕ) : 2*b*f i≤g i := by
    have hh := positive_sum b (T-a*(i:ℝ)) hb M
    have he : T-a*(i:ℝ)+b=T+b-a*(i:ℝ) := by ring
    simpa only [f,g,he] using hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range N) => hinner i)
  rw [←Finset.mul_sum] at hsum
  have hscaled := mul_le_mul_of_nonneg_left hsum (show 0≤3*a by positivity)
  have houter := positive_square_sum a (T+b) ha N
  have hmax : max 0 (T+b+a)=T+b+a := max_eq_right (by linarith)
  rw [hmax] at houter
  apply (le_div_iff₀ (by positivity : 0<6*a*b)).mpr
  change (∑ i ∈ Finset.range N, f i)*(6*a*b)≤_
  change 3*a*(∑ i ∈ Finset.range N, g i)≤(T+b+a)^3 at houter
  nlinarith only [hscaled,houter]

/-- The bounding rectangle is built from the actual finite exponent set.
No numerical distinctness or ordering of its weights is required. -/
theorem finite_weight_moment : CF04FiniteWeightMoment := by
  classical
  intro a b ha hb S T hT
  let w : ℕ×ℕ → ℝ := fun e => a*(e.1:ℝ)+b*(e.2:ℝ)
  let f : ℕ×ℕ → ℝ := fun e => max 0 (T-w e)
  obtain ⟨N,hN⟩ := (S.image Prod.fst).exists_nat_subset_range
  obtain ⟨M,hM⟩ := (S.image Prod.snd).exists_nat_subset_range
  have hsub : S⊆(Finset.range N).product (Finset.range M) := by
    intro e he
    exact Finset.mem_product.mpr ⟨hN (Finset.mem_image_of_mem Prod.fst he),
      hM (Finset.mem_image_of_mem Prod.snd he)⟩
  have hsum : (∑ e ∈ S, f e)≤∑ e ∈ (Finset.range N).product (Finset.range M), f e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => le_max_left _ _)
  have hrect := positive_part_rectangle a b T ha hb hT N M
  have hrect' : (∑ e ∈ (Finset.range N).product (Finset.range M), f e)≤
      (T+a+b)^3/(6*a*b) := by
    calc
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M, f (i,j) :=
        Finset.sum_product (Finset.range N) (Finset.range M) f
      _ ≤ _ := by simpa [f,w,sub_add_eq_sub_sub] using hrect
  have hpoint : (S.card:ℝ)*T≤(∑ e ∈ S, w e)+(∑ e ∈ S, f e) := by
    calc
      _ = ∑ _e ∈ S, T := by simp
      _ ≤ ∑ e ∈ S, (w e+f e) := by
        apply Finset.sum_le_sum
        intro e he
        have hh : T-w e≤max 0 (T-w e) := le_max_right _ _
        dsimp [f]
        linarith
      _ = _ := Finset.sum_add_distrib
  have hf := hsum.trans hrect'
  change (S.card:ℝ)*T-(T+a+b)^3/(6*a*b)≤∑ e ∈ S, w e
  linarith

/-- Optimizing the finite moment bound preserves the sharp leading constant.
If the optimizing T is negative, the claimed lower bound is already nonpositive. -/
theorem optimized_weight_moment : CF04OptimizedWeightMoment := by
  intro a b ha hb S
  let H : ℝ := S.card
  let R : ℝ := Real.sqrt (2*a*b*H)
  have hH : 0≤H := Nat.cast_nonneg _
  have hR : 0≤R := Real.sqrt_nonneg _
  have hR₂ : R^2=2*a*b*H := Real.sq_sqrt (by positivity)
  have hweights : 0≤∑ e ∈ S, (a*(e.1:ℝ)+b*(e.2:ℝ)) := by
    apply Finset.sum_nonneg
    intro e he
    positivity
  have hbound : (2/3)*H*R-H*(a+b)≤∑ e ∈ S, (a*(e.1:ℝ)+b*(e.2:ℝ)) := by
    by_cases hT : 0≤R-a-b
    · have hh := finite_weight_moment a b ha hb S (R-a-b) hT
      have he : R-a-b+a+b=R := by ring
      rw [he] at hh
      have hcube : R^3=2*a*b*H*R := by nlinarith only [congrArg (fun x : ℝ => x*R) hR₂]
      have hid : H*(R-a-b)-R^3/(6*a*b)=(2/3)*H*R-H*(a+b) := by
        field_simp [ha.ne',hb.ne']
        nlinarith only [hcube]
      change H*(R-a-b)-R^3/(6*a*b)≤_ at hh
      rwa [hid] at hh
    · have hh := mul_le_mul_of_nonneg_left (show R≤a+b by linarith) hH
      have hprod := mul_nonneg hH hR
      linarith
  refine ⟨hbound,?_⟩
  intro hab
  have hh := mul_le_mul_of_nonneg_left hab hH
  change (2/3)*H*R-2*H*b≤_
  linarith

end
end P0365Subquarter
