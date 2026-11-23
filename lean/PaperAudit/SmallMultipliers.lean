import PaperProofs.SmallMultipliers

namespace P0365Subquarter
noncomputable section
set_option pp.all true
#print CF03DyadicProductLabels
#print CF03SmallMultiplierLabels
#print CF03OriginalSmallMultiplierCount
#print CF03OriginalSmallMultiplierSubpower
#check (dyadic_product_labels : CF03DyadicProductLabels)
#check (small_multiplier_labels : CF03SmallMultiplierLabels)
#check (original_small_multiplier_count : CF03OriginalSmallMultiplierCount)
#check (original_small_multiplier_subpower : CF03OriginalSmallMultiplierSubpower)
#print axioms dyadic_product_labels
#print axioms small_multiplier_labels
#print axioms original_small_multiplier_count
#print axioms original_small_multiplier_subpower
set_option pp.all false

example : CF03DyadicProductLabels := by
  intro Y k S hS
  exact dyadic_product_labels Y k S hS
example : CF03SmallMultiplierLabels := by
  intro Y S hS
  exact small_multiplier_labels Y S hS
example : CF03OriginalSmallMultiplierCount := by
  intro hThue Y S hS
  exact original_small_multiplier_count hThue Y S hS
example : CF03OriginalSmallMultiplierSubpower := by
  intro hThue ε hε
  exact original_small_multiplier_subpower hThue ε hε

-- The positive product boundary Y0 is empty; Y1 allows just one label.
example (S : Finset (ℕ×ℕ))
    (hS : ∀ z ∈ S, 0<z.1 ∧ 0<z.2 ∧ z.1*z.2≤0) : S.card=0 := by
  have h := small_multiplier_labels 0 S hS
  simpa using h
example (S : Finset (ℕ×ℕ))
    (hS : ∀ z ∈ S, 0<z.1 ∧ 0<z.2 ∧ z.1*z.2≤1) : S.card≤1 := by
  simpa using small_multiplier_labels 1 S hS
-- The first dyadic bin can saturate the Y budget exactly.
example : ((Finset.Icc 1 4).image (fun v : ℕ => (1,v))).card=4 := by decide
-- Without positivity, product zero would allow more than zero labels.
example : (({(0,1),(0,2)}:Finset (ℕ×ℕ)).card>0) ∧
    (∀ z ∈ ({(0,1),(0,2)}:Finset (ℕ×ℕ)), z.1*z.2=0) := by decide
-- A dyadic range wholly above Y has no positive label.
example (S : Finset (ℕ×ℕ))
    (hS : ∀ z ∈ S, 0<z.1 ∧ 0<z.2 ∧ z.1*z.2≤1 ∧ 2≤z.1) : S=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hu,hv,hprod,hlo⟩ := hS z hz
  nlinarith
-- Fractional real cutoffs below one do not require division by Y or Stewart.
example (S : Finset ℕ)
    (hS : ∀ n ∈ S, ∃ b d u v : ℕ, PairSource n b d u v ∧ (u*v:ℝ)≤1/2) : S=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨b,d,u,v,hs,hp⟩ := hS n hn
  have hpos : 1≤u*v := Nat.succ_le_iff.mpr (Nat.mul_pos hs.2.2.1 hs.2.2.2.1)
  have hreal : (1:ℝ)≤(u:ℝ)*v := by exact_mod_cast hpos
  linarith
-- The genuine8/9 source lies at multiplier product3.
example : PairSource 8 2 1 1 3 ∧ (1:ℕ)*3≤3 := by
  constructor
  · norm_num [PairSource]
    exact Nat.prime_two.squarefree
  · decide

end
end P0365Subquarter
