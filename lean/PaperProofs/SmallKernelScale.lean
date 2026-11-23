import PaperTargets.SmallKernelScale
import PaperProofs.SmallKernels
import PaperProofs.RulingCounts

namespace P0365Subquarter
noncomputable section
set_option autoImplicit false

/-- Floors retain the original population; the existing elementary logarithm
bound pays the finite Pell factor uniformly at the original real shell scale. -/
theorem original_small_kernel_subpower : CF02OriginalSmallKernelSubpower := by
  intro ε hε
  obtain ⟨C,hC,hlog⟩ := ruling_log_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro X Y hX hY S hS
  let N := Nat.floor (2*X)
  let K := Nat.floor Y
  have hN : (N:ℝ)≤2*X := Nat.floor_le (by linarith)
  have hK : (K:ℝ)≤Y := Nat.floor_le hY
  have hnat := small_kernel_product_count K N S (by
    intro n hn
    obtain ⟨hnX,b,d,u,v,hs,hp⟩ := hS n hn
    refine ⟨Nat.le_floor hnX,b,d,u,v,hs,?_⟩
    apply Nat.le_floor
    exact_mod_cast hp)
  have hlogs : Nat.log 2 (2*N+1)+1≤8401+Nat.log 2 (2*N+1) := by omega
  have hb : ((Nat.log 2 (2*N+1)+1:ℕ):ℝ)≤C*X^ε := by
    have hh : ((Nat.log 2 (2*N+1)+1:ℕ):ℝ)≤(8401+Nat.log 2 (2*N+1):ℝ) := by
      exact_mod_cast hlogs
    exact hh.trans (hlog X hX N hN)
  calc
    (S.card:ℝ) ≤ (K:ℝ)*((Nat.log 2 (2*N+1)+1:ℕ):ℝ) := by exact_mod_cast hnat
    _ ≤ Y*(C*X^ε) := mul_le_mul hK hb (by positivity) hY
    _ = C*Y*X^ε := by ring

end
end P0365Subquarter
