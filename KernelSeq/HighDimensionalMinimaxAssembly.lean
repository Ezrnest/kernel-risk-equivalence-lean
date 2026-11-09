import KernelSeq.HighDimensionalPhaseLimits
import KernelSeq.PinskerMinimaxAssembly

/-! Assemble the actual normalized spherical risks once both bounds hold. -/

namespace KernelSeq
open Filter Asymptotics
open scoped Topology
noncomputable section

theorem dimensionRisk_rate_of_normalized_limit {I : Type*} {l : Filter I}
    {d f : I → ℝ} {ζ C : ℝ} (hd : ∀ i, 0 < d i) (hC : C ≠ 0)
    (h : Tendsto (fun i => d i^ζ*f i) l (𝓝 C)) :
    f =Θ[l] (fun i => d i^(-ζ)) := by
  have hh : Tendsto (fun i => f i / d i^(-ζ)) l (𝓝 C) := by
    apply h.congr
    intro i
    rw [Real.rpow_neg (hd i).le, div_inv_eq_mul, mul_comm]
  exact (isTheta_of_div_tendsto_nhds_ne_zero hh hC).symm

theorem highDimensionalMinimax_of_bounds {I : Type*} {l : Filter I}
    (d R M : I → ℝ) {ζ C : ℝ} (hd : ∀ i, 0 < d i) (hC : 0 < C)
    (hR : Tendsto (fun i => d i^ζ*R i) l (𝓝 C))
    (hRM : ∀ᶠ i in l, M i ≤ R i)
    (hM : ∀ δ, 0 < δ → δ < 1 → ∀ ε > 0,
      ∀ᶠ i in l, C*(1-δ)-ε ≤ d i^ζ*M i) :
    Tendsto (fun i => d i^ζ*M i) l (𝓝 C) ∧
      Tendsto (fun i => R i/M i) l (𝓝 1) ∧
      M =Θ[l] (fun i => d i^(-ζ)) := by
  have hUpper (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in l, d i^ζ*M i ≤ C+ε := by
    filter_upwards [hRM,hR.eventually (gt_mem_nhds (show C < C+ε by linarith))] with i hi hu
    exact (mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (hd i).le _)).trans hu.le
  have hLower (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ i in l, C*(1-δ)^(1 : ℝ)-ε ≤ d i^ζ*M i := by
    simpa only [Real.rpow_one] using hM δ hδ hδ1 ε hε
  have hL := tendsto_of_pinsker_shaved_bounds (fun i => d i^ζ*M i)
    hC zero_lt_one le_rfl hUpper hLower
  have hRatio := hR.div hL hC.ne'
  rw [div_self hC.ne'] at hRatio
  refine ⟨hL,hRatio.congr (fun i => ?_),dimensionRisk_rate_of_normalized_limit hd hC.ne' hL⟩
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos (hd i) ζ).ne'

theorem highDimensional_rate_of_minimax_le {I : Type*} {l : Filter I}
    {d M W : I → ℝ} {ζ C : ℝ} (hd : ∀ i, 0 < d i) (hC : 0 < C)
    (hM : Tendsto (fun i => d i^ζ*M i) l (𝓝 C))
    (hW0 : ∀ᶠ i in l, 0 ≤ W i)
    (hMW : ∀ᶠ i in l, M i ≤ W i)
    (hW : W =O[l] (fun i => d i^(-ζ))) :
    W =Θ[l] (fun i => d i^(-ζ)) ∧ W =Θ[l] M := by
  have hMθ := dimensionRisk_rate_of_normalized_limit hd hC.ne' hM
  have hMle : M =O[l] W := by
    apply IsBigO.of_bound 1
    filter_upwards [hMW,hW0,hM.eventually (lt_mem_nhds hC)] with i hi hw hm
    have hm' : 0 < M i := pos_of_mul_pos_right hm (Real.rpow_nonneg (hd i).le _)
    simpa only [Real.norm_eq_abs,abs_of_pos hm',abs_of_nonneg hw,one_mul] using hi
  have hθ : W =Θ[l] (fun i => d i^(-ζ)) := ⟨hW,hMθ.symm.isBigO.trans hMle⟩
  exact ⟨hθ,hθ.trans hMθ.symm⟩

end
end KernelSeq
