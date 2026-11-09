import KernelSeq.AuxiliaryFilter

/-!
# Spectral clipping

The clipping filter satisfies spectral admissibility and the logarithmic
residual contract, including at the kink.
The constants are uniform in the regularization and spectral upper bound.
-/

namespace KernelSeq.ResidualFilter

noncomputable section

/-- The actual nonsmooth spectral clipping inverse filter. -/
def clipping (lam t : ℝ) : ℝ := 1 / max t lam

theorem clipping_shrinkage {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    shrinkage (clipping lam) t = min (t / lam) 1 := by
  unfold shrinkage clipping
  by_cases ht : t ≤ lam
  · rw [max_eq_right ht, min_eq_left ((div_le_one hlam).2 ht), mul_one_div]
  · have hlt : lam < t := lt_of_not_ge ht
    rw [max_eq_left hlt.le, min_eq_right ((le_div_iff₀ hlam).2 (by simpa using hlt.le))]
    exact mul_one_div_cancel (ne_of_gt (hlam.trans hlt))

theorem clipping_residual {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    residual (clipping lam) t = max (1 - t / lam) 0 := by
  rw [residual, clipping_shrinkage hlam]
  by_cases ht : t / lam ≤ 1
  · rw [min_eq_left ht, max_eq_left (sub_nonneg.mpr ht)]
  · rw [min_eq_right (le_of_not_ge ht), max_eq_right (by linarith)]
    ring

theorem continuous_clipping {lam : ℝ} (hlam : 0 < lam) : Continuous (clipping lam) := by
  apply continuous_const.div (continuous_id.max continuous_const)
  intro t
  exact ne_of_gt (hlam.trans_le (le_max_right t lam))

/-- Borel admissibility holds on the closed spectral interval, with no exclusion
of zero or the threshold. -/
theorem clipping_spectralFilter {lam M : ℝ} (hlam : 0 < lam) :
    SpectralFilter M (clipping lam) := by
  constructor
  · exact ((continuous_clipping hlam).comp continuous_subtype_val).measurable
  · intro t _
    exact one_div_nonneg.mpr (hlam.le.trans (le_max_right t lam))
  · intro t ht
    rw [clipping_shrinkage hlam]
    exact ⟨le_min (div_nonneg ht.1 hlam.le) (by norm_num), min_le_right _ _⟩

theorem clipping_inverse_size {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    |(t + lam) * clipping lam t| ≤ 2 := by
  have hm : 0 < max t lam := hlam.trans_le (le_max_right _ _)
  rw [clipping, mul_one_div, abs_of_nonneg (div_nonneg (by positivity) hm.le)]
  apply (div_le_iff₀ hm).2
  linarith [le_max_left t lam, le_max_right t lam]

private def clippedExp (u : ℝ) : ℝ := min (Real.exp u - 1) 1

private theorem clippedExp_mem {u : ℝ} (hu : 0 ≤ u) : clippedExp u ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_min (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hu)) (by norm_num), min_le_right _ _⟩

private theorem clippedExp_eq (u : ℝ) :
    clippedExp u = Real.exp (min u (Real.log 2)) - 1 := by
  by_cases hu : u ≤ Real.log 2
  · rw [min_eq_left hu, clippedExp, min_eq_left]
    have h := Real.exp_le_exp.mpr hu
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  · have he : 1 ≤ Real.exp u - 1 := by
      have h := Real.exp_le_exp.mpr (le_of_not_ge hu)
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
      linarith
    rw [min_eq_right (le_of_not_ge hu), Real.exp_log (by norm_num : (0 : ℝ) < 2),
      clippedExp, min_eq_right he]
    norm_num

private theorem clippedExp_lipschitz (u v : ℝ) :
    |clippedExp u - clippedExp v| ≤ 2 * |u - v| := by
  have hmin : |min u (Real.log 2) - min v (Real.log 2)| ≤ |u - v| := by
    simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (u - v))] using
      abs_min_sub_min_le_max u (Real.log 2) v (Real.log 2)
  rw [clippedExp_eq, clippedExp_eq]
  have he := abs_exp_sub_exp_le_upper (min_le_right u (Real.log 2))
    (min_le_right v (Real.log 2))
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have heq : (Real.exp (min u (Real.log 2)) - 1) -
      (Real.exp (min v (Real.log 2)) - 1) =
      Real.exp (min u (Real.log 2)) - Real.exp (min v (Real.log 2)) := by ring
  rw [heq]
  exact he.trans (mul_le_mul_of_nonneg_left hmin (by norm_num))

theorem clipping_weightedResidual {lam u : ℝ} (hlam : 0 < lam) :
    weightedResidual lam 1 (clipping lam) u = 1 - (clippedExp u) ^ 2 := by
  have hcoord : spectralCoordinate lam u / lam = Real.exp u - 1 := by
    unfold spectralCoordinate
    field_simp
  rw [weightedResidual, Real.rpow_one, residual, clipping_shrinkage hlam, hcoord]
  unfold clippedExp
  have hrat : (spectralCoordinate lam u + lam) / lam = Real.exp u := by
    unfold spectralCoordinate
    field_simp
    ring
  rw [hrat]
  by_cases hu : Real.exp u - 1 ≤ 1
  · rw [min_eq_left hu]
    ring
  · rw [min_eq_right (le_of_not_ge hu)]
    ring

theorem clipping_weightedResidual_mem {lam u : ℝ} (hlam : 0 < lam) (hu : 0 ≤ u) :
    weightedResidual lam 1 (clipping lam) u ∈ Set.Icc (0 : ℝ) 1 := by
  rw [clipping_weightedResidual hlam]
  have hq := clippedExp_mem hu
  constructor <;> nlinarith [hq.1, hq.2, sq_nonneg (clippedExp u)]

/-- The residual contract for clipping has `ρ=1`, `A=4`, uniformly in `lam,M`.
The proof controls the kink directly, without a derivative hypothesis there. -/
theorem clipping_contract {lam M : ℝ} (hlam : 0 < lam) :
    Contract lam M 1 4 (clipping lam) := by
  constructor
  · norm_num
  · intro u hu
    have hP := clipping_weightedResidual_mem hlam hu.1
    have hF := clipping_inverse_size hlam (spectralCoordinate_nonneg hlam.le hu.1)
    change |inverseProfile lam (clipping lam) u| + |weightedResidual lam 1 (clipping lam) u| ≤ 4
    rw [abs_of_nonneg hP.1]
    exact (add_le_add hF hP.2).trans (by norm_num)
  · intro u hu v hv
    rw [clipping_weightedResidual hlam, clipping_weightedResidual hlam]
    have hqu := clippedExp_mem hu.1
    have hqv := clippedExp_mem hv.1
    have hsum : |clippedExp u + clippedExp v| ≤ 2 := by
      rw [abs_of_nonneg (add_nonneg hqu.1 hqv.1)]
      linarith [hqu.2, hqv.2]
    calc
      |(1 - clippedExp u ^ 2) - (1 - clippedExp v ^ 2)| =
          |clippedExp u - clippedExp v| * |clippedExp u + clippedExp v| := by
        rw [← abs_mul]
        apply abs_eq_abs.mpr
        right
        ring
      _ ≤ |clippedExp u - clippedExp v| * 2 :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ ≤ (2 * |u - v|) * 2 := mul_le_mul_of_nonneg_right (clippedExp_lipschitz u v) (by norm_num)
      _ = 4 * |u - v| := by ring

theorem clipping_zero {lam : ℝ} (hlam : 0 < lam) : clipping lam 0 = lam⁻¹ := by
  simp [clipping, max_eq_right hlam.le, one_div]

theorem clipping_at_threshold (lam : ℝ) : clipping lam lam = lam⁻¹ := by
  simp [clipping, one_div]

theorem clipping_residual_zero (lam : ℝ) : residual (clipping lam) 0 = 1 := by
  simp [residual, shrinkage]

theorem clipping_residual_at_threshold {lam : ℝ} (hlam : 0 < lam) :
    residual (clipping lam) lam = 0 := by
  rw [clipping_residual hlam]
  simp [hlam.ne']

end
end KernelSeq.ResidualFilter
