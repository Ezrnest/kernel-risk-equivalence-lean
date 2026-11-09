import KernelSeq.CommonVarianceBernstein
import KernelSeq.InfiniteBernstein

/-!
# Discharging the actual covariance Bernstein interface

The common-variance matrix theorem proves the exact finite interface used by
all covariance applications. The zero-sample case is handled as an empty
tail event. Hence the finite spectral-subspace interface is supplied by a
theorem, rather than an external proof parameter. The older broader general
sum-variance Bernstein proposition is not asserted or needed here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ι H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace Ω]

/-- The exact common-majorant finite Bernstein proposition is now proved. -/
theorem finiteUniformIntrinsicBernstein_proved (b : HilbertBasis ι ℝ H) (P : Measure Ω) :
    FiniteUniformIntrinsicBernstein b P := by
  intro hP hFin
  letI : IsProbabilityMeasure P := hP
  letI : FiniteDimensional ℝ H := hFin
  letI : Finite ι := b.orthonormal.linearIndependent.finite
  letI : Fintype ι := Fintype.ofFinite _
  intro n Y R V t hR0 hYm _hYi _hY2 hind hmean hY hR _hVp hvar hVnorm ht
  by_cases hn : n = 0
  · subst n
    have ht0 : 0 < t := by
      have hs := Real.sqrt_pos.mpr hVnorm
      linarith
    have hempty : {ω | t ≤ ‖∑ i : Fin 0, Y i ω‖} = ∅ := by
      ext ω
      simp [not_le.mpr ht0]
    rw [hempty, measure_empty]
    exact bot_le
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hinv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnR
  let W : H →L[ℝ] H := (n : ℝ)⁻¹ • V
  have hWnorm : 0 < ‖W‖ := by
    rw [show W = (n : ℝ)⁻¹ • V by rfl, norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
    exact mul_pos hinv hVnorm
  have hv : (n : ℝ) * ‖W‖ = ‖V‖ := by
    rw [show W = (n : ℝ)⁻¹ • V by rfl, norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
    field_simp [hnR.ne']
  have htrace : basisTrace b W / ‖W‖ = basisTrace b V / ‖V‖ := by
    rw [show W = (n : ℝ)⁻¹ • V by rfl,
      basisTrace_smul b (n : ℝ)⁻¹ V (hasSum_fintype _).summable,
      norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
    field_simp [hnR.ne', hVnorm.ne']
  have htW : Real.sqrt ((n : ℝ) * ‖W‖) + R / 3 ≤ t := by simpa only [hv] using ht
  have htail := finite_commonVariance_bernstein b hn0 Y hYm hind hY hR0 hR hmean
    W hWnorm hvar t htW
  simpa only [hv, htrace] using htail

omit [CompleteSpace H] in
/-- Every actual finite spectral compression now has a proved Bernstein
instance. No model-specific concentration rate is an input. -/
theorem finiteSpectralBernstein_proved (b : HilbertBasis ι ℝ H) (P : Measure Ω) :
    FiniteSpectralBernstein b P := by
  intro s
  exact finiteUniformIntrinsicBernstein_proved (finiteCompressionBasis b s) P

end
end KernelSeq
