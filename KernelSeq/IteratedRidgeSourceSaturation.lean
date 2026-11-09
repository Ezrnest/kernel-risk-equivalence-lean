import KernelSeq.SourceQualification
import KernelSeq.IteratedRidgeFilter

/-!
# Actual source-ball saturation for iterated ridge

The lower bound uses one actual positive population spectral direction as a
source-ball target. No lower bound on the coordinates of an arbitrary target
is assumed. The constants are independent of the regularization parameter.
-/

open MeasureTheory
open scoped Classical

namespace KernelSeq
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

theorem featureSourceWorstBias_iteratedRidge_le (k : X → H) (hk : MemLp k 2 μ)
    {lam M s R : ℝ} {ν : ℕ} (hlam : 0 < lam) (hν : 0 < ν)
    (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) :
    featureSourceWorstBias k hk s hs R (ResidualFilter.iteratedRidge lam ν) ≤
      ((ν : ℝ)+1)^2 * (1+M)^(s-min s (2*(ν : ℝ))) * R^2 *
        lam^(min s (2*(ν : ℝ))) :=
  featureSourceWorstBias_le_qualification k hk _ hlam hs hR hM
    (ResidualFilter.iteratedRidge_spectralFilter hlam ν)
    (ResidualFilter.iteratedRidge_contract hlam hν)

/-- A source vector in one genuine positive eigendirection supplies the
lower bound, including multiplicities and an arbitrary ambient prediction space. -/
theorem featureSourceWorstBias_iteratedRidge_ge_direction
    (k : X → H) (hk : MemLp k 2 μ)
    {lam M s R : ℝ} (ν : ℕ) (hlam : 0 < lam) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) (hsmall : lam ≤ i.1.1) :
    R^2 * i.1.1^s / (2*i.1.1)^(2*ν) * lam^(2*ν) ≤
      featureSourceWorstBias k hk s hs R (ResidualFilter.iteratedRidge lam ν) := by
  have hr : lam/(2*i.1.1) ≤ lam/(i.1.1+lam) :=
    div_le_div_of_nonneg_left hlam.le (by linarith [i.2]) (by linarith)
  have hrsq := pow_le_pow_left₀
    (div_nonneg hlam.le (by linarith [i.2] : 0 ≤ 2*i.1.1)) hr (2*ν)
  have hweight : i.1.1^s / (2*i.1.1)^(2*ν) * lam^(2*ν) ≤
      featureSourceBiasWeight k hk s (ResidualFilter.iteratedRidge lam ν) i := by
    have hm := mul_le_mul_of_nonneg_left hrsq (Real.rpow_nonneg i.2.le s)
    unfold featureSourceBiasWeight
    rw [ResidualFilter.iteratedRidge_residual (by linarith [i.2] : i.1.1+lam ≠ 0)]
    calc
      _ = i.1.1^s * (lam/(2*i.1.1))^(2*ν) := by rw [div_pow]; ring
      _ ≤ i.1.1^s * (lam/(i.1.1+lam))^(2*ν) := hm
      _ = _ := by rw [← pow_mul]; congr 2; omega
  rw [featureSourceWorstBias_eq k hk hs hR hM _
    (ResidualFilter.iteratedRidge_spectralFilter hlam ν)]
  have hi := featureSourceBiasWeight_le_spectralSup k hk hs hM
    (ResidualFilter.iteratedRidge lam ν) (ResidualFilter.iteratedRidge_spectralFilter hlam ν) i
  calc
    _ = R^2 * (i.1.1^s / (2*i.1.1)^(2*ν) * lam^(2*ν)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hweight.trans hi) (sq_nonneg R)

/-- For smoothness at least `2ν`, the actual worst prediction bias over the
source ball is comparable to `lam^(2ν)`, uniformly on `0 < lam ≤ t_i`. -/
theorem featureSourceWorstBias_iteratedRidge_saturation
    (k : X → H) (hk : MemLp k 2 μ)
    {M s R : ℝ} {ν : ℕ} (hν : 0 < ν) (hs : 2*(ν : ℝ) ≤ s) (hR : 0 < R)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (i : PredictionSingularIndex (featureEmbedding μ k hk)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ i.1.1 →
      c*lam^(2*ν) ≤ featureSourceWorstBias k hk s
          (by exact (show 0 ≤ 2*(ν : ℝ) by positivity).trans hs : 0 ≤ s) R (ResidualFilter.iteratedRidge lam ν) ∧
      featureSourceWorstBias k hk s (by exact (show 0 ≤ 2*(ν : ℝ) by positivity).trans hs : 0 ≤ s) R
          (ResidualFilter.iteratedRidge lam ν) ≤ C*lam^(2*ν) := by
  let c := R^2 * i.1.1^s / (2*i.1.1)^(2*ν)
  let C := ((ν : ℝ)+1)^2 * (1+M)^(s-2*(ν : ℝ)) * R^2
  have hMn : 0 ≤ M := (norm_nonneg _).trans hM
  have ht : 0 < i.1.1 := i.2
  have hs0 : 0 ≤ s := (show 0 ≤ 2*(ν : ℝ) by positivity).trans hs
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨c, C, hc, hC, ?_⟩
  intro lam hlam hsmall
  constructor
  · exact featureSourceWorstBias_iteratedRidge_ge_direction k hk ν hlam
      hs0 hR.le hM i hsmall
  · have hexp : 2*(ν : ℝ) = ((2*ν : ℕ) : ℝ) := by push_cast; ring
    have hb := featureSourceWorstBias_iteratedRidge_le k hk hlam hν hs0 hR.le hM
    rw [min_eq_right hs] at hb
    simpa only [hexp, Real.rpow_natCast, C] using hb

end
end KernelSeq
