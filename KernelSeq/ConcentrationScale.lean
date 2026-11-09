import KernelSeq.FilterDimension

/-!
# Variance compatibility and intrinsic Bernstein scales

A deterministic rate reduction under variance compatibility.
The retention may approach zero: no positive lower bound on it is imposed.
The actual filter-dimension comparison supplies the scalar majorant used by
the model specialization at the end.
-/

open Filter Topology

namespace KernelSeq

noncomputable def dimensionLog (N : ℝ) : ℝ := Real.log (Real.exp 1 + N)

noncomputable def intrinsicDimensionLog (N r : ℝ) : ℝ :=
  Real.log (Real.exp 1 + N / r)

theorem one_le_dimensionLog {N : ℝ} (hN : 0 ≤ N) : 1 ≤ dimensionLog N := by
  have h := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hN)
  simpa only [Real.log_exp, dimensionLog] using h

theorem intrinsicDimensionLog_le {N r : ℝ} (hN : 0 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) :
    intrinsicDimensionLog N r ≤ dimensionLog N + Real.log (1 / r) := by
  have he : Real.exp 1 + N / r ≤ (Real.exp 1 + N) / r := by
    apply (le_div_iff₀ hr).mpr
    have he := mul_le_of_le_one_right (Real.exp_pos 1).le hr1
    rw [add_mul, div_mul_cancel₀ N hr.ne']
    linarith
  have hl := Real.log_le_log (add_pos_of_pos_of_nonneg (Real.exp_pos 1)
    (div_nonneg hN hr.le)) he
  rw [Real.log_div (ne_of_gt (add_pos_of_pos_of_nonneg (Real.exp_pos 1) hN)) hr.ne'] at hl
  simpa only [dimensionLog, intrinsicDimensionLog, one_div, Real.log_inv, sub_eq_add_neg] using hl

theorem retention_mul_log_inverse_le_one {r : ℝ} (hr : 0 < r) :
    r * Real.log (1 / r) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (one_div_pos.mpr hr)
  have hm := mul_le_mul_of_nonneg_left h hr.le
  have he : r * (1 / r - 1) = 1 - r := by field_simp
  rw [he] at hm
  exact hm.trans (sub_le_self _ hr.le)

/-- The intrinsic square-root variance term is bounded by the ordinary
dimension-log variance term, uniformly even as retention tends to zero. -/
theorem retention_mul_intrinsicDimensionLog_le {N r : ℝ}
    (hN : 0 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) :
    r * intrinsicDimensionLog N r ≤ 2 * dimensionLog N := by
  have hl := mul_le_mul_of_nonneg_left (intrinsicDimensionLog_le hN hr hr1) hr.le
  have hlog := one_le_dimensionLog hN
  have hfirst := mul_le_of_le_one_left (by linarith : 0 ≤ dimensionLog N) hr1
  have hsecond := retention_mul_log_inverse_le_one hr
  nlinarith

/-- The linear Bernstein term divided by the ordinary square-root scale is
bounded by two quantities forced to zero by variance compatibility. -/
theorem intrinsic_linear_ratio_le {u N r : ℝ} (hu : 0 ≤ u)
    (hN : 0 ≤ N) (hr : 0 < r) (hr1 : r ≤ 1) :
    u * intrinsicDimensionLog N r / dimensionLog N ≤ u + u / r := by
  have hlog := one_le_dimensionLog hN
  have hlogpos : 0 < dimensionLog N := by linarith
  have hsmall : Real.log (1 / r) ≤ dimensionLog N / r := by
    apply (le_div_iff₀ hr).mpr
    have h := retention_mul_log_inverse_le_one hr
    nlinarith
  have hle : intrinsicDimensionLog N r ≤ dimensionLog N * (1 + 1 / r) := by
    calc
      _ ≤ dimensionLog N + Real.log (1 / r) := intrinsicDimensionLog_le hN hr hr1
      _ ≤ dimensionLog N + dimensionLog N / r := add_le_add le_rfl hsmall
      _ = _ := by ring
  apply (div_le_iff₀ hlogpos).mpr
  have h := mul_le_mul_of_nonneg_left hle hu
  convert h using 1
  ring

/-- Quantitative consequences of the actual `Q ≤ E² r N` comparison.
There is no division by `E` and no retention lower bound. -/
theorem variance_compatibility_sqrt_bounds {v N Q r E : ℝ}
    (hQ : 0 < Q) (hr : 0 < r) (hr1 : r ≤ 1)
    (hcomp : Q ≤ E ^ 2 * r * N) :
    Real.sqrt v ≤ E ^ 2 * (N / Q * Real.sqrt v) ∧
      Real.sqrt v / r ≤ E ^ 2 * (N / Q * Real.sqrt v) := by
  have hfac : 1 ≤ E ^ 2 * r * N / Q := (le_div_iff₀ hQ).mpr (by simpa using hcomp)
  have hbound : Real.sqrt v / r ≤ E ^ 2 * (N / Q * Real.sqrt v) := by
    have hm := mul_le_mul_of_nonneg_right hfac (div_nonneg (Real.sqrt_nonneg v) hr.le)
    simp only [one_mul] at hm
    refine hm.trans_eq ?_
    field_simp
  refine ⟨?_, hbound⟩
  apply le_trans _ hbound
  apply (le_div_iff₀ hr).mpr
  exact mul_le_of_le_one_right (Real.sqrt_nonneg v) hr1

/-- The scalar rate conclusions in the variance-compatible concentration
corollary, for arbitrary index filters and retention approaching zero. -/
theorem variance_compatibility_scale_limits {J : Type*} {l : Filter J}
    (v N Q r : J → ℝ) (E : ℝ)
    (hgood : ∀ᶠ i in l, 0 ≤ v i ∧ 0 ≤ N i ∧ 0 < Q i ∧ 0 < r i ∧ r i ≤ 1 ∧
      Q i ≤ E ^ 2 * r i * N i)
    (hcompat : Tendsto (fun i => N i / Q i * Real.sqrt (v i)) l (𝓝 0)) :
    Tendsto v l (𝓝 0) ∧
      Tendsto (fun i => Real.sqrt (v i) / r i) l (𝓝 0) ∧
      Tendsto (fun i => Real.sqrt (v i) * intrinsicDimensionLog (N i) (r i) /
        dimensionLog (N i)) l (𝓝 0) := by
  have hupper : Tendsto (fun i => E ^ 2 * (N i / Q i * Real.sqrt (v i))) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hcompat
  have hsqrt : Tendsto (fun i => Real.sqrt (v i)) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall (fun i => Real.sqrt_nonneg _))
    filter_upwards [hgood] with i hi
    exact (variance_compatibility_sqrt_bounds hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2).1
  have hrho : Tendsto (fun i => Real.sqrt (v i) / r i) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · filter_upwards [hgood] with i hi
      exact div_nonneg (Real.sqrt_nonneg _) hi.2.2.2.1.le
    · filter_upwards [hgood] with i hi
      exact (variance_compatibility_sqrt_bounds hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2).2
  have hv : Tendsto v l (𝓝 0) := by
    have hsq : Tendsto (fun i => Real.sqrt (v i) ^ 2) l (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0)] using hsqrt.pow 2
    apply hsq.congr'
    filter_upwards [hgood] with i hi
    exact Real.sq_sqrt hi.1
  refine ⟨hv, hrho, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_add] using hsqrt.add hrho)
  · filter_upwards [hgood] with i hi
    have hlog := one_le_dimensionLog hi.2.1
    have hint := one_le_dimensionLog (div_nonneg hi.2.1 hi.2.2.2.1.le)
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by exact hint.trans' zero_le_one))
      (hlog.trans' zero_le_one)
  · filter_upwards [hgood] with i hi
    exact intrinsic_linear_ratio_le (Real.sqrt_nonneg _) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1

section ActualDimensions

open MeasureTheory

variable {J X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Variance compatibility of the actual main filter implies the scale limits
without a uniform lower bound on the normalized covariance norm. `M,ρ,A`
are common constants outside the regularization index. -/
theorem feature_variance_compatibility_scale_limits {l : Filter J}
    (k : X → H) (hk : MemLp k 2 μ) (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    (φ : J → ℝ → ℝ) {M ρ A : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (v : J → ℝ) (hv : ∀ᶠ i in l, 0 ≤ v i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt (v i)) l (𝓝 0)) :
    Tendsto v l (𝓝 0) ∧
      Tendsto (fun i => Real.sqrt (v i) / featureCovarianceRetention k hk (lam i)) l (𝓝 0) ∧
      Tendsto (fun i => Real.sqrt (v i) *
        intrinsicDimensionLog (featureEffectiveDimension k hk (lam i))
          (featureCovarianceRetention k hk (lam i)) /
        dimensionLog (featureEffectiveDimension k hk (lam i))) l (𝓝 0) := by
  apply variance_compatibility_scale_limits v
    (fun i => featureEffectiveDimension k hk (lam i))
    (fun i => featureFilterDimension k hk (φ i))
    (fun i => featureCovarianceRetention k hk (lam i)) A _ hcompat
  filter_upwards [hv, hQ] with i hvi hQi
  exact ⟨hvi, featureEffectiveDimension_nonneg k hk (lam i) (hlam i), hQi,
    featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hQi,
    featureCovarianceRetention_le_one k hk (lam i) (hlam i),
    featureFilterDimension_le_retention k hk (φ i) (hlam i) hM (hf i) (h i)⟩

end ActualDimensions

end KernelSeq
