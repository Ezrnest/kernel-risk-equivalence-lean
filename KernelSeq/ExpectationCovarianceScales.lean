import KernelSeq.ConcentrationScale
import KernelSeq.NormalizedBernstein

/-!
# Expectation covariance scales forced by original variance compatibility

No lower bound on retention or leverage is assumed. In particular the inverse
sample-size limit needed for actual leave-one-out inclusion is derived from
the same variance compatibility, not added as an asymptotic hypothesis.
-/

open Filter Topology MeasureTheory

namespace KernelSeq
noncomputable section

theorem variance_compatibility_inverse_sample_le {n L N Q r E : ℝ}
    (hn : 0 < n) (hN : 0 ≤ N) (hQ : 0 < Q) (hr : 0 < r)
    (hr1 : r ≤ 1) (hrL : r ≤ L) (hcomp : Q ≤ E^2*r*N) :
    1/n ≤ E^4 * (N/Q * Real.sqrt (L*dimensionLog N/n))^2 := by
  have hL : 0 < L := hr.trans_le hrL
  have hell : 1 ≤ dimensionLog N := one_le_dimensionLog hN
  have hv : 0 ≤ L*dimensionLog N/n := by positivity
  have hs := (variance_compatibility_sqrt_bounds
    (v := L*dimensionLog N/n) hQ hr hr1 hcomp).2
  have hsq := pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg _) hr.le) hs 2
  rw [div_pow, Real.sq_sqrt hv] at hsq
  have hsr : r^2 ≤ L*dimensionLog N := by
    calc
      r^2 ≤ r := by nlinarith
      _ ≤ L := hrL
      _ ≤ L*dimensionLog N := le_mul_of_one_le_right hL.le hell
  calc
    1/n = (r^2/n)/r^2 := by field_simp
    _ ≤ (L*dimensionLog N/n)/r^2 :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hsr hn.le) (sq_nonneg _)
    _ ≤ (E^2*(N/Q*Real.sqrt (L*dimensionLog N/n)))^2 := hsq
    _ = _ := by ring

/-- All three deterministic smallness conditions used for the fixed-threshold
and leave-one-out covariance tails follow from original variance compatibility. -/
theorem variance_compatibility_expectation_covariance_limits {J : Type*} {l : Filter J}
    (n L N Q r : J → ℝ) (E : ℝ)
    (hgood : ∀ᶠ i in l, 0<n i ∧ 0≤N i ∧ 0<Q i ∧ 0<r i ∧ r i≤1 ∧
      r i≤L i ∧ Q i≤E^2*r i*N i)
    (hcompat : Tendsto (fun i => N i/Q i*Real.sqrt (L i*dimensionLog (N i)/n i)) l (𝓝 0)) :
    Tendsto (fun i => L i/n i) l (𝓝 0) ∧
      Tendsto (fun i => L i*intrinsicDimensionLog (N i) (r i)/n i) l (𝓝 0) ∧
      Tendsto (fun i => (L i+1)/n i) l (𝓝 0) := by
  let v := fun i => L i*dimensionLog (N i)/n i
  have hvgood : ∀ᶠ i in l, 0≤v i ∧ 0≤N i ∧ 0<Q i ∧ 0<r i ∧ r i≤1 ∧
      Q i≤E^2*r i*N i := by
    filter_upwards [hgood] with i hi
    exact ⟨div_nonneg (mul_nonneg (hi.2.2.2.1.le.trans hi.2.2.2.2.2.1)
      (zero_le_one.trans (one_le_dimensionLog hi.2.1))) hi.1.le,
      hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.2⟩
  obtain ⟨hv, _, hlinear⟩ := variance_compatibility_scale_limits v N Q r E hvgood hcompat
  have hsqrt : Tendsto (fun i => Real.sqrt (v i)) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hv
  have hLn : Tendsto (fun i => L i/n i) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hv
    · filter_upwards [hgood] with i hi
      exact div_nonneg (hi.2.2.2.1.le.trans hi.2.2.2.2.2.1) hi.1.le
    · filter_upwards [hgood] with i hi
      exact div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (hi.2.2.2.1.le.trans hi.2.2.2.2.2.1)
          (one_le_dimensionLog hi.2.1)) hi.1.le
  have hIL : Tendsto (fun i => L i*intrinsicDimensionLog (N i) (r i)/n i) l (𝓝 0) := by
    have ht := hsqrt.mul hlinear
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hgood, hvgood] with i hi hvi
    rw [← mul_div_assoc, ← mul_assoc, ← pow_two, Real.sq_sqrt hvi.1]
    dsimp only [v]
    have he : dimensionLog (N i) ≠ 0 := ne_of_gt (by linarith [one_le_dimensionLog hi.2.1])
    field_simp [he]
  have hinv : Tendsto (fun i => 1/n i) l (𝓝 0) := by
    have hu : Tendsto (fun i => E^4*(N i/Q i*Real.sqrt (L i*dimensionLog (N i)/n i))^2) l (𝓝 0) := by
      simpa only [zero_pow (by norm_num : 2≠0), mul_zero] using tendsto_const_nhds.mul (hcompat.pow 2)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · filter_upwards [hgood] with i hi
      exact one_div_nonneg.mpr hi.1.le
    · filter_upwards [hgood] with i hi
      exact variance_compatibility_inverse_sample_le hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1
        hi.2.2.2.2.1 hi.2.2.2.2.2.1 hi.2.2.2.2.2.2
  refine ⟨hLn, hIL, ?_⟩
  simpa only [add_div, one_div, add_zero] using hLn.add hinv

variable {J X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual feature-model specialization of all expectation covariance
scales, derived from the manuscript's original variance compatibility alone. -/
theorem feature_variance_compatibility_expectation_covariance_limits {l : Filter J}
    (n : J → ℕ) (hn : ∀ i, 0<n i) (k : X → H) (hk : MemLp k 2 μ)
    (lam : J → ℝ) (hlam : ∀ i, 0<lam i) (φ : J → ℝ → ℝ) {M ρ A : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L : J → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y≤L i)
    (hQ : ∀ᶠ i in l, 0<featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i*dimensionLog (featureEffectiveDimension k hk (lam i))/(n i:ℝ))) l (𝓝 0)) :
    Tendsto (fun i => L i/(n i:ℝ)) l (𝓝 0) ∧
      Tendsto (fun i => L i*intrinsicDimensionLog (featureEffectiveDimension k hk (lam i))
        (featureCovarianceRetention k hk (lam i))/(n i:ℝ)) l (𝓝 0) ∧
      Tendsto (fun i => (L i+1)/(n i:ℝ)) l (𝓝 0) := by
  apply variance_compatibility_expectation_covariance_limits (fun i => (n i:ℝ)) L
    (fun i => featureEffectiveDimension k hk (lam i))
    (fun i => featureFilterDimension k hk (φ i))
    (fun i => featureCovarianceRetention k hk (lam i)) A _ hcompat
  filter_upwards [hQ] with i hQi
  have hrL : featureCovarianceRetention k hk (lam i) ≤ L i := by
    rw [← bernsteinFeature_covariance_norm k hk (lam i)]
    exact populationCovariance_norm_le_feature_bound _ (bernsteinFeature_memLp k hk (lam i)) (hL i)
  exact ⟨Nat.cast_pos.mpr (hn i), featureEffectiveDimension_nonneg k hk (lam i) (hlam i), hQi,
    featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hQi,
    featureCovarianceRetention_le_one k hk (lam i) (hlam i), hrL,
    featureFilterDimension_le_retention k hk (φ i) (hlam i) hM (hf i) (h i)⟩

/-- In particular, the exact leave-one-out deletion and fixed-tail thresholds
eventually apply, without an extra sample-size or retention hypothesis. -/
theorem feature_variance_compatibility_eventually_covariance_small {l : Filter J}
    (n : J → ℕ) (hn : ∀ i, 0<n i) (k : X → H) (hk : MemLp k 2 μ)
    (lam : J → ℝ) (hlam : ∀ i, 0<lam i) (φ : J → ℝ → ℝ) {M ρ A : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L : J → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y≤L i)
    (hQ : ∀ᶠ i in l, 0<featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i*dimensionLog (featureEffectiveDimension k hk (lam i))/(n i:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, (L i+1)/(n i:ℝ)≤1/8 ∧
      L i*intrinsicDimensionLog (featureEffectiveDimension k hk (lam i))
        (featureCovarianceRetention k hk (lam i))/(n i:ℝ)≤1/65536 := by
  obtain ⟨_, hi, hs⟩ := feature_variance_compatibility_expectation_covariance_limits
    n hn k hk lam hlam φ hM hf h L hL hQ hcompat
  filter_upwards [hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/8)),
    hi.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/65536))] with i hsi hii
  exact ⟨hsi.le, hii.le⟩

end
end KernelSeq
