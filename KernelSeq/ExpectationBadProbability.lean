import KernelSeq.ExpectationCovarianceScales
import KernelSeq.ExpectationCovarianceTail
import KernelSeq.ExpectationScale

/-!
# Vanishing actual bad-design probability from original compatibility

The fixed-quarter covariance event has vanishing real probability under the
original variance compatibility alone. Its actual Bernstein estimate and
all deterministic smallness conditions are supplied internally.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

variable {H X Ω J : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {l : Filter J}

theorem feature_bad_design_probability_of_original_compatibility
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (x : (i : J) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : J → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L : J → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0)) :
    Tendsto (fun i => P.real {ω | 1 / 4 < actualCovarianceDeviation k hk (lam i)
      (fun j => x i j ω)}) l (𝓝 0) := by
  have hlimits := feature_variance_compatibility_expectation_covariance_limits
    n hn k hk lam hlam φ hM hf h L hL hQ hcompat
  have hsmall := feature_variance_compatibility_eventually_covariance_small
    n hn k hk lam hlam φ hM hf h L hL hQ hcompat
  have hrpos : ∀ᶠ i in l, 0 < featureCovarianceRetention k hk (lam i) := hQ.mono fun i hi =>
    featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hi
  have hLpos : ∀ᶠ i in l, 0 < L i := by
    filter_upwards [hrpos] with i hi
    apply hi.trans_le
    rw [← bernsteinFeature_covariance_norm k hk (lam i)]
    exact populationCovariance_norm_le_feature_bound _ (bernsteinFeature_memLp k hk (lam i)) (hL i)
  have ht := expectation_scale_polynomial_tail L (fun i => (n i : ℝ)) (fun _ => 0)
    hLpos (Eventually.of_forall fun i => Nat.cast_pos.mpr (hn i))
    (Eventually.of_forall fun _ => le_rfl)
    (by simpa only [add_zero, Real.log_exp, mul_one] using hlimits.1)
    (a := 0) (by norm_num) (c := (1 / 65536 : ℝ)) (by norm_num)
  simp only [add_zero, Real.one_rpow, one_mul] at ht
  have hu := ht.const_mul 8
  simp only [mul_zero] at hu
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hu
  filter_upwards [hrpos, hsmall] with i hi hsi
  have hp : 0 ≤ 8 * Real.exp (-(1 / 65536 : ℝ) * (n i : ℝ) / L i) := by positivity
  have hb := actual_bad_design_exponential_tail k hk (hlam i) (hn i) (x i) (hlaw i)
    (hind i) (hL i) hi hsi.2
  have he : -(n i : ℝ) / (65536 * L i) = -(1 / 65536 : ℝ) * (n i : ℝ) / L i := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hb
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hp)

end
end KernelSeq
