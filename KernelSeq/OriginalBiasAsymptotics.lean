import KernelSeq.ActualBiasTransfer
import KernelSeq.SchattenAsymptotics
import KernelSeq.LocalizationScale
import KernelSeq.SequenceBenchmark

/-!
# Original localization scales and actual bias asymptotics

The stochastic coefficients are derived from the original variance/source
compatibility conditions and the actual Bernstein/Schatten estimates. The
full localized interaction inequality is kept as the visible upstream core
lemma: this module does not prove that operator inequality or HMS.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace KernelSeq

noncomputable section

/-- Deterministic convergence gives convergence in outer measure for the
corresponding constant random variables, for arbitrary measures and filters. -/
theorem deterministic_tendstoInMeasure_zero {J Ω : Type*} [MeasurableSpace Ω]
    {l : Filter J} (P : Measure Ω) {a : J → ℝ} (ha : Tendsto a l (𝓝 0)) :
    TendstoInMeasure P (fun i _ => a i) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_zero]
  have hn : Tendsto (fun i => ‖a i‖) l (𝓝 0) := by simpa only [norm_zero] using ha.norm
  apply tendsto_const_nhds.congr'
  filter_upwards [hn.eventually (eventually_lt_nhds hε)] with i hi
  have he : {ω : Ω | ε ≤ ‖a i‖} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le.mpr hi
  rw [he, measure_empty]

/-- Original variance compatibility and a vanishing weighted square-root
scale imply weighted covariance convergence directly from exponential tails.
The weight may diverge, and zero leverage is allowed in this generic lemma. -/
theorem weighted_covariance_limit_of_threshold_tails
    {J Ω : Type*} [MeasurableSpace Ω] {l : Filter J} (P : Measure Ω)
    (δ : J → Ω → ℝ) (L n N Q r w : J → ℝ) (A : ℝ)
    (hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < n i ∧ 0 ≤ N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ Q i ≤ A ^ 2 * r i * N i)
    (hcompat : Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0))
    (hw : ∀ᶠ i in l, 0 ≤ w i)
    (hscale : Tendsto (fun i => w i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0))
    (htail : ∀ z : ℝ, 0 ≤ z → ∀ᶠ i in l,
      P {ω | normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z < |δ i ω|} ≤
        ENNReal.ofReal (8 * Real.exp (-z))) :
    TendstoInMeasure P (fun i ω => w i * δ i ω) l (fun _ => 0) := by
  apply tendstoInMeasure_zero_of_exponential_thresholds P (fun i ω => w i * δ i ω)
    (fun z i => w i * normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z)
  · intro z hz
    obtain ⟨C, _, hb⟩ := variance_compatibility_intrinsicThreshold_tight_bound
      L n N Q r A hgood hcompat z hz
    have hlim : Tendsto (fun i => C * (w i * Real.sqrt (L i * dimensionLog (N i) / n i))) l (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hscale
    apply squeeze_zero' _ _ hlim
    · filter_upwards [hgood, hw] with i hi hwi
      exact mul_nonneg hwi (normalizedIntrinsicThreshold_nonneg hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.2.1 hz)
    · filter_upwards [hw, hb] with i hwi hbi
      exact (mul_le_mul_of_nonneg_left hbi hwi).trans_eq (by ring)
  · intro z hz
    filter_upwards [hw, htail z hz] with i hwi hti
    refine (measure_mono ?_).trans hti
    intro ω hω
    change w i * normalizedIntrinsicThreshold (L i) (n i) (N i) (r i) z < ‖w i * δ i ω‖ at hω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwi] at hω
    by_cases hw0 : w i = 0
    · simp only [hw0, zero_mul, lt_self_iff_false] at hω
    · exact (mul_lt_mul_iff_of_pos_left (lt_of_le_of_ne hwi (Ne.symm hw0))).mp hω

section ActualCovariance

variable {J X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P] {l : Filter J}

theorem actual_weighted_covariance_of_compatibility
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (x : (i : J) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : J → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L w : J → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hw : ∀ᶠ i in l, 0 ≤ w i) (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0))
    (hscale : Tendsto (fun i => w i * Real.sqrt
      (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0))
    (hTropp : ∀ i, FiniteSpectralBernstein
      (featureCovarianceBasis (bernsteinFeature k hk (lam i))
        (bernsteinFeature_memLp k hk (lam i))) P) :
    TendstoInMeasure P (fun i ω => w i * actualCovarianceDeviation k hk (lam i)
      (fun j => x i j ω)) l (fun _ => 0) := by
  let N := fun i => featureEffectiveDimension k hk (lam i)
  let Q := fun i => featureFilterDimension k hk (φ i)
  let r := fun i => featureCovarianceRetention k hk (lam i)
  have hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < (n i : ℝ) ∧ 0 ≤ N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ Q i ≤ A ^ 2 * r i * N i := by
    filter_upwards [hQ] with i hQi
    exact ⟨feature_sq_bound_nonneg (bernsteinFeature k hk (lam i)) (hL i), Nat.cast_pos.mpr (hn i),
      featureEffectiveDimension_nonneg k hk (lam i) (hlam i), hQi,
      featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hQi,
      featureCovarianceRetention_le_one k hk (lam i) (hlam i),
      featureFilterDimension_le_retention k hk (φ i) (hlam i) hM (hf i) (h i)⟩
  apply weighted_covariance_limit_of_threshold_tails P _ L (fun i => (n i : ℝ)) N Q r w A
    hgood hcompat hw hscale
  intro z hz
  filter_upwards [hgood] with i hi
  simpa only [normalizedIntrinsicThreshold, intrinsicDimensionLog, dimensionLog,
    N, r, actualCovarianceDeviation, covarianceRelativeDeviation, abs_norm] using
    normalized_covariance_bernstein_tail k hk (lam i) (hlam i) (hTropp i) (hn i)
      (x i) (hlaw i) (hind i) (hL i) hi.2.2.2.2.1 z hz

/-- Positive actual filter variance forces positive leverage, so the cutoff
is not silently zero through a division-by-zero convention. -/
theorem actual_leverage_bound_pos_of_filterDimension_pos
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam)
    (φ : ℝ → ℝ) {M ρ A L : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hQ : 0 < featureFilterDimension k hk φ) : 0 < L := by
  have hr := featureCovarianceRetention_pos_of_filterDimension_pos k hk φ hlam hM hf h hQ
  have hb := populationCovariance_norm_le_feature_bound (bernsteinFeature k hk lam)
    (bernsteinFeature_memLp k hk lam) hL
  rw [bernsteinFeature_covariance_norm] at hb
  exact hr.trans_le hb

end ActualCovariance

section DeterministicScales

/-- The original logarithmic source-compatibility scale. -/
def originalBiasGamma (L n N : ℝ) : ℝ :=
  Real.sqrt (L * dimensionLog N / n) * Real.log (Real.exp 1 + Real.sqrt (N / dimensionLog N))

theorem originalBiasGamma_nonneg (L n N : ℝ) : 0 ≤ originalBiasGamma L n N := by
  have hl : 1 ≤ Real.log (Real.exp 1 + Real.sqrt (N / dimensionLog N)) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  exact mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans hl)

def originalBiasCutoffCap (A : ℝ) : ℝ := min 1 (1 / (4 * (A + 1)))

def originalBiasCutoff (A L n N Q S : ℝ) : ℝ :=
  localizationCutoff (originalBiasCutoffCap A) (L * dimensionLog N / n)
    (n * S * originalBiasGamma L n N ^ 2 / Q)

theorem originalBiasCutoffCap_pos {A : ℝ} (hA : 0 ≤ A) : 0 < originalBiasCutoffCap A := by
  exact lt_min zero_lt_one (by positivity)

/-- Square-root versions of the actual cutoff limits. Positivity is derived
from `v+ζ`, rather than presuming both numerator scales are positive. -/
theorem localizationCutoff_sqrt_limits {J : Type*} {l : Filter J}
    {v ζ : J → ℝ} {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hv : Tendsto v l (𝓝 0)) (hζ : Tendsto ζ l (𝓝 0))
    (hvn : ∀ᶠ i in l, 0 ≤ v i) (hζn : ∀ᶠ i in l, 0 ≤ ζ i)
    (hs : ∀ᶠ i in l, 0 < v i + ζ i) :
    (∀ᶠ i in l, 0 < localizationCutoff τ₀ (v i) (ζ i)) ∧
      Tendsto (fun i => localizationCutoff τ₀ (v i) (ζ i)) l (𝓝 0) ∧
      Tendsto (fun i => Real.sqrt (v i) / localizationCutoff τ₀ (v i) (ζ i)) l (𝓝 0) ∧
      Tendsto (fun i => Real.sqrt (ζ i) / localizationCutoff τ₀ (v i) (ζ i)) l (𝓝 0) := by
  obtain ⟨hp, ht, hvr, hζr⟩ := localizationCutoff_limits hτ₀ hv hζ hvn hζn hs
  refine ⟨hp, ht, ?_, ?_⟩
  · have hh : Tendsto (fun i => Real.sqrt (v i / localizationCutoff τ₀ (v i) (ζ i) ^ 2)) l (𝓝 0) := by
      simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hvr
    apply hh.congr'
    filter_upwards [hvn, hp] with i hvi hpi
    rw [Real.sqrt_div hvi, Real.sqrt_sq_eq_abs, abs_of_pos hpi]
  · have hh : Tendsto (fun i => Real.sqrt (ζ i / localizationCutoff τ₀ (v i) (ζ i) ^ 2)) l (𝓝 0) := by
      simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hζr
    apply hh.congr'
    filter_upwards [hζn, hp] with i hζi hpi
    rw [Real.sqrt_div hζi, Real.sqrt_sq_eq_abs, abs_of_pos hpi]

theorem source_gamma_weight_eq {n S Q γ τ : ℝ}
    (hS : 0 ≤ n * S / Q) (hγ : 0 ≤ γ) :
    Real.sqrt (n * S / Q) / τ * γ = Real.sqrt (n * S * γ ^ 2 / Q) / τ := by
  rw [show n * S * γ ^ 2 / Q = (n * S / Q) * γ ^ 2 by ring,
    Real.sqrt_mul hS, Real.sqrt_sq hγ]
  ring

/-- The actual source estimate turns the squared beta term into a constant
multiple of the weighted actual Schatten endpoint squared. -/
theorem localized_beta_energy_le {C A Xi τ n S Q σ W : ℝ}
    (hτ : 0 < τ) (hn : 0 < n) (hS : 0 ≤ S) (hQ : 0 < Q) (hσ : 0 < σ)
    (hW : W ≤ (A + 1) ^ 2 * S) :
    (C * Xi / τ) ^ 2 * W / (σ ^ 2 / n * Q) ≤
      (C * (A + 1) / σ) ^ 2 * (Real.sqrt (n * S / Q) / τ * Xi) ^ 2 := by
  have hden : 0 < σ ^ 2 / n * Q := mul_pos (div_pos (sq_pos_of_pos hσ) hn) hQ
  calc
    _ ≤ (C * Xi / τ) ^ 2 * ((A + 1) ^ 2 * S) / (σ ^ 2 / n * Q) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (sq_nonneg _)) hden.le
    _ = _ := by
      simp only [mul_pow, div_pow, Real.sq_sqrt (div_nonneg (mul_nonneg hn.le hS) hQ.le)]
      field_simp [hτ.ne', hn.ne', hQ.ne', hσ.ne']

end DeterministicScales

section SourceEnergy

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

theorem featureSequenceSourceEnergy_nonneg (k : X → H) (hk : MemLp k 2 μ)
    {lam α : ℝ} (hlam : 0 < lam) (f : Lp ℝ 2 μ) :
    0 ≤ featureSequenceSourceEnergy k hk lam α f := by
  apply tsum_nonneg
  intro i
  apply mul_nonneg _ (sq_nonneg _)
  exact Real.rpow_nonneg (div_nonneg hlam.le (by linarith [i.2])) _

end SourceEnergy

section ActualCoefficients

variable {I J X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P] {l : Filter J} [NeBot l]

def actualOriginalBiasCutoff (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (φ : ℝ → ℝ)
    (α : ℝ) (f : Lp ℝ 2 μ) (L : ℝ) (n : ℕ) (A : ℝ) : ℝ :=
  originalBiasCutoff A L (n : ℝ) (featureEffectiveDimension k hk lam)
    (featureFilterDimension k hk φ) (featureSequenceSourceEnergy k hk lam α f)

/-- All localization coefficient limits follow from the two original scalar
compatibility conditions. In particular neither epsilon/beta probability
limits nor a vector-error estimate are hypotheses. The sole external
probability theorem is the displayed finite Bernstein premise. -/
theorem actual_original_bias_coefficient_limits (b : HilbertBasis I ℝ H)
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (x : (i : J) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A α : ℝ} (hα : 0 ≤ α) (hαρ : α / 2 ≤ ρ)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : J → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i)) (f : J → Lp ℝ 2 μ)
    (hsupport : ∀ i, f i ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure)
    (σ C : ℝ) (hσ : 0 < σ) (L : J → ℝ)
    (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0))
    (hsource : Tendsto (fun i => (n i : ℝ) * featureSequenceSourceEnergy k hk (lam i) α (f i) *
      originalBiasGamma (L i) (n i : ℝ) (featureEffectiveDimension k hk (lam i)) ^ 2 /
        featureFilterDimension k hk (φ i)) l (𝓝 0))
    (hTropp : ∀ i, FiniteSpectralBernstein
      (featureCovarianceBasis (bernsteinFeature k hk (lam i))
        (bernsteinFeature_memLp k hk (lam i))) P) :
    let τ := fun i => actualOriginalBiasCutoff k hk (lam i) (φ i) α (f i) (L i) (n i) A
    (∀ᶠ i in l, τ i ∈ Set.Ioc (0 : ℝ) (originalBiasCutoffCap A)) ∧
      Tendsto τ l (𝓝 0) ∧ Tendsto (fun i => L i / (n i : ℝ)) l (𝓝 0) ∧
      TendstoInMeasure P (fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)) l (fun _ => 0) ∧
      TendstoInMeasure P (fun i ω => C * (τ i +
        actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) / τ i)) l (fun _ => 0) ∧
      TendstoInMeasure P (fun i ω =>
        (C * hsSchattenEndpoint b (manuscriptMixedColumns b k hk (lam i) (fun j => x i j ω)) / τ i) ^ 2 *
          ‖actualBiasWeight k hk (φ i) (hlam i) hα hM (hf i) (f i)‖ ^ 2 /
            (σ ^ 2 / (n i : ℝ) * featureFilterDimension k hk (φ i))) l (fun _ => 0) := by
  let N := fun i => featureEffectiveDimension k hk (lam i)
  let Q := fun i => featureFilterDimension k hk (φ i)
  let S := fun i => featureSequenceSourceEnergy k hk (lam i) α (f i)
  let γ := fun i => originalBiasGamma (L i) (n i : ℝ) (N i)
  let v := fun i => L i * dimensionLog (N i) / (n i : ℝ)
  let ζ := fun i => (n i : ℝ) * S i * γ i ^ 2 / Q i
  let τ := fun i => actualOriginalBiasCutoff k hk (lam i) (φ i) α (f i) (L i) (n i) A
  let δ := fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)
  let Xi := fun i ω => hsSchattenEndpoint b (manuscriptMixedColumns b k hk (lam i) (fun j => x i j ω))
  have hLn i : 0 ≤ L i := feature_sq_bound_nonneg (bernsteinFeature k hk (lam i)) (hL i)
  have hN i : 0 ≤ N i := featureEffectiveDimension_nonneg k hk (lam i) (hlam i)
  have hS i : 0 ≤ S i := featureSequenceSourceEnergy_nonneg k hk (hlam i) (f i)
  have hvn : ∀ᶠ i in l, 0 ≤ v i := Eventually.of_forall fun i =>
    div_nonneg (mul_nonneg (hLn i) (zero_le_one.trans (one_le_dimensionLog (hN i)))) (Nat.cast_nonneg _)
  have hζn : ∀ᶠ i in l, 0 ≤ ζ i := by
    filter_upwards [hQ] with i hQi
    exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hS i)) (sq_nonneg _)) hQi.le
  have hv0 : Tendsto v l (𝓝 0) :=
    (feature_variance_compatibility_scale_limits k hk lam hlam φ hM hf h v hvn hQ hcompat).1
  have hζ0 : Tendsto ζ l (𝓝 0) := hsource
  have hspos : ∀ᶠ i in l, 0 < v i + ζ i := by
    filter_upwards [hQ, hζn] with i hQi hζi
    have hLp := actual_leverage_bound_pos_of_filterDimension_pos k hk (lam i) (hlam i)
      (φ i) hM (hf i) (h i) (hL i) hQi
    have hvp : 0 < v i := div_pos (mul_pos hLp (by linarith [one_le_dimensionLog (hN i)]))
      (Nat.cast_pos.mpr (hn i))
    exact add_pos_of_pos_of_nonneg hvp hζi
  obtain ⟨i₀, _⟩ := hQ.exists
  have hA : 0 ≤ A := (h i₀).constant_nonneg (hlam i₀) ((norm_nonneg _).trans hM)
  obtain ⟨hτp, hτ0, hvs, hζs⟩ := localizationCutoff_sqrt_limits
    (originalBiasCutoffCap_pos hA) hv0 hζ0 hvn hζn hspos
  have hτpos : ∀ᶠ i in l, 0 < τ i := hτp
  have hτlim : Tendsto τ l (𝓝 0) := hτ0
  have hLrate : Tendsto (fun i => L i / (n i : ℝ)) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i => div_nonneg (hLn i) (Nat.cast_nonneg _)) _ hv0
    filter_upwards with i
    have hh := le_mul_of_one_le_right (div_nonneg (hLn i) (Nat.cast_nonneg (n i)))
      (one_le_dimensionLog (hN i))
    change L i / (n i : ℝ) ≤ L i * dimensionLog (N i) / (n i : ℝ)
    exact hh.trans_eq (by ring)
  have hδweight : TendstoInMeasure P (fun i ω => (1 / τ i) * δ i ω) l (fun _ => 0) := by
    apply actual_weighted_covariance_of_compatibility n hn x hlaw hind k hk lam hlam hM φ hf h
      L (fun i => 1 / τ i) hL (hτpos.mono fun i hi => one_div_nonneg.mpr hi.le) hQ hcompat _ hTropp
    change Tendsto (fun i => (1 / τ i) * Real.sqrt (v i)) l (𝓝 0)
    have hvτ : Tendsto (fun i => Real.sqrt (v i) / τ i) l (𝓝 0) := hvs
    convert hvτ using 1
    funext i
    ring
  have hδdiv : TendstoInMeasure P (fun i ω => δ i ω / τ i) l (fun _ => 0) := by
    apply TendstoInMeasure.congr_left (fun i => Eventually.of_forall fun ω => ?_) hδweight
    ring
  have hτprob := deterministic_tendstoInMeasure_zero P hτlim
  have hδ0 : TendstoInMeasure P δ l (fun _ => 0) := by
    apply TendstoInMeasure.congr' _ EventuallyEq.rfl (tendstoInMeasure_mul_zero hδdiv hτprob)
    filter_upwards [hτpos] with i hpi
    exact Eventually.of_forall fun ω => div_mul_cancel₀ (δ i ω) hpi.ne'
  have hε := tendstoInMeasure_const_mul_zero (tendstoInMeasure_add_zero hτprob hδdiv) C
  let w := fun i => Real.sqrt ((n i : ℝ) * S i / Q i) / τ i
  have hw : ∀ᶠ i in l, 0 ≤ w i := hτpos.mono fun i hi => div_nonneg (Real.sqrt_nonneg _) hi.le
  have hwγ : Tendsto (fun i => w i * γ i) l (𝓝 0) := by
    apply hζs.congr'
    filter_upwards [hQ] with i hi
    exact (source_gamma_weight_eq (τ := τ i)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hS i)) hi.le)
      (originalBiasGamma_nonneg _ _ _)).symm
  have hXi : TendstoInMeasure P (fun i ω => w i * Xi i ω) l (fun _ => 0) := by
    apply actual_weighted_schatten_endpoint_of_compatibility b n hn x hlaw hind k hk lam hlam
      hM φ hf h L w hL hw hQ hcompat _ hTropp
    simpa only [γ, originalBiasGamma, mul_assoc] using hwγ
  have hβ : TendstoInMeasure P (fun i ω => (C * Xi i ω / τ i) ^ 2 *
      ‖actualBiasWeight k hk (φ i) (hlam i) hα hM (hf i) (f i)‖ ^ 2 /
        (σ ^ 2 / (n i : ℝ) * Q i)) l (fun _ => 0) := by
    apply tendstoInMeasure_zero_of_eventually_norm_le P _
      (fun i ω => (C * (A + 1) / σ) ^ 2 * (w i * Xi i ω) ^ 2)
      (tendstoInMeasure_const_mul_zero (tendstoInMeasure_sq_zero hXi) _) _
    filter_upwards [hQ, hτpos] with i hQi hpi ω
    have hden : 0 < σ ^ 2 / (n i : ℝ) * Q i :=
      mul_pos (div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr (hn i))) hQi
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hden.le)]
    exact localized_beta_energy_le hpi (Nat.cast_pos.mpr (hn i)) (hS i) hQi hσ
      (populationResidualWeight_norm_sq_le_sequenceSource k hk (φ i) (hlam i) hα hαρ hM
        (hf i) (h i) (hsupport i))
  refine ⟨?_, hτlim, hLrate, hδ0, hε, hβ⟩
  filter_upwards [hτpos] with i hpi
  exact ⟨hpi, min_le_left _ _⟩

/-- Original-scale actual bias transfer conditional only on the full localized
interaction core lemma (and the visible finite Bernstein theorem). The core
is the original pointwise operator bound for every admissible cutoff, not an
assumed epsilon/beta rate or a bound on the final estimator error. This module
does not establish that upstream localized/HMS inequality. -/
theorem actual_bias_transfer_from_original_scales (b : HilbertBasis I ℝ H)
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (x : (i : J) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (lam : J → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A α : ℝ} (hα : 0 ≤ α) (hαρ : α / 2 ≤ ρ)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hMX : ∀ i ω, ‖empiricalCovariance (fun j => k (x i j ω))‖ ≤ M)
    (φ : J → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i)) (f : J → Lp ℝ 2 μ)
    (hsupport : ∀ i, f i ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure)
    (σ C : ℝ) (hσ : 0 < σ) (L : J → ℝ)
    (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0))
    (hsource : Tendsto (fun i => (n i : ℝ) * featureSequenceSourceEnergy k hk (lam i) α (f i) *
      originalBiasGamma (L i) (n i : ℝ) (featureEffectiveDimension k hk (lam i)) ^ 2 /
        featureFilterDimension k hk (φ i)) l (𝓝 0))
    (hTropp : ∀ i, FiniteSpectralBernstein
      (featureCovarianceBasis (bernsteinFeature k hk (lam i))
        (bernsteinFeature_memLp k hk (lam i))) P)
    (hlocalized : ∀ᶠ i in l, ∀ (ω : Ω) (τ : ℝ),
      τ ∈ Set.Ioc (0 : ℝ) (originalBiasCutoffCap A) →
      actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) ≤ 1 / 4 →
      ‖actualInteractionPrediction k hk (φ i) (hlam i) hM (fun j => x i j ω)
        (hMX i ω) (hf i) (h i) (f i)‖ ≤
        C * (τ + actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) / τ) *
          ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ +
        (C * hsSchattenEndpoint b (manuscriptMixedColumns b k hk (lam i) (fun j => x i j ω)) / τ) *
          ‖actualBiasWeight k hk (φ i) (hlam i) hα hM (hf i) (f i)‖) :
    TendstoInMeasure P (fun i ω =>
      |actualEmpiricalBiasEnergy k hk (φ i) (hlam i) (fun j => x i j ω) (hMX i ω) (h i) (f i) -
        ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ ^ 2| /
      (‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ ^ 2 +
        σ ^ 2 / (n i : ℝ) * featureFilterDimension k hk (φ i))) l (fun _ => 0) := by
  let τ := fun i => actualOriginalBiasCutoff k hk (lam i) (φ i) α (f i) (L i) (n i) A
  obtain ⟨hτ, _, hLrate, hδ, hε, hβ⟩ := actual_original_bias_coefficient_limits b n hn x hlaw hind
    k hk lam hlam hα hαρ hM φ hf h f hsupport σ C hσ L hL hQ hcompat hsource hTropp
  apply actual_common_bias_transfer n hn x hlaw (fun i _ _ hij => (hind i).indepFun hij)
    k hk lam hlam hα hM hMX φ hf h f σ hσ hQ L hL hLrate
    (fun i ω => C * (τ i + actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) / τ i))
    (fun i ω => C * hsSchattenEndpoint b (manuscriptMixedColumns b k hk (lam i) (fun j => x i j ω)) / τ i)
    hδ hε hβ
  filter_upwards [hlocalized, hτ] with i hi hτi ω hdi
  exact hi ω (τ i) hτi hdi

end ActualCoefficients

end
end KernelSeq
