import KernelSeq.ActualVarianceTransfer
import KernelSeq.EmpiricalEffectiveDimension
import KernelSeq.ProbabilisticVariance

/-!
# Asymptotic variance transfer for the actual feature/sample model

The stochastic reductions below use actual HS moments and actual empirical
effective-dimension tails. They do not assume trace, HS-existence, square-root,
or final variance-comparison certificates. Operator-norm covariance convergence
is still an explicit input; this file does not supply its Bernstein rate.
All limiting arguments use arbitrary filters and outer measures.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace KernelSeq

/-- An actual nonnegative integrable error with vanishing mean bound converges
in measure. This is the outer-measure first-moment Markov reduction. -/
theorem tendstoInMeasure_zero_of_nonneg_integral_bound
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {P : Measure Ω}
    (f : ι → Ω → ℝ) (a : ι → ℝ) (hf : ∀ i, Integrable (f i) P)
    (hbound : ∀ᶠ i in l, (∀ᵐ ω ∂P, 0 ≤ f i ω) ∧ (∫ ω, f i ω ∂P) ≤ a i)
    (ha : Tendsto a l (𝓝 0)) : TendstoInMeasure P f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_zero, Real.norm_eq_abs]
  have hlim : Tendsto (fun i => ENNReal.ofReal (a i / ε)) l (𝓝 0) := by
    simpa only [zero_div, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (ha.div_const ε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hlim (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hbound] with i hi
  have hm := ((hf i).div_const ε).measure_le_integral
    (hi.1.mono (fun _ hω => div_nonneg hω hε.le))
    (s := {ω | ε ≤ f i ω}) (fun ω hω => by
      change ε ≤ f i ω at hω
      rw [le_div_iff₀ hε]
      simpa only [one_mul] using hω)
  calc
    P {ω | ε ≤ |f i ω|} ≤ P {ω | ε ≤ f i ω} := by
      apply measure_mono_ae
      filter_upwards [hi.1] with ω hω
      change (ε ≤ |f i ω| → ε ≤ f i ω)
      intro htail
      simpa only [abs_of_nonneg hω] using htail
    _ ≤ ENNReal.ofReal (a i / ε) := by
      refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [integral_div]
      exact div_le_div_of_nonneg_right hi.2 hε.le

/-- A scalar error tending to zero times a uniformly outer-Markov-tight
quantity on good events still tends to zero. No independence or measurability
between the two factors is required. -/
theorem tendstoInMeasure_mul_zero_of_good_tail
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {P : Measure Ω}
    (f K : ι → Ω → ℝ) (G : ι → Set Ω) (C : ℝ) (hC : 0 ≤ C)
    (hf : TendstoInMeasure P f l (fun _ => 0))
    (hbad : Tendsto (fun i => P (G i)ᶜ) l (𝓝 0))
    (htail : ∀ᶠ i in l, ∀ M : ℝ, 0 < M →
      P {ω | ω ∈ G i ∧ M ≤ |K i ω|} ≤ ENNReal.ofReal (C / M)) :
    TendstoInMeasure P (fun i ω => f i ω * K i ω) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_zero, Real.norm_eq_abs]
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ζ hζ
  obtain ⟨r, hr, hrζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hζ
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  let M : ℝ := 1 + 4 * C / r
  have hM : 0 < M := by dsimp [M]; positivity
  have hMr : (r : ℝ) * M = r + 4 * C := by
    dsimp [M]
    field_simp [hrpos.ne']
  have hCM : C / M ≤ (r : ℝ) / 4 := by
    apply (div_le_iff₀ hM).mpr
    nlinarith [hMr]
  have hp : 0 < ENNReal.ofReal ((r : ℝ) / 4) := ENNReal.ofReal_pos.mpr (by positivity)
  have hfε : Tendsto (fun i => P {ω | ε / M ≤ |f i ω|}) l (𝓝 0) := by
    simpa only [sub_zero, Real.norm_eq_abs] using
      (tendstoInMeasure_iff_norm.mp hf) (ε / M) (div_pos hε hM)
  filter_upwards [htail, ENNReal.tendsto_nhds_zero.mp hbad _ hp,
    ENNReal.tendsto_nhds_zero.mp hfε _ hp] with i hi hbi hfi
  have hsub : {ω | ε ≤ |f i ω * K i ω|} ⊆
      (G i)ᶜ ∪ ({ω | ε / M ≤ |f i ω|} ∪ {ω | ω ∈ G i ∧ M ≤ |K i ω|}) := by
    intro ω hω
    change ε ≤ |f i ω * K i ω| at hω
    by_cases hg : ω ∈ G i
    · by_cases hff : ε / M ≤ |f i ω|
      · exact Or.inr (Or.inl hff)
      · refine Or.inr (Or.inr ⟨hg, ?_⟩)
        by_contra hkk
        have hk : |K i ω| ≤ M := (lt_of_not_ge hkk).le
        have hm : |f i ω| * M < ε := (lt_div_iff₀ hM).mp (lt_of_not_ge hff)
        have hb := mul_le_mul_of_nonneg_left hk (abs_nonneg (f i ω))
        rw [abs_mul] at hω
        linarith
    · exact Or.inl hg
  have hsmall : ENNReal.ofReal ((r : ℝ) / 4) + ENNReal.ofReal ((r : ℝ) / 4) +
      ENNReal.ofReal ((r : ℝ) / 4) ≤ (r : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal (by nlinarith : (r : ℝ) / 4 + r / 4 + r / 4 ≤ r)
  calc
    P {ω | ε ≤ |f i ω * K i ω|} ≤
        P (G i)ᶜ + (P {ω | ε / M ≤ |f i ω|} + P {ω | ω ∈ G i ∧ M ≤ |K i ω|}) :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl (measure_union_le _ _)))
    _ ≤ ENNReal.ofReal ((r : ℝ) / 4) +
        (ENNReal.ofReal ((r : ℝ) / 4) + ENNReal.ofReal ((r : ℝ) / 4)) :=
      add_le_add hbi (add_le_add hfi ((hi M hM).trans (ENNReal.ofReal_le_ofReal hCM)))
    _ ≤ ζ := by rw [← add_assoc]; exact hsmall.trans hrζ.le

/-- Convergence in measure controls every fixed positive exceptional threshold. -/
theorem measure_exceed_tendsto_zero_of_tendstoInMeasure
    {ι Ω : Type*} [MeasurableSpace Ω] {l : Filter ι} {P : Measure Ω}
    (f : ι → Ω → ℝ) (hf : TendstoInMeasure P f l (fun _ => 0))
    (c : ℝ) (hc : 0 < c) : Tendsto (fun i => P {ω | c < f i ω}) l (𝓝 0) := by
  have ht : Tendsto (fun i => P {ω | c ≤ |f i ω|}) l (𝓝 0) := by
    simpa only [sub_zero, Real.norm_eq_abs] using (tendstoInMeasure_iff_norm.mp hf) c hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds ht (fun _ => zero_le)
  intro i
  apply measure_mono
  intro ω hω
  change c < f i ω at hω
  exact hω.le.trans (le_abs_self _)

variable {ι Ω X H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {P : Measure Ω} {μ : Measure X} [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
  {l : Filter ι}

omit [TopologicalSpace.SeparableSpace H] in
/-- Actual empirical effective dimensions are nonnegative. -/
theorem actual_empiricalEffectiveDimension_nonneg {n : ℕ} (z : Fin n → H)
    (lam : ℝ) (hlam : 0 < lam) : 0 ≤ empiricalEffectiveDimension z lam := by
  apply tsum_nonneg
  intro j
  have hj := compactEigenvalue_nonneg _ (empiricalCovariance_isCompact z)
    (empiricalCovariance_isPositive z) j
  exact div_nonneg hj (add_nonneg hj hlam.le)

/-- The genuine normalized HS error satisfies `η²/Q → 0` from the source
second-moment scale, without requiring `Q` or `N1` bounded away from zero. -/
theorem actual_hs_error_sq_div_tendstoInMeasure
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (hind : ∀ i, Pairwise (fun j k => IndepFun (x i j) (x i k) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (L Q : ι → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hQ : ∀ᶠ i in l, 0 < Q i)
    (hscale : Tendsto (fun i => L i * featureEffectiveDimension k hk (lam i) /
      ((n i : ℝ) * Q i)) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω =>
      ‖normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) k hk (lam i)
        (fun j => x i j ω)‖ ^ 2 / Q i) l (fun _ => 0) := by
  apply tendstoInMeasure_zero_of_nonneg_integral_bound _
    (fun i => L i * featureEffectiveDimension k hk (lam i) / ((n i : ℝ) * Q i)) _ _ hscale
  · intro i
    have hm := memLp_normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk)
      (hn i) (x i) (hlaw i) k hk (lam i) (hL i)
    exact ((memLp_two_iff_integrable_sq_norm hm.1).mp hm).div_const (Q i)
  · filter_upwards [hQ] with i hQi
    refine ⟨Eventually.of_forall (fun ω => div_nonneg (sq_nonneg _) hQi.le), ?_⟩
    rw [integral_div]
    have hb := integral_normalizedHSCovarianceFluctuation_sq_le (featureCovarianceBasis k hk)
      (hn i) (x i) (hlaw i) (hind i) k hk (lam i) (hlam i) (hL i)
    refine (div_le_div_of_nonneg_right hb hQi.le).trans_eq ?_
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Positive filter variance forces positive `N1`, by the actual filter
majorant. No positive lower bound on `N1` is inferred or assumed. -/
theorem featureEffectiveDimension_pos_of_filterDimension_pos
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hQ : 0 < featureFilterDimension k hk φ) : 0 < featureEffectiveDimension k hk lam := by
  by_contra hnot
  have hb := featureFilterDimension_le_effectiveDimension k hk φ hlam hM hf h
  have hp : A ^ 2 * featureEffectiveDimension k hk lam ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg A) (not_lt.mp hnot)
  linarith

omit [IsProbabilityMeasure P] in
/-- The actual empirical effective-dimension product vanishes from
`δ N1/Q → 0`, using the proved good-event Markov tail and splitting. No
independence of `δ` and the empirical dimension is used. -/
theorem actual_delta_empiricalDimension_div_tendstoInMeasure
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (Q : ι → ℝ) (hQ : ∀ᶠ i in l, 0 < Q i)
    (hN : ∀ᶠ i in l, 0 < featureEffectiveDimension k hk (lam i))
    (hδ : TendstoInMeasure P (fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω))
      l (fun _ => 0))
    (hδN : TendstoInMeasure P (fun i ω =>
      actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) *
        featureEffectiveDimension k hk (lam i) / Q i) l (fun _ => 0)) :
    TendstoInMeasure P (fun i ω =>
      actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) *
        empiricalEffectiveDimension (fun j => k (x i j ω)) (lam i) / Q i) l (fun _ => 0) := by
  let δ := fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)
  let N := fun i => featureEffectiveDimension k hk (lam i)
  let K := fun i ω => empiricalEffectiveDimension (fun j => k (x i j ω)) (lam i) / N i
  let f := fun i ω => δ i ω * N i / Q i
  let G := fun i => {ω | δ i ω ≤ 1 / 4}
  have hbad : Tendsto (fun i => P (G i)ᶜ) l (𝓝 0) := by
    simpa only [G, Set.compl_setOf, not_le] using
      measure_exceed_tendsto_zero_of_tendstoInMeasure δ hδ (1 / 4) (by norm_num)
  have htail : ∀ᶠ i in l, ∀ M : ℝ, 0 < M →
      P {ω | ω ∈ G i ∧ M ≤ |K i ω|} ≤ ENNReal.ofReal (2 / M) := by
    filter_upwards [hN] with i hNi M hM
    have hb := measure_empiricalEffectiveDimension_good_ge_le (hn i) (x i) (hlaw i)
      k hk (lam i) (hlam i) (t := M * N i) (mul_pos hM hNi)
    calc
      _ ≤ P {ω | sampleCovarianceDeviation k hk (lam i) (fun j => x i j ω) ≤ 1 / 4 ∧
          M * N i ≤ empiricalEffectiveDimension (fun j => k (x i j ω)) (lam i)} := by
        apply measure_mono
        intro ω hω
        refine ⟨hω.1, ?_⟩
        have hnonneg : 0 ≤ K i ω := div_nonneg
          (actual_empiricalEffectiveDimension_nonneg _ (lam i) (hlam i)) hNi.le
        have hh : M ≤ K i ω := by simpa only [abs_of_nonneg hnonneg] using hω.2
        exact (le_div_iff₀ hNi).mp hh
      _ ≤ ENNReal.ofReal (2 * N i / (M * N i)) := hb
      _ = ENNReal.ofReal (2 / M) := by
        congr 1
        dsimp [N]
        field_simp [hNi.ne', hM.ne']
  have hp := tendstoInMeasure_mul_zero_of_good_tail f K G 2 (by norm_num) hδN hbad htail
  apply TendstoInMeasure.congr' _ (EventuallyEq.rfl) hp
  filter_upwards [hN, hQ] with i hNi hQi
  exact Eventually.of_forall (fun ω => by
    dsimp [f, K, N, δ]
    field_simp [hNi.ne', hQi.ne'])

/-- The actual variance conclusion from the source operator-probability scales
and the genuine HS moment scale. The covariance spectral interval bounds are
analytic boundedness premises, and can be supplied by a bounded kernel; no
trace, HS-existence, square-root, or final variance certificate is assumed.
No lower bound on the positive effective dimensions is required. -/
theorem actual_variance_relative_tendstoInMeasure
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (hind : ∀ i, Pairwise (fun j k => IndepFun (x i j) (x i k) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hMX : ∀ i ω, ‖empiricalCovariance (fun j => k (x i j ω))‖ ≤ M)
    (φ : ι → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L : ι → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hδ : TendstoInMeasure P (fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω))
      l (fun _ => 0))
    (hδN : TendstoInMeasure P (fun i ω =>
      actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) *
        featureEffectiveDimension k hk (lam i) / featureFilterDimension k hk (φ i)) l (fun _ => 0))
    (hscale : Tendsto (fun i => L i * featureEffectiveDimension k hk (lam i) /
      ((n i : ℝ) * featureFilterDimension k hk (φ i))) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω =>
      |actualVarianceEnergy k hk (φ i) (hlam i) (fun j => x i j ω) (hMX i ω) (h i) -
        featureFilterDimension k hk (φ i)| / featureFilterDimension k hk (φ i)) l (fun _ => 0) := by
  let Q := fun i => featureFilterDimension k hk (φ i)
  let δ := fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)
  let Nhat := fun i ω => empiricalEffectiveDimension (fun j => k (x i j ω)) (lam i)
  let W := fun i ω => empiricalFilterDimension (fun j => k (x i j ω)) (φ i)
  let a := fun i ω => actualVarianceEnergy k hk (φ i) (hlam i) (fun j => x i j ω) (hMX i ω) (h i)
  let d := fun i ω => ‖actualShrinkageDifferenceColumns k hk (φ i) (hlam i) hM
    (fun j => x i j ω) (hMX i ω) (hf i) (h i)‖
  let η := fun i ω => ‖normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) k hk (lam i)
    (fun j => x i j ω)‖
  let G := fun i => {ω | δ i ω ≤ 1 / 4}
  have hbad : Tendsto (fun i => P (G i)ᶜ) l (𝓝 0) := by
    simpa only [G, Set.compl_setOf, not_le] using
      measure_exceed_tendsto_zero_of_tendstoInMeasure δ hδ (1 / 4) (by norm_num)
  have hNpos : ∀ᶠ i in l, 0 < featureEffectiveDimension k hk (lam i) := by
    filter_upwards [hQ] with i hQi
    exact featureEffectiveDimension_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hQi
  have hη : TendstoInMeasure P (fun i ω => η i ω ^ 2 / Q i) l (fun _ => 0) :=
    actual_hs_error_sq_div_tendstoInMeasure n hn x hlaw hind k hk lam hlam L Q hL hQ hscale
  have hd : TendstoInMeasure P (fun i ω => d i ω ^ 2 / Q i) l (fun _ => 0) := by
    apply tendstoInMeasure_zero_of_good_events P _
      (fun i ω => (2 * A * (1 + ρ)) ^ 2 * (η i ω ^ 2 / Q i)) G hbad
      (tendstoInMeasure_const_mul_zero hη _) _
    filter_upwards [hQ] with i hQi ω hω
    have hb := actualShrinkageDifferenceColumns_norm_le_eta k hk (φ i) (hlam i) hM
      (fun j => x i j ω) (hMX i ω) (hf i) (h i) hω
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hQi.le)]
    simpa only [mul_pow, mul_div_assoc] using div_le_div_of_nonneg_right hs hQi.le
  have hNhat : TendstoInMeasure P (fun i ω => δ i ω * Nhat i ω / Q i) l (fun _ => 0) :=
    actual_delta_empiricalDimension_div_tendstoInMeasure n hn x hlaw k hk lam hlam Q hQ hNpos hδ hδN
  apply probabilistic_variance_transfer_on_good_events P a W Nhat δ d Q A G hQ hbad _ _ _ hδ hd hNhat
  · exact Eventually.of_forall (fun i => Eventually.of_forall (fun ω hω =>
      ⟨tsum_nonneg (fun _ => sq_nonneg _), actual_empiricalEffectiveDimension_nonneg _ (lam i) (hlam i),
        norm_nonneg _, norm_nonneg _, hω⟩))
  · exact Eventually.of_forall (fun i => Eventually.of_forall (fun ω _ =>
      empirical_variance_trace_abs_sub_le (featureEmbedding μ k hk)
        (populationCovariance_feature_isCompact μ k hk) _ (φ i) (hlam i) (hMX i ω) (hf i) (h i)))
  · exact Eventually.of_forall (fun i => Eventually.of_forall (fun ω _ =>
      actual_variance_sqrt_comparison k hk (φ i) (hlam i) hM (fun j => x i j ω)
        (hMX i ω) (hf i) (h i)))

end KernelSeq
