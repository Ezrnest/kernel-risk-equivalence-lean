import KernelSeq.EmpiricalMeasurability
import KernelSeq.ConditionalRisk

/-!
# Conditional risk of the actual empirical spectral estimator

The feature embedding, empirical filter, prediction coefficients, and prediction
bias are actual maps. Their design strong measurability and the bias L² property
are derived from bounded strongly measurable features, an L² target, and the
design laws. The final conditional expectation is not an assumed certificate.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal MeasureTheory

namespace KernelSeq

variable {X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The actual feature embedding, with its L²-feature input proved from the
primitive source assumptions. -/
noncomputable def boundedFeatureEmbedding (μ : Measure X) [IsProbabilityMeasure μ]
    (k : X → H) (hk : StronglyMeasurable k) (κ : ℝ) (hb : ∀ x, ‖k x‖ ≤ κ) :
    H →L[ℝ] Lp ℝ 2 μ :=
  featureEmbedding μ k (feature_memLp_of_bound μ k hk.aestronglyMeasurable κ (Eventually.of_forall hb))

omit [CompleteSpace H] in
theorem boundedFeatureEmbedding_norm_le (k : X → H) (hk : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0 ≤ κ) (hb : ∀ x, ‖k x‖ ≤ κ) :
    ‖boundedFeatureEmbedding μ k hk κ hb‖ ≤ κ :=
  featureEmbedding_norm_le μ k _ κ hκ (Eventually.of_forall hb)

/-- One actual observation-noise prediction coefficient. -/
noncomputable def featureSamplePredictionCoefficient (k : X → H) (hk : StronglyMeasurable k)
    (κ : ℝ) (hb : ∀ x, ‖k x‖ ≤ κ) {n : ℕ} (hn : 0 < n)
    (Z : Fin n → Ω → X × ℝ) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) (ω : Ω) : Lp ℝ 2 μ :=
  empiricalPredictionCoefficient (boundedFeatureEmbedding μ k hk κ hb) hn
    (fun j => k ((Z j ω).1)) κ
    (fun j => pow_le_pow_left₀ (norm_nonneg _) (hb ((Z j ω).1)) 2) φ hlam h i

/-- The actual conditional mean prediction error. -/
noncomputable def featureSamplePredictionBias (k : X → H) (hk : StronglyMeasurable k)
    (κ : ℝ) (hb : ∀ x, ‖k x‖ ≤ κ) {n : ℕ} (hn : 0 < n)
    (Z : Fin n → Ω → X × ℝ) (f : X → ℝ) (hfLp : MemLp f 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (ω : Ω) : Lp ℝ 2 μ :=
  boundedFeatureEmbedding μ k hk κ hb
    (empiricalSpectralEstimator hn (fun j => k ((Z j ω).1)) κ
      (fun j => pow_le_pow_left₀ (norm_nonneg _) (hb ((Z j ω).1)) 2)
      (fun j => f ((Z j ω).1)) φ hlam h) - hfLp.toLp f

/-- The actual observed-response prediction error. -/
noncomputable def featureSamplePredictionError (k : X → H) (hk : StronglyMeasurable k)
    (κ : ℝ) (hb : ∀ x, ‖k x‖ ≤ κ) {n : ℕ} (hn : 0 < n)
    (Z : Fin n → Ω → X × ℝ) (f : X → ℝ) (hfLp : MemLp f 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (ω : Ω) : Lp ℝ 2 μ :=
  boundedFeatureEmbedding μ k hk κ hb
    (empiricalSpectralEstimator hn (fun j => k ((Z j ω).1)) κ
      (fun j => pow_le_pow_left₀ (norm_nonneg _) (hb ((Z j ω).1)) 2)
      (fun j => (Z j ω).2) φ hlam h) - hfLp.toLp f

omit [MeasurableSpace Ω] in
theorem featureSamplePredictionCoefficient_norm_le (k : X → H) (hk : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0 ≤ κ) (hb : ∀ x, ‖k x‖ ≤ κ) {n : ℕ} (hn : 0 < n)
    (Z : Fin n → Ω → X × ℝ) (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) (ω : Ω) :
    ‖featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i ω‖ ≤
      A * κ ^ 2 / ((n : ℝ) * lam) :=
  empiricalPredictionCoefficient_norm_le _ hn _ κ hκ
    (boundedFeatureEmbedding_norm_le k hk κ hκ hb)
    (fun j => hb ((Z j ω).1)) φ hlam h i

omit [MeasurableSpace Ω] in
/-- Design measurability is derived for the actual prediction coefficients. -/
theorem featureSamplePredictionCoefficient_design_stronglyMeasurable
    (k : X → H) (hk : StronglyMeasurable k) (κ : ℝ) (hb : ∀ x, ‖k x‖ ≤ κ)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (φ : ℝ → ℝ) {lam ρ A : ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (i : Fin n) :
    StronglyMeasurable[⨆ j, observationDesignSigma (Z j)]
      (featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i) :=
  observation_empiricalPredictionCoefficient_design_stronglyMeasurable _ hn Z k hk κ
    (fun x => pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) φ hlam hf h i

omit [MeasurableSpace Ω] in
theorem featureSamplePredictionBias_design_stronglyMeasurable
    (k : X → H) (hk : StronglyMeasurable k) (κ : ℝ) (hb : ∀ x, ‖k x‖ ≤ κ)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (f : X → ℝ)
    (hfm : Measurable f) (hfLp : MemLp f 2 μ) (φ : ℝ → ℝ) {lam ρ A : ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    StronglyMeasurable[⨆ j, observationDesignSigma (Z j)]
      (featureSamplePredictionBias k hk κ hb hn Z f hfLp φ hlam h) := by
  exact ((boundedFeatureEmbedding μ k hk κ hb).continuous.comp_stronglyMeasurable
    (observation_empiricalMeanEstimator_design_stronglyMeasurable hn Z k hk κ
      (fun x => pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) f hfm φ hlam hf h)).sub stronglyMeasurable_const

omit [MeasurableSpace Ω] in
/-- Exact finite response representation of the actual conditional bias. -/
theorem featureSamplePredictionBias_eq_sum (k : X → H) (hk : StronglyMeasurable k)
    (κ : ℝ) (hb : ∀ x, ‖k x‖ ≤ κ) {n : ℕ} (hn : 0 < n)
    (Z : Fin n → Ω → X × ℝ) (f : X → ℝ) (hfLp : MemLp f 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (ω : Ω) :
    featureSamplePredictionBias k hk κ hb hn Z f hfLp φ hlam h ω =
      (∑ i, f ((Z i ω).1) • featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i ω) -
        hfLp.toLp f := by
  unfold featureSamplePredictionBias featureSamplePredictionCoefficient
  rw [empiricalSpectralEstimator_prediction_sum]

omit [IsProbabilityMeasure P] in
/-- Scalar L² times an actually bounded random vector is L². -/
theorem memLp_scalar_smul_of_bounded_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Ω → ℝ} (hg : MemLp g 2 P) {a : Ω → E} (ha : AEStronglyMeasurable a P)
    {C : ℝ} (hC : ∀ᵐ ω ∂P, ‖a ω‖ ≤ C) : MemLp (fun ω => g ω • a ω) 2 P := by
  apply (hg.norm.mul_const C).mono' (hg.1.smul ha)
  filter_upwards [hC] with ω hω
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left hω (norm_nonneg _)

/-- The actual prediction bias is L² under the source model. In particular this
is not retained as a conditional-risk premise. -/
theorem memLp_featureSamplePredictionBias (k : X → H) (hk : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0 ≤ κ) (hb : ∀ x, ‖k x‖ ≤ κ) {n : ℕ} (hn : 0 < n)
    (Z : Fin n → Ω → X × ℝ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, MeasurePreserving (fun ω => (Z i ω).1) P μ)
    (f : X → ℝ) (hfLp : MemLp f 2 μ) (φ : ℝ → ℝ) {lam ρ A : ℝ}
    (hlam : 0 < lam) (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    MemLp (featureSamplePredictionBias k hk κ hb hn Z f hfLp φ hlam h) 2 P := by
  have hm : (⨆ j, observationDesignSigma (Z j)) ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup_le (fun j => (hZ j).fst.comap_le)
  have ha (i : Fin n) : AEStronglyMeasurable
      (featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i) P :=
    ((featureSamplePredictionCoefficient_design_stronglyMeasurable k hk κ hb hn Z φ hlam hf h i).mono hm).aestronglyMeasurable
  have hprod (i : Fin n) : MemLp (fun ω => f ((Z i ω).1) •
      featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i ω) 2 P := by
    apply memLp_scalar_smul_of_bounded_vector (hfLp.comp_measurePreserving (hlaw i)) (ha i)
    exact Eventually.of_forall (featureSamplePredictionCoefficient_norm_le k hk κ hκ hb hn Z φ hlam h i)
  have he : featureSamplePredictionBias k hk κ hb hn Z f hfLp φ hlam h =
      (fun ω => (∑ i, f ((Z i ω).1) •
        featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i ω) - hfLp.toLp f) := by
    funext ω
    exact featureSamplePredictionBias_eq_sum k hk κ hb hn Z f hfLp φ hlam h ω
  rw [he]
  convert (memLp_finsetSum' Finset.univ (fun i _ => hprod i)).sub
    (memLp_const (hfLp.toLp f)) using 1
  funext ω
  simp only [Pi.sub_apply, Finset.sum_apply]

omit [MeasurableSpace Ω] in
/-- Actual observed prediction error equals the conditional bias plus the
coefficient-weighted observation noises. -/
theorem featureSamplePredictionError_decomposition (k : X → H) (hk : StronglyMeasurable k)
    (κ : ℝ) (hb : ∀ x, ‖k x‖ ≤ κ) {n : ℕ} (hn : 0 < n)
    (Z : Fin n → Ω → X × ℝ) (f : X → ℝ) (hfLp : MemLp f 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (ω : Ω) :
    featureSamplePredictionError k hk κ hb hn Z f hfLp φ hlam h ω =
      featureSamplePredictionBias k hk κ hb hn Z f hfLp φ hlam h ω +
        ∑ i, observationNoise (Z i) f ω •
          featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i ω := by
  have hd := empiricalSpectralEstimator_prediction_noise_decomposition
    (boundedFeatureEmbedding μ k hk κ hb) hn (fun j => k ((Z j ω).1)) κ
    (fun j => pow_le_pow_left₀ (norm_nonneg _) (hb ((Z j ω).1)) 2)
    (fun j => f ((Z j ω).1)) (fun j => observationNoise (Z j) f ω) (hfLp.toLp f) φ hlam h
  have hy : (fun j => f ((Z j ω).1) + observationNoise (Z j) f ω) =
      (fun j => (Z j ω).2) := by
    funext j
    dsimp only [observationNoise]
    ring
  rw [hy] at hd
  exact hd

/-- The exact conditional bias/variance formula for the actual empirical
spectral estimator. Bias L², design measurability, coefficient bounds, and
all-design noise moments are all derived from the displayed source assumptions. -/
theorem empirical_spectral_conditional_risk (k : X → H) (hk : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0 ≤ κ) (hb : ∀ x, ‖k x‖ ≤ κ) {n : ℕ} (hn : 0 < n)
    (Z : Fin n → Ω → X × ℝ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, MeasurePreserving (fun ω => (Z i ω).1) P μ)
    (f : X → ℝ) (hfm : Measurable f) (hfLp : MemLp f 2 μ)
    (σ : ℝ) (hσ : 0 < σ) (hind : iIndepFun Z P)
    (hmean : ∀ i, P[observationNoise (Z i) f | observationDesignSigma (Z i)] =ᵐ[P]
      (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => observationNoise (Z i) f ω ^ 2) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => σ ^ 2))
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ) (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) :
    Integrable (fun ω => ‖featureSamplePredictionError k hk κ hb hn Z f hfLp φ hlam h ω‖ ^ 2) P ∧
    P[(fun ω => ‖featureSamplePredictionError k hk κ hb hn Z f hfLp φ hlam h ω‖ ^ 2) |
      ⨆ i, observationDesignSigma (Z i)] =ᵐ[P]
      (fun ω => ‖featureSamplePredictionBias k hk κ hb hn Z f hfLp φ hlam h ω‖ ^ 2 +
        σ ^ 2 * ∑ i, ‖featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i ω‖ ^ 2) := by
  have hrLp := memLp_featureSamplePredictionBias k hk κ hκ hb hn Z hZ hlaw f hfLp φ hlam hf h
  have hr := featureSamplePredictionBias_design_stronglyMeasurable k hk κ hb hn Z f hfm hfLp φ hlam hf h
  have ha := featureSamplePredictionCoefficient_design_stronglyMeasurable (μ := μ) k hk κ hb hn Z φ hlam hf h
  let C := A * κ ^ 2 / ((n : ℝ) * lam)
  have hC : 0 ≤ C := div_nonneg
    (mul_nonneg (h.constant_nonneg hlam (sq_nonneg κ)) (sq_nonneg κ))
    (mul_nonneg (Nat.cast_nonneg n) hlam.le)
  have hab (i : Fin n) : ∀ᵐ ω ∂P,
      ‖featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i ω‖ ≤ C :=
    Eventually.of_forall (featureSamplePredictionCoefficient_norm_le k hk κ hκ hb hn Z φ hlam h i)
  obtain ⟨hint, hce⟩ := observation_pair_conditional_risk Z f σ hZ hfm hσ hind hmean hsecond
    (featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h)
    (featureSamplePredictionBias k hk κ hb hn Z f hfLp φ hlam h) hrLp hr ha (fun _ => C) (fun _ => hC) hab
  have he : (fun ω => ‖featureSamplePredictionError k hk κ hb hn Z f hfLp φ hlam h ω‖ ^ 2) =
      (fun ω => ‖featureSamplePredictionBias k hk κ hb hn Z f hfLp φ hlam h ω +
        ∑ i, observationNoise (Z i) f ω •
          featureSamplePredictionCoefficient (μ := μ) k hk κ hb hn Z φ hlam h i ω‖ ^ 2) := by
    funext ω
    rw [featureSamplePredictionError_decomposition]
  rw [he]
  exact ⟨hint, hce⟩

end KernelSeq
