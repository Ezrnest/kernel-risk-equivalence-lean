import KernelSeq.SequenceBenchmark
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Risk of the actual infinite Gaussian sequence model

The noise is given on an arbitrary probability space by standard Gaussian
marginal laws. Independence is unnecessary for this diagonal squared risk.
Square summability of the random error is derived by Tonelli, rather than
postulated. The resulting `lp` random variable has a globally strongly
measurable representative and the prescribed coordinates almost everywhere.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BigOperators

namespace KernelSeq

noncomputable section

attribute [local instance] Classical.propDecidable

variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω] {P : Measure Ω}

/-- Totalize a square-summable sequence by zero on the exceptional set. -/
noncomputable def squareSequence (e : ι → Ω → ℝ) (ω : Ω) : lp (fun _ : ι => ℝ) 2 :=
  if h : Memℓp (fun i => e i ω) 2 then ⟨fun i => e i ω, h⟩ else 0

omit [Countable ι] [MeasurableSpace Ω] in
theorem squareSequence_apply {e : ι → Ω → ℝ} {ω : Ω}
    (h : Memℓp (fun i => e i ω) 2) (i : ι) : squareSequence e ω i = e i ω := by
  simp only [squareSequence, dif_pos h]

/-- Finite total expected coordinate energy forces almost sure `ℓ²` membership. -/
theorem ae_memℓp_of_summable_integral_sq (e : ι → Ω → ℝ)
    (he : ∀ i, Integrable (fun ω => e i ω ^ 2) P)
    (hs : Summable (fun i => ∫ ω, e i ω ^ 2 ∂P)) :
    ∀ᵐ ω ∂P, Memℓp (fun i => e i ω) 2 := by
  have hfinite : (∫⁻ ω, ∑' i, ENNReal.ofReal (e i ω ^ 2) ∂P) ≠ ∞ := by
    rw [lintegral_tsum (fun i => (he i).aemeasurable.ennreal_ofReal)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (he _) (.of_forall fun _ => sq_nonneg _)]
    exact hs.tsum_ofReal_ne_top
  have hae := ae_lt_top' (AEMeasurable.tsum
    (fun i => (he i).aemeasurable.ennreal_ofReal)) hfinite
  filter_upwards [hae] with ω hω
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  have hsum := ENNReal.summable_toReal hω.ne
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofNat,
    Real.rpow_two, Real.norm_eq_abs, sq_abs] using hsum

theorem squareSequence_aestronglyMeasurable (e : ι → Ω → ℝ)
    (he : ∀ i, AEStronglyMeasurable (e i) P)
    (hae : ∀ᵐ ω ∂P, Memℓp (fun i => e i ω) 2) :
    AEStronglyMeasurable (squareSequence e) P := by
  classical
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
    (f := fun s ω => ∑ i ∈ s, lp.single 2 i (e i ω))
  · intro s
    exact s.aestronglyMeasurable_fun_sum fun i _ =>
      (lp.singleContinuousLinearMap ℝ (fun _ : ι => ℝ) 2 i).continuous.comp_aestronglyMeasurable
        (he i)
  · filter_upwards [hae] with ω hω
    simpa only [HasSum, SummationFilter.unconditional, squareSequence_apply hω] using
      lp.hasSum_single (by simp : (2 : ℝ≥0∞) ≠ ∞) (squareSequence e ω)

omit [Countable ι] in
theorem squareSequence_norm_sq_ae (e : ι → Ω → ℝ)
    (hae : ∀ᵐ ω ∂P, Memℓp (fun i => e i ω) 2) :
    (fun ω => ‖squareSequence e ω‖ ^ 2) =ᵐ[P] (fun ω => ∑' i, e i ω ^ 2) := by
  filter_upwards [hae] with ω hω
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [squareSequence_apply hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem squareSequence_integral_norm_sq (e : ι → Ω → ℝ)
    (he : ∀ i, MemLp (e i) 2 P)
    (hs : Summable (fun i => ∫ ω, e i ω ^ 2 ∂P)) :
    MemLp (squareSequence e) 2 P ∧
      (∫ ω, ‖squareSequence e ω‖ ^ 2 ∂P) = ∑' i, ∫ ω, e i ω ^ 2 ∂P := by
  have hae := ae_memℓp_of_summable_integral_sq e (fun i => (he i).integrable_sq) hs
  have hmeas := squareSequence_aestronglyMeasurable e (fun i => (he i).1) hae
  have hsum_norm : Summable (fun i => ∫ ω, ‖e i ω ^ 2‖ ∂P) := by
    simpa only [Real.norm_eq_abs, abs_sq] using hs
  have hi := integral_tsum_of_summable_integral_norm
    (fun i => (he i).integrable_sq) hsum_norm
  have hfin : (∫⁻ ω, ENNReal.ofReal (‖squareSequence e ω‖ ^ 2) ∂P) < ∞ := by
    have hnonneg := fun i ω => sq_nonneg (e i ω)
    have hsq : ∀ᵐ ω ∂P,
        ENNReal.ofReal (‖squareSequence e ω‖ ^ 2) =
          ∑' i, ENNReal.ofReal (e i ω ^ 2) := by
      filter_upwards [hae, squareSequence_norm_sq_ae e hae] with ω hω heq
      rw [heq, ENNReal.ofReal_tsum_of_nonneg (fun i => hnonneg i ω)]
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
        hω.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    rw [lintegral_congr_ae hsq,
      lintegral_tsum (fun i => (he i).aemeasurable.pow_const 2 |>.ennreal_ofReal)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (he _).integrable_sq
      (.of_forall fun _ => sq_nonneg _)]
    exact hs.tsum_ofReal_lt_top
  have hint : Integrable (fun ω => ‖squareSequence e ω‖ ^ 2) P :=
    ⟨hmeas.norm.pow 2, (hasFiniteIntegral_iff_ofReal (.of_forall fun _ => sq_nonneg _)).2 hfin⟩
  exact ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 hint,
    (integral_congr_ae (squareSequence_norm_sq_ae e hae)).trans hi.symm⟩

section GaussianMoments

theorem standardGaussian_memLp {ξ : Ω → ℝ}
    (hξ : HasLaw ξ (gaussianReal 0 1) P) : MemLp ξ 2 P := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  rw [← hξ.map_eq] at h
  simpa only [Function.id_comp] using h.comp_of_map hξ.aemeasurable

theorem standardGaussian_integral {ξ : Ω → ℝ}
    (hξ : HasLaw ξ (gaussianReal 0 1) P) : (∫ ω, ξ ω ∂P) = 0 := by
  rw [hξ.integral_eq, integral_id_gaussianReal]

theorem standardGaussian_integral_sq {ξ : Ω → ℝ}
    (hξ : HasLaw ξ (gaussianReal 0 1) P) : (∫ ω, ξ ω ^ 2 ∂P) = 1 := by
  have hg : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] using
      (variance_eq_integral (X := fun x : ℝ => x) (μ := gaussianReal 0 1)
        measurable_id.aemeasurable).symm.trans
        (variance_fun_id_gaussianReal (μ := 0) (v := 1))
  exact (hξ.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun x : ℝ => x ^ 2) (gaussianReal 0 1))).trans hg

end GaussianMoments

section DiagonalRisk

variable [IsProbabilityMeasure P]

theorem affine_integral_sq_of_standard_moments {ξ : Ω → ℝ}
    (hξ : MemLp ξ 2 P) (hmean : (∫ ω, ξ ω ∂P) = 0)
    (hsecond : (∫ ω, ξ ω ^ 2 ∂P) = 1) (a b : ℝ) :
    (∫ ω, (a + b * ξ ω) ^ 2 ∂P) = a ^ 2 + b ^ 2 := by
  have hi := hξ.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heq : (fun ω => (a + b * ξ ω) ^ 2) =
      fun ω => (a ^ 2 + (2 * a * b) * ξ ω) + b ^ 2 * ξ ω ^ 2 := by
    funext ω
    ring
  have h1 : Integrable (fun ω => a ^ 2 + (2 * a * b) * ξ ω) P :=
    (integrable_const (a ^ 2)).add (hi.const_mul (2 * a * b))
  have h2 : Integrable (fun ω => b ^ 2 * ξ ω ^ 2) P := hξ.integrable_sq.const_mul (b ^ 2)
  rw [heq, integral_add h1 h2, integral_add (integrable_const (a ^ 2)) (hi.const_mul (2 * a * b)),
    integral_const_mul, integral_const_mul, hmean, hsecond, integral_const]
  simp

/-- The random diagonal sequence, defined also on its null exceptional set. -/
noncomputable def diagonalSequenceError (a b : ι → ℝ) (ξ : ι → Ω → ℝ) :
    Ω → lp (fun _ : ι => ℝ) 2 :=
  squareSequence (fun i ω => a i + b i * ξ i ω)

theorem diagonalSequenceError_moment (a b : ι → ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, MemLp (ξ i) 2 P)
    (hmean : ∀ i, (∫ ω, ξ i ω ∂P) = 0)
    (hsecond : ∀ i, (∫ ω, ξ i ω ^ 2 ∂P) = 1)
    (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    MemLp (diagonalSequenceError a b ξ) 2 P ∧
      (∫ ω, ‖diagonalSequenceError a b ξ ω‖ ^ 2 ∂P) =
        (∑' i, a i ^ 2) + ∑' i, b i ^ 2 := by
  have he : ∀ i, MemLp (fun ω => a i + b i * ξ i ω) 2 P :=
    fun i => (memLp_const (a i)).add ((hξ i).const_mul (b i))
  have hm i := affine_integral_sq_of_standard_moments (hξ i) (hmean i) (hsecond i) (a i) (b i)
  have hs : Summable (fun i => ∫ ω, (a i + b i * ξ i ω) ^ 2 ∂P) := by
    simp_rw [hm]
    exact ha.add hb
  obtain ⟨hmem, hrisk⟩ := squareSequence_integral_norm_sq
    (fun i ω => a i + b i * ξ i ω) he hs
  refine ⟨hmem, ?_⟩
  rw [diagonalSequenceError, hrisk]
  simp_rw [hm]
  exact ha.tsum_add hb

theorem diagonalSequenceError_coordinates_ae (a b : ι → ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, MemLp (ξ i) 2 P)
    (hmean : ∀ i, (∫ ω, ξ i ω ∂P) = 0)
    (hsecond : ∀ i, (∫ ω, ξ i ω ^ 2 ∂P) = 1)
    (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    ∀ᵐ ω ∂P, ∀ i, diagonalSequenceError a b ξ ω i = a i + b i * ξ i ω := by
  have he : ∀ i, MemLp (fun ω => a i + b i * ξ i ω) 2 P :=
    fun i => (memLp_const (a i)).add ((hξ i).const_mul (b i))
  have hm i := affine_integral_sq_of_standard_moments (hξ i) (hmean i) (hsecond i) (a i) (b i)
  have hs : Summable (fun i => ∫ ω, (a i + b i * ξ i ω) ^ 2 ∂P) := by
    simp_rw [hm]
    exact ha.add hb
  filter_upwards [ae_memℓp_of_summable_integral_sq
    (fun i ω => a i + b i * ξ i ω) (fun i => (he i).integrable_sq) hs] with ω hω
  intro i
  exact squareSequence_apply (e := fun i ω => a i + b i * ξ i ω) (ω := ω) hω i

/-- A globally strongly measurable version of the actual Gaussian error. -/
noncomputable def diagonalGaussianError (a b : ι → ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    Ω → lp (fun _ : ι => ℝ) 2 :=
  ((diagonalSequenceError_moment a b ξ (fun i => standardGaussian_memLp (hξ i))
    (fun i => standardGaussian_integral (hξ i))
    (fun i => standardGaussian_integral_sq (hξ i)) ha hb).1).1.mk _

theorem diagonalGaussianError_stronglyMeasurable (a b : ι → ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    StronglyMeasurable (diagonalGaussianError a b ξ hξ ha hb) :=
  AEStronglyMeasurable.stronglyMeasurable_mk _

theorem diagonalGaussianError_ae_eq (a b : ι → ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    diagonalGaussianError a b ξ hξ ha hb =ᵐ[P] diagonalSequenceError a b ξ :=
  AEStronglyMeasurable.ae_eq_mk _ |>.symm

theorem diagonalGaussianError_risk (a b : ι → ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    (ha : Summable (fun i => a i ^ 2)) (hb : Summable (fun i => b i ^ 2)) :
    MemLp (diagonalGaussianError a b ξ hξ ha hb) 2 P ∧
      (∀ᵐ ω ∂P, ∀ i, diagonalGaussianError a b ξ hξ ha hb ω i = a i + b i * ξ i ω) ∧
      (∫ ω, ‖diagonalGaussianError a b ξ hξ ha hb ω‖ ^ 2 ∂P) =
        (∑' i, a i ^ 2) + ∑' i, b i ^ 2 := by
  have hmoment := diagonalSequenceError_moment a b ξ (fun i => standardGaussian_memLp (hξ i))
    (fun i => standardGaussian_integral (hξ i))
    (fun i => standardGaussian_integral_sq (hξ i)) ha hb
  have heq := diagonalGaussianError_ae_eq a b ξ hξ ha hb
  refine ⟨hmoment.1.ae_eq heq.symm, ?_, ?_⟩
  · filter_upwards [heq, diagonalSequenceError_coordinates_ae a b ξ
      (fun i => standardGaussian_memLp (hξ i)) (fun i => standardGaussian_integral (hξ i))
      (fun i => standardGaussian_integral_sq (hξ i)) ha hb] with ω hω hc
    simpa only [hω] using hc
  · exact (integral_congr_ae (heq.fun_comp fun x => ‖x‖ ^ 2)).trans hmoment.2

end DiagonalRisk

omit [Countable ι] in
theorem summable_shrinkage_error_bias (q f : ι → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (hf : Summable (fun i => f i ^ 2)) :
    Summable (fun i => ((q i - 1) * f i) ^ 2) := by
  refine hf.of_nonneg_of_le (fun i => sq_nonneg _) fun i => ?_
  rw [mul_pow]
  apply mul_le_of_le_one_left (sq_nonneg _)
  have hi := hq i
  nlinarith [mul_nonneg hi.1 (sub_nonneg.mpr hi.2)]

omit [Countable ι] in
theorem summable_scaled_sequence_noise (q : ι → ℝ) (c : ℝ)
    (hq : Summable (fun i => q i ^ 2)) : Summable (fun i => (c * q i) ^ 2) := by
  simpa only [mul_pow] using hq.mul_left (c ^ 2)

section ShrinkageRisk

variable [IsProbabilityMeasure P]

/-- A concrete measurable `ℓ²` error for observations `f_j+c ξ_j`, after
coordinatewise shrinkage by `q_j`. The bias summability proof can come from
`f ∈ ℓ²` and `0 ≤ q ≤ 1`, or from the actual supported spectral bias. -/
noncomputable def gaussianShrinkageError (q f : ι → ℝ) (c : ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    (hbias : Summable (fun i => ((q i - 1) * f i) ^ 2))
    (hq : Summable (fun i => q i ^ 2)) : Ω → lp (fun _ : ι => ℝ) 2 :=
  diagonalGaussianError (fun i => (q i - 1) * f i) (fun i => c * q i) ξ hξ hbias
    (summable_scaled_sequence_noise q c hq)

theorem gaussianShrinkageError_stronglyMeasurable (q f : ι → ℝ) (c : ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    (hbias : Summable (fun i => ((q i - 1) * f i) ^ 2))
    (hq : Summable (fun i => q i ^ 2)) :
    StronglyMeasurable (gaussianShrinkageError q f c ξ hξ hbias hq) :=
  diagonalGaussianError_stronglyMeasurable _ _ _ _ _ _

theorem gaussianShrinkageError_risk (q f : ι → ℝ) (c : ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    (hbias : Summable (fun i => ((q i - 1) * f i) ^ 2))
    (hq : Summable (fun i => q i ^ 2)) :
    MemLp (gaussianShrinkageError q f c ξ hξ hbias hq) 2 P ∧
      (∀ᵐ ω ∂P, ∀ i, gaussianShrinkageError q f c ξ hξ hbias hq ω i =
        (q i - 1) * f i + c * q i * ξ i ω) ∧
      (∫ ω, ‖gaussianShrinkageError q f c ξ hξ hbias hq ω‖ ^ 2 ∂P) =
        (∑' i, (1 - q i) ^ 2 * f i ^ 2) + c ^ 2 * ∑' i, q i ^ 2 := by
  have h := diagonalGaussianError_risk (fun i => (q i - 1) * f i)
    (fun i => c * q i) ξ hξ hbias (summable_scaled_sequence_noise q c hq)
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  congr 1
  · apply tsum_congr
    intro i
    ring
  · simp_rw [mul_pow]
    exact tsum_mul_left

theorem gaussianShrinkageError_integrable_norm_sq (q f : ι → ℝ) (c : ℝ) (ξ : ι → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    (hbias : Summable (fun i => ((q i - 1) * f i) ^ 2))
    (hq : Summable (fun i => q i ^ 2)) :
    Integrable (fun ω => ‖gaussianShrinkageError q f c ξ hξ hbias hq ω‖ ^ 2) P :=
  (gaussianShrinkageError_risk q f c ξ hξ hbias hq).1.integrable_norm_pow (by norm_num)

end ShrinkageRisk

section ActualFeatureSequence

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

omit [TopologicalSpace.SeparableSpace H] in
private theorem featureGaussianBias_summable (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {M : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) {f : Lp ℝ 2 μ}
    (hf : f ∈ PredictionRange (featureEmbedding μ k hk)) :
    Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) =>
      ((ResidualFilter.shrinkage φ i.1.1 - 1) * featureSequenceCoefficient k hk f i) ^ 2) := by
  apply (summable_featureSequenceBias k hk φ hM hfilter hf).congr
  intro i
  dsimp only [ResidualFilter.residual]
  ring

/-- The infinite Gaussian model uses precisely the positive singular index of
the actual feature embedding. No separability of the ambient prediction `L²`
space and no independence assumption on the noise coordinates are required. -/
noncomputable def featureGaussianSequenceError (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (hf : f ∈ PredictionRange (featureEmbedding μ k hk))
    (σ : ℝ) (n : ℕ)
    (ξ : PredictionSingularIndex (featureEmbedding μ k hk) → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) :
    Ω → lp (fun _ : PredictionSingularIndex (featureEmbedding μ k hk) => ℝ) 2 := by
  letI := predictionSingularIndex_countable (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk)
  exact gaussianShrinkageError (fun i => ResidualFilter.shrinkage φ i.1.1)
    (featureSequenceCoefficient k hk f) (σ / Real.sqrt (n : ℝ)) ξ hξ
    (featureGaussianBias_summable k hk φ hM hfilter hf)
    (summable_positive_sequence_filterDimension k hk φ hlam hM hfilter h)

theorem featureGaussianSequenceError_stronglyMeasurable (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (hf : f ∈ PredictionRange (featureEmbedding μ k hk))
    (σ : ℝ) (n : ℕ)
    (ξ : PredictionSingularIndex (featureEmbedding μ k hk) → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) :
    StronglyMeasurable (featureGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n ξ hξ) := by
  letI := predictionSingularIndex_countable (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk)
  exact gaussianShrinkageError_stronglyMeasurable _ _ _ _ _ _ _

/-- The expected squared error of the actual infinite Gaussian sequence
estimator equals the previously defined manuscript benchmark. -/
theorem featureGaussianSequenceError_risk (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (hf : f ∈ PredictionRange (featureEmbedding μ k hk))
    (σ : ℝ) (n : ℕ) (hn : 0 < n)
    (ξ : PredictionSingularIndex (featureEmbedding μ k hk) → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) :
    MemLp (featureGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n ξ hξ) 2 P ∧
      (∀ᵐ ω ∂P, ∀ i,
        featureGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n ξ hξ ω i =
          (ResidualFilter.shrinkage φ i.1.1 - 1) * featureSequenceCoefficient k hk f i +
            (σ / Real.sqrt (n : ℝ)) * ResidualFilter.shrinkage φ i.1.1 * ξ i ω) ∧
      (∫ ω, ‖featureGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n ξ hξ ω‖ ^ 2 ∂P) =
        sequenceBenchmark k hk φ f σ n := by
  letI := predictionSingularIndex_countable (featureEmbedding μ k hk)
    (populationCovariance_feature_isCompact μ k hk)
  have hrisk := gaussianShrinkageError_risk (fun i => ResidualFilter.shrinkage φ i.1.1)
    (featureSequenceCoefficient k hk f) (σ / Real.sqrt (n : ℝ)) ξ hξ
    (featureGaussianBias_summable k hk φ hM hfilter hf)
    (summable_positive_sequence_filterDimension k hk φ hlam hM hfilter h)
  refine ⟨hrisk.1, hrisk.2.1, hrisk.2.2.trans ?_⟩
  rw [div_pow, Real.sq_sqrt (le_of_lt (Nat.cast_pos.mpr hn))]
  rfl

theorem featureGaussianSequenceError_integrable_norm_sq (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (hf : f ∈ PredictionRange (featureEmbedding μ k hk))
    (σ : ℝ) (n : ℕ) (hn : 0 < n)
    (ξ : PredictionSingularIndex (featureEmbedding μ k hk) → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) :
    Integrable (fun ω =>
      ‖featureGaussianSequenceError k hk φ hlam hM hfilter h f hf σ n ξ hξ ω‖ ^ 2) P :=
  (featureGaussianSequenceError_risk k hk φ hlam hM hfilter h f hf σ n hn ξ hξ).1.integrable_norm_pow
    (by norm_num)

/-- The infinite Gaussian risk is exactly the actual population residual bias
plus the actual filter dimension, with both series already proved finite. -/
theorem featureGaussianSequenceError_risk_eq_population (k : X → H) (hk : MemLp k 2 μ)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ)
    (hf : f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure)
    (σ : ℝ) (n : ℕ) (hn : 0 < n)
    (ξ : PredictionSingularIndex (featureEmbedding μ k hk) → Ω → ℝ)
    (hξ : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) :
    let hf' : f ∈ PredictionRange (featureEmbedding μ k hk) := by
      simpa only [predictionCovariance, closure_range_self_comp_adjoint] using hf
    (∫ ω, ‖featureGaussianSequenceError k hk φ hlam hM hfilter h f hf' σ n ξ hξ ω‖ ^ 2 ∂P) =
      ‖populationSpectralResidual k hk φ hM hfilter f‖ ^ 2 +
        σ ^ 2 / (n : ℝ) * featureFilterDimension k hk φ := by
  dsimp only
  exact (featureGaussianSequenceError_risk k hk φ hlam hM hfilter h f _ σ n hn ξ hξ).2.2.trans
    (sequenceBenchmark_eq_population k hk φ hM hfilter hf σ n)

end ActualFeatureSequence

end

end KernelSeq
