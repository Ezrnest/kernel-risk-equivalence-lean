import KernelSeq.ExpectationGoodMoments
import KernelSeq.ExpectationGoodDimension
import KernelSeq.VarianceCompatibility
import KernelSeq.EmpiricalMeasurability

/-!
# Actual variance envelope on the good covariance event

Variance comparison on the good-design event. Actual trace and
Hilbert--Schmidt comparisons are proved upstream; this module substitutes
their true `d ≤ 2 A (1+ρ) η` consequence and normalizes by the actual positive
filter dimension. Moment bounds, rather than the desired L¹ conclusion, are
the only probabilistic inputs to the final integral estimate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

private theorem variance_good_normalized_polynomial {Q N d δ K η : ℝ}
    (hQ : 0 < Q) (hd : 0 ≤ d) (hδsmall : δ ≤ 1 / 4) (hdη : d ≤ K * η) :
    ((1 + δ) * d ^ 2 + Real.sqrt Q * d + δ * (Q + N)) / Q ≤
      (5 / 4 : ℝ) * K ^ 2 * η ^ 2 / Q + K * η / Real.sqrt Q + δ + δ * N / Q := by
  have hd2 : d ^ 2 ≤ K ^ 2 * η ^ 2 := by simpa only [mul_pow] using pow_le_pow_left₀ hd hdη 2
  have hfirst : (1 + δ) * d ^ 2 ≤ (5 / 4 : ℝ) * K ^ 2 * η ^ 2 := by
    have h := mul_le_mul (by linarith : 1 + δ ≤ (5 / 4 : ℝ)) hd2
      (sq_nonneg d) (by norm_num : (0 : ℝ) ≤ 5 / 4)
    nlinarith
  have hcross := mul_le_mul_of_nonneg_left hdη (Real.sqrt_nonneg Q)
  have hnum : (1 + δ) * d ^ 2 + Real.sqrt Q * d + δ * (Q + N) ≤
      (5 / 4 : ℝ) * K ^ 2 * η ^ 2 + Real.sqrt Q * K * η + δ * Q + δ * N := by nlinarith
  refine (div_le_div_of_nonneg_right hnum hQ.le).trans_eq ?_
  have hs : Real.sqrt Q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  field_simp [hQ.ne', hs]
  nlinarith [Real.sq_sqrt hQ.le]

private theorem variance_moment_envelope_mono {C K Q H H' D D' N N' : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hQ : 0 < Q) (hH : H ≤ H') (hD : D ≤ D') (hN : N ≤ N') :
    C * ((5 / 4 : ℝ) * K ^ 2 * H / Q + K * Real.sqrt H / Real.sqrt Q +
      Real.sqrt D + Real.sqrt D * Real.sqrt N / Q) ≤
    C * ((5 / 4 : ℝ) * K ^ 2 * H' / Q + K * Real.sqrt H' / Real.sqrt Q +
      Real.sqrt D' + Real.sqrt D' * Real.sqrt N' / Q) := by
  apply mul_le_mul_of_nonneg_left _ hC
  exact add_le_add (add_le_add (add_le_add
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH (by positivity)) hQ.le)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH) hK)
      (Real.sqrt_nonneg Q))) (Real.sqrt_le_sqrt hD))
    (div_le_div_of_nonneg_right (mul_le_mul (Real.sqrt_le_sqrt hD) (Real.sqrt_le_sqrt hN)
      (Real.sqrt_nonneg N) (Real.sqrt_nonneg D')) hQ.le)

variable {X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrate the genuine four-term variance envelope. Cauchy--Schwarz
controls the correlated product, so no independence of its two factors is
assumed. The dominated scalar risk is proved integrable as part of the result. -/
theorem integral_variance_envelope_le [IsFiniteMeasure P]
    {f δ η N : Ω → ℝ} {C K Q : ℝ} (hmass : P.real Set.univ ≤ 1)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hQ : 0 < Q)
    (hf : AEStronglyMeasurable f P) (hfn : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (hδ : MemLp δ 2 P) (hη : MemLp η 2 P) (hN : MemLp N 2 P)
    (hδn : ∀ᵐ ω ∂P, 0 ≤ δ ω) (hηn : ∀ᵐ ω ∂P, 0 ≤ η ω)
    (hNn : ∀ᵐ ω ∂P, 0 ≤ N ω)
    (hbound : ∀ᵐ ω ∂P, f ω ≤ C * ((5 / 4 : ℝ) * K ^ 2 * η ω ^ 2 / Q +
      K * η ω / Real.sqrt Q + δ ω + δ ω * N ω / Q)) :
    Integrable f P ∧ (∫ ω, f ω ∂P) ≤ C *
      ((5 / 4 : ℝ) * K ^ 2 * (∫ ω, η ω ^ 2 ∂P) / Q +
        K * Real.sqrt (∫ ω, η ω ^ 2 ∂P) / Real.sqrt Q +
        Real.sqrt (∫ ω, δ ω ^ 2 ∂P) +
        Real.sqrt (∫ ω, δ ω ^ 2 ∂P) * Real.sqrt (∫ ω, N ω ^ 2 ∂P) / Q) := by
  have hi₁ := (hη.integrable_sq.const_mul ((5 / 4 : ℝ) * K ^ 2)).div_const Q
  have hi₂ := ((hη.integrable (by norm_num)).const_mul K).div_const (Real.sqrt Q)
  have hi₃ := hδ.integrable (by norm_num)
  have hi₄ : Integrable (fun ω => δ ω * N ω / Q) P :=
    (memLp_one_iff_integrable.mp (hN.mul hδ)).div_const Q
  have hg := (((hi₁.add hi₂).add hi₃).add hi₄).const_mul C
  dsimp only [Pi.add_apply] at hg
  have hfi : Integrable f P := by
    apply hg.mono' hf
    filter_upwards [hfn, hbound] with ω hn hb
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hb
  refine ⟨hfi, (integral_mono_ae hfi hg hbound).trans ?_⟩
  have he₁ := integral_add ((hi₁.add hi₂).add hi₃) hi₄
  have he₂ := integral_add (hi₁.add hi₂) hi₃
  have he₃ := integral_add hi₁ hi₂
  dsimp only [Pi.add_apply] at he₁ he₂ he₃
  rw [integral_const_mul, he₁, he₂, he₃, integral_div, integral_const_mul,
    integral_div, integral_const_mul, integral_div]
  have hmδ := integral_abs_le_sqrt_second_moment hmass hδ
  have hmη := integral_abs_le_sqrt_second_moment hmass hη
  have hmN := integral_abs_mul_le_sqrt_second_moments hδ hN
  have heδ : (∫ ω, |δ ω| ∂P) = ∫ ω, δ ω ∂P := integral_congr_ae (hδn.mono fun _ h => abs_of_nonneg h)
  have heη : (∫ ω, |η ω| ∂P) = ∫ ω, η ω ∂P := integral_congr_ae (hηn.mono fun _ h => abs_of_nonneg h)
  have heN : (∫ ω, |δ ω| * |N ω| ∂P) = ∫ ω, δ ω * N ω ∂P := by
    apply integral_congr_ae
    filter_upwards [hδn, hNn] with ω hd hn
    rw [abs_of_nonneg hd, abs_of_nonneg hn]
  rw [heδ] at hmδ
  rw [heη] at hmη
  rw [heN] at hmN
  apply mul_le_mul_of_nonneg_left _ hC
  exact add_le_add (add_le_add (add_le_add le_rfl
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmη hK) (Real.sqrt_nonneg Q))) hmδ)
    (div_le_div_of_nonneg_right hmN hQ.le)

/-- The manuscript's actual good-event pointwise variance envelope, with
explicit constants and no trace, HS, or square-root comparison hypotheses. -/
theorem actual_good_variance_normalized_bound
    [TopologicalSpace.SeparableSpace H]
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hQ : 0 < featureFilterDimension k hk φ)
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4) :
    |actualVarianceEnergy k hk φ hlam x hMX h - featureFilterDimension k hk φ| /
        featureFilterDimension k hk φ ≤ (4 * (1 + A ^ 2)) *
      ((5 / 4 : ℝ) * (2 * A * (1 + ρ)) ^ 2 *
          ‖normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) k hk lam x‖ ^ 2 /
            featureFilterDimension k hk φ +
        (2 * A * (1 + ρ)) *
          ‖normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) k hk lam x‖ /
            Real.sqrt (featureFilterDimension k hk φ) +
        actualCovarianceDeviation k hk lam x +
        actualCovarianceDeviation k hk lam x * empiricalEffectiveDimension (fun i => k (x i)) lam /
          featureFilterDimension k hk φ) := by
  have hb := div_le_div_of_nonneg_right
    (actual_variance_comparison_polynomial k hk φ hlam hM x hMX hf h hδ) hQ.le
  rw [mul_div_assoc] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (variance_good_normalized_polynomial hQ (norm_nonneg _) hδ
      (actualShrinkageDifferenceColumns_norm_le_eta k hk φ hlam hM x hMX hf h hδ))
    (by positivity))

omit [IsProbabilityMeasure μ] in
/-- Measurability of the actual variance energy is derived from the finite
filtered prediction columns, even if the inverse filter jumps at zero. -/
theorem stronglyMeasurable_actualVarianceEnergy {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (k : X → H) (hk : MemLp k 2 μ)
    (hz : ∀ i, StronglyMeasurable (fun ω => k (x i ω)))
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hMX : ∀ ω, ‖empiricalCovariance (fun i => k (x i ω))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    StronglyMeasurable (fun ω => actualVarianceEnergy k hk φ hlam (fun i => x i ω) (hMX ω) h) := by
  let T := fun ω => empiricalCovariance (fun i => k (x i ω))
  have hT : StronglyMeasurable T := stronglyMeasurable_empiricalCovariance _ hz
  have hcol (i : Fin n) : StronglyMeasurable (fun ω => featureEmbedding μ k hk
      (compactFilterOperator (T ω) (empiricalCovariance_isCompact _)
        (empiricalCovariance_isPositive _) φ hlam (hMX ω) h (k (x i ω)))) := by
    apply (featureEmbedding μ k hk).continuous.comp_stronglyMeasurable
    apply stronglyMeasurable_compactFilterOperator_apply T hT
      (fun _ => empiricalCovariance_isCompact _) (fun _ => empiricalCovariance_isPositive _)
      hlam hMX φ hf h _ (hz i)
    intro ω z hz0
    exact (real_inner_comm (k (x i ω)) z).trans
      (sample_inner_eq_zero_of_empiricalCovariance_eq_zero hn (fun j => k (x j ω)) hz0 i)
  have heq : (fun ω => actualVarianceEnergy k hk φ hlam (fun i => x i ω) (hMX ω) h) =
      (n : ℝ)⁻¹ • ∑ i, fun ω => ‖featureEmbedding μ k hk
        (compactFilterOperator (T ω) (empiricalCovariance_isCompact _)
          (empiricalCovariance_isPositive _) φ hlam (hMX ω) h (k (x i ω)))‖ ^ 2 := by
    funext ω
    simp only [actualVarianceEnergy_eq_prediction_column_energy, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul, T]
  rw [heq]
  exact (Finset.stronglyMeasurable_sum Finset.univ (fun i _ => (hcol i).norm.pow 2)).const_smul _

/-- The actual good-event variance comparison is integrable and satisfies
the true L²-moment envelope. The only covariance moment hypothesis is L²
existence of the real deviation; no variance-transfer conclusion, HS
comparison, empirical-dimension rate, or independence of those quantities
is an input. Every expectation in the bound is an actual restricted integral. -/
theorem setIntegral_actual_variance_relative_le [IsProbabilityMeasure P]
    [TopologicalSpace.SeparableSpace H] {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hMX : ∀ ω, ‖empiricalCovariance (fun i => k (x i ω))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hQ : 0 < featureFilterDimension k hk φ) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (G : Set Ω) (hG : MeasurableSet G)
    (hgood : ∀ ω ∈ G, actualCovarianceDeviation k hk lam (fun i => x i ω) ≤ 1 / 4)
    (hd : MemLp (fun ω => actualCovarianceDeviation k hk lam (fun i => x i ω)) 2 P) :
    let Q := featureFilterDimension k hk φ
    let K := 2 * A * (1 + ρ)
    let δ := fun ω => actualCovarianceDeviation k hk lam (fun i => x i ω)
    let η := fun ω => ‖normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) k hk lam (fun i => x i ω)‖
    let N := fun ω => empiricalEffectiveDimension (fun i => k (x i ω)) lam
    let f := fun ω => |actualVarianceEnergy k hk φ hlam (fun i => x i ω) (hMX ω) h - Q| / Q
    IntegrableOn f G P ∧ (∫ ω in G, f ω ∂P) ≤ (4 * (1 + A ^ 2)) *
      ((5 / 4 : ℝ) * K ^ 2 * (∫ ω in G, η ω ^ 2 ∂P) / Q +
        K * Real.sqrt (∫ ω in G, η ω ^ 2 ∂P) / Real.sqrt Q +
        Real.sqrt (∫ ω in G, δ ω ^ 2 ∂P) +
        Real.sqrt (∫ ω in G, δ ω ^ 2 ∂P) * Real.sqrt (∫ ω in G, N ω ^ 2 ∂P) / Q) := by
  dsimp only
  let Q := featureFilterDimension k hk φ
  let K := 2 * A * (1 + ρ)
  let a := fun ω => actualVarianceEnergy k hk φ hlam (fun i => x i ω) (hMX ω) h
  let δ := fun ω => actualCovarianceDeviation k hk lam (fun i => x i ω)
  let η := fun ω => ‖normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) k hk lam (fun i => x i ω)‖
  let N := fun ω => empiricalEffectiveDimension (fun i => k (x i ω)) lam
  have hA := h.constant_nonneg hlam ((norm_nonneg _).trans hM)
  have hK : 0 ≤ K := by dsimp only [K]; positivity [h.rho_pos]
  have hmass : (P.restrict G).real Set.univ ≤ 1 := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using
      (measureReal_le_one (μ := P) (s := G))
  have hη : MemLp η 2 (P.restrict G) :=
    (memLp_normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) hn x hlaw k hk lam hL).norm.restrict G
  have hN : MemLp N 2 (P.restrict G) :=
    memLp_empiricalEffectiveDimension_on_good x hlaw k hk hks lam hlam hL G hG hgood
  have ha : StronglyMeasurable a := stronglyMeasurable_actualVarianceEnergy hn x k hk
    (fun i => hks.comp_measurable (hlaw i).measurable) φ hlam hMX hf h
  have hm : AEStronglyMeasurable (fun ω => |a ω - Q| / Q) (P.restrict G) := by
    have hfun : (fun ω => |a ω - Q| / Q) = Q⁻¹ • (fun ω => ‖a ω - Q‖) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, div_eq_mul_inv, mul_comm]
    rw [hfun]
    exact ((ha.sub stronglyMeasurable_const).norm.const_smul Q⁻¹).aestronglyMeasurable
  have hN0 (ω : Ω) : 0 ≤ N ω := by
    apply tsum_nonneg
    intro i
    have ht := compactEigenvalue_nonneg _ (empiricalCovariance_isCompact (fun i => k (x i ω)))
      (empiricalCovariance_isPositive _) i
    exact div_nonneg ht (add_nonneg ht hlam.le)
  apply integral_variance_envelope_le hmass (by positivity) hK hQ hm
    (Filter.Eventually.of_forall fun _ => div_nonneg (abs_nonneg _) hQ.le)
    (hd.restrict G) hη hN
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) (Filter.Eventually.of_forall hN0)
  filter_upwards [ae_restrict_mem hG] with ω hω
  exact actual_good_variance_normalized_bound k hk φ hlam hM (fun i => x i ω) (hMX ω)
    hf h hQ (hgood ω hω)

/-- The actual iid good-event variance envelope after substituting the
proved HS second moment and actual empirical-dimension second moment.
Only the genuine operator-deviation second moment remains on the right.
There is no desired variance convergence or empirical-dimension moment
certificate in the hypotheses. -/
theorem setIntegral_actual_variance_relative_le_covariance_moment [IsProbabilityMeasure P]
    [TopologicalSpace.SeparableSpace H] {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hind : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hMX : ∀ ω, ‖empiricalCovariance (fun i => k (x i ω))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hQ : 0 < featureFilterDimension k hk φ) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (G : Set Ω) (hG : MeasurableSet G)
    (hgood : ∀ ω ∈ G, actualCovarianceDeviation k hk lam (fun i => x i ω) ≤ 1 / 4)
    (hd : MemLp (fun ω => actualCovarianceDeviation k hk lam (fun i => x i ω)) 2 P) :
    let Q := featureFilterDimension k hk φ
    let K := 2 * A * (1 + ρ)
    let N₁ := featureEffectiveDimension k hk lam
    let H₂ := L / (n : ℝ) * N₁
    let D₂ := ∫ ω, actualCovarianceDeviation k hk lam (fun i => x i ω) ^ 2 ∂P
    let f := fun ω => |actualVarianceEnergy k hk φ hlam (fun i => x i ω) (hMX ω) h - Q| / Q
    IntegrableOn f G P ∧ (∫ ω in G, f ω ∂P) ≤ (4 * (1 + A ^ 2)) *
      ((5 / 4 : ℝ) * K ^ 2 * H₂ / Q + K * Real.sqrt H₂ / Real.sqrt Q +
        Real.sqrt D₂ + Real.sqrt D₂ * Real.sqrt (4 * (N₁ ^ 2 + H₂)) / Q) := by
  dsimp only
  have hb := setIntegral_actual_variance_relative_le hn x hlaw k hk hks φ hlam hM hMX hf h hQ hL G hG hgood hd
  dsimp only at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  let η := fun ω => ‖normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) k hk lam (fun i => x i ω)‖
  have hη : MemLp η 2 P :=
    (memLp_normalizedHSCovarianceFluctuation (featureCovarianceBasis k hk) hn x hlaw k hk lam hL).norm
  have hηbound : (∫ ω in G, η ω ^ 2 ∂P) ≤ L / (n : ℝ) * featureEffectiveDimension k hk lam := by
    exact (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) hη.integrable_sq).trans
      (integral_normalizedHSCovarianceFluctuation_sq_le (featureCovarianceBasis k hk)
        hn x hlaw hind k hk lam hlam hL)
  have hdbound : (∫ ω in G, actualCovarianceDeviation k hk lam (fun i => x i ω) ^ 2 ∂P) ≤
      ∫ ω, actualCovarianceDeviation k hk lam (fun i => x i ω) ^ 2 ∂P :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) hd.integrable_sq
  have hNbound := setIntegral_empiricalEffectiveDimension_sq_le hn x hlaw hind k hk hks lam hlam hL G hG hgood
  have hA := h.constant_nonneg hlam ((norm_nonneg _).trans hM)
  have hK : 0 ≤ 2 * A * (1 + ρ) := by positivity [h.rho_pos]
  exact variance_moment_envelope_mono (by positivity) hK hQ hηbound hdbound hNbound


end
end KernelSeq
