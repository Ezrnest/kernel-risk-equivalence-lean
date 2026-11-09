import KernelSeq.OriginalBiasAsymptotics
import KernelSeq.RKHSVarianceEnergy
import KernelSeq.RiskAssembly

/-!
# Actual risk assembly at the original manuscript scales

The bias, variance, sequence benchmark, and conditional-risk identities refer to
actual feature/RKHS operators. The complete localized interaction core remains
an explicit intermediate premise, together with the named finite Bernstein leaf.
No stochastic rate, positive bias lower bound, or variance-retention lower bound
is an input to the assembled conclusion.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace KernelSeq

noncomputable section

/-- Convergence of an actual ratio implies convergence of its absolute error. -/
theorem ratio_tendstoInMeasure_absolute_error {J Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {l : Filter J} {r : J → Ω → ℝ}
    (hr : TendstoInMeasure P r l (fun _ => 1)) :
    TendstoInMeasure P (fun i ω => |r i ω - 1|) l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hr ⊢
  intro ε hε
  simpa only [sub_zero, Real.norm_eq_abs, abs_abs] using hr ε hε

/-- Algebra for the usual normalized total-risk absolute error. -/
theorem normalized_risk_error_eq_ratio_error (R D : ℝ) (hD : 0 < D) :
    |R - D| / D = |R / D - 1| := by
  calc
    |R - D| / D = |R - D| / |D| := by rw [abs_of_pos hD]
    _ = |R / D - 1| := by rw [← abs_div, sub_div, div_self hD.ne']

section Feature

variable {I J X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P] {l : Filter J} [NeBot l]

/-- The actual feature-model total risk divided by the exact sequence benchmark.
The original localization core is displayed in full as the sole pending pointwise
operator estimate; its vanishing probability rates are derived, not postulated. -/
theorem actual_risk_ratio_from_original_scales (b : HilbertBasis I ℝ H)
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
      (actualEmpiricalBiasEnergy k hk (φ i) (hlam i) (fun j => x i j ω) (hMX i ω) (h i) (f i) +
        σ ^ 2 / (n i : ℝ) * actualVarianceEnergy k hk (φ i) (hlam i)
          (fun j => x i j ω) (hMX i ω) (h i)) /
      sequenceBenchmark k hk (φ i) (f i) σ (n i)) l (fun _ => 1) := by
  have hb := actual_bias_transfer_from_original_scales b n hn x hlaw hind k hk lam hlam
    hα hαρ hM hMX φ hf h f hsupport σ C hσ L hL hQ hcompat hsource hTropp hlocalized
  have hv := actual_variance_relative_of_compatibility n hn x hlaw hind k hk lam hlam
    hM hMX φ hf h L hL hQ hcompat hTropp
  have hv' : TendstoInMeasure P (fun i ω =>
      |σ ^ 2 / (n i : ℝ) * actualVarianceEnergy k hk (φ i) (hlam i)
          (fun j => x i j ω) (hMX i ω) (h i) -
        σ ^ 2 / (n i : ℝ) * featureFilterDimension k hk (φ i)| /
      (σ ^ 2 / (n i : ℝ) * featureFilterDimension k hk (φ i))) l (fun _ => 0) := by
    apply TendstoInMeasure.congr_left (fun i => Eventually.of_forall fun ω => ?_) hv
    exact (positive_scaled_variance_relative_error _ _ (σ ^ 2 / (n i : ℝ))
      (div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr (hn i)))).symm
  have hr := risk_ratio_tendstoInMeasure_one P
    (fun i ω => actualEmpiricalBiasEnergy k hk (φ i) (hlam i)
      (fun j => x i j ω) (hMX i ω) (h i) (f i))
    (fun i ω => σ ^ 2 / (n i : ℝ) * actualVarianceEnergy k hk (φ i) (hlam i)
      (fun j => x i j ω) (hMX i ω) (h i))
    (fun i => ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ ^ 2)
    (fun i => σ ^ 2 / (n i : ℝ) * featureFilterDimension k hk (φ i))
    (Eventually.of_forall fun _ => sq_nonneg _)
    (by
      filter_upwards [hQ] with i hi
      exact mul_pos (div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr (hn i))) hi) hb hv'
  apply TendstoInMeasure.congr_left (fun i => Eventually.of_forall fun ω => ?_) hr
  rw [sequenceBenchmark_eq_population k hk (φ i) hM (hf i) (hsupport i)]


end Feature

/-- The usual normalized absolute error needs only an eventually positive benchmark. -/
theorem normalized_risk_error_tendstoInMeasure_of_ratio
    {J Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {l : Filter J}
    (R : J → Ω → ℝ) (D : J → ℝ) (hD : ∀ᶠ i in l, 0 < D i)
    (hr : TendstoInMeasure P (fun i ω => R i ω / D i) l (fun _ => 1)) :
    TendstoInMeasure P (fun i ω => |R i ω - D i| / D i) l (fun _ => 0) := by
  apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl (ratio_tendstoInMeasure_absolute_error hr)
  filter_upwards [hD] with i hi
  exact Eventually.of_forall fun ω => (normalized_risk_error_eq_ratio_error (R i ω) (D i) hi).symm

section RKHS

variable {I J X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P] {l : Filter J} [NeBot l]

/-- The original kernel-diagonal bound supplies the actual population spectral bound. -/
theorem rkhs_population_covariance_bound
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2) :
    ‖populationCovariance (featureEmbedding μ (rkhsFeature (X := X) (H := H))
      (rkhsFeature_memLp μ hK κ hκ hdiag))‖ ≤ κ ^ 2 := by
  apply populationCovariance_norm_le_feature_bound
  exact Eventually.of_forall fun y => by simpa only [rkhsFeature_norm_sq] using hdiag y

omit [MeasurableSpace X] [SecondCountableTopology H]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [NeBot l] in
/-- Every actual empirical covariance has the same bound, derived directly from the kernel. -/
theorem rkhs_empirical_covariance_bound
    (κ : ℝ) (_hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (x : Fin n → X) :
    ‖empiricalCovariance (fun j => rkhsFeature (X := X) (H := H) (x j))‖ ≤ κ ^ 2 :=
  norm_empiricalCovariance_le_bound hn _ κ (fun j => by
    simpa only [rkhsFeature_norm_sq] using hdiag (x j))

/-- The actual conditional expectation of prediction loss, given all observed designs. -/
def rkhsConditionalPredictionRisk
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → X × ℝ) (f : Lp ℝ 2 μ)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) : Ω → ℝ :=
  P[(fun ω => ‖rkhsEmpiricalPrediction hK κ hκ hdiag hn (fun j => (Z j ω).1)
    (fun j => (Z j ω).2) φ hlam h - f‖ ^ 2) | ⨆ j, observationDesignSigma (Z j)]

/-- Actual canonical RKHS conditional risk versus the exact population sequence benchmark,
under the original two scales. The pending localized operator core and finite Bernstein leaf
are explicitly displayed, while the actual conditional-expectation formula is derived from
individual observation moments. The ambient prediction `L²` space need not be separable. -/
theorem rkhs_conditional_risk_from_original_scales (b : HilbertBasis I ℝ H)
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (Z : (i : J) → Fin (n i) → Ω → X × ℝ)
    (hZ : ∀ i j, Measurable (Z i j))
    (hlaw : ∀ i j, MeasurePreserving (fun ω => (Z i j ω).1) P μ)
    (hind : ∀ i, iIndepFun (Z i) P) (f : J → Lp ℝ 2 μ) (σ : ℝ) (hσ : 0 < σ)
    (hmean : ∀ i j, P[observationNoise (Z i j) (lpRepresentative (f i)) |
      observationDesignSigma (Z i j)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i j, P[(fun ω => observationNoise (Z i j) (lpRepresentative (f i)) ω ^ 2) |
      observationDesignSigma (Z i j)] =ᵐ[P] (fun _ => σ ^ 2))
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i) {ρ A α : ℝ}
    (hα : 0 ≤ α) (hαρ : α / 2 ≤ ρ) (φ : J → ℝ → ℝ)
    (hf : ∀ i, ResidualFilter.SpectralFilter (κ ^ 2) (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) (κ ^ 2) ρ A (φ i)) (L : J → ℝ) (C : ℝ) :
    let k := rkhsFeature (X := X) (H := H)
    let hk := rkhsFeature_memLp μ hK κ hκ hdiag
    let hM := rkhs_population_covariance_bound (μ := μ) hK κ hκ hdiag
    let x := fun i j ω => (Z i j ω).1
    let hMX := fun i ω => rkhs_empirical_covariance_bound κ hκ hdiag (hn i) (fun j => x i j ω)
    let Q := fun i => featureFilterDimension k hk (φ i)
    (∀ i, f i ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure) →
    (∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i) →
    (∀ᶠ i in l, 0 < Q i) →
    Tendsto (fun i => featureEffectiveDimension k hk (lam i) / Q i * Real.sqrt
      (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0) →
    Tendsto (fun i => (n i : ℝ) * featureSequenceSourceEnergy k hk (lam i) α (f i) *
      originalBiasGamma (L i) (n i : ℝ) (featureEffectiveDimension k hk (lam i)) ^ 2 / Q i) l (𝓝 0) →
    (∀ i, FiniteSpectralBernstein (featureCovarianceBasis (bernsteinFeature k hk (lam i))
      (bernsteinFeature_memLp k hk (lam i))) P) →
    (∀ᶠ i in l, ∀ (ω : Ω) (τ : ℝ), τ ∈ Set.Ioc (0 : ℝ) (originalBiasCutoffCap A) →
      actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) ≤ 1 / 4 →
      ‖actualInteractionPrediction k hk (φ i) (hlam i) hM (fun j => x i j ω)
        (hMX i ω) (hf i) (h i) (f i)‖ ≤
        C * (τ + actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) / τ) *
          ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ +
        (C * hsSchattenEndpoint b (manuscriptMixedColumns b k hk (lam i) (fun j => x i j ω)) / τ) *
          ‖actualBiasWeight k hk (φ i) (hlam i) hα hM (hf i) (f i)‖) →
    TendstoInMeasure P (fun i ω =>
      rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) (f i) (φ i) (hlam i) (h i) ω /
        sequenceBenchmark k hk (φ i) (f i) σ (n i)) l (fun _ => 1) ∧
    TendstoInMeasure P (fun i ω =>
      |rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) (f i) (φ i) (hlam i) (h i) ω -
        sequenceBenchmark k hk (φ i) (f i) σ (n i)| /
          sequenceBenchmark k hk (φ i) (f i) σ (n i)) l (fun _ => 0) := by
  dsimp only
  intro hsupport hL hQ hcompat hsource hTropp hlocalized
  let k := rkhsFeature (X := X) (H := H)
  let hk := rkhsFeature_memLp μ hK κ hκ hdiag
  let hM := rkhs_population_covariance_bound (μ := μ) hK κ hκ hdiag
  let x := fun i j ω => (Z i j ω).1
  let hMX := fun i ω => rkhs_empirical_covariance_bound κ hκ hdiag (hn i) (fun j => x i j ω)
  have hxind : ∀ i, iIndepFun (x i) P := by
    intro i
    exact (hind i).comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  have hr := actual_risk_ratio_from_original_scales b n hn x hlaw hxind k hk lam hlam
    hα hαρ hM hMX φ hf h f hsupport σ C hσ L hL hQ hcompat hsource hTropp hlocalized
  have hce (i : J) := (rkhs_conditional_prediction_risk_energy hK κ hκ hdiag (hn i)
    (Z i) (hZ i) (hlaw i) (f i) σ hσ (hind i) (hmean i) (hsecond i)
    (φ i) (hlam i) (hf i) (h i)).2
  have hratio : TendstoInMeasure P (fun i ω =>
      rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) (f i) (φ i) (hlam i) (h i) ω /
        sequenceBenchmark k hk (φ i) (f i) σ (n i)) l (fun _ => 1) := by
    apply TendstoInMeasure.congr_left (fun i => ?_) hr
    filter_upwards [hce i] with ω hi
    unfold rkhsConditionalPredictionRisk
    rw [hi]
    rfl
  refine ⟨hratio, normalized_risk_error_tendstoInMeasure_of_ratio _ _ ?_ hratio⟩
  filter_upwards [hQ] with i hi
  rw [sequenceBenchmark_eq_population k hk (φ i) hM (hf i) (hsupport i)]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _)
    (mul_pos (div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr (hn i))) hi)

end RKHS
end
end KernelSeq
