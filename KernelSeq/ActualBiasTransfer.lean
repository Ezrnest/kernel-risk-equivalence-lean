import KernelSeq.SpectralInteraction
import KernelSeq.ProbabilisticBias
import KernelSeq.FilteredRHSBound

/-!
# Actual common bias transfer from an interaction bound

The empirical mean prediction, population spectral solution, residual, and
interaction are actual operators. This module formalizes the common bias
transfer proposition with the interaction inequality and its probability
rates as explicit inputs; it does not assert the localized interaction theorem.
The prediction space is the full `L²(μ)`, with no separability hypothesis on it.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace KernelSeq

noncomputable section

variable {ι X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ]

local instance actualBiasMeasurableSpace : MeasurableSpace H := borel H
local instance actualBiasBorelSpace : BorelSpace H := ⟨rfl⟩

/-- The actual conditional-mean spectral prediction from the noiseless response
values of the selected `L²` target representative. -/
noncomputable def actualMeanPrediction (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  featureEmbedding μ k hk (compactFilterOperator (empiricalCovariance (fun i => k (x i)))
    (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX h
    (empiricalRepresenter (fun i => k (x i)) (fun i => f (x i))))

noncomputable def actualEmpiricalBiasEnergy (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) (f : Lp ℝ 2 μ) : ℝ :=
  ‖actualMeanPrediction k hk φ hlam x hMX h f - f‖ ^ 2

/-- The actual mean prediction minus population prediction. -/
noncomputable def actualBiasError (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  actualMeanPrediction k hk φ hlam x hMX h f -
    featureEmbedding μ k hk (populationSpectralSolution k hk φ hlam hM h f)

/-- The actual source weight `a_{λ,α}(L) f`. Its target-norm control is not
assumed here; the common proposition uses this actual norm explicitly. -/
noncomputable def actualBiasWeight (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  compactResidualWeightOperator (predictionCovariance (featureEmbedding μ k hk))
    (predictionCovariance_feature_isCompact μ k hk) (predictionCovariance_isPositive _) φ
    hlam hα ((predictionCovariance_norm_eq_population _).trans_le hM) hf f

/-- The actual operator error decomposition after prediction embedding. -/
theorem actualBiasError_decomposition (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) :
    actualBiasError k hk φ hlam hM x hMX h f =
      featureEmbedding μ k hk (compactFilterOperator (empiricalCovariance (fun i => k (x i)))
        (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX h
        (rhsFluctuation k hk f (populationSpectralSolution k hk φ hlam hM h f) x)) +
      featureEmbedding μ k hk (compactInteraction (empiricalCovariance (fun i => k (x i)))
        (populationCovariance (featureEmbedding μ k hk)) (empiricalCovariance_isCompact _)
        (populationCovariance_feature_isCompact μ k hk) (empiricalCovariance_isPositive _)
        (populationCovariance_isPositive _) φ hlam hMX hM hf h ((featureEmbedding μ k hk).adjoint f)) := by
  unfold actualBiasError actualMeanPrediction
  rw [← map_sub, spectral_estimator_error_decomposition k hk φ hlam hM x hMX hf h f, map_add]

/-- The bias-risk identity holds in the actual `L²` space, including a zero
population residual. No support or injectivity premise is needed for this algebra. -/
theorem actual_bias_energy_eq (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) :
    ‖populationSpectralResidual k hk φ hM hf f - actualBiasError k hk φ hlam hM x hMX h f‖ ^ 2 =
      actualEmpiricalBiasEnergy k hk φ hlam x hMX h f := by
  rw [← populationSpectralSolution_residual k hk φ hlam hM hf h f]
  unfold actualBiasError actualEmpiricalBiasEnergy
  have heq : f - featureEmbedding μ k hk (populationSpectralSolution k hk φ hlam hM h f) -
      (actualMeanPrediction k hk φ hlam x hMX h f -
        featureEmbedding μ k hk (populationSpectralSolution k hk φ hlam hM h f)) =
      f - actualMeanPrediction k hk φ hlam x hMX h f := by abel
  rw [heq, norm_sub_rev]

/-- A zero actual spectral residual forces the actual unnormalized sampled RHS
to be zero a.s.; inverse-zero conventions cannot conceal an error term. -/
theorem actual_spectral_rhs_zero_ae_of_residual_zero
    {n : ℕ} (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (hr : populationSpectralResidual k hk φ hM hf f = 0) :
    (fun ω => rhsFluctuation k hk f (populationSpectralSolution k hk φ hlam hM h f) (fun i => x i ω)) =ᵐ[P] 0 := by
  apply rhsFluctuation_eq_zero_ae_of_residual_zero x hlaw k hk f _
  rw [populationSpectralSolution_residual k hk φ hlam hM hf h f, hr]

/-- The actual RHS-to-residual amplitude used in the source proof. -/
noncomputable def actualBiasRHSAmplitude (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) {n : ℕ} (x : Fin n → X) : ℝ :=
  (2 * A) * ‖‖populationSpectralResidual k hk φ hM hf f‖⁻¹ •
    normalizedRHS k hk lam f (populationSpectralSolution k hk φ hlam hM h f) x‖

variable [IsProbabilityMeasure P]

/-- The actual RHS amplitude converges to zero, proved from the real normalized
RHS theorem rather than supplied as an error-coefficient conclusion. -/
theorem actualBiasRHSAmplitude_tendstoInMeasure {l : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (hind : ∀ i, Pairwise (fun j k => IndepFun (x i j) (x i k) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A : ℝ} (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ι → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i)) (f : ι → Lp ℝ 2 μ)
    (L : ι → ℝ) (hLnonneg : ∀ i, 0 ≤ L i)
    (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hrate : Tendsto (fun i => L i / (n i : ℝ)) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω => actualBiasRHSAmplitude k hk (φ i) (hlam i) hM (hf i) (h i)
      (f i) (fun j => x i j ω)) l (fun _ => 0) := by
  have hz := spectral_normalizedRHS_div_residual_tendstoInMeasure n hn x hlaw hind k hk lam hlam
    hM φ hf h f L hLnonneg hL hrate
  have hnorm := tendstoInMeasure_continuousAt_const hz (fun z : H => ‖z‖) continuous_norm.continuousAt
  have hzero : TendstoInMeasure P (fun i ω =>
      ‖‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖⁻¹ •
        normalizedRHS k hk (lam i) (f i) (populationSpectralSolution k hk (φ i) (hlam i) hM (h i) (f i))
          (fun j => x i j ω)‖) l (fun _ => 0) := by simpa only [norm_zero] using hnorm
  exact tendstoInMeasure_const_mul_zero hzero (2 * A)

/-- The actual interaction prediction `S G S* f` appearing in the common
proposition. Its localized norm estimate remains an explicit input below. -/
noncomputable def actualInteractionPrediction (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  featureEmbedding μ k hk (compactInteraction (empiricalCovariance (fun i => k (x i)))
    (populationCovariance (featureEmbedding μ k hk)) (empiricalCovariance_isCompact _)
    (populationCovariance_feature_isCompact μ k hk) (empiricalCovariance_isPositive _)
    (populationCovariance_isPositive _) φ hlam hMX hM hf h ((featureEmbedding μ k hk).adjoint f))

theorem actualBiasRHSAmplitude_nonneg (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) {n : ℕ} (x : Fin n → X) :
    0 ≤ actualBiasRHSAmplitude k hk φ hlam hM hf h f x :=
  mul_nonneg (mul_nonneg (by norm_num)
    (h.constant_nonneg hlam ((norm_nonneg _).trans hM))) (norm_nonneg _)

/-- The actual filtered RHS is bounded by the actual small RHS amplitude times
the residual norm. The explicit zero-RHS premise here is proved a.s. from the
sample law in the final theorem, including zero population residuals. -/
theorem actual_filtered_rhs_le_amplitude (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4)
    (hzero : ‖populationSpectralResidual k hk φ hM hf f‖ = 0 →
      rhsFluctuation k hk f (populationSpectralSolution k hk φ hlam hM h f) x = 0) :
    ‖featureEmbedding μ k hk (compactFilterOperator (empiricalCovariance (fun i => k (x i)))
      (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX h
      (rhsFluctuation k hk f (populationSpectralSolution k hk φ hlam hM h f) x))‖ ≤
      actualBiasRHSAmplitude k hk φ hlam hM hf h f x * ‖populationSpectralResidual k hk φ hM hf f‖ := by
  by_cases hr : ‖populationSpectralResidual k hk φ hM hf f‖ = 0
  · rw [hzero hr, map_zero, map_zero, norm_zero, hr, mul_zero]
  · refine (actual_filtered_rhsFluctuation_bound k hk φ hlam x hMX h hδ f
      (populationSpectralSolution k hk φ hlam hM h f)).trans_eq ?_
    unfold actualBiasRHSAmplitude
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    field_simp [hr]

/-- The actual vector-error estimate is derived from the proved decomposition,
filtered RHS estimate, and the original interaction bound. Absolute coefficients
avoid imposing irrelevant positivity outside the covariance good event. -/
theorem actualBiasError_norm_le_of_interaction (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A α : ℝ} (hlam : 0 < lam) (hα : 0 ≤ α)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (f : Lp ℝ 2 μ) (ε β : ℝ) (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4)
    (hzero : ‖populationSpectralResidual k hk φ hM hf f‖ = 0 →
      rhsFluctuation k hk f (populationSpectralSolution k hk φ hlam hM h f) x = 0)
    (hinter : ‖actualInteractionPrediction k hk φ hlam hM x hMX hf h f‖ ≤
      ε * ‖populationSpectralResidual k hk φ hM hf f‖ + β * ‖actualBiasWeight k hk φ hlam hα hM hf f‖) :
    ‖actualBiasError k hk φ hlam hM x hMX h f‖ ≤
      (actualBiasRHSAmplitude k hk φ hlam hM hf h f x + |ε|) *
        ‖populationSpectralResidual k hk φ hM hf f‖ + |β| * ‖actualBiasWeight k hk φ hlam hα hM hf f‖ := by
  rw [actualBiasError_decomposition k hk φ hlam hM x hMX hf h f]
  have hrhs := actual_filtered_rhs_le_amplitude k hk φ hlam hM x hMX hf h f hδ hzero
  have htri := (norm_add_le _ _).trans (add_le_add hrhs hinter)
  have he := mul_le_mul_of_nonneg_right (le_abs_self ε)
    (norm_nonneg (populationSpectralResidual k hk φ hM hf f))
  have hb := mul_le_mul_of_nonneg_right (le_abs_self β) (norm_nonneg (actualBiasWeight k hk φ hlam hα hM hf f))
  dsimp only [actualInteractionPrediction] at htri
  linarith

/-- The actual common bias-transfer proposition. The only operator estimate
left explicit is the original interaction inequality. The RHS amplitude, its
probability limit, the vector error bound, and the zero-residual branch are
proved from the actual sampled model. The deterministic variance scale may
vanish asymptotically but is eventually positive.

The exponent range is slightly broader than the manuscript's `0 < α ≤ 1`:
this transfer step itself uses only `0 ≤ α`. Target functions may vary with
the index, and neither their norms nor their residual norms are bounded below.
-/
theorem actual_bias_transfer_of_interaction {l : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (hind : ∀ i, Pairwise (fun j k => IndepFun (x i j) (x i k) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A α : ℝ} (hα : 0 ≤ α)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hMX : ∀ i ω, ‖empiricalCovariance (fun j => k (x i j ω))‖ ≤ M)
    (φ : ι → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i)) (f : ι → Lp ℝ 2 μ)
    (L V : ι → ℝ)
    (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hrate : Tendsto (fun i => L i / (n i : ℝ)) l (𝓝 0))
    (hV : ∀ᶠ i in l, 0 < V i) (ε β : ι → Ω → ℝ)
    (hδ : TendstoInMeasure P (fun i ω => actualCovarianceDeviation k hk (lam i)
      (fun j => x i j ω)) l (fun _ => 0))
    (hε : TendstoInMeasure P ε l (fun _ => 0))
    (hβ : TendstoInMeasure P (fun i ω => β i ω ^ 2 *
      ‖actualBiasWeight k hk (φ i) (hlam i) hα hM (hf i) (f i)‖ ^ 2 / V i)
      l (fun _ => 0))
    (hinter : ∀ᶠ i in l, ∀ ω,
      actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) ≤ 1 / 4 →
      ‖actualInteractionPrediction k hk (φ i) (hlam i) hM (fun j => x i j ω)
        (hMX i ω) (hf i) (h i) (f i)‖ ≤
      ε i ω * ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ +
      β i ω * ‖actualBiasWeight k hk (φ i) (hlam i) hα hM (hf i) (f i)‖) :
    TendstoInMeasure P (fun i ω =>
      |actualEmpiricalBiasEnergy k hk (φ i) (hlam i) (fun j => x i j ω) (hMX i ω) (h i) (f i) -
        ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ ^ 2| /
      (‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ ^ 2 + V i)) l (fun _ => 0) := by
  let r := fun i => populationSpectralResidual k hk (φ i) hM (hf i) (f i)
  let Z := fun i ω => rhsFluctuation k hk (f i)
    (populationSpectralSolution k hk (φ i) (hlam i) hM (h i) (f i)) (fun j => x i j ω)
  let δ := fun i ω => actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)
  let b := fun i ω => actualBiasRHSAmplitude k hk (φ i) (hlam i) hM (hf i) (h i) (f i)
    (fun j => x i j ω)
  let u := fun i ω => b i ω + |ε i ω|
  let c := fun i ω => |β i ω| * ‖actualBiasWeight k hk (φ i) (hlam i) hα hM (hf i) (f i)‖
  let e := fun i ω => actualBiasError k hk (φ i) (hlam i) hM (fun j => x i j ω)
    (hMX i ω) (h i) (f i)
  let G := fun i => {ω | δ i ω ≤ 1 / 4 ∧ (‖r i‖ = 0 → Z i ω = 0)}
  have hzero : ∀ i, ∀ᵐ ω ∂P, ‖r i‖ = 0 → Z i ω = 0 := by
    intro i
    by_cases hr : ‖r i‖ = 0
    · have hz := actual_spectral_rhs_zero_ae_of_residual_zero (x i) (hlaw i) k hk
        (φ i) (hlam i) hM (hf i) (h i) (f i) (norm_eq_zero.mp hr)
      filter_upwards [hz] with ω hω _
      exact hω
    · exact Eventually.of_forall fun _ hr' => (hr hr').elim
  have hbad : Tendsto (fun i => P (G i)ᶜ) l (𝓝 0) := by
    have ht : Tendsto (fun i => P {ω | 1 / 4 ≤ |δ i ω|}) l (𝓝 0) := by
      simpa only [sub_zero, Real.norm_eq_abs] using
        (tendstoInMeasure_iff_norm.mp hδ) (1 / 4) (by norm_num)
    have htail : Tendsto (fun i => P {ω | 1 / 4 < δ i ω}) l (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      intro i
      apply measure_mono
      intro ω hω
      change 1 / 4 < δ i ω at hω
      exact hω.le.trans (le_abs_self _)
    have heq : ∀ i, P (G i)ᶜ = P {ω | 1 / 4 < δ i ω} := by
      intro i
      apply measure_congr
      filter_upwards [hzero i] with ω hω
      apply propext
      change (¬ (δ i ω ≤ 1 / 4 ∧ (‖r i‖ = 0 → Z i ω = 0))) ↔ 1 / 4 < δ i ω
      constructor
      · intro hnot
        exact lt_of_not_ge (fun hd => hnot ⟨hd, hω⟩)
      · intro hlt hpair
        exact not_lt_of_ge hpair.1 hlt
    exact htail.congr' (Eventually.of_forall fun i => (heq i).symm)
  have hLnonneg : ∀ i, 0 ≤ L i := by
    intro i
    obtain ⟨y, hy⟩ := (hL i).exists
    exact (sq_nonneg ‖featureRegularizedInvSqrt μ k hk (lam i) (k y)‖).trans hy
  have hb := actualBiasRHSAmplitude_tendstoInMeasure n hn x hlaw hind k hk lam hlam hM
    φ hf h f L hLnonneg hL hrate
  have heps := tendstoInMeasure_continuousAt_const hε (fun t : ℝ => |t|) continuous_abs.continuousAt
  have hu : TendstoInMeasure P u l (fun _ => 0) := by
    exact tendstoInMeasure_add_zero hb (by simpa only [abs_zero] using heps)
  have hc : ∀ i ω, 0 ≤ c i ω := fun i ω => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hsmall : TendstoInMeasure P (fun i ω => c i ω ^ 2 / V i) l (fun _ => 0) := by
    simpa only [c, mul_pow, sq_abs] using hβ
  have he : ∀ᶠ i in l, ∀ ω ∈ G i, ‖e i ω‖ ≤ u i ω * ‖r i‖ + c i ω := by
    filter_upwards [hinter] with i hi ω hω
    exact actualBiasError_norm_le_of_interaction k hk (φ i) (hlam i) hα hM (fun j => x i j ω)
      (hMX i ω) (hf i) (h i) (f i) (ε i ω) (β i ω) hω.1 hω.2 (hi ω hω.1)
  have hp := probabilistic_bias_transfer_on_good_events P (fun i _ => r i) e u c V G hbad
    (Eventually.of_forall fun i => Eventually.of_forall fun ω => hc i ω)
    (Eventually.of_forall fun i ω _ => ⟨add_nonneg
      (actualBiasRHSAmplitude_nonneg k hk (φ i) (hlam i) hM (hf i) (h i) (f i) _) (abs_nonneg _), hc i ω⟩)
    hV he hu hsmall
  apply TendstoInMeasure.congr_left (fun i => Eventually.of_forall fun ω => ?_) hp
  rw [actual_bias_energy_eq k hk (φ i) (hlam i) hM (fun j => x i j ω) (hMX i ω) (hf i) (h i) (f i)]

/-- The manuscript's common bias comparison with the actual population filter
trace and sequence variance `V = σ² Nq / n`. Positivity of `Nq` is required;
a zero scalar filter is not silently excluded by its contract. Finiteness of
the trace is proved in `FilterDimension`, rather than an additional premise.

Only the feature Hilbert space is separable. The target lives in the full
`L²(μ)`, and the theorem remains valid for a varying target. The localized
interaction inequality and its two probability rates are the stated inputs
of this common proposition, not a claim of the localized main theorem.
-/
theorem actual_common_bias_transfer [TopologicalSpace.SeparableSpace H] {l : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i) (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (hind : ∀ i, Pairwise (fun j k => IndepFun (x i j) (x i k) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    {M ρ A α : ℝ} (hα : 0 ≤ α)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hMX : ∀ i ω, ‖empiricalCovariance (fun j => k (x i j ω))‖ ≤ M)
    (φ : ι → ℝ → ℝ) (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i)) (f : ι → Lp ℝ 2 μ)
    (σ : ℝ) (hσ : 0 < σ) (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (L : ι → ℝ)
    (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hrate : Tendsto (fun i => L i / (n i : ℝ)) l (𝓝 0))
    (ε β : ι → Ω → ℝ)
    (hδ : TendstoInMeasure P (fun i ω => actualCovarianceDeviation k hk (lam i)
      (fun j => x i j ω)) l (fun _ => 0))
    (hε : TendstoInMeasure P ε l (fun _ => 0))
    (hβ : TendstoInMeasure P (fun i ω => β i ω ^ 2 *
      ‖actualBiasWeight k hk (φ i) (hlam i) hα hM (hf i) (f i)‖ ^ 2 /
      (σ ^ 2 / (n i : ℝ) * featureFilterDimension k hk (φ i))) l (fun _ => 0))
    (hinter : ∀ᶠ i in l, ∀ ω,
      actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) ≤ 1 / 4 →
      ‖actualInteractionPrediction k hk (φ i) (hlam i) hM (fun j => x i j ω)
        (hMX i ω) (hf i) (h i) (f i)‖ ≤
      ε i ω * ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ +
      β i ω * ‖actualBiasWeight k hk (φ i) (hlam i) hα hM (hf i) (f i)‖) :
    TendstoInMeasure P (fun i ω =>
      |actualEmpiricalBiasEnergy k hk (φ i) (hlam i) (fun j => x i j ω) (hMX i ω) (h i) (f i) -
        ‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ ^ 2| /
      (‖populationSpectralResidual k hk (φ i) hM (hf i) (f i)‖ ^ 2 +
        σ ^ 2 / (n i : ℝ) * featureFilterDimension k hk (φ i))) l (fun _ => 0) := by
  apply actual_bias_transfer_of_interaction n hn x hlaw hind k hk lam hlam hα hM hMX
    φ hf h f L (fun i => σ ^ 2 / (n i : ℝ) * featureFilterDimension k hk (φ i)) hL hrate
    ?_ ε β hδ hε hβ hinter
  filter_upwards [hQ] with i hi
  exact mul_pos (div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr (hn i))) hi

end

end KernelSeq
