import KernelSeq.ActualBiasTransfer
import KernelSeq.EmpiricalConditionalRisk

/-!
# Actual mean prediction and bias-error measurability

The arbitrary L2 target is evaluated through its original a.e. representative.
The exact finite response rule and the proved measurable prediction
coefficients supply strong a.e. measurability and square integrability. No
separability of the ambient prediction L2 space is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {H X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ]

theorem memLp_actualMeanPrediction {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0 ≤ κ) (hkb : ∀ y, ‖k y‖ ≤ κ)
    (hMX : ∀ ω, ‖empiricalCovariance (fun i => k (x i ω))‖ ≤ κ ^ 2)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (f : Lp ℝ 2 μ) :
    MemLp (fun ω => actualMeanPrediction k hk φ hlam (fun i => x i ω) (hMX ω) h f) 2 P := by
  let S := featureEmbedding μ k hk
  let v := fun i ω => k (x i ω)
  let hv := fun ω i => pow_le_pow_left₀ (norm_nonneg _) (hkb (x i ω)) 2
  let a := fun i ω => empiricalPredictionCoefficient S hn (fun j => v j ω) κ (hv ω) φ hlam h i
  have has (i : Fin n) : StronglyMeasurable (a i) :=
    stronglyMeasurable_empiricalPredictionCoefficient S hn v
      (fun j => hks.comp_measurable (hlaw j).measurable) κ hv φ hlam hf h i
  have hab (i : Fin n) (ω : Ω) : ‖a i ω‖ ≤ A * κ ^ 2 / ((n : ℝ) * lam) :=
    empiricalPredictionCoefficient_norm_le S hn _ κ hκ
      (featureEmbedding_norm_le μ k hk κ hκ (Filter.Eventually.of_forall hkb))
      (fun j => hkb (x j ω)) φ hlam h i
  have hi (i : Fin n) : MemLp (fun ω => f (x i ω) • a i ω) 2 P :=
    memLp_scalar_smul_of_bounded_vector ((Lp.memLp f).comp_measurePreserving (hlaw i))
      (has i).aestronglyMeasurable (Filter.Eventually.of_forall (hab i))
  have hs := memLp_finsetSum' Finset.univ (fun i _ => hi i)
  convert hs using 1
  funext ω
  change S (empiricalSpectralEstimator hn (fun j => v j ω) κ (hv ω)
    (fun j => f (x j ω)) φ hlam h) = _
  simpa only [a, Finset.sum_apply] using empiricalSpectralEstimator_prediction_sum S hn
    (fun j => v j ω) κ (hv ω) (fun j => f (x j ω)) φ hlam h

/-- The actual vector error is strongly a.e. measurable without an ambient
prediction-space separability assumption or an extra measurability input. -/
theorem aestronglyMeasurable_actualBiasError {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0 ≤ κ) (hkb : ∀ y, ‖k y‖ ≤ κ)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ κ ^ 2)
    (hMX : ∀ ω, ‖empiricalCovariance (fun i => k (x i ω))‖ ≤ κ ^ 2)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (f : Lp ℝ 2 μ) :
    AEStronglyMeasurable
      (fun ω => actualBiasError k hk φ hlam hM (fun i => x i ω) (hMX ω) h f) P :=
  (memLp_actualMeanPrediction hn x hlaw k hk hks κ hκ hkb hMX φ hlam hf h f).1.sub
    aestronglyMeasurable_const

variable [IsFiniteMeasure P]

/-- The actual empirical bias energy has a true finite integral. -/
theorem integrable_actualEmpiricalBiasEnergy {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (κ : ℝ) (hκ : 0 ≤ κ) (hkb : ∀ y, ‖k y‖ ≤ κ)
    (hMX : ∀ ω, ‖empiricalCovariance (fun i => k (x i ω))‖ ≤ κ ^ 2)
    (φ : ℝ → ℝ) {lam ρ A : ℝ} (hlam : 0 < lam)
    (hf : ResidualFilter.SpectralFilter (κ ^ 2) φ)
    (h : ResidualFilter.Contract lam (κ ^ 2) ρ A φ) (f : Lp ℝ 2 μ) :
    Integrable (fun ω => actualEmpiricalBiasEnergy k hk φ hlam (fun i => x i ω) (hMX ω) h f) P := by
  have hm := (memLp_actualMeanPrediction hn x hlaw k hk hks κ hκ hkb hMX φ hlam hf h f).sub
    (memLp_const f)
  exact (memLp_two_iff_integrable_sq_norm hm.1).mp hm

end
end KernelSeq
