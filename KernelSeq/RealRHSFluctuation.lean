import KernelFoundations.RegularizedFeatures
import KernelSeq.CompactSpectral
import KernelSeq.CompactCovariance
import KernelSeq.RHSAsymptotics
import KernelSeq.RKHSFeature

/-!
# Right-hand-side fluctuations with the actual real inverse square root

The covariance is the actual `S* S` of an L² feature embedding. Its compactness
and positivity are proved inputs from the model, rather than extra hypotheses.
For positive regularization the normalizer is the constructed real inverse
square root. The residual remains exactly `f - S h`; no spectral identity for
a particular choice of `h` is assumed here.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace KernelSeq

export KernelFoundations (
  featureRegularizedInvSqrt featureRegularizedInvSqrt_isSelfAdjoint
  featureRegularizedInvSqrt_normalizes featureRegularizedInvSqrt_norm_le
  normalizedLeverage normalizedLeverage_le_norm_sq_div
  normalizedLeverage_ae_le_of_sq_bound
  normalizedLeverage_ae_le_of_norm_bound normalizedLeverage_rkhs_le
)

variable {ι X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ]

/-- The actual normalized empirical-minus-population right-hand side. -/
noncomputable def normalizedRHS (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) (f : Lp ℝ 2 μ) (h : H) {n : ℕ} (x : Fin n → X) : H :=
  featureRegularizedInvSqrt μ k hk lam (rhsFluctuation k hk f h x)

variable [IsProbabilityMeasure P]

/-- The actual normalized fluctuation is square integrable under an a.e.
leverage bound. No inverse-square-root hypothesis is present. -/
theorem memLp_normalizedRHS {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (f : Lp ℝ 2 μ) (h : H)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    MemLp (fun ω => normalizedRHS k hk lam f h (fun i => x i ω)) 2 P :=
  memLp_rhsFluctuation hn x hlaw k hk f h (featureRegularizedInvSqrt μ k hk lam) hL

variable [MeasurableSpace H] [BorelSpace H]

/-- The actual real-normalized second moment is at most leverage divided by
sample size times the exact population residual norm squared. -/
theorem integral_normalizedRHS_sq_le {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (f : Lp ℝ 2 μ) (h : H)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    (∫ ω, ‖normalizedRHS k hk lam f h (fun i => x i ω)‖ ^ 2 ∂P) ≤
      L / (n : ℝ) * ‖f - featureEmbedding μ k hk h‖ ^ 2 :=
  integral_rhsFluctuation_sq_le hn x hlaw hindep k hk f h
    (featureRegularizedInvSqrt μ k hk lam) hL

/-- The crude kernel-bound version, using the actual inverse-root norm estimate. -/
theorem integral_normalizedRHS_sq_le_crude {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam)
    (κ : ℝ) (hκ : ∀ᵐ y ∂μ, ‖k y‖ ^ 2 ≤ κ ^ 2)
    (f : Lp ℝ 2 μ) (h : H) :
    (∫ ω, ‖normalizedRHS k hk lam f h (fun i => x i ω)‖ ^ 2 ∂P) ≤
      κ ^ 2 / (lam * (n : ℝ)) * ‖f - featureEmbedding μ k hk h‖ ^ 2 := by
  simpa only [div_div] using integral_normalizedRHS_sq_le hn x hlaw hindep k hk lam f h
    (normalizedLeverage_ae_le_of_sq_bound k hk lam hlam κ hκ)

/-- An explicit tail bound for the actual real-normalized right-hand side. -/
theorem measure_normalizedRHS_ge_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (f : Lp ℝ 2 μ) (h : H)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ ‖normalizedRHS k hk lam f h (fun i => x i ω)‖} ≤
      ENNReal.ofReal (L / (n : ℝ) * ‖f - featureEmbedding μ k hk h‖ ^ 2 / t ^ 2) := by
  let z : Ω → H := fun ω => normalizedRHS k hk lam f h (fun i => x i ω)
  have hz := memLp_normalizedRHS hn x hlaw k hk lam f h hL
  change MemLp z 2 P at hz
  have hi := (memLp_two_iff_integrable_sq_norm hz.1).mp hz
  have hm := (hi.div_const (t ^ 2)).measure_le_integral
    (Eventually.of_forall (fun ω => div_nonneg (sq_nonneg ‖z ω‖) (sq_nonneg t)))
    (s := {ω | t ≤ ‖z ω‖}) (fun ω hω => by
      rw [le_div_iff₀ (sq_pos_of_pos ht)]
      change t ≤ ‖z ω‖ at hω
      nlinarith [norm_nonneg (z ω)])
  refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (integral_normalizedRHS_sq_le hn x hlaw hindep k hk lam f h hL) (sq_nonneg t)

/-- The normalized residual fluctuation has second moment at most `L/n`, also
when the population residual is zero. -/
theorem integral_scaled_normalizedRHS_sq_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (f : Lp ℝ 2 μ) (h : H)
    {L : ℝ} (hLnonneg : 0 ≤ L)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L) :
    (∫ ω, ‖‖f - featureEmbedding μ k hk h‖⁻¹ •
      normalizedRHS k hk lam f h (fun i => x i ω)‖ ^ 2 ∂P) ≤ L / (n : ℝ) :=
  integral_scaled_rhsFluctuation_sq_le hn x hlaw hindep k hk f h
    (featureRegularizedInvSqrt μ k hk lam) hLnonneg hL

/-- Stochastic negligibility for a family of actual real inverse square roots,
with the manuscript's sharper a.e. leverage hypothesis. -/
theorem normalizedRHS_div_residual_tendstoInMeasure {l : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (hindep : ∀ i, Pairwise (fun j k => IndepFun (x i j) (x i k) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ)
    (f : ι → Lp ℝ 2 μ) (h : ι → H) (L : ι → ℝ) (hLnonneg : ∀ i, 0 ≤ L i)
    (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hrate : Tendsto (fun i => L i / (n i : ℝ)) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω => ‖f i - featureEmbedding μ k hk (h i)‖⁻¹ •
      normalizedRHS k hk (lam i) (f i) (h i) (fun j => x i j ω)) l (fun _ => 0) :=
  rhsFluctuation_div_residual_tendstoInMeasure n hn x hlaw hindep k hk f h
    (fun i => featureRegularizedInvSqrt μ k hk (lam i)) L hLnonneg hL hrate

/-- A concrete probability-family conclusion requiring only a bounded kernel
and `κ²/(n λ) → 0`. The sharper leverage rate can use the preceding theorem. -/
theorem normalizedRHS_div_residual_tendstoInMeasure_crude {l : Filter ι}
    (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (hindep : ∀ i, Pairwise (fun j k => IndepFun (x i j) (x i k) P))
    (k : X → H) (hk : MemLp k 2 μ) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i)
    (κ : ℝ) (hκ : ∀ᵐ y ∂μ, ‖k y‖ ^ 2 ≤ κ ^ 2)
    (f : ι → Lp ℝ 2 μ) (h : ι → H)
    (hrate : Tendsto (fun i => κ ^ 2 / (lam i * (n i : ℝ))) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω => ‖f i - featureEmbedding μ k hk (h i)‖⁻¹ •
      normalizedRHS k hk (lam i) (f i) (h i) (fun j => x i j ω)) l (fun _ => 0) := by
  apply normalizedRHS_div_residual_tendstoInMeasure n hn x hlaw hindep k hk lam f h
    (fun i => κ ^ 2 / lam i) (fun i => div_nonneg (sq_nonneg κ) (hlam i).le)
    (fun i => normalizedLeverage_ae_le_of_sq_bound k hk (lam i) (hlam i) κ hκ)
  simpa only [div_div] using hrate

end KernelSeq
