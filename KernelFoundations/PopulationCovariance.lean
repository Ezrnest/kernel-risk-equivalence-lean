import KernelFoundations.FeatureEmbedding
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Population covariance integral

Identifies the operators constructed from the `L²` feature embedding
with their feature integrals. The operator integral is in operator norm. The
feature map is square integrable; it need not have full support or injective embedding.
-/

open MeasureTheory InnerProductSpace

namespace KernelFoundations

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X}

omit [CompleteSpace H] in
/-- The feature-weighted prediction is Bochner integrable by Hölder. -/
theorem integrable_feature_smul (k : X → H) (hk : MemLp k 2 μ) (f : Lp ℝ 2 μ) :
    Integrable (fun x => f x • k x) μ := by
  exact memLp_one_iff_integrable.mp (hk.smul (Lp.memLp f))

/-- The adjoint is the feature-weighted Bochner integral. -/
theorem featureEmbedding_adjoint_eq_integral (k : X → H) (hk : MemLp k 2 μ)
    (f : Lp ℝ 2 μ) :
    (featureEmbedding μ k hk).adjoint f = ∫ x, f x • k x ∂μ := by
  apply ext_inner_left ℝ
  intro h
  rw [featureEmbedding_adjoint_pairing, ← integral_inner (integrable_feature_smul k hk f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [inner_smul_right, real_inner_comm, mul_comm]

omit [CompleteSpace H] in
/-- The rank-one feature covariance is Bochner integrable in operator norm. -/
theorem integrable_rankOne_feature (k : X → H) (hk : MemLp k 2 μ) :
    Integrable (fun x => rankOne ℝ (k x) (k x)) μ := by
  have hmeas : AEStronglyMeasurable (fun x => rankOne ℝ (k x) (k x)) μ :=
    ((rankOne ℝ).continuous.clm_apply continuous_id).comp_aestronglyMeasurable hk.1
  apply (hk.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).mono' hmeas
  exact Filter.Eventually.of_forall fun x => by simp [pow_two]

/-- Action of the population covariance on each Hilbert vector. -/
theorem populationCovariance_feature_apply (k : X → H) (hk : MemLp k 2 μ) (h : H) :
    populationCovariance (featureEmbedding μ k hk) h =
      ∫ x, inner ℝ (k x) h • k x ∂μ := by
  change (featureEmbedding μ k hk).adjoint (featureEmbedding μ k hk h) = _
  rw [featureEmbedding_adjoint_eq_integral]
  apply integral_congr_ae
  filter_upwards [featureEmbedding_ae μ k hk h] with x hx
  rw [hx]

/-- The covariance defined as `S* S` equals the rank-one Bochner integral. -/
theorem populationCovariance_eq_integral (k : X → H) (hk : MemLp k 2 μ) :
    populationCovariance (featureEmbedding μ k hk) =
      ∫ x, rankOne ℝ (k x) (k x) ∂μ := by
  ext h
  rw [populationCovariance_feature_apply,
    ContinuousLinearMap.integral_apply (integrable_rankOne_feature k hk)]
  rfl

end KernelFoundations
