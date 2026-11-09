import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The feature embedding into the prediction space

Constructs the actual bounded linear map `h ↦ (x ↦ ⟨k x,h⟩)` into `L²(μ)`.
For a bounded measurable RKHS feature map this is the canonical embedding.
The construction applies to possibly noninjective embeddings and
infinite-dimensional spaces. The statement takes a feature map satisfying
`MemLp`.
-/

open MeasureTheory

namespace KernelFoundations

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The continuous embedding attached to an `L²` feature vector. -/
noncomputable def featureEmbeddingLp (μ : Measure X) (k : Lp H 2 μ) :
    H →L[ℝ] Lp ℝ 2 μ :=
  ((innerSL ℝ (E := H)).compLpL₂ 2 μ).flip k

theorem featureEmbeddingLp_norm_le (μ : Measure X) (k : Lp H 2 μ) :
    ‖featureEmbeddingLp μ k‖ ≤ ‖k‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro h
  change ‖(innerSL ℝ h).compLp k‖ ≤ ‖k‖ * ‖h‖
  simpa only [innerSL_apply_norm, mul_comm] using
    ContinuousLinearMap.norm_compLp_le (innerSL ℝ h) k

/-- Canonical feature embedding, well-defined on the feature's `L²` class. -/
noncomputable def featureEmbedding (μ : Measure X) (k : X → H) (hk : MemLp k 2 μ) :
    H →L[ℝ] Lp ℝ 2 μ :=
  featureEmbeddingLp μ (hk.toLp k)

/-- The prediction function agrees almost everywhere with the feature inner product. -/
theorem featureEmbedding_ae (μ : Measure X) (k : X → H) (hk : MemLp k 2 μ) (h : H) :
    featureEmbedding μ k hk h =ᵐ[μ] fun x => inner ℝ (k x) h := by
  change (innerSL ℝ h).compLp (hk.toLp k) =ᵐ[μ] fun x => inner ℝ (k x) h
  have hcomp := ContinuousLinearMap.coeFn_compLp (innerSL ℝ h) (hk.toLp k)
  filter_upwards [hcomp, hk.coeFn_toLp] with x hx hkx
  simpa only [innerSL_apply_apply, hkx, real_inner_comm] using hx

omit [InnerProductSpace ℝ H] in
/-- Bounded strongly measurable feature maps have the required `L²` class. -/
theorem feature_memLp_of_bound (μ : Measure X) [IsFiniteMeasure μ]
    (k : X → H) (hk : AEStronglyMeasurable k μ) (κ : ℝ)
    (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ) : MemLp k 2 μ :=
  MemLp.of_bound hk κ hbound

/-- The diagonal kernel bound gives the usual embedding norm bound. -/
theorem featureEmbedding_norm_le (μ : Measure X) [IsProbabilityMeasure μ]
    (k : X → H) (hk : MemLp k 2 μ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ) : ‖featureEmbedding μ k hk‖ ≤ κ := by
  apply (featureEmbeddingLp_norm_le μ (hk.toLp k)).trans
  have hb : ∀ᵐ x ∂μ, ‖(hk.toLp k) x‖ ≤ κ := by
    filter_upwards [hk.coeFn_toLp, hbound] with x hx hbx
    simpa only [hx] using hbx
  simpa [measureUnivNNReal, measure_univ] using Lp.norm_le_of_ae_bound hκ hb

variable {μ : Measure X}

/-- The covariance and prediction operators attached to an embedding. -/
noncomputable def populationCovariance [CompleteSpace H]
    (S : H →L[ℝ] Lp ℝ 2 μ) : H →L[ℝ] H :=
  S.adjoint.comp S

noncomputable def predictionCovariance [CompleteSpace H]
    (S : H →L[ℝ] Lp ℝ 2 μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  S.comp S.adjoint

theorem populationCovariance_isPositive [CompleteSpace H]
    (S : H →L[ℝ] Lp ℝ 2 μ) : (populationCovariance S).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self S

theorem predictionCovariance_isPositive [CompleteSpace H]
    (S : H →L[ℝ] Lp ℝ 2 μ) : (predictionCovariance S).IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint S

/-- The population covariance quadratic form is the squared prediction norm. -/
theorem populationCovariance_quadratic [CompleteSpace H]
    (S : H →L[ℝ] Lp ℝ 2 μ) (h : H) :
    inner ℝ h (populationCovariance S h) = ‖S h‖ ^ 2 := by
  change inner ℝ h (S.adjoint (S h)) = _
  rw [S.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- Weak integral characterization of the actual feature-embedding adjoint. -/
theorem featureEmbedding_adjoint_pairing [CompleteSpace H]
    (k : X → H) (hk : MemLp k 2 μ) (h : H) (f : Lp ℝ 2 μ) :
    inner ℝ h ((featureEmbedding μ k hk).adjoint f) =
      ∫ x, inner ℝ (k x) h * f x ∂μ := by
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [featureEmbedding_ae μ k hk h] with x hx
  simp [hx, mul_comm]

/-- The covariance norm is the square of the prediction embedding norm. -/
theorem populationCovariance_norm [CompleteSpace H]
    (S : H →L[ℝ] Lp ℝ 2 μ) : ‖populationCovariance S‖ = ‖S‖ ^ 2 := by
  simpa only [populationCovariance, pow_two] using S.norm_adjoint_comp_self

/-- Population spectral upper bound following from bounded features. -/
theorem featureCovariance_norm_le [CompleteSpace H] [IsProbabilityMeasure μ]
    (k : X → H) (hk : MemLp k 2 μ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ) :
    ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ κ ^ 2 := by
  rw [populationCovariance_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (featureEmbedding_norm_le μ k hk κ hκ hbound) 2

/-- The scalar `L²` representative has exactly its Hilbert-space squared norm. -/
theorem integral_sq_L2 {μ : Measure X} (r : Lp ℝ 2 μ) : (∫ x, r x ^ 2 ∂μ) = ‖r‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change (∫ x, r x ^ 2 ∂μ) = ∫ x, inner ℝ (r x) (r x) ∂μ
  simp

end KernelFoundations
