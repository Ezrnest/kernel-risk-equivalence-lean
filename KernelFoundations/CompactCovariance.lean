import KernelFoundations.PopulationCovariance
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Convex.Integral

/-!
# Compactness of the actual feature covariance

The covariance attached to an L² feature embedding is the operator-norm
Bochner integral of rank-one operators. Compact operators form a closed real
linear subspace, so this integral is compact. This proves compactness of the
population covariance operator on a possibly infinite-dimensional space.
-/

open MeasureTheory InnerProductSpace

namespace KernelFoundations

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A rank-one operator factors through the locally compact scalar field. -/
theorem isCompactOperator_rankOne_real (u v : H) : IsCompactOperator (rankOne ℝ u v) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℝ u)).comp_clm (innerSL ℝ v)

variable [CompleteSpace H]

/-- Bochner expectations of integrable compact operators remain compact. -/
theorem isCompactOperator_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A : X → H →L[ℝ] H)
    (hA : Integrable A μ) (hcompact : ∀ᵐ x ∂μ, IsCompactOperator (A x)) :
    IsCompactOperator (∫ x, A x ∂μ : H →L[ℝ] H) := by
  let K : Submodule ℝ (H →L[ℝ] H) := compactOperator (RingHom.id ℝ) H H
  change (∫ x, A x ∂μ) ∈ K
  apply K.convex.integral_mem
  · exact isClosed_setOf_isCompactOperator
  · exact hcompact
  · exact hA

/-- The actual population covariance S* S is compact for every square-integrable
feature map over a probability space. Injectivity and support assumptions are
unnecessary; the zero feature and finite-rank cases are included. -/
theorem populationCovariance_feature_isCompact {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (k : X → H) (hk : MemLp k 2 μ) :
    IsCompactOperator (populationCovariance (featureEmbedding μ k hk)) := by
  rw [populationCovariance_eq_integral]
  exact isCompactOperator_integral μ _ (integrable_rankOne_feature k hk)
    (Filter.Eventually.of_forall fun x => isCompactOperator_rankOne_real (k x) (k x))

end KernelFoundations
