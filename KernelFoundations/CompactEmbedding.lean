import KernelFoundations.CompactCovariance
import KernelFoundations.RKHSFeature
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

/-!
# Compactness of a feature embedding from compact covariance

For bounded maps between real Hilbert spaces, compactness of `S* S` implies
compactness of `S`. This uses a finite-net quadratic-form estimate, without
constructing an operator square root.
-/

open Set Filter Metric MeasureTheory

namespace KernelFoundations

variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The basic modulus connecting image differences to covariance differences. -/
theorem norm_image_sub_sq_le_covariance (S : H →L[ℝ] E) (x y : H) :
    ‖S x - S y‖ ^ 2 ≤ ‖x - y‖ * ‖(S.adjoint.comp S) x - (S.adjoint.comp S) y‖ := by
  rw [← map_sub S, S.apply_norm_sq_eq_inner_adjoint_right]
  simpa only [RCLike.re_to_real, map_sub] using
    real_inner_le_norm (x - y) ((S.adjoint.comp S) (x - y))

/-- Compact covariance makes the embedding compact, including infinite-dimensional
spaces and a noninjective embedding. -/
theorem isCompactOperator_of_adjoint_comp_self (S : H →L[ℝ] E)
    (hT : IsCompactOperator (S.adjoint.comp S)) : IsCompactOperator S := by
  classical
  let T := S.adjoint.comp S
  have htbT : TotallyBounded (T '' closedBall (0 : H) 1) :=
    (hT.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  have htbS : TotallyBounded (S '' closedBall (0 : H) 1) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    have heps : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε)
    obtain ⟨t, htSub, htFin, htCov⟩ := htbT.exists_subset (Metric.dist_mem_uniformity heps)
    letI : Fintype t := htFin.fintype
    choose g hgBall hgT using fun y : t => htSub y.property
    refine ⟨Set.range (fun y : t => S (g y)), Set.finite_range _, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    have hcover := htCov (Set.mem_image_of_mem T hx)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hcover
    obtain ⟨y, hy, hxy⟩ := hcover
    refine Set.mem_iUnion₂.mpr ⟨S (g ⟨y, hy⟩), Set.mem_range_self (⟨y, hy⟩ : t), ?_⟩
    change dist (S x) (S (g ⟨y, hy⟩)) < ε
    have hxNorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hgNorm : ‖g ⟨y, hy⟩‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hgBall ⟨y, hy⟩
    have hdiff : ‖x - g ⟨y, hy⟩‖ ≤ 2 := by
      calc
        ‖x - g ⟨y, hy⟩‖ ≤ ‖x‖ + ‖g ⟨y, hy⟩‖ := norm_sub_le _ _
        _ ≤ 2 := by linarith
    have hnear : ‖T x - T (g ⟨y, hy⟩)‖ < ε ^ 2 / 2 := by
      rw [hgT ⟨y, hy⟩]
      simpa only [dist_eq_norm] using hxy
    have hbound := norm_image_sub_sq_le_covariance S x (g ⟨y, hy⟩)
    have hprod : ‖x - g ⟨y, hy⟩‖ * ‖T x - T (g ⟨y, hy⟩)‖ ≤
        2 * ‖T x - T (g ⟨y, hy⟩)‖ :=
      mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
    rw [dist_eq_norm]
    change ‖S x - S (g ⟨y, hy⟩)‖ ^ 2 ≤
      ‖x - g ⟨y, hy⟩‖ * ‖T x - T (g ⟨y, hy⟩)‖ at hbound
    nlinarith [norm_nonneg (S x - S (g ⟨y, hy⟩))]
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall S.toLinearMap zero_lt_one).mpr
    (htbS.closure.isCompact_of_isClosed isClosed_closure)

/-- Compactness also passes to the prediction covariance `S S*`. -/
theorem isCompactOperator_comp_adjoint_of_adjoint_comp_self (S : H →L[ℝ] E)
    (hT : IsCompactOperator (S.adjoint.comp S)) : IsCompactOperator (S.comp S.adjoint) :=
  (isCompactOperator_of_adjoint_comp_self S hT).comp_clm S.adjoint

/-- Compactness of the actual square-integrable feature embedding. -/
theorem featureEmbedding_isCompact {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (k : X → H) (hk : MemLp k 2 μ) :
    IsCompactOperator (featureEmbedding μ k hk) :=
  isCompactOperator_of_adjoint_comp_self _ (populationCovariance_feature_isCompact μ k hk)

/-- Compactness of the actual prediction covariance `L = S S*`. -/
theorem predictionCovariance_feature_isCompact {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (k : X → H) (hk : MemLp k 2 μ) :
    IsCompactOperator (predictionCovariance (featureEmbedding μ k hk)) :=
  (featureEmbedding_isCompact μ k hk).comp_clm (featureEmbedding μ k hk).adjoint

/-- Compactness of the canonical RKHS embedding for a bounded measurable kernel. -/
theorem rkhsEmbedding_isCompact {X : Type*} [MeasurableSpace X]
    [SecondCountableTopology H] [RKHS ℝ H X ℝ]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2) :
    IsCompactOperator (rkhsEmbedding μ hK κ hκ hdiag) :=
  featureEmbedding_isCompact μ _ (rkhsFeature_memLp μ hK κ hκ hdiag)

/-- Compactness of the canonical RKHS prediction covariance. -/
theorem rkhsPredictionCovariance_isCompact {X : Type*} [MeasurableSpace X]
    [SecondCountableTopology H] [RKHS ℝ H X ℝ]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2) :
    IsCompactOperator (predictionCovariance (rkhsEmbedding μ hK κ hκ hdiag)) :=
  (rkhsEmbedding_isCompact μ hK κ hκ hdiag).comp_clm (rkhsEmbedding μ hK κ hκ hdiag).adjoint

end KernelFoundations
