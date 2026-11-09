import KernelSeq.NormalizedCovariance
import KernelSeq.EmpiricalSpectral
import KernelSeq.HilbertSchmidtIdeal

/-!
# Actual mixed-normalization perturbation

The real operator-norm and Hilbert–Schmidt bounds for mixed perturbations. The
transition factor between population and empirical inverse roots is bounded directly
from the proved relative quadratic-form comparison. Square roots, covariance
factorization and Hilbert--Schmidt membership are constructed, not premises of
the actual sample specialization.
-/

namespace KernelSeq

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem compactRegularizedSqrt_apply_norm_sq (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (lam : ℝ) (hlam : 0 ≤ lam) (x : H) :
    ‖compactRegularizedSqrt T hc hp lam x‖ ^ 2 =
      inner ℝ x ((T + lam • (1 : H →L[ℝ] H)) x) := by
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    (compactRegularizedSqrt_isSelfAdjoint T hc hp lam).adjoint_eq]
  change inner ℝ x ((compactRegularizedSqrt T hc hp lam *
    compactRegularizedSqrt T hc hp lam) x) = _
  rw [compactRegularizedSqrt_sq T hc hp lam hlam]

noncomputable def realNormalizedPerturbation (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (lam : ℝ) : H →L[ℝ] H :=
  compactRegularizedInvSqrt T hc hp lam * (TX - T) * compactRegularizedInvSqrt T hc hp lam

noncomputable def rootTransition (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) : H →L[ℝ] H :=
  compactRegularizedSqrt T hc hp lam * compactRegularizedInvSqrt TX hcX hpX lam

noncomputable def realMixedPerturbation (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) : H →L[ℝ] H :=
  compactRegularizedInvSqrt T hc hp lam * (TX - T) * compactRegularizedInvSqrt TX hcX hpX lam

/-- The manuscript's orientation of the mixed perturbation. -/
noncomputable def manuscriptMixedPerturbation (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) : H →L[ℝ] H :=
  compactRegularizedInvSqrt TX hcX hpX lam * (TX - T) * compactRegularizedInvSqrt T hc hp lam

theorem realMixedPerturbation_adjoint (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) :
    (realMixedPerturbation T TX hc hcX hp hpX lam).adjoint =
      manuscriptMixedPerturbation T TX hc hcX hp hpX lam := by
  simp only [realMixedPerturbation, manuscriptMixedPerturbation, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.adjoint_comp, map_sub, hp.isSelfAdjoint.adjoint_eq,
    hpX.isSelfAdjoint.adjoint_eq, (compactRegularizedInvSqrt_isSelfAdjoint T hc hp lam).adjoint_eq,
    (compactRegularizedInvSqrt_isSelfAdjoint TX hcX hpX lam).adjoint_eq,
    ContinuousLinearMap.comp_assoc]

/-- Exact mixed factorization through the actual normalized perturbation. -/
theorem realMixedPerturbation_factorization (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    realNormalizedPerturbation T TX hc hp lam * rootTransition T TX hc hcX hp hpX lam =
      realMixedPerturbation T TX hc hcX hp hpX lam := by
  dsimp only [realNormalizedPerturbation, rootTransition, realMixedPerturbation]
  calc
    _ = compactRegularizedInvSqrt T hc hp lam * (TX - T) *
        (compactRegularizedInvSqrt T hc hp lam * compactRegularizedSqrt T hc hp lam) *
          compactRegularizedInvSqrt TX hcX hpX lam := by simp only [mul_assoc]
    _ = _ := by rw [compactRegularizedInvSqrt_mul_sqrt T hc hp lam hlam, mul_one]

/-- The transition root factor is uniformly bounded on the good event.
This is derived from actual root identities and relative quadratic forms. -/
theorem rootTransition_norm_le (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 2) :
    ‖rootTransition T TX hc hcX hp hpX lam‖ ≤ Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  let y := compactRegularizedInvSqrt TX hcX hpX lam x
  have hq := (compact_regularized_relative_comparison_real T TX hc hp lam hlam y).1
  have hδeq : ‖Ring.inverse (compactRegularizedSqrt T hc hp lam) *
      (TX + lam • (1 : H →L[ℝ] H) - (T + lam • 1)) *
        Ring.inverse (compactRegularizedSqrt T hc hp lam)‖ =
      ‖realNormalizedPerturbation T TX hc hp lam‖ := by
    congr 1
    congr 2
    abel
  rw [hδeq, ← compactRegularizedSqrt_apply_norm_sq T hc hp lam hlam.le] at hq
  have hx : compactRegularizedSqrt TX hcX hpX lam y = x := by
    exact congrArg (fun A : H →L[ℝ] H => A x)
      (compactRegularizedSqrt_mul_invSqrt TX hcX hpX lam hlam)
  rw [← compactRegularizedSqrt_apply_norm_sq TX hcX hpX lam hlam.le, hx] at hq
  have hd := mul_le_mul_of_nonneg_right hδ
    (sq_nonneg ‖compactRegularizedSqrt T hc hp lam y‖)
  have hnorm : ‖compactRegularizedSqrt T hc hp lam y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by nlinarith
  change ‖compactRegularizedSqrt T hc hp lam y‖ ≤ Real.sqrt 2 * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact hnorm

theorem realMixedPerturbation_norm_le (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 2) :
    ‖realMixedPerturbation T TX hc hcX hp hpX lam‖ ≤
      Real.sqrt 2 * ‖realNormalizedPerturbation T TX hc hp lam‖ := by
  rw [← realMixedPerturbation_factorization T TX hc hcX hp hpX lam hlam]
  exact (norm_mul_le _ _).trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (rootTransition_norm_le T TX hc hcX hp hpX lam hlam hδ)
      (norm_nonneg (realNormalizedPerturbation T TX hc hp lam)))

/-- The operator-norm bound for the mixed perturbation. -/
theorem manuscriptMixedPerturbation_norm_le (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 4) :
    ‖manuscriptMixedPerturbation T TX hc hcX hp hpX lam‖ ≤
      2 * ‖realNormalizedPerturbation T TX hc hp lam‖ := by
  rw [← realMixedPerturbation_adjoint, LinearIsometryEquiv.norm_map]
  refine (realMixedPerturbation_norm_le T TX hc hcX hp hpX lam hlam
    (hδ.trans (by norm_num))).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Mixed HS columns are constructed by an actual bounded right composition. -/
noncomputable def mixedPerturbationColumns (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι H) (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) : HilbertSchmidtColumns ι H :=
  hsRightComposition b b b (rootTransition T TX hc hcX hp hpX lam) c

theorem mixedPerturbationColumns_norm_le (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι H) (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1 / 2) :
    ‖mixedPerturbationColumns b c T TX hc hcX hp hpX lam‖ ≤ Real.sqrt 2 * ‖c‖ := by
  refine (hsRightComposition_norm_le b b b _ c).trans ?_
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (rootTransition_norm_le T TX hc hcX hp hpX lam hlam hδ) (norm_nonneg c)

theorem hilbertSchmidtOperator_mixedPerturbationColumns (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι H) (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hrepr : hilbertSchmidtOperator b c = realNormalizedPerturbation T TX hc hp lam) :
    hilbertSchmidtOperator b (mixedPerturbationColumns b c T TX hc hcX hp hpX lam) =
      realMixedPerturbation T TX hc hcX hp hpX lam := by
  rw [mixedPerturbationColumns, hilbertSchmidtOperator_rightComposition, hrepr]
  exact realMixedPerturbation_factorization T TX hc hcX hp hpX lam hlam

section ActualSample

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The mixed covariance perturbation of the actual sample, as genuine HS columns. -/
noncomputable def sampleMixedPerturbationColumns (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) {n : ℕ} (x : Fin n → X) :
    HilbertSchmidtColumns ι H :=
  mixedPerturbationColumns b (normalizedHSCovarianceFluctuation b k hk lam x)
    (populationCovariance (featureEmbedding μ k hk))
    (empiricalCovariance (fun i => k (x i)))
    (populationCovariance_feature_isCompact μ k hk)
    (empiricalCovariance_isCompact _) (populationCovariance_isPositive _)
    (empiricalCovariance_isPositive _) lam

/-- Exact actual-sample HS reconstruction; no perturbation-factorization input
or Hilbert--Schmidt membership certificate is present. -/
theorem hilbertSchmidtOperator_sampleMixedPerturbationColumns
    (b : HilbertBasis ι ℝ H) (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam)
    {n : ℕ} (x : Fin n → X) :
    hilbertSchmidtOperator b (sampleMixedPerturbationColumns b k hk lam x) =
      featureRegularizedInvSqrt μ k hk lam *
        (empiricalCovariance (fun i => k (x i)) - populationCovariance (featureEmbedding μ k hk)) *
        compactRegularizedInvSqrt (empiricalCovariance (fun i => k (x i)))
          (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) lam := by
  apply hilbertSchmidtOperator_mixedPerturbationColumns b
    (normalizedHSCovarianceFluctuation b k hk lam x) _ _ _ _ _ _ lam hlam
  exact hilbertSchmidtOperator_normalizedHSCovarianceFluctuation b k hk lam x

/-- The manuscript's actual mixed HS bound on its good event. -/
theorem sampleMixedPerturbationColumns_norm_le (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hδ : ‖featureRegularizedInvSqrt μ k hk lam *
      (empiricalCovariance (fun i => k (x i)) - populationCovariance (featureEmbedding μ k hk)) *
        featureRegularizedInvSqrt μ k hk lam‖ ≤ 1 / 2) :
    ‖sampleMixedPerturbationColumns b k hk lam x‖ ≤
      Real.sqrt 2 * ‖normalizedHSCovarianceFluctuation b k hk lam x‖ :=
  mixedPerturbationColumns_norm_le b _ _ _ _ _ _ _ lam hlam hδ

/-- HS columns in the manuscript's exact orientation. -/
noncomputable def manuscriptMixedColumns (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) {n : ℕ} (x : Fin n → X) :
    HilbertSchmidtColumns ι H :=
  hsAdjointColumns b b (sampleMixedPerturbationColumns b k hk lam x)

theorem hilbertSchmidtOperator_manuscriptMixedColumns (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) {n : ℕ} (x : Fin n → X) :
    hilbertSchmidtOperator b (manuscriptMixedColumns b k hk lam x) =
      manuscriptMixedPerturbation (populationCovariance (featureEmbedding μ k hk))
        (empiricalCovariance (fun i => k (x i))) (populationCovariance_feature_isCompact μ k hk)
        (empiricalCovariance_isCompact _) (populationCovariance_isPositive _)
        (empiricalCovariance_isPositive _) lam := by
  rw [manuscriptMixedColumns, hilbertSchmidtOperator_adjoint,
    hilbertSchmidtOperator_sampleMixedPerturbationColumns b k hk lam hlam x]
  exact realMixedPerturbation_adjoint _ _ _ _ _ _ lam

/-- The Hilbert–Schmidt bound for the mixed perturbation of the sample covariance. -/
theorem manuscriptMixedColumns_norm_le (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hδ : ‖featureRegularizedInvSqrt μ k hk lam *
      (empiricalCovariance (fun i => k (x i)) - populationCovariance (featureEmbedding μ k hk)) *
        featureRegularizedInvSqrt μ k hk lam‖ ≤ 1 / 4) :
    ‖manuscriptMixedColumns b k hk lam x‖ ≤
      2 * ‖normalizedHSCovarianceFluctuation b k hk lam x‖ := by
  rw [manuscriptMixedColumns, hsAdjointColumns_norm]
  refine (sampleMixedPerturbationColumns_norm_le b k hk lam hlam x
    (hδ.trans (by norm_num))).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end ActualSample

end KernelSeq
