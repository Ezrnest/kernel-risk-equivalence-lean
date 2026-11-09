import KernelSeq.SpectralInteraction
import KernelSeq.ActualVarianceTransfer
import KernelSeq.EmpiricalEffectiveDimension

/-!
# The actual uniformly filtered right-hand-side bound

The weighted empirical filter is constructed from the original scalar contract,
with its operator norm proved by the actual spectral basis. Actual inverse-root
factorization and the root-transition bound then give the `2 A` estimate used
for bias transfer on a possibly nonseparable prediction Hilbert space.
-/

namespace KernelSeq

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual regularized filter with scalar weight `(t+λ) φ(t)`. Its bounded
profile is proved from the first term of the manuscript's scalar size bound. -/
noncomputable def compactRegularizedFilterOperator (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) : H →L[ℝ] H :=
  compactSpectralMultiplier T hc hp (fun t => (t + lam) * φ t) A
    (h.constant_nonneg hlam ((norm_nonneg T).trans hM))
    (fun _ ht => (h.spectral_size hlam ⟨ht.1, ht.2.trans hM⟩).1)

theorem compactRegularizedFilterOperator_norm_le (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    ‖compactRegularizedFilterOperator T hc hp φ hlam hM h‖ ≤ A :=
  compactSpectralMultiplier_norm_le _ _ _ _ _ _ _

/-- The weighted spectral multiplier is exactly the two-sided root-filter-root
product, including the zero eigenspace and discontinuous original profiles. -/
theorem compactRegularizedFilterOperator_eq_root_filter_root (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    compactRegularizedFilterOperator T hc hp φ hlam hM h =
      compactRegularizedSqrt T hc hp lam * compactFilterOperator T hc hp φ hlam hM h *
        compactRegularizedSqrt T hc hp lam := by
  ext x
  apply (compactEigenbasis T hc hp.isSymmetric).repr.injective
  ext i
  simp only [compactRegularizedFilterOperator, compactFilterOperator, mul_apply_eq_comp,
    compactSpectralMultiplier_repr, compactRegularizedSqrt_repr]
  have hs := Real.sq_sqrt (add_nonneg (compactEigenvalue_nonneg T hc hp i) hlam.le)
  calc
    ((i.1 + lam) * φ i.1) * (compactEigenbasis T hc hp.isSymmetric).repr x i =
        (Real.sqrt (i.1 + lam)) ^ 2 * φ i.1 *
          (compactEigenbasis T hc hp.isSymmetric).repr x i := by rw [hs]
    _ = _ := by ring

/-- The original filter is recovered exactly using the actual inverse roots. -/
theorem compactFilterOperator_eq_invSqrt_regularizedFilter_invSqrt (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hM : ‖T‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    compactFilterOperator T hc hp φ hlam hM h =
      compactRegularizedInvSqrt T hc hp lam *
        compactRegularizedFilterOperator T hc hp φ hlam hM h *
          compactRegularizedInvSqrt T hc hp lam := by
  symm
  rw [compactRegularizedFilterOperator_eq_root_filter_root]
  calc
    _ = (compactRegularizedInvSqrt T hc hp lam * compactRegularizedSqrt T hc hp lam) *
        compactFilterOperator T hc hp φ hlam hM h *
          (compactRegularizedSqrt T hc hp lam * compactRegularizedInvSqrt T hc hp lam) := by
      simp only [mul_assoc]
    _ = _ := by rw [compactRegularizedInvSqrt_mul_sqrt T hc hp lam hlam,
      compactRegularizedSqrt_mul_invSqrt T hc hp lam hlam, one_mul, mul_one]

section Prediction

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual prediction map after the population inverse root is a contraction. -/
theorem prediction_population_invSqrt_norm_le (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (lam : ℝ) (hlam : 0 < lam) :
    ‖S.comp (compactRegularizedInvSqrt (S.adjoint.comp S) hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam)‖ ≤ 1 := by
  let R := compactRegularizedInvSqrt (S.adjoint.comp S) hc
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam
  have heq : (S.comp R).adjoint.comp (S.comp R) =
      compactNormalizedCovariance (S.adjoint.comp S) hc
        (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam := by
    simp only [R, compactNormalizedCovariance, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp,
      (compactRegularizedInvSqrt_isSelfAdjoint (S.adjoint.comp S) hc
        (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam).adjoint_eq,
      ContinuousLinearMap.comp_assoc]
  have hsq : ‖S.comp R‖ ^ 2 ≤ 1 := by
    calc
      ‖S.comp R‖ ^ 2 = ‖(S.comp R).adjoint.comp (S.comp R)‖ := by
        rw [ContinuousLinearMap.norm_adjoint_comp_self, pow_two]
      _ = _ := congrArg norm heq
      _ ≤ 1 := compactNormalizedCovariance_norm_le_one _ _ _ lam hlam
  change ‖S.comp R‖ ≤ 1
  nlinarith [norm_nonneg (S.comp R)]

/-- The actual empirical inverse-root prediction factor is bounded by `sqrt 2`
on the covariance good event. The factorization is derived from root cancellation. -/
theorem prediction_empirical_invSqrt_norm_le (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (TX : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation (S.adjoint.comp S) TX hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam‖ ≤ 1 / 2) :
    ‖S.comp (compactRegularizedInvSqrt TX hcX hpX lam)‖ ≤ Real.sqrt 2 := by
  let R := compactRegularizedInvSqrt (S.adjoint.comp S) hc
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam
  let Q := compactRegularizedSqrt (S.adjoint.comp S) hc
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam
  let RX := compactRegularizedInvSqrt TX hcX hpX lam
  let B := rootTransition (S.adjoint.comp S) TX hc hcX
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) hpX lam
  have heq : (S.comp R).comp B = S.comp RX := by
    calc
      (S.comp R).comp B = S.comp ((R * Q).comp RX) := by
        simp only [B, rootTransition, Q, RX, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
      _ = _ := by
        rw [show R * Q = 1 from compactRegularizedInvSqrt_mul_sqrt _ _ _ lam hlam]
        rfl
  have hS : ‖S.comp R‖ ≤ 1 := prediction_population_invSqrt_norm_le S hc lam hlam
  have hB : ‖B‖ ≤ Real.sqrt 2 := rootTransition_norm_le _ _ _ _ _ _ lam hlam hδ
  calc
    ‖S.comp RX‖ = ‖(S.comp R).comp B‖ := congrArg norm heq.symm
    _ ≤ ‖S.comp R‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * Real.sqrt 2 := mul_le_mul hS hB (norm_nonneg B) zero_le_one
    _ = _ := one_mul _

/-- The genuine uniform filtered RHS estimate. All factors are constructed
from the original scalar filter contract and actual adjoint-product covariance. -/
theorem filtered_rhs_bound (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (TX : H →L[ℝ] H)
    (hcX : IsCompactOperator TX) (hpX : TX.IsPositive) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) (hMX : ‖TX‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ)
    (hδ : ‖realNormalizedPerturbation (S.adjoint.comp S) TX hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam‖ ≤ 1 / 2) (Z : H) :
    ‖S (compactFilterOperator TX hcX hpX φ hlam hMX h Z)‖ ≤
      2 * A * ‖compactRegularizedInvSqrt (S.adjoint.comp S) hc
        (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam Z‖ := by
  let R := compactRegularizedInvSqrt (S.adjoint.comp S) hc
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) lam
  let RX := compactRegularizedInvSqrt TX hcX hpX lam
  let F := compactRegularizedFilterOperator TX hcX hpX φ hlam hMX h
  have hA : 0 ≤ A := h.constant_nonneg hlam ((norm_nonneg TX).trans hMX)
  have hF : ‖F‖ ≤ A := compactRegularizedFilterOperator_norm_le TX hcX hpX φ hlam hMX h
  have hSRX : ‖S.comp RX‖ ≤ Real.sqrt 2 :=
    prediction_empirical_invSqrt_norm_le S hc TX hcX hpX lam hlam hδ
  have hsquare := invSqrt_apply_norm_sq_le_two (S.adjoint.comp S) TX hc hcX
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) hpX lam hlam hδ Z
  have hRX : ‖RX Z‖ ≤ Real.sqrt 2 * ‖R Z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hsquare
  have hfac : compactFilterOperator TX hcX hpX φ hlam hMX h = RX * F * RX :=
    compactFilterOperator_eq_invSqrt_regularizedFilter_invSqrt TX hcX hpX φ hlam hMX h
  calc
    ‖S (compactFilterOperator TX hcX hpX φ hlam hMX h Z)‖ = ‖S (RX (F (RX Z)))‖ := by
      rw [hfac]
      rfl
    _ ≤ Real.sqrt 2 * ‖F (RX Z)‖ := (S.comp RX).le_of_opNorm_le hSRX _
    _ ≤ Real.sqrt 2 * (A * ‖RX Z‖) :=
      mul_le_mul_of_nonneg_left (F.le_of_opNorm_le hF _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt 2 * (A * (Real.sqrt 2 * ‖R Z‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRX hA) (Real.sqrt_nonneg _)
    _ = 2 * A * ‖R Z‖ := by
      calc
        _ = (Real.sqrt 2 * Real.sqrt 2) * (A * ‖R Z‖) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

end Prediction

section ActualFeature

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual feature/sample specialization of the uniform RHS estimate.
Only the empirical spectral bound is needed for this term; the prediction
space is the full `L²(μ)` and is not assumed separable. -/
theorem actual_filtered_rhs_bound (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ)
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 2) (Z : H) :
    ‖featureEmbedding μ k hk
      (compactFilterOperator (empiricalCovariance (fun i => k (x i)))
        (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX h Z)‖ ≤
      2 * A * ‖featureRegularizedInvSqrt μ k hk lam Z‖ := by
  exact filtered_rhs_bound (featureEmbedding μ k hk) (populationCovariance_feature_isCompact μ k hk)
    (empiricalCovariance (fun i => k (x i))) (empiricalCovariance_isCompact _)
    (empiricalCovariance_isPositive _) φ hlam hMX h hδ Z

/-- The precise actual RHS-fluctuation term on the manuscript's quarter event.
The deterministic population solution may be substituted for `g`; no RHS or
regularized-filter certificate is assumed. -/
theorem actual_filtered_rhsFluctuation_bound (k : X → H) (hk : MemLp k 2 μ) (φ : ℝ → ℝ)
    {lam M ρ A : ℝ} (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hMX : ‖empiricalCovariance (fun i => k (x i))‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ)
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4) (f : Lp ℝ 2 μ) (g : H) :
    ‖featureEmbedding μ k hk
      (compactFilterOperator (empiricalCovariance (fun i => k (x i)))
        (empiricalCovariance_isCompact _) (empiricalCovariance_isPositive _) φ hlam hMX h
          (rhsFluctuation k hk f g x))‖ ≤
      2 * A * ‖normalizedRHS k hk lam f g x‖ := by
  exact actual_filtered_rhs_bound k hk φ hlam x hMX h (hδ.trans (by norm_num))
    (rhsFluctuation k hk f g x)

end ActualFeature

end KernelSeq
