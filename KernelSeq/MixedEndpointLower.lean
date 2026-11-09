import KernelSeq.SchattenAsymptotics
import KernelSeq.TopEigenCompression

/-!
# Lower bounds for actual Schatten endpoints and mixed perturbations

The true top singular value of a compact HS operator proves that every finite
Schatten norm dominates its operator norm. Hence the optimized `p S_p`
endpoint dominates twice the operator norm. A reverse regularized-root
transition then controls the actual normalized covariance error by that actual
mixed-perturbation endpoint on its covariance good event.

No Schatten domination, reverse factorization, or top-eigenvector certificate
is a premise. The zero operator and an empty basis-index type are handled
without selecting a nonexistent singular vector. No separability is assumed.
-/

namespace KernelSeq

variable {ι H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual finite Schatten norm dominates the actual operator norm. A top
singular coordinate is derived from compactness only in the nonzero branch. -/
theorem opNorm_le_hsSchattenNorm (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    ‖hilbertSchmidtOperator b c‖ ≤ hsSchattenNorm b c p := by
  have hp0 : 0 < p := by linarith
  by_cases hz : ‖hilbertSchmidtOperator b c‖ = 0
  · rw [hz]
    exact Real.rpow_nonneg (tsum_nonneg
      (fun i : HSSingularIndex b c => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _)) _
  · have hpos : 0 < ‖hilbertSchmidtOperator b c‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hnorm : ‖hsSingularCovariance b c‖ = ‖hilbertSchmidtOperator b c‖ ^ 2 := by
      simp only [hsSingularCovariance, ContinuousLinearMap.norm_adjoint_comp_self, pow_two]
    have hcovpos : 0 < ‖hsSingularCovariance b c‖ := by rw [hnorm]; positivity
    obtain ⟨j, hj⟩ := exists_compactEigenvalue_eq_norm (hsSingularCovariance b c)
      (hsSingularCovariance_isCompact b c) (hsSingularCovariance_isPositive b c) hcovpos
    have hterm : (‖hilbertSchmidtOperator b c‖ ^ 2) ^ (p / 2) ≤
        ∑' i : HSSingularIndex b c, i.1 ^ (p / 2) := by
      rw [← hnorm, ← hj]
      exact (summable_hsSingularPower b c hp).le_tsum j
        (fun i _ => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _)
    have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (sq_nonneg _) _) hterm
      (one_div_nonneg.mpr hp0.le)
    have hid : ((‖hilbertSchmidtOperator b c‖ ^ 2) ^ (p / 2)) ^ (1 / p) =
        ‖hilbertSchmidtOperator b c‖ := by
      rw [← Real.rpow_natCast ‖hilbertSchmidtOperator b c‖ 2,
        ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _)]
      norm_num only [Nat.cast_ofNat]
      rw [show ((2 : ℝ) * (p / 2)) * (1 / p) = 1 by field_simp, Real.rpow_one]
    rw [hid] at hroot
    exact hroot

/-- The optimized actual endpoint controls twice the actual operator norm,
including the zero operator and arbitrary Hilbert-basis index types. -/
theorem two_opNorm_le_hsSchattenEndpoint (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) :
    2 * ‖hilbertSchmidtOperator b c‖ ≤ hsSchattenEndpoint b c := by
  apply le_csInf
  · exact ⟨_, Set.mem_range_self (⟨2, le_rfl⟩ : {p : ℝ // 2 ≤ p})⟩
  · rintro _ ⟨p, rfl⟩
    exact (mul_le_mul_of_nonneg_right p.2 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (opNorm_le_hsSchattenNorm b c p.2) (by linarith [p.2]))

section ReverseTransition

/-- The actual reverse root transition from population-normalized coordinates
into empirical regularized coordinates. -/
noncomputable def reverseRootTransition (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) : H →L[ℝ] H :=
  compactRegularizedSqrt TX hcX hpX lam * compactRegularizedInvSqrt T hc hp lam

/-- The upper relative quadratic comparison bounds the actual reverse
transition. Its hypothesis permits every normalized deviation at most one. -/
theorem reverseRootTransition_norm_le (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1) :
    ‖reverseRootTransition T TX hc hcX hp hpX lam‖ ≤ Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  let y := compactRegularizedInvSqrt T hc hp lam x
  have hq := (compact_regularized_relative_comparison_real T TX hc hp lam hlam y).2
  have hδeq : ‖Ring.inverse (compactRegularizedSqrt T hc hp lam) *
      (TX + lam • (1 : H →L[ℝ] H) - (T + lam • 1)) *
        Ring.inverse (compactRegularizedSqrt T hc hp lam)‖ =
      ‖realNormalizedPerturbation T TX hc hp lam‖ := by
    congr 1
    congr 2
    abel
  rw [hδeq, ← compactRegularizedSqrt_apply_norm_sq T hc hp lam hlam.le,
    ← compactRegularizedSqrt_apply_norm_sq TX hcX hpX lam hlam.le] at hq
  have hx : compactRegularizedSqrt T hc hp lam y = x :=
    congrArg (fun A : H →L[ℝ] H => A x) (compactRegularizedSqrt_mul_invSqrt T hc hp lam hlam)
  rw [hx] at hq
  have hd := mul_le_mul_of_nonneg_right hδ (sq_nonneg ‖x‖)
  change ‖compactRegularizedSqrt TX hcX hpX lam y‖ ≤ Real.sqrt 2 * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

/-- Exact reverse factorization into the actual manuscript-oriented mixed
perturbation. The cancellation uses the constructed empirical regularized
square root and inverse root, rather than an assumed inverse factor. -/
theorem reverseRootTransition_adjoint_mul_mixed (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam) :
    (reverseRootTransition T TX hc hcX hp hpX lam).adjoint *
      manuscriptMixedPerturbation T TX hc hcX hp hpX lam =
      realNormalizedPerturbation T TX hc hp lam := by
  have hadj : (reverseRootTransition T TX hc hcX hp hpX lam).adjoint =
      compactRegularizedInvSqrt T hc hp lam * compactRegularizedSqrt TX hcX hpX lam := by
    simp only [reverseRootTransition, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      (compactRegularizedInvSqrt_isSelfAdjoint T hc hp lam).adjoint_eq,
      (compactRegularizedSqrt_isSelfAdjoint TX hcX hpX lam).adjoint_eq]
  rw [hadj]
  dsimp only [manuscriptMixedPerturbation, realNormalizedPerturbation]
  calc
    _ = compactRegularizedInvSqrt T hc hp lam *
        (compactRegularizedSqrt TX hcX hpX lam * compactRegularizedInvSqrt TX hcX hpX lam) *
          (TX - T) * compactRegularizedInvSqrt T hc hp lam := by simp only [mul_assoc]
    _ = _ := by rw [compactRegularizedSqrt_mul_invSqrt TX hcX hpX lam hlam, mul_one]

/-- Reverse mixed comparison with the direct `sqrt(2)` constant. -/
theorem normalizedPerturbation_norm_le_sqrt_two_mul_mixed (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1) :
    ‖realNormalizedPerturbation T TX hc hp lam‖ ≤
      Real.sqrt 2 * ‖manuscriptMixedPerturbation T TX hc hcX hp hpX lam‖ := by
  rw [← reverseRootTransition_adjoint_mul_mixed T TX hc hcX hp hpX lam hlam]
  refine (norm_mul_le _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_right
    (reverseRootTransition_norm_le T TX hc hcX hp hpX lam hlam hδ) (norm_nonneg _)

/-- The convenient reverse mixed bound with constant two. -/
theorem normalizedPerturbation_norm_le_two_mul_mixed (T TX : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1) :
    ‖realNormalizedPerturbation T TX hc hp lam‖ ≤
      2 * ‖manuscriptMixedPerturbation T TX hc hcX hp hpX lam‖ := by
  refine (normalizedPerturbation_norm_le_sqrt_two_mul_mixed T TX hc hcX hp hpX lam hlam hδ).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Any actual HS reconstruction of the mixed perturbation gives the reverse
normalized-covariance endpoint bound. -/
theorem normalizedPerturbation_norm_le_endpoint (b : HilbertBasis ι ℝ H)
    (T TX : H →L[ℝ] H) (hc : IsCompactOperator T) (hcX : IsCompactOperator TX)
    (hp : T.IsPositive) (hpX : TX.IsPositive) (lam : ℝ) (hlam : 0 < lam)
    (hδ : ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ 1)
    (c : HilbertSchmidtColumns ι H)
    (hcK : hilbertSchmidtOperator b c = manuscriptMixedPerturbation T TX hc hcX hp hpX lam) :
    ‖realNormalizedPerturbation T TX hc hp lam‖ ≤ hsSchattenEndpoint b c := by
  have hK := two_opNorm_le_hsSchattenEndpoint b c
  rw [hcK] at hK
  exact (normalizedPerturbation_norm_le_two_mul_mixed T TX hc hcX hp hpX lam hlam hδ).trans hK

end ReverseTransition

section ActualSample

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The actual sample deviation is absorbed by the actual manuscript mixed
Schatten endpoint on the source quarter event, with constant one. No HS,
reverse-factor, or Schatten-domination premise remains in this specialization. -/
theorem actualCovarianceDeviation_le_manuscriptMixedEndpoint (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) {n : ℕ} (x : Fin n → X)
    (hδ : actualCovarianceDeviation k hk lam x ≤ 1 / 4) :
    actualCovarianceDeviation k hk lam x ≤
      hsSchattenEndpoint b (manuscriptMixedColumns b k hk lam x) := by
  exact normalizedPerturbation_norm_le_endpoint b (populationCovariance (featureEmbedding μ k hk))
    (empiricalCovariance (fun i => k (x i))) (populationCovariance_feature_isCompact μ k hk)
    (empiricalCovariance_isCompact _) (populationCovariance_isPositive _) (empiricalCovariance_isPositive _)
    lam hlam (hδ.trans (by norm_num)) _ (hilbertSchmidtOperator_manuscriptMixedColumns b k hk lam hlam x)

end ActualSample

end KernelSeq
