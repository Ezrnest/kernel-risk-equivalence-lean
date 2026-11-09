import KernelSeq.RealRHSFluctuation
import KernelSeq.PopulationCovariance
import KernelSeq.RealOperatorRoots

/-!
# Feature symmetries preserve the actual regularized leverage

The covariance commutation is proved by a genuine measure-preserving change
of variables in its Bochner integral. The leverage is identified with the
actual resolvent quadratic form, so no commutation of a chosen eigenbasis or
an inverse-square-root symmetry certificate is needed.
-/

namespace KernelSeq
open MeasureTheory
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem populationCovariance_commutes_featureSymmetry (k : X → H) (hk : MemLp k 2 μ)
    (r : X ≃ᵐ X) (hr : MeasurePreserving r μ μ) (U : H ≃ₗᵢ[ℝ] H)
    (hkr : ∀ x, k (r x) = U (k x)) :
    Commute (populationCovariance (featureEmbedding μ k hk)) U.toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro h
  change populationCovariance (featureEmbedding μ k hk) (U h) =
    U (populationCovariance (featureEmbedding μ k hk) h)
  rw [populationCovariance_feature_apply, populationCovariance_feature_apply]
  calc
    _ = ∫ x, inner ℝ (k (r x)) (U h) • k (r x) ∂μ :=
      (hr.integral_comp r.measurableEmbedding _).symm
    _ = ∫ x, U (inner ℝ (k x) h • k x) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change inner ℝ (k (r x)) (U h) • k (r x) = U (inner ℝ (k x) h • k x)
        rw [hkr, U.inner_map_map, map_smul]
    _ = _ := U.toLinearIsometry.integral_comp_comm _

/-- True leverage equals the resolvent energy of the true feature vector. -/
theorem normalizedLeverage_eq_resolvent_inner (k : X → H) (hk : MemLp k 2 μ)
    {lam : ℝ} (hlam : 0 < lam) (x : X) :
    normalizedLeverage k hk lam x = inner ℝ (k x)
      (Ring.inverse (populationCovariance (featureEmbedding μ k hk) + lam • (1 : H →L[ℝ] H)) (k x)) := by
  let R := featureRegularizedInvSqrt μ k hk lam
  have ha : R.adjoint = R := (featureRegularizedInvSqrt_isSelfAdjoint k hk lam).adjoint_eq
  have hsq := compactRegularizedInvSqrt_sq (populationCovariance (featureEmbedding μ k hk))
    (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)) lam hlam
  change ‖R (k x)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, ← R.adjoint_inner_right, ha]
  change inner ℝ (k x) ((R * R) (k x)) = _
  have hsqR : R * R = Ring.inverse
      (populationCovariance (featureEmbedding μ k hk) + lam • (1 : H →L[ℝ] H)) := hsq
  rw [hsqR]

omit [CompleteSpace H] in
private theorem commute_ringInverse_right {A B : H →L[ℝ] H} (hA : IsUnit A) (hAB : Commute A B) :
    Commute (Ring.inverse A) B := by
  change Ring.inverse A * B = B * Ring.inverse A
  calc
    _ = Ring.inverse A * B * (A * Ring.inverse A) := by rw [Ring.mul_inverse_cancel A hA, mul_one]
    _ = Ring.inverse A * (B * A) * Ring.inverse A := by simp only [mul_assoc]
    _ = Ring.inverse A * (A * B) * Ring.inverse A := by rw [hAB.eq]
    _ = _ := by rw [← mul_assoc (Ring.inverse A) A, Ring.inverse_mul_cancel A hA, one_mul]

/-- Invariance is derived from the actual covariance integral and resolvent;
no inverse-root equivariance or constant-leverage conclusion is an input. -/
theorem normalizedLeverage_featureSymmetry (k : X → H) (hk : MemLp k 2 μ)
    (r : X ≃ᵐ X) (hr : MeasurePreserving r μ μ) (U : H ≃ₗᵢ[ℝ] H)
    (hkr : ∀ x, k (r x) = U (k x)) {lam : ℝ} (hlam : 0 < lam) (x : X) :
    normalizedLeverage k hk lam (r x) = normalizedLeverage k hk lam x := by
  let T := populationCovariance (featureEmbedding μ k hk)
  have hTU := populationCovariance_commutes_featureSymmetry k hk r hr U hkr
  have hA : IsUnit (T + lam • (1 : H →L[ℝ] H)) :=
    regularized_isUnit_real T ((ContinuousLinearMap.nonneg_iff_isPositive T).2
      (populationCovariance_isPositive (featureEmbedding μ k hk))) lam hlam
  have hAU : Commute (T + lam • (1 : H →L[ℝ] H)) U.toLinearIsometry.toContinuousLinearMap := by
    change (T + lam • (1 : H →L[ℝ] H)) * U.toLinearIsometry.toContinuousLinearMap =
      U.toLinearIsometry.toContinuousLinearMap * (T + lam • (1 : H →L[ℝ] H))
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hTU.eq]
  have hRU := commute_ringInverse_right hA hAU
  rw [normalizedLeverage_eq_resolvent_inner k hk hlam,
    normalizedLeverage_eq_resolvent_inner k hk hlam, hkr]
  have hh := congrArg (fun C : H →L[ℝ] H => C (k x)) hRU.eq
  change Ring.inverse (T + lam • (1 : H →L[ℝ] H)) (U (k x)) =
    U (Ring.inverse (T + lam • (1 : H →L[ℝ] H)) (k x)) at hh
  rw [hh, U.inner_map_map]

end
end KernelSeq
