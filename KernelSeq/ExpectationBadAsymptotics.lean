import KernelSeq.ExpectationBadRisk
import KernelSeq.ExpectationBadNormalization
import KernelSeq.ExpectationDimension
import KernelSeq.ExpectationScale
import KernelSeq.ExpectationCovarianceScales
import KernelSeq.ExpectationCovarianceTail
import KernelSeq.OriginalScaleParameters

/-!
# Actual bad-design risk vanishes at the original expectation scale

The actual leave-one-out events, their independent target-square integrals,
their proved covariance tails and the actual global estimator envelope are
combined here. Only the original model, filter, support, variance compatibility
and additional logarithmic expectation scale remain. There is no probability,
integrability, leave-one-out, or bad-risk estimate supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace KernelSeq
noncomputable section

variable {H X Ω J : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {l : Filter J}

/-- Negligible normalized risk on the actual fixed-quarter bad design event,
with all event and analytic estimates proved internally. -/
theorem rkhs_bad_risk_from_original_expectation_scale
    (hK : Measurable (fun p : X × X => rkhsKernel (X := X) (H := H) p.1 p.2))
    (κ : ℝ) (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (X := X) (H := H) x x ≤ κ ^ 2)
    (n : J → ℕ) (hn : ∀ i, 0 < n i) (Z : (i : J) → Fin (n i) → Ω → X × ℝ)
    (hZ : ∀ i j, Measurable (Z i j))
    (hlaw : ∀ i j, MeasurePreserving (fun ω => (Z i j ω).1) P μ)
    (hind : ∀ i, iIndepFun (Z i) P) (f : Lp ℝ 2 μ) (σ : ℝ) (hσ : 0 < σ)
    (hmean : ∀ i j, P[observationNoise (Z i j) (lpRepresentative f) |
      observationDesignSigma (Z i j)] =ᵐ[P] (fun _ => 0))
    (hsecond : ∀ i j, P[(fun ω => observationNoise (Z i j) (lpRepresentative f) ω ^ 2) |
      observationDesignSigma (Z i j)] =ᵐ[P] (fun _ => σ ^ 2))
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i) {ρ A : ℝ} (φ : J → ℝ → ℝ)
    (hf : ∀ i, ResidualFilter.SpectralFilter (κ ^ 2) (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) (κ ^ 2) ρ A (φ i)) :
    let k := rkhsFeature (X := X) (H := H)
    let hk := rkhsFeature_memLp μ hK κ hκ hdiag
    let L := fun i => featureLeverageEssentialSup k hk (lam i)
    let Q := fun i => featureFilterDimension k hk (φ i)
    f ∈ (predictionCovariance (featureEmbedding μ k hk)).range.topologicalClosure →
    (∀ᶠ i in l, 0 < Q i) →
    Tendsto (fun i => featureEffectiveDimension k hk (lam i) / Q i * Real.sqrt
      (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0) →
    Tendsto (fun i => L i / (n i : ℝ) *
      Real.log (Real.exp 1 + (n i : ℝ) / (lam i * Q i))) l (𝓝 0) →
    Tendsto (fun i =>
      (∫ ω in {ω | 1 / 4 < actualCovarianceDeviation k hk (lam i) (fun j => (Z i j ω).1)},
        rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag (hn i) (Z i) f
          (φ i) (hlam i) (h i) ω ∂P) / sequenceBenchmark k hk (φ i) f σ (n i)) l (𝓝 0) := by
  dsimp only
  intro hsupport hQ hcompat hexpect
  let k := rkhsFeature (X := X) (H := H)
  let hk := rkhsFeature_memLp μ hK κ hκ hdiag
  let hM := rkhs_population_covariance_bound (μ := μ) hK κ hκ hdiag
  let L := fun i => featureLeverageEssentialSup k hk (lam i)
  let Q := fun i => featureFilterDimension k hk (φ i)
  let x := fun i j ω => (Z i j ω).1
  let B := fun i => {ω | 1 / 4 < actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)}
  let Bi := fun i j => leaveOneOutCovarianceBad k hk (lam i) j (x i)
  let p := fun i => 8 * Real.exp (-(1 / 65536 : ℝ) * (n i : ℝ) / L i)
  let F := 2 * ‖f‖ ^ 2
  let K := (A * κ ^ 2) ^ 2 * (2 * ‖f‖ ^ 2 + σ ^ 2)
  let D := fun i => sequenceBenchmark k hk (φ i) f σ (n i)
  have hκsq : ∀ᵐ y ∂μ, ‖k y‖ ^ 2 ≤ κ ^ 2 := Eventually.of_forall fun y =>
    pow_le_pow_left₀ (norm_nonneg _) (rkhsFeature_norm_le κ hκ hdiag y) 2
  have hL (i : J) : ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i :=
    normalizedLeverage_ae_le_essentialSup k hk (hlam i) hκsq
  have hxind (i : J) : iIndepFun (x i) P :=
    (hind i).comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  have hlimits := feature_variance_compatibility_expectation_covariance_limits
    n hn k hk lam hlam φ hM hf h L hL hQ hcompat
  have hsmall := feature_variance_compatibility_eventually_covariance_small
    n hn k hk lam hlam φ hM hf h L hL hQ hcompat
  have hrpos : ∀ᶠ i in l, 0 < featureCovarianceRetention k hk (lam i) := hQ.mono fun i hi =>
    featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hi
  have hLpos : ∀ᶠ i in l, 0 < L i := by
    filter_upwards [hrpos] with i hi
    apply hi.trans_le
    rw [← bernsteinFeature_covariance_norm k hk (lam i)]
    exact populationCovariance_norm_le_feature_bound _ (bernsteinFeature_memLp k hk (lam i)) (hL i)
  have hQL : ∀ᶠ i in l, Q i ≤ A ^ 2 * L i := Eventually.of_forall fun i =>
    (featureFilterDimension_le_effectiveDimension k hk (φ i) (hlam i) hM (hf i) (h i)).trans
      (mul_le_mul_of_nonneg_left (featureEffectiveDimension_le_essentialSup k hk (hlam i) hκsq)
        (sq_nonneg A))
  have hQn := eventually_filterDimension_le_sample_of_le Q L (fun i => (n i : ℝ))
    (sq_nonneg A) (hQ.mono fun _ hi => hi.le)
    (Eventually.of_forall fun i => Nat.cast_pos.mpr (hn i)) hQL hlimits.1
  have hpoly := expectation_scale_global_envelope_tail_of_square_bound L (fun i => (n i : ℝ))
    lam Q (B := A ^ 2 * κ ^ 4) (by positivity) hLpos
    (Eventually.of_forall fun i => by exact_mod_cast hn i)
    (Eventually.of_forall hlam) hQ hQn
    (Eventually.of_forall fun i =>
      lambda_sq_mul_featureFilterDimension_le_sq_bound k hk (φ i) κ hκsq (hlam i) hM (hf i) (h i))
    hexpect (c := (1 / 65536 : ℝ)) (by norm_num)
  have hu := hpoly.const_mul (8 * ((F + K) / σ ^ 2))
  simp only [mul_zero] at hu
  have hp (i : J) : 0 ≤ p i := by dsimp only [p]; positivity
  have heqp (i : J) : 8 * Real.exp (-(n i : ℝ) / (65536 * L i)) = p i := by
    dsimp only [p]
    congr 2
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  apply squeeze_zero' _ _ hu
  · filter_upwards [hQ] with i hi
    have hD : 0 < D i := by
      dsimp only [D]
      rw [sequenceBenchmark_eq_population k hk (φ i) hM (hf i) hsupport σ (n i)]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos (div_pos (sq_pos_of_pos hσ) (Nat.cast_pos.mpr (hn i))) hi)
    exact div_nonneg
      (integral_nonneg_of_ae (ae_restrict_of_ae
        (rkhsConditionalPredictionRisk_nonneg_ae (P := P) hK κ hκ hdiag (hn i) (Z i) f
          (φ i) (hlam i) (h i)))) hD.le
  · filter_upwards [hQ, hsmall, hrpos] with i hiQ hiSmall hir
    have hPb : P.real (B i) ≤ p i := by
      have ht := actual_bad_design_exponential_tail k hk (hlam i) (hn i) (x i) (hlaw i)
        (hxind i) (hL i) hir hiSmall.2
      rw [heqp i] at ht
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ht).trans_eq (ENNReal.toReal_ofReal (hp i))
    have hPbi (j : Fin (n i)) : P.real (Bi i j) ≤ p i := by
      have ht := leaveOneOutCovarianceBad_exponential_tail k hk (hlam i) (hn i) j (x i)
        (hlaw i) (hxind i) (hL i) hir hiSmall.2
      rw [heqp i] at ht
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top ht).trans_eq (ENNReal.toReal_ofReal (hp i))
    have hupper := integral_rkhs_conditional_risk_bad_le hK κ hκ hdiag (hn i) (Z i) (hZ i)
      (hlaw i) f σ hσ (hind i) (hmean i) (hsecond i) (φ i) (hlam i) (hf i) (h i)
      (B i) (Bi i)
      (fun j => measurableSet_otherPairs_leaveOneOutCovarianceBad k hk
        (rkhsFeature_stronglyMeasurable hK) (lam i) j (Z i))
      (fun j => actual_bad_design_subset_leaveOneOut_ae k hk (hlam i) (hn i) j (x i)
        (hlaw i) (hL i) hiSmall.1) hPb hPbi
    have hupper' : (∫ ω in B i, rkhsConditionalPredictionRisk (P := P) hK κ hκ hdiag
        (hn i) (Z i) f (φ i) (hlam i) (h i) ω ∂P) ≤ (F + K / lam i ^ 2) * p i := by
      convert hupper using 1
      dsimp only [F, K]
      ring
    have hD : σ ^ 2 / (n i : ℝ) * Q i ≤ D i := by
      dsimp only [D]
      rw [sequenceBenchmark_eq_population k hk (φ i) hM (hf i) hsupport σ (n i)]
      exact le_add_of_nonneg_left (sq_nonneg _)
    have hb := normalize_bad_risk_envelope_le (Nat.cast_pos.mpr (hn i)) (hlam i) hiQ hσ
      (by dsimp only [F]; positivity) (by dsimp only [K]; positivity) (hp i) hD hupper'
    exact hb.trans_eq (by dsimp only [p]; ring)

end
end KernelSeq
