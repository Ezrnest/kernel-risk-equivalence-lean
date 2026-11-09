import KernelSeq.UniformGoodMoments

/-!
# Common-constant finite-row good-event variance bound

The actual normalized variance error is bounded by `C (c+c²)`, where `c`
is the original variance-compatibility scale. Constants depend only on the
common residual-filter parameters. Both scalar smallness requirements hold
eventually under the original compatibility, with no lower bound on retention
or effective dimension and no stochastic moment certificate in the input.
-/

open MeasureTheory ProbabilityTheory

namespace KernelSeq
noncomputable section

def uniformVarianceRiskConstant (ρ A : ℝ) : ℝ :=
  4 * (1 + A ^ 2) * ((5 / 4 : ℝ) * (2 * A * (1 + ρ)) ^ 2 * A ^ 2 +
    (2 * A * (1 + ρ)) * A + Real.sqrt uniformCovarianceMomentConstant * (A ^ 2 + 4))

theorem uniformVarianceRiskConstant_nonneg {ρ A : ℝ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A) :
    0 ≤ uniformVarianceRiskConstant ρ A := by unfold uniformVarianceRiskConstant; positivity

private theorem uniform_variance_scalar_bound {L n N Q r A ρ D : ℝ}
    (hL : 0 ≤ L) (hn : 0 < n) (hN : 0 < N) (hQ : 0 < Q)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrN : r ≤ N) (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (hcomp : Q ≤ A ^ 2 * r * N)
    (hD : D ≤ uniformCovarianceMomentConstant * (L * dimensionLog N / n))
    (hsmall : A ^ 4 * (N / Q * Real.sqrt (L * dimensionLog N / n)) ^ 2 ≤ 1) :
    let H := L / n * N
    let K := 2 * A * (1 + ρ)
    let c := N / Q * Real.sqrt (L * dimensionLog N / n)
    (4 * (1 + A ^ 2)) * ((5 / 4 : ℝ) * K ^ 2 * H / Q +
      K * Real.sqrt H / Real.sqrt Q + Real.sqrt D +
      Real.sqrt D * Real.sqrt (4 * (N ^ 2 + H)) / Q) ≤
      uniformVarianceRiskConstant ρ A * (c + c ^ 2) := by
  dsimp only
  let v := L * dimensionLog N / n
  let H := L / n * N
  let K := 2 * A * (1 + ρ)
  let c := N / Q * Real.sqrt v
  have hv : 0 ≤ v := div_nonneg (mul_nonneg hL (zero_le_one.trans (one_le_dimensionLog hN.le))) hn.le
  have hH : 0 ≤ H := mul_nonneg (div_nonneg hL hn.le) hN.le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hc : 0 ≤ c := mul_nonneg (div_nonneg hN.le hQ.le) (Real.sqrt_nonneg _)
  have hrootv : Real.sqrt v ≤ A ^ 2 * c := (variance_compatibility_sqrt_bounds hQ hr hr1 hcomp).1
  have hHdiv : H / Q ≤ A ^ 2 * c ^ 2 := by
    have heq : c * Real.sqrt v = H / Q * dimensionLog N := by
      dsimp only [c]
      rw [mul_assoc, ← pow_two, Real.sq_sqrt hv]
      dsimp only [H, v]
      ring
    have hb : H / Q ≤ c * Real.sqrt v := by
      rw [heq]
      exact le_mul_of_one_le_right (div_nonneg hH hQ.le) (one_le_dimensionLog hN.le)
    have ht := mul_le_mul_of_nonneg_left hrootv hc
    nlinarith
  have hHroot : Real.sqrt H / Real.sqrt Q ≤ A * c := by
    have hs : Real.sqrt (H / Q) ≤ Real.sqrt ((A * c) ^ 2) :=
      Real.sqrt_le_sqrt (hHdiv.trans_eq (by ring))
    rwa [Real.sqrt_div hH Q, Real.sqrt_sq (mul_nonneg hA hc)] at hs
  have hHsmall : H ≤ N ^ 2 := by
    have hs := (variance_compatibility_leverage_div_dimension_le hL hn hN hQ hr hr1 hrN hcomp).trans hsmall
    have hLn : L / n ≤ N := (div_le_iff₀ hn).mpr (by nlinarith [(div_le_one (mul_pos hn hN)).mp hs])
    dsimp only [H]
    nlinarith [mul_le_mul_of_nonneg_right hLn hN.le]
  have hDs : Real.sqrt D ≤ Real.sqrt uniformCovarianceMomentConstant * Real.sqrt v := by
    simpa only [Real.sqrt_mul uniformCovarianceMomentConstant_nonneg] using Real.sqrt_le_sqrt hD
  have hDsmall : Real.sqrt D ≤ Real.sqrt uniformCovarianceMomentConstant * A ^ 2 * c := by
    exact hDs.trans ((mul_le_mul_of_nonneg_left hrootv
      (Real.sqrt_nonneg uniformCovarianceMomentConstant)).trans_eq (by ring))
  have hNs : Real.sqrt (4 * (N ^ 2 + H)) ≤ 4 * N := by
    have hs : 4 * (N ^ 2 + H) ≤ (4 * N) ^ 2 := by nlinarith [sq_nonneg N]
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 4 * N)] using Real.sqrt_le_sqrt hs
  have hcross : Real.sqrt D * Real.sqrt (4 * (N ^ 2 + H)) / Q ≤
      4 * Real.sqrt uniformCovarianceMomentConstant * c := by
    exact (div_le_div_of_nonneg_right (mul_le_mul hDs hNs (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hQ.le).trans_eq (by dsimp only [c]; ring)
  have h₁ : (5 / 4 : ℝ) * K ^ 2 * H / Q ≤ (5 / 4 : ℝ) * K ^ 2 * A ^ 2 * c ^ 2 := by
    simpa only [mul_div_assoc, mul_assoc] using
      mul_le_mul_of_nonneg_left hHdiv (by positivity : 0 ≤ (5 / 4 : ℝ) * K ^ 2)
  have h₂ : K * Real.sqrt H / Real.sqrt Q ≤ K * A * c := by
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hHroot hK
  let B₂ := (5 / 4 : ℝ) * K ^ 2 * A ^ 2
  let B₁ := K * A + Real.sqrt uniformCovarianceMomentConstant * (A ^ 2 + 4)
  have hB₂ : 0 ≤ B₂ := by dsimp only [B₂]; positivity
  have hB₁ : 0 ≤ B₁ := by dsimp only [B₁]; positivity
  have hb : (5 / 4 : ℝ) * K ^ 2 * H / Q + K * Real.sqrt H / Real.sqrt Q + Real.sqrt D +
      Real.sqrt D * Real.sqrt (4 * (N ^ 2 + H)) / Q ≤ B₂ * c ^ 2 + B₁ * c := by
    dsimp only [B₂, B₁]
    nlinarith
  calc
    _ ≤ (4 * (1 + A ^ 2)) * (B₂ * c ^ 2 + B₁ * c) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (4 * (1 + A ^ 2)) * ((B₂ + B₁) * (c + c ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg hB₂ hc, mul_nonneg hB₁ (sq_nonneg c)]
    _ = _ := by dsimp only [uniformVarianceRiskConstant, B₂, B₁, K, c, v]; ring

variable {ι H X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- A genuine finite-row variance bound with one constant common to all
models. Actual covariance, HS and effective-dimension moments are supplied
internally; only the two displayed deterministic smallness tests remain. -/
theorem setIntegral_actual_good_variance_uniform_row (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (hind : iIndepFun x P)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (φ : ℝ → ℝ) {lam M ρ A L : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hMX : ∀ ω, ‖empiricalCovariance (fun j => k (x j ω))‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hQ : 0 < featureFilterDimension k hk φ)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hlinear : Real.sqrt (L * dimensionLog (featureEffectiveDimension k hk lam) / (n : ℝ)) *
      intrinsicDimensionLog (featureEffectiveDimension k hk lam) (featureCovarianceRetention k hk lam) /
        dimensionLog (featureEffectiveDimension k hk lam) ≤ 1)
    (hcompat : A ^ 4 * (featureEffectiveDimension k hk lam / featureFilterDimension k hk φ *
      Real.sqrt (L * dimensionLog (featureEffectiveDimension k hk lam) / (n : ℝ))) ^ 2 ≤ 1) :
    let Q := featureFilterDimension k hk φ
    let c := featureEffectiveDimension k hk lam / Q *
      Real.sqrt (L * dimensionLog (featureEffectiveDimension k hk lam) / (n : ℝ))
    (∫ ω in {ω | actualCovarianceDeviation k hk lam (fun j => x j ω) ≤ 1 / 4},
      |actualVarianceEnergy k hk φ hlam (fun j => x j ω) (hMX ω) h - Q| / Q ∂P) ≤
      uniformVarianceRiskConstant ρ A * (c + c ^ 2) := by
  dsimp only
  let G := {ω | actualCovarianceDeviation k hk lam (fun j => x j ω) ≤ 1 / 4}
  have hG : MeasurableSet G := measurableSet_le
    (stronglyMeasurable_actualCovarianceDeviation k hk lam x
      (fun j => hks.comp_measurable (hlaw j).measurable)).measurable measurable_const
  have hd := integral_actualCovarianceDeviation_sq_le_uniform_row b hn x hlaw hind k hk φ hlam hM hf h hQ hL hlinear
  have hb := (setIntegral_actual_variance_relative_le_covariance_moment hn x hlaw
    (fun _ _ hij => hind.indepFun hij) k hk hks φ hlam hM hMX hf h hQ hL G hG (fun _ hω => hω)
      (memLp_actualCovarianceDeviation b hn x hlaw k hk lam hL)).2
  refine hb.trans ?_
  exact uniform_variance_scalar_bound
    (feature_sq_bound_nonneg (bernsteinFeature k hk lam) hL) (Nat.cast_pos.mpr hn)
    (featureEffectiveDimension_pos_of_filterDimension_pos k hk φ hlam hM hf h hQ) hQ
    (featureCovarianceRetention_pos_of_filterDimension_pos k hk φ hlam hM hf h hQ)
    (featureCovarianceRetention_le_one k hk lam hlam)
    (featureCovarianceRetention_le_effectiveDimension k hk lam hlam)
    (h.constant_nonneg hlam ((norm_nonneg _).trans hM)) h.rho_pos.le
    (featureFilterDimension_le_retention k hk φ hlam hM hf h) hd hcompat

end
end KernelSeq
