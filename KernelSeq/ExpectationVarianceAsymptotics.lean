import KernelSeq.ExpectationGoodVariance
import KernelSeq.ExpectationCovarianceScales
import KernelSeq.ExpectationCovarianceMoments

/-!
# Original compatibility controls the actual good-event variance expectation

The source comparison permits both retention and effective dimension to
approach zero. In particular `L/(n N₁) → 0` is a consequence of the original
compatibility, rather than an extra scale assumption. This makes the true
empirical-dimension moment compatible with Cauchy--Schwarz.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace KernelSeq
noncomputable section

/-- The actual normalized covariance norm is at most its genuine integrated
feature energy, with no trace certificate or finite-dimensional restriction. -/
theorem featureCovarianceRetention_le_effectiveDimension
    {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) (hlam : 0 < lam) :
    featureCovarianceRetention k hk lam ≤ featureEffectiveDimension k hk lam := by
  rw [← bernsteinFeature_covariance_norm k hk lam,
    populationCovariance_eq_integral _ (bernsteinFeature_memLp k hk lam)]
  calc
    _ ≤ ∫ y, ‖InnerProductSpace.rankOne ℝ (bernsteinFeature k hk lam y)
        (bernsteinFeature k hk lam y)‖ ∂μ := norm_integral_le_integral_norm _
    _ = _ := by
      simpa only [InnerProductSpace.norm_rankOne, ← pow_two] using
        integral_bernsteinFeature_norm_sq k hk lam hlam

/-- The inverse effective sample size follows from original compatibility.
The extra retention inequality is the genuine `r ≤ N₁` just proved above. -/
theorem variance_compatibility_leverage_div_dimension_le {L n N Q r A : ℝ}
    (hL : 0 ≤ L) (hn : 0 < n) (hN : 0 < N) (hQ : 0 < Q)
    (hr : 0 < r) (hr1 : r ≤ 1) (hrN : r ≤ N) (hcomp : Q ≤ A ^ 2 * r * N) :
    L / (n * N) ≤ A ^ 4 * (N / Q * Real.sqrt (L * dimensionLog N / n)) ^ 2 := by
  let v := L * dimensionLog N / n
  have hell := one_le_dimensionLog hN.le
  have hv : 0 ≤ v := div_nonneg (mul_nonneg hL (by linarith)) hn.le
  have hs := (variance_compatibility_sqrt_bounds (v := v) hQ hr hr1 hcomp).2
  have hs2 := pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg v) hr.le) hs 2
  rw [div_pow, Real.sq_sqrt hv] at hs2
  have hr2 : r ^ 2 ≤ N := by nlinarith
  calc
    _ = (L / n) / N := by ring
    _ ≤ v / N := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right hL hell) hn.le) hN.le
    _ ≤ v / r ^ 2 := div_le_div_of_nonneg_left hv (sq_pos_of_pos hr) hr2
    _ ≤ _ := hs2.trans_eq (by ring)

/-- Original compatibility alone yields the extra scalar ratio used in
the good-event effective-dimension second moment, without a lower bound
on either retention or effective dimension. -/
theorem variance_compatibility_leverage_div_dimension_tendsto_zero
    {I : Type*} {l : Filter I} (L n N Q r : I → ℝ) (A : ℝ)
    (hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < n i ∧ 0 < N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ r i ≤ N i ∧ Q i ≤ A ^ 2 * r i * N i)
    (hcompat : Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0)) :
    Tendsto (fun i => L i / (n i * N i)) l (𝓝 0) := by
  have hu : Tendsto (fun i => A ^ 4 *
      (N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) ^ 2) l (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using (hcompat.pow 2).const_mul (A ^ 4)
  apply squeeze_zero' _ _ hu
  · filter_upwards [hgood] with i hi
    exact div_nonneg hi.1 (mul_pos hi.2.1 hi.2.2.1).le
  · filter_upwards [hgood] with i hi
    rcases hi with ⟨hL, hn, hN, hQ, hr, hr1, hrN, hcomp⟩
    exact variance_compatibility_leverage_div_dimension_le hL hn hN hQ hr hr1 hrN hcomp

private theorem variance_mixed_moment_bound {D H C v N Q : ℝ}
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hQ : 0 < Q)
    (hD : D ≤ C * v) (hH : H ≤ N ^ 2) :
    Real.sqrt D * Real.sqrt (4 * (N ^ 2 + H)) / Q ≤
      (4 * Real.sqrt C) * (N / Q * Real.sqrt v) := by
  have hDs : Real.sqrt D ≤ Real.sqrt C * Real.sqrt v := by
    simpa only [Real.sqrt_mul hC] using Real.sqrt_le_sqrt hD
  have hNs : Real.sqrt (4 * (N ^ 2 + H)) ≤ 4 * N := by
    have hh : 4 * (N ^ 2 + H) ≤ (4 * N) ^ 2 := by nlinarith [sq_nonneg N]
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 4 * N)] using Real.sqrt_le_sqrt hh
  exact (div_le_div_of_nonneg_right (mul_le_mul hDs hNs (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg C) (Real.sqrt_nonneg v))) hQ.le).trans_eq (by ring)

/-- The complete scalar expectation envelope vanishes at the original
variance-compatibility scale. The displayed second-moment majorant is an
intermediate scalar hypothesis; the actual model theorem supplies it from
the locally proved integrated Bernstein estimate. -/
theorem variance_compatibility_expectation_envelope_tendsto_zero
    {I : Type*} {l : Filter I} (L n N Q r D : I → ℝ) (A C CE K : ℝ) (hC : 0 ≤ C)
    (hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < n i ∧ 0 < N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ r i ≤ N i ∧ Q i ≤ A ^ 2 * r i * N i)
    (hD : ∀ᶠ i in l, 0 ≤ D i ∧ D i ≤ C * (L i * dimensionLog (N i) / n i))
    (hcompat : Tendsto (fun i => N i / Q i * Real.sqrt (L i * dimensionLog (N i) / n i)) l (𝓝 0)) :
    Tendsto (fun i => CE * ((5 / 4 : ℝ) * K ^ 2 * (L i / n i * N i) / Q i +
      K * Real.sqrt (L i / n i * N i) / Real.sqrt (Q i) + Real.sqrt (D i) +
      Real.sqrt (D i) * Real.sqrt (4 * (N i ^ 2 + L i / n i * N i)) / Q i)) l (𝓝 0) := by
  let v := fun i => L i * dimensionLog (N i) / n i
  let H := fun i => L i / n i * N i
  have hb : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < n i ∧ 0 ≤ N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ Q i ≤ A ^ 2 * r i * N i := by
    filter_upwards [hgood] with i hi
    rcases hi with ⟨hL, hn, hN, hQ, hr, hr1, hrN, hc⟩
    exact ⟨hL, hn, hN.le, hQ, hr, hr1, hc⟩
  have hvgood : ∀ᶠ i in l, 0 ≤ v i ∧ 0 ≤ N i ∧ 0 < Q i ∧ 0 < r i ∧ r i ≤ 1 ∧
      Q i ≤ A ^ 2 * r i * N i := by
    filter_upwards [hb] with i hi
    rcases hi with ⟨hL, hn, hN, hQ, hr, hr1, hc⟩
    exact ⟨div_nonneg (mul_nonneg hL (zero_le_one.trans (one_le_dimensionLog hN))) hn.le,
      hN, hQ, hr, hr1, hc⟩
  have hv := (variance_compatibility_scale_limits v N Q r A hvgood hcompat).1
  have hHdiv : Tendsto (fun i => H i / Q i) l (𝓝 0) := by
    have ht := variance_compatibility_hs_moment_scale_limit L n N Q r A hb hcompat
    apply ht.congr'
    exact Filter.Eventually.of_forall fun i => by dsimp only [H]; ring
  have hHroot : Tendsto (fun i => Real.sqrt (H i) / Real.sqrt (Q i)) l (𝓝 0) := by
    have ht := hHdiv.sqrt
    simp only [Real.sqrt_zero] at ht
    apply ht.congr'
    filter_upwards [hgood] with i hi
    exact Real.sqrt_div (mul_nonneg (div_nonneg hi.1 hi.2.1.le) hi.2.2.1.le) (Q i)
  have hDzero : Tendsto D l (𝓝 0) := by
    apply squeeze_zero' (hD.mono fun _ hi => hi.1) (hD.mono fun _ hi => hi.2)
    simpa only [mul_zero] using hv.const_mul C
  have hratio := variance_compatibility_leverage_div_dimension_tendsto_zero L n N Q r A hgood hcompat
  have hsmall : ∀ᶠ i in l, H i ≤ N i ^ 2 := by
    filter_upwards [hgood, hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi hs
    have hLn : L i / n i ≤ N i := (div_le_iff₀ hi.2.1).mpr
      (by nlinarith [(div_lt_one (mul_pos hi.2.1 hi.2.2.1)).mp hs])
    dsimp only [H]
    nlinarith [mul_le_mul_of_nonneg_right hLn hi.2.2.1.le]
  have hcross : Tendsto (fun i => Real.sqrt (D i) * Real.sqrt (4 * (N i ^ 2 + H i)) / Q i) l (𝓝 0) := by
    have hu : Tendsto (fun i => (4 * Real.sqrt C) * (N i / Q i * Real.sqrt (v i))) l (𝓝 0) := by
      simpa only [mul_zero] using hcompat.const_mul (4 * Real.sqrt C)
    apply squeeze_zero' _ _ hu
    · filter_upwards [hgood] with i hi
      exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hi.2.2.2.1.le
    · filter_upwards [hgood, hvgood, hD, hsmall] with i hi hv hiD hiH
      exact variance_mixed_moment_bound hC hi.2.2.1.le hi.2.2.2.1 hiD.2 hiH
  have ht := ((((hHdiv.const_mul ((5 / 4 : ℝ) * K ^ 2)).add (hHroot.const_mul K)).add
    hDzero.sqrt).add hcross).const_mul CE
  simpa only [H, Real.sqrt_zero, mul_zero, add_zero, mul_div_assoc] using ht

/-- The actual covariance deviation is strongly measurable from the real
feature/sample maps; hence its quarter-event is a genuine measurable event. -/
theorem stronglyMeasurable_actualCovarianceDeviation
    {X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {μ : Measure X} [IsProbabilityMeasure μ] (k : X → H) (hk : MemLp k 2 μ)
    (lam : ℝ) {n : ℕ} (x : Fin n → Ω → X)
    (hz : ∀ i, StronglyMeasurable (fun ω => k (x i ω))) :
    StronglyMeasurable (fun ω => actualCovarianceDeviation k hk lam (fun i => x i ω)) := by
  let R := featureRegularizedInvSqrt μ k hk lam
  let T := populationCovariance (featureEmbedding μ k hk)
  have hTX := stronglyMeasurable_empiricalCovariance (fun i ω => k (x i ω)) hz
  change StronglyMeasurable (fun ω => ‖R * (empiricalCovariance (fun i => k (x i ω)) - T) * R‖)
  exact ((stronglyMeasurable_const.mul (hTX.sub stronglyMeasurable_const)).mul stronglyMeasurable_const).norm

/-- The actual good-event relative variance converges in L¹ under the
manuscript's original variance compatibility alone. The integrated Bernstein
second moment, HS bound, empirical-dimension moment, and pointwise variance
comparison are all supplied by proved theorems inside this proof. There is
no external concentration leaf, moment certificate or limiting-error input. -/
theorem actual_good_variance_relative_L1_of_compatibility
    {I X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] {l : Filter I}
    (n : I → ℕ) (hn : ∀ i, 0 < n i) (x : (i : I) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (hks : StronglyMeasurable k)
    (lam : I → ℝ) (hlam : ∀ i, 0 < lam i) (φ : I → ℝ → ℝ) {M ρ A : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hMX : ∀ i ω, ‖empiricalCovariance (fun j => k (x i j ω))‖ ≤ M)
    (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L : I → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y ≤ L i)
    (hQ : ∀ᶠ i in l, 0 < featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) *
        Real.sqrt (L i * dimensionLog (featureEffectiveDimension k hk (lam i)) / (n i : ℝ))) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω in {ω | actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) ≤ 1 / 4},
      |actualVarianceEnergy k hk (φ i) (hlam i) (fun j => x i j ω) (hMX i ω) (h i) -
        featureFilterDimension k hk (φ i)| / featureFilterDimension k hk (φ i) ∂P) l (𝓝 0) := by
  let N := fun i => featureEffectiveDimension k hk (lam i)
  let Q := fun i => featureFilterDimension k hk (φ i)
  let r := fun i => featureCovarianceRetention k hk (lam i)
  let D := fun i => ∫ ω, actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) ^ 2 ∂P
  let G := fun i => {ω | actualCovarianceDeviation k hk (lam i) (fun j => x i j ω) ≤ 1 / 4}
  have hgood : ∀ᶠ i in l, 0 ≤ L i ∧ 0 < (n i : ℝ) ∧ 0 < N i ∧ 0 < Q i ∧
      0 < r i ∧ r i ≤ 1 ∧ r i ≤ N i ∧ Q i ≤ A ^ 2 * r i * N i := by
    filter_upwards [hQ] with i hQi
    exact ⟨feature_sq_bound_nonneg (bernsteinFeature k hk (lam i)) (hL i), Nat.cast_pos.mpr (hn i),
      featureEffectiveDimension_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hQi,
      hQi, featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i) (hlam i) hM (hf i) (h i) hQi,
      featureCovarianceRetention_le_one k hk (lam i) (hlam i),
      featureCovarianceRetention_le_effectiveDimension k hk (lam i) (hlam i),
      featureFilterDimension_le_retention k hk (φ i) (hlam i) hM (hf i) (h i)⟩
  have hDm := integral_actualCovarianceDeviation_sq_le_original_scale_eventually (featureCovarianceBasis k hk)
    n hn x hlaw hind k hk lam hlam φ hM hf h L hL hQ hcompat
  have hD : ∀ᶠ i in l, 0 ≤ D i ∧ D i ≤ (768 * Real.exp 1) *
      (L i * dimensionLog (N i) / (n i : ℝ)) := by
    filter_upwards [hDm] with i hi
    exact ⟨integral_nonneg fun _ => sq_nonneg _, hi⟩
  have hlim := variance_compatibility_expectation_envelope_tendsto_zero L (fun i => (n i : ℝ)) N Q r D A
    (768 * Real.exp 1) (4 * (1 + A ^ 2)) (2 * A * (1 + ρ)) (by positivity) hgood hD hcompat
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hQ] with i hi
    exact integral_nonneg fun _ => div_nonneg (abs_nonneg _) hi.le
  · filter_upwards [hQ] with i hi
    have hG : MeasurableSet (G i) := by
      exact measurableSet_le
        (stronglyMeasurable_actualCovarianceDeviation k hk (lam i) (x i)
          (fun j => hks.comp_measurable (hlaw i j).measurable)).measurable measurable_const
    exact (setIntegral_actual_variance_relative_le_covariance_moment (hn i) (x i) (hlaw i)
      (fun _ _ hij => (hind i).indepFun hij)
      k hk hks (φ i) (hlam i) hM (hMX i) (hf i) (h i) hi (hL i) (G i) hG (fun _ hω => hω)
      (memLp_actualCovarianceDeviation (featureCovarianceBasis k hk) (hn i) (x i) (hlaw i) k hk (lam i) (hL i))).2

end
end KernelSeq
