import KernelSeq.ExpectationExponentialMoments
import KernelSeq.ExpectationCovarianceScales
import KernelSeq.ProvedBernstein

/-!
# Actual normalized covariance moments at the original variance scale

The operator-norm second moment is obtained by integrating the genuine
Bernstein tail. The HS second moment is used for integrability only, and is
not substituted for the sharper operator scale.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

theorem bernsteinThreshold_growth_le {v R ell z : ℝ}
    (hv : 0≤v) (hR : 0≤R) (hell : 1≤ell) (hz : 0≤z) :
    bernsteinThreshold v R (ell+z) ≤ bernsteinThreshold v R ell*(1+z) := by
  have he0 : 0≤ell := zero_le_one.trans hell
  have he : ell+z ≤ ell*(1+z)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hell) hz, mul_nonneg he0 (sq_nonneg z)]
  have hroot : Real.sqrt (v*(ell+z)) ≤ Real.sqrt (v*ell)*(1+z) := by
    calc
      _ ≤ Real.sqrt ((v*ell)*(1+z)^2) := Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left he hv])
      _ = _ := by rw [Real.sqrt_mul (mul_nonneg hv he0), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by linarith : 0≤1+z)]
  have hlin : R*(ell+z) ≤ R*ell*(1+z) := by
    have hh : ell+z ≤ ell*(1+z) := by nlinarith [mul_nonneg (sub_nonneg.mpr hell) hz]
    nlinarith [mul_le_mul_of_nonneg_left hh hR]
  unfold bernsteinThreshold
  nlinarith

theorem normalizedBernsteinBase_sq_le {n L r ell : ℝ}
    (hn : 0<n) (hL : 0≤L) (hr : 0≤r) (hell : 0≤ell) :
    (bernsteinThreshold (n*L*r) (2*L) ell/n)^2 ≤
      8*(L*r*ell/n)+32*(L*ell/n)^2 := by
  have hs := Real.sq_sqrt (show 0≤n*L*r*ell by positivity)
  have hh : (2*Real.sqrt (n*L*r*ell)+4*L*ell)^2 ≤
      8*(Real.sqrt (n*L*r*ell))^2+32*(L*ell)^2 := by
    nlinarith [sq_nonneg (2*Real.sqrt (n*L*r*ell)-4*L*ell)]
  change ((2*Real.sqrt (n*L*r*ell)+2*(2*L)*ell)/n)^2 ≤ _
  calc
    _ = (2*Real.sqrt (n*L*r*ell)+4*L*ell)^2/n^2 := by rw [div_pow]; ring
    _ ≤ (8*(Real.sqrt (n*L*r*ell))^2+32*(L*ell)^2)/n^2 :=
      div_le_div_of_nonneg_right hh (sq_nonneg _)
    _ = _ := by rw [hs]; field_simp

variable {ι X H Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- L² integrability of the actual operator norm, from its genuine HS
representation. This statement asserts no sharp moment rate. -/
theorem memLp_actualCovarianceDeviation (b : HilbertBasis ι ℝ H)
    {n : ℕ} (hn : 0<n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) {L : ℝ}
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y≤L) :
    MemLp (fun ω => actualCovarianceDeviation k hk lam (fun j => x j ω)) 2 P := by
  have hz := memLp_normalizedHSCovarianceFluctuation b hn x hlaw k hk lam hL
  have hm := ((hilbertSchmidtOperator b).comp_memLp' hz).norm
  have he : (fun ω => ‖hilbertSchmidtOperator b
      (normalizedHSCovarianceFluctuation b k hk lam (fun j => x j ω))‖) =
      (fun ω => actualCovarianceDeviation k hk lam (fun j => x j ω)) := by
    funext ω
    rw [hilbertSchmidtOperator_normalizedHSCovarianceFluctuation]
    rfl
  dsimp only [Function.comp_apply] at hm
  rw [he] at hm
  exact hm

variable [TopologicalSpace.SeparableSpace H]

/-- Actual nonasymptotic operator second moment with the intrinsic logarithm.
Every concentration input is supplied by the locally proved Bernstein theorem. -/
theorem integral_actualCovarianceDeviation_sq_le_intrinsic (b : HilbertBasis ι ℝ H)
    (k : X → H) (hk : MemLp k 2 μ) {lam L : ℝ} (hlam : 0<lam)
    {n : ℕ} (hn : 0<n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (hind : iIndepFun x P)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y≤L)
    (hr : 0<featureCovarianceRetention k hk lam) :
    (∫ ω, actualCovarianceDeviation k hk lam (fun j => x j ω)^2 ∂P) ≤
      (16*Real.exp 1)*(8*(L*featureCovarianceRetention k hk lam*
        intrinsicDimensionLog (featureEffectiveDimension k hk lam)
          (featureCovarianceRetention k hk lam)/(n:ℝ))+
        32*(L*intrinsicDimensionLog (featureEffectiveDimension k hk lam)
          (featureCovarianceRetention k hk lam)/(n:ℝ))^2) := by
  let r := featureCovarianceRetention k hk lam
  let N := featureEffectiveDimension k hk lam
  let ell := intrinsicDimensionLog N r
  let a := bernsteinThreshold ((n:ℝ)*L*r) (2*L) ell/(n:ℝ)
  have hnR : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hLpos : 0<L := hr.trans_le (by
    rw [← bernsteinFeature_covariance_norm k hk lam]
    exact populationCovariance_norm_le_feature_bound _ (bernsteinFeature_memLp k hk lam) hL)
  have hell : 1≤ell := one_le_dimensionLog
    (div_nonneg (featureEffectiveDimension_nonneg k hk lam hlam) hr.le)
  have ha : 0<a := by
    dsimp only [a, bernsteinThreshold]
    have he : 0<ell := by linarith
    positivity
  have ht (z : ℝ) (hz : 0≤z) : P {ω | a*(1+z)<actualCovarianceDeviation k hk lam (fun j => x j ω)} ≤
      ENNReal.ofReal (8*Real.exp (-z)) := by
    have htail := normalized_covariance_bernstein_tail k hk lam hlam
      (finiteSpectralBernstein_proved _ P) hn x hlaw hind hL hr z hz
    have hth := bernsteinThreshold_growth_le (show 0≤(n:ℝ)*L*r by positivity)
      (show 0≤2*L by positivity) hell hz
    apply (measure_mono (t := {ω | bernsteinThreshold ((n:ℝ)*L*r) (2*L) (ell+z)/(n:ℝ) <
      actualCovarianceDeviation k hk lam (fun j => x j ω)}) ?_).trans htail
    intro ω hω
    change a*(1+z)<actualCovarianceDeviation k hk lam (fun j => x j ω) at hω
    have hh : bernsteinThreshold ((n:ℝ)*L*r) (2*L) (ell+z)/(n:ℝ) ≤ a*(1+z) := by
      exact (div_le_div_of_nonneg_right hth hnR.le).trans_eq (by dsimp only [a]; ring)
    exact hh.trans_lt hω
  have hm := integral_sq_le_of_linear_exponential_tail
    (memLp_actualCovarianceDeviation b hn x hlaw k hk lam hL)
    (Eventually.of_forall fun ω => norm_nonneg _) ha (by norm_num : (1:ℝ)≤8) ht
  have hs := normalizedBernsteinBase_sq_le hnR hLpos.le hr.le (zero_le_one.trans hell)
  calc
    _ ≤ (2*8*Real.exp 1)*a^2 := hm
    _ = (16*Real.exp 1)*a^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (show 0≤16*Real.exp 1 by positivity)

/-- The small intrinsic-linear ratio forced by variance compatibility makes
its square negligible on the ordinary variance scale. -/
theorem intrinsic_linear_sq_le_variance {n L N r : ℝ}
    (hn : 0<n) (hL : 0≤L) (hN : 0≤N) (hr : 0<r)
    (hsmall : Real.sqrt (L*dimensionLog N/n)*intrinsicDimensionLog N r/dimensionLog N ≤ 1) :
    (L*intrinsicDimensionLog N r/n)^2 ≤ L*dimensionLog N/n := by
  let v := L*dimensionLog N/n
  have hell : 1≤dimensionLog N := one_le_dimensionLog hN
  have he : dimensionLog N≠0 := ne_of_gt (by linarith)
  have hv : 0≤v := by dsimp only [v]; positivity
  have hq0 : 0≤Real.sqrt v*intrinsicDimensionLog N r/dimensionLog N :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans
      (one_le_dimensionLog (div_nonneg hN hr.le)))) (zero_le_one.trans hell)
  have hq2 : (Real.sqrt v*intrinsicDimensionLog N r/dimensionLog N)^2 ≤ 1 := by nlinarith
  have hid : L*intrinsicDimensionLog N r/n = v*(intrinsicDimensionLog N r/dimensionLog N) := by
    dsimp only [v]
    field_simp [he]
  rw [hid, mul_pow]
  calc
    _ = v*(Real.sqrt v*intrinsicDimensionLog N r/dimensionLog N)^2 := by
      have hsquare : (Real.sqrt v*intrinsicDimensionLog N r/dimensionLog N)^2 =
          v*(intrinsicDimensionLog N r)^2/(dimensionLog N)^2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hv]
      rw [hsquare]
      field_simp [he]
    _ ≤ v*1 := mul_le_mul_of_nonneg_left hq2 hv
    _ = _ := mul_one v

/-- The exact manuscript operator second-moment scale, eventually under its
original variance compatibility. There is no retention lower bound or
integrated-concentration premise. -/
theorem integral_actualCovarianceDeviation_sq_le_original_scale_eventually
    {J : Type*} {l : Filter J} (b : HilbertBasis ι ℝ H)
    (n : J → ℕ) (hn : ∀ i, 0<n i) (x : (i:J) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ) (hind : ∀ i, iIndepFun (x i) P)
    (k : X → H) (hk : MemLp k 2 μ) (lam : J → ℝ) (hlam : ∀ i, 0<lam i)
    (φ : J → ℝ → ℝ) {M ρ A : ℝ}
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ∀ i, ResidualFilter.SpectralFilter M (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) M ρ A (φ i))
    (L : J → ℝ) (hL : ∀ i, ∀ᵐ y ∂μ, normalizedLeverage k hk (lam i) y≤L i)
    (hQ : ∀ᶠ i in l, 0<featureFilterDimension k hk (φ i))
    (hcompat : Tendsto (fun i => featureEffectiveDimension k hk (lam i) /
      featureFilterDimension k hk (φ i) * Real.sqrt
        (L i*dimensionLog (featureEffectiveDimension k hk (lam i))/(n i:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, (∫ ω, actualCovarianceDeviation k hk (lam i) (fun j => x i j ω)^2 ∂P) ≤
      (768*Real.exp 1)*(L i*dimensionLog (featureEffectiveDimension k hk (lam i))/(n i:ℝ)) := by
  let N := fun i => featureEffectiveDimension k hk (lam i)
  let r := fun i => featureCovarianceRetention k hk (lam i)
  let v := fun i => L i*dimensionLog (N i)/(n i:ℝ)
  have hL0 (i : J) : 0≤L i := feature_sq_bound_nonneg (bernsteinFeature k hk (lam i)) (hL i)
  have hv (i : J) : 0≤v i := div_nonneg (mul_nonneg (hL0 i)
    (zero_le_one.trans (one_le_dimensionLog (featureEffectiveDimension_nonneg k hk (lam i) (hlam i)))))
      (Nat.cast_nonneg _)
  have hsc := feature_variance_compatibility_scale_limits k hk lam hlam φ hM hf h
    v (Eventually.of_forall hv) hQ hcompat
  filter_upwards [hQ, hsc.2.2.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with i hQi hsmall
  have hnR : 0<(n i:ℝ) := Nat.cast_pos.mpr (hn i)
  have hN : 0≤N i := featureEffectiveDimension_nonneg k hk (lam i) (hlam i)
  have hr : 0<r i := featureCovarianceRetention_pos_of_filterDimension_pos k hk (φ i)
    (hlam i) hM (hf i) (h i) hQi
  have hr1 : r i≤1 := featureCovarianceRetention_le_one k hk (lam i) (hlam i)
  have hfirst : L i*r i*intrinsicDimensionLog (N i) (r i)/(n i:ℝ) ≤ 2*v i := by
    have hh := mul_le_mul_of_nonneg_left (retention_mul_intrinsicDimensionLog_le hN hr hr1) (hL0 i)
    calc
      _ ≤ L i*(2*dimensionLog (N i))/(n i:ℝ) := by
        simpa only [mul_assoc] using div_le_div_of_nonneg_right hh hnR.le
      _ = 2*v i := by dsimp only [v]; ring
  have hsecond : (L i*intrinsicDimensionLog (N i) (r i)/(n i:ℝ))^2 ≤ v i :=
    intrinsic_linear_sq_le_variance hnR (hL0 i) hN hr hsmall.le
  have hm := integral_actualCovarianceDeviation_sq_le_intrinsic b k hk (hlam i) (hn i)
    (x i) (hlaw i) (hind i) (hL i) hr
  calc
    _ ≤ (16*Real.exp 1)*(8*(L i*r i*intrinsicDimensionLog (N i) (r i)/(n i:ℝ))+
        32*(L i*intrinsicDimensionLog (N i) (r i)/(n i:ℝ))^2) := hm
    _ ≤ (16*Real.exp 1)*(8*(2*v i)+32*v i) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤16*Real.exp 1)
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
        (mul_le_mul_of_nonneg_left hsecond (by norm_num))
    _ = _ := by ring

end
end KernelSeq
