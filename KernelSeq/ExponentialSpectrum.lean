import KernelSeq.PolynomialSpectrum

/-!
# Exponential envelopes of the actual positive covariance spectrum

The stretched-exponential series is genuinely summable for every positive
power. Its actual sum supplies a common fractional-moment constant, and hence
an effective-dimension upper bound at any arbitrarily small positive power.
No moment or dimension estimate is assumed as an application hypothesis.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelSeq
noncomputable section

/-- The genuine series constant for an exponential spectral envelope. -/
def stretchedExponentialMomentConstant (c0 ν p : ℝ) : ℝ :=
  ∑' j : ℕ, Real.exp (-(c0*p)*((j:ℝ)+1)^ν)

theorem stretchedExponentialMomentConstant_nonneg (c0 ν p : ℝ) :
    0 ≤ stretchedExponentialMomentConstant c0 ν p :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

/-- Every stretched exponential is summable: its product with `(j+1)^2`
tends to zero, giving an actual comparison with the convergent p-series. -/
theorem summable_stretchedExponential {c ν : ℝ} (hc : 0<c) (hν : 0<ν) :
    Summable (fun j : ℕ => Real.exp (-c*((j:ℝ)+1)^ν)) := by
  have hn : Tendsto (fun j : ℕ => (j:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
  have hnr := (tendsto_rpow_atTop hν).comp hn
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2/ν) c hc).comp hnr
  have heq (j : ℕ) : (((j:ℝ)+1)^ν)^(2/ν) = ((j:ℝ)+1)^2 := by
    rw [← Real.rpow_mul (by positivity : 0≤(j:ℝ)+1)]
    have he : ν*(2/ν)=2 := by field_simp [hν.ne']
    rw [he, Real.rpow_two]
  have ht' : Tendsto (fun j : ℕ => ((j:ℝ)+1)^2 * Real.exp (-c*((j:ℝ)+1)^ν)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, heq] using ht
  have hprod := ht'.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  have hseries : Summable (fun j : ℕ => ((j:ℝ)+1)^(-2:ℝ)) := by
    have hh : Summable (fun j : ℕ => (j:ℝ)^(-2:ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hh
  apply hseries.of_norm_bounded_eventually_nat
  filter_upwards [hprod] with j hj
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_neg (by positivity : 0≤(j:ℝ)+1),
    Real.rpow_two, ← one_div]
  apply (le_div_iff₀ (by positivity : 0<((j:ℝ)+1)^2)).mpr
  nlinarith

theorem summable_stretchedExponentialMoment {c0 ν p : ℝ}
    (hc0 : 0<c0) (hν : 0<ν) (hp : 0<p) :
    Summable (fun j : ℕ => Real.exp (-(c0*p)*((j:ℝ)+1)^ν)) :=
  summable_stretchedExponential (mul_pos hc0 hp) hν

theorem stretchedExponentialMomentConstant_pos {c0 ν p : ℝ}
    (hc0 : 0<c0) (hν : 0<ν) (hp : 0<p) :
    0 < stretchedExponentialMomentConstant c0 ν p := by
  unfold stretchedExponentialMomentConstant
  exact (Real.exp_pos _).trans_le
    ((summable_stretchedExponentialMoment hc0 hν hp).le_tsum 0 (fun _ _ => (Real.exp_pos _).le))

private theorem exponential_envelope_rpow {C c0 ν p : ℝ} (hC : 0≤C) (j : ℕ) :
    (C*Real.exp (-c0*((j:ℝ)+1)^ν))^p =
      C^p * Real.exp (-(c0*p)*((j:ℝ)+1)^ν) := by
  rw [Real.mul_rpow hC (Real.exp_pos _).le, ← Real.exp_mul]
  have he : (-c0*((j:ℝ)+1)^ν)*p = -(c0*p)*((j:ℝ)+1)^ν := by ring
  rw [he]

theorem summable_moment_of_exponential_upper {w : ℕ→ℝ} {C c0 ν p : ℝ}
    (hw : ∀ j, 0≤w j) (hC : 0≤C) (hc0 : 0<c0) (hν : 0<ν) (hp : 0<p)
    (hupper : ∀ j, w j≤C*Real.exp (-c0*((j:ℝ)+1)^ν)) :
    Summable (fun j => w j^p) := by
  apply ((summable_stretchedExponentialMoment hc0 hν hp).mul_left (C^p)).of_nonneg_of_le
    (fun j => Real.rpow_nonneg (hw j) _)
  intro j
  have hh := Real.rpow_le_rpow (hw j) (hupper j) hp.le
  rwa [exponential_envelope_rpow hC j] at hh

theorem moment_le_exponential_constant {w : ℕ→ℝ} {C c0 ν p : ℝ}
    (hw : ∀ j, 0≤w j) (hC : 0≤C) (hc0 : 0<c0) (hν : 0<ν) (hp : 0<p)
    (hupper : ∀ j, w j≤C*Real.exp (-c0*((j:ℝ)+1)^ν)) :
    (∑' j, w j^p) ≤ C^p * stretchedExponentialMomentConstant c0 ν p := by
  have hpoint (j : ℕ) : w j^p ≤ C^p * Real.exp (-(c0*p)*((j:ℝ)+1)^ν) := by
    rw [← exponential_envelope_rpow hC j]
    exact Real.rpow_le_rpow (hw j) (hupper j) hp.le
  have hh := (summable_moment_of_exponential_upper hw hC hc0 hν hp hupper).tsum_le_tsum
    hpoint ((summable_stretchedExponentialMoment hc0 hν hp).mul_left (C^p))
  simpa only [tsum_mul_left, stretchedExponentialMomentConstant] using hh

/-- A common spectral bound and a common eventual threshold produce a
common global envelope; finite initial coordinates are not silently dropped. -/
def exponentialEnvelopeGlobalConstant (C M c0 ν : ℝ) (J : ℕ) : ℝ :=
  C+M*Real.exp (c0*((J:ℝ)+1)^ν)

theorem exponential_upper_global_of_threshold {w : ℕ→ℝ} {C M c0 ν : ℝ} (J : ℕ)
    (hC : 0≤C) (hM : 0≤M) (hc0 : 0≤c0) (hν : 0≤ν)
    (hwM : ∀ j, w j≤M)
    (hupper : ∀ j, J≤j → w j≤C*Real.exp (-c0*((j:ℝ)+1)^ν)) :
    ∀ j, w j≤exponentialEnvelopeGlobalConstant C M c0 ν J * Real.exp (-c0*((j:ℝ)+1)^ν) := by
  intro j
  have hCM : C≤exponentialEnvelopeGlobalConstant C M c0 ν J :=
    le_add_of_nonneg_right (mul_nonneg hM (Real.exp_pos _).le)
  by_cases hj : J≤j
  · exact (hupper j hj).trans (mul_le_mul_of_nonneg_right hCM (Real.exp_pos _).le)
  have hj' : (j:ℝ)+1≤(J:ℝ)+1 := by
    exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt (lt_of_not_ge hj)) 1
  have hexp : c0*((j:ℝ)+1)^ν ≤ c0*((J:ℝ)+1)^ν :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hj' hν) hc0
  have hlarge : 1≤Real.exp (c0*((J:ℝ)+1)^ν-c0*((j:ℝ)+1)^ν) :=
    Real.one_le_exp_iff.mpr (sub_nonneg.mpr hexp)
  calc
    _ ≤ M := hwM j
    _ ≤ M*Real.exp (c0*((J:ℝ)+1)^ν-c0*((j:ℝ)+1)^ν) := le_mul_of_one_le_right hM hlarge
    _ = (M*Real.exp (c0*((J:ℝ)+1)^ν))*Real.exp (-c0*((j:ℝ)+1)^ν) := by
      rw [sub_eq_add_neg, Real.exp_add]
      simp only [neg_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (Real.exp_pos _).le

theorem exists_exponential_upper_global_of_eventually {w : ℕ→ℝ} {C M c0 ν : ℝ}
    (hC : 0≤C) (hM : 0≤M) (hc0 : 0≤c0) (hν : 0≤ν)
    (hwM : ∀ j, w j≤M)
    (hupper : ∀ᶠ j in atTop, w j≤C*Real.exp (-c0*((j:ℝ)+1)^ν)) :
    ∃ C' : ℝ, 0≤C' ∧ ∀ j, w j≤C'*Real.exp (-c0*((j:ℝ)+1)^ν) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hupper
  refine ⟨exponentialEnvelopeGlobalConstant C M c0 ν J, ?_,
    exponential_upper_global_of_threshold J hC hM hc0 hν hwM hJ⟩
  unfold exponentialEnvelopeGlobalConstant
  positivity

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

omit [TopologicalSpace.SeparableSpace H] [IsProbabilityMeasure μ] in
/-- The original exponential envelope supplies a true moment of the actual
covariance, including every positive eigenvalue with its multiplicity. -/
theorem featureSpectralMoment_le_exponential (k : X→H) (hk : MemLp k 2 μ)
    (e : FeatureSpectrumEnumeration k hk) {C c0 ν p : ℝ}
    (hC : 0≤C) (hc0 : 0<c0) (hν : 0<ν) (hp : 0<p)
    (hupper : ∀ j, enumeratedEigenvalue k hk e j≤C*Real.exp (-c0*((j:ℝ)+1)^ν)) :
    featureSpectralMoment k hk p ≤ C^p * stretchedExponentialMomentConstant c0 ν p := by
  rw [featureSpectralMoment_eq_enumerated k hk e p]
  exact moment_le_exponential_constant (fun j => (e j).2.le) hC hc0 hν hp hupper

theorem featureEffectiveDimension_le_exponential (k : X→H) (hk : MemLp k 2 μ)
    (e : FeatureSpectrumEnumeration k hk) {lam C c0 ν p : ℝ}
    (hlam : 0<lam) (hC : 0≤C) (hc0 : 0<c0) (hν : 0<ν) (hp : 0<p) (hp1 : p≤1)
    (hupper : ∀ j, enumeratedEigenvalue k hk e j≤C*Real.exp (-c0*((j:ℝ)+1)^ν)) :
    featureEffectiveDimension k hk lam ≤
      (C^p * stretchedExponentialMomentConstant c0 ν p) * lam^(-p) := by
  have hs := summable_moment_of_exponential_upper (fun j => (e j).2.le) hC hc0 hν hp hupper
  have hsi : Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) => i.1.1^p) :=
    e.summable_iff.mp hs
  have hm := featureSpectralMoment_le_exponential k hk e hC hc0 hν hp hupper
  exact (featureEffectiveDimension_le_fractional_moment k hk hlam hp.le hp1 hsi).trans
    ((mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hlam.le (-p))).trans_eq (mul_comm _ _))

/-- Uniform eventual spectral constants and a uniform norm bound supply
a common finite-row dimension bound, including the initial spectral prefix. -/
theorem featureEffectiveDimension_le_exponential_threshold
    (k : X→H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk) (J : ℕ)
    {lam C M c0 ν p : ℝ} (hlam : 0<lam) (hC : 0≤C)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hc0 : 0<c0) (hν : 0<ν) (hp : 0<p) (hp1 : p≤1)
    (hupper : ∀ j, J≤j → enumeratedEigenvalue k hk e j≤C*Real.exp (-c0*((j:ℝ)+1)^ν)) :
    featureEffectiveDimension k hk lam ≤
      ((exponentialEnvelopeGlobalConstant C M c0 ν J)^p *
        stretchedExponentialMomentConstant c0 ν p) * lam^(-p) := by
  have hMn : 0≤M := (norm_nonneg _).trans hM
  have hglobal := exponential_upper_global_of_threshold J hC hMn hc0.le hν.le
    (fun j => (featureCovarianceEigenvalue_mem k hk hM (e j).1).2) hupper
  have hCg : 0≤exponentialEnvelopeGlobalConstant C M c0 ν J := by
    unfold exponentialEnvelopeGlobalConstant
    positivity
  exact featureEffectiveDimension_le_exponential k hk e hlam hCg hc0 hν hp hp1 hglobal

omit [TopologicalSpace.SeparableSpace H] in
/-- The actual spectrum's norm bound converts its asymptotic upper envelope
to a global one. For uniform families the threshold must itself be common. -/
theorem exists_enumerated_exponential_upper_global_of_eventually
    (k : X→H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk)
    {C M c0 ν : ℝ} (hC : 0≤C)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hc0 : 0≤c0) (hν : 0≤ν)
    (hupper : ∀ᶠ j in atTop, enumeratedEigenvalue k hk e j≤C*Real.exp (-c0*((j:ℝ)+1)^ν)) :
    ∃ C' : ℝ, 0≤C' ∧ ∀ j, enumeratedEigenvalue k hk e j≤C'*Real.exp (-c0*((j:ℝ)+1)^ν) :=
  exists_exponential_upper_global_of_eventually hC ((norm_nonneg _).trans hM) hc0 hν
    (fun j => (featureCovarianceEigenvalue_mem k hk hM (e j).1).2) hupper

/-- A lower exponential envelope gives a common nonzero resolved direction
and therefore a common quarter lower bound on the actual filter dimension. -/
theorem featureFilterDimension_ge_quarter_of_exponential_lower
    (k : X→H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk)
    (φ : ℝ→ℝ) {lam M ρ A c c0 ν : ℝ}
    (hlam : 0<lam) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hlower : ∀ j : ℕ, c*Real.exp (-c0*((j:ℝ)+1)^ν)≤enumeratedEigenvalue k hk e j)
    (hsmall : lam*ResidualFilter.resolvedScaleFactor ρ A≤c*Real.exp (-c0)) :
    (1/4:ℝ)≤featureFilterDimension k hk φ := by
  have hzero : c*Real.exp (-c0)≤enumeratedEigenvalue k hk e 0 := by
    simpa only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] using hlower 0
  have hq := h.resolved_shrinkage_ge_half hlam (featureCovarianceEigenvalue_mem k hk hM (e 0).1)
    (hsmall.trans hzero)
  have hb := (summable_positive_sequence_filterDimension k hk φ hlam hM hf h).le_tsum (e 0)
    (fun _ _ => sq_nonneg _)
  rw [← featureFilterDimension_eq_positive_sequence] at hb
  change (1/2:ℝ)≤ResidualFilter.shrinkage φ (e 0).1.1 at hq
  nlinarith [sq_nonneg (ResidualFilter.shrinkage φ (e 0).1.1-1/2)]

/-- An eventual lower envelope can use its first valid coordinate, without
requiring a sorted enumeration or a lower bound on omitted initial indices. -/
theorem featureFilterDimension_ge_quarter_of_exponential_lower_threshold
    (k : X→H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk) (J : ℕ)
    (φ : ℝ→ℝ) {lam M ρ A c c0 ν : ℝ}
    (hlam : 0<lam) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hlower : ∀ j : ℕ, J≤j → c*Real.exp (-c0*((j:ℝ)+1)^ν)≤enumeratedEigenvalue k hk e j)
    (hsmall : lam*ResidualFilter.resolvedScaleFactor ρ A≤c*Real.exp (-c0*((J:ℝ)+1)^ν)) :
    (1/4:ℝ)≤featureFilterDimension k hk φ := by
  have hq := h.resolved_shrinkage_ge_half hlam (featureCovarianceEigenvalue_mem k hk hM (e J).1)
    (hsmall.trans (hlower J le_rfl))
  have hb := (summable_positive_sequence_filterDimension k hk φ hlam hM hf h).le_tsum (e J)
    (fun _ _ => sq_nonneg _)
  rw [← featureFilterDimension_eq_positive_sequence] at hb
  change (1/2:ℝ)≤ResidualFilter.shrinkage φ (e J).1.1 at hq
  nlinarith [sq_nonneg (ResidualFilter.shrinkage φ (e J).1.1-1/2)]

def exponentialResolvedCutoff (ρ A c c0 ν : ℝ) (J : ℕ) : ℝ :=
  c*Real.exp (-c0*((J:ℝ)+1)^ν)/ResidualFilter.resolvedScaleFactor ρ A

theorem exponentialResolvedCutoff_pos {ρ A c c0 ν : ℝ} (hA : 0≤A) (hc : 0<c) (J : ℕ) :
    0<exponentialResolvedCutoff ρ A c c0 ν J :=
  div_pos (mul_pos hc (Real.exp_pos _)) (ResidualFilter.resolvedScaleFactor_pos hA)

theorem featureFilterDimension_ge_quarter_of_lambda_le_exponential_cutoff
    (k : X→H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk) (J : ℕ)
    (φ : ℝ→ℝ) {lam M ρ A c c0 ν : ℝ}
    (hlam : 0<lam) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖≤M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hlower : ∀ j : ℕ, J≤j → c*Real.exp (-c0*((j:ℝ)+1)^ν)≤enumeratedEigenvalue k hk e j)
    (hsmall : lam≤exponentialResolvedCutoff ρ A c c0 ν J) :
    (1/4:ℝ)≤featureFilterDimension k hk φ := by
  apply featureFilterDimension_ge_quarter_of_exponential_lower_threshold k hk e J φ hlam hM hf h hlower
  exact (le_div_iff₀ (ResidualFilter.resolvedScaleFactor_pos
    (ρ := ρ) (h.constant_nonneg hlam ((norm_nonneg _).trans hM)))).mp hsmall

end
end KernelSeq
