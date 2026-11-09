import KernelSeq.SphericalSpectralSums
import KernelSeq.SphericalPhaseCutoffGaps
import KernelSeq.SpherePolynomialLayerDimension
import KernelSeq.CovarianceMoments

/-!
# The actual variance constant for the spherical smoothed cutoff

The spectral plateaus turn the actual, regrouped population filter
dimension into the finite low-degree sum plus the partially retained degree.
Only the leading layer contributes to its sharp equivalent.
-/

namespace KernelSeq
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators
noncomputable section

variable {I : Type*} {l : Filter I} (ι : I → Type*)
  [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
  (H : I → Type*) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, CompleteSpace (H i)] [∀ i, TopologicalSpace.SeparableSpace (H i)]
  (k : ∀ i, KernelSphere (EuclideanSpace ℝ (ι i)) → H i)
  (hk : ∀ i, MemLp (k i) 2 uniformSphere)
  (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
  (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
  (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
  (hkernel : ∀ i x y, inner ℝ (k i x) (k i y) = zonalSphereKernel Φ x y)

local notation "dim" => fun i m => (Module.finrank ℝ (spherePolynomialLayer (ι i) m) : ℝ)
local notation "deg" => fun i m => zonalSphereDegreeValue (ι := ι i) a m

include ha hseries hΦ hkernel in
theorem spherical_phaseCutoff_filterDimension_eventually_eq (p : ℕ) {w : ℝ}
    (χ : ℝ → ℝ) (hχ : ResidualFilter.PhaseCutoffProfile w χ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    ∀ᶠ i in l, featureFilterDimension (k i) (hk i) (ResidualFilter.smoothedCutoff (deg i p) χ) =
      (∑ j ∈ Finset.range p, dim i j) + w^2 * dim i p := by
  filter_upwards [spherical_phaseCutoff_gaps ι a ha Φ hseries hΦ hd p] with i hi
  let lam := deg i p
  let φ := ResidualFilter.smoothedCutoff lam χ
  have hlam : 0 < lam := zonalSphereDegreeValue_pos_of_smooth a ha Φ hseries hΦ p
  have hM : ‖populationCovariance (featureEmbedding uniformSphere (k i) (hk i))‖ ≤ Φ 1 := by
    apply populationCovariance_norm_le_feature_bound
    exact Eventually.of_forall fun x => by
      rw [← real_inner_self_eq_norm_sq, hkernel i x x, zonalSphereKernel_diag]
  have hQ := hasSum_zonalSphere_filterDimension (k i) (hk i) a ha Φ hseries
    (hkernel i) hΦ φ hlam hM (ResidualFilter.phaseCutoff_spectralFilter hχ)
    (ResidualFilter.phaseCutoff_contract hlam ((norm_nonneg _).trans hM) hχ)
  have hzero (j : ℕ) (hj : p < j) : ResidualFilter.shrinkage φ (deg i j) = 0 := by
    apply ResidualFilter.phaseCutoff_shrinkage_zero_of_le_half hlam hχ
    have hmid := hi.2.2 j hj
    have hhigh := hi.2.1
    change 2 * deg i (p+1) ≤ lam at hhigh
    linarith
  have hone (j : ℕ) (hj : j < p) : ResidualFilter.shrinkage φ (deg i j) = 1 :=
    ResidualFilter.phaseCutoff_shrinkage_one_of_ge_twice hlam hχ (hi.1 j hj)
  have hp : ResidualFilter.shrinkage φ (deg i p) = w :=
    ResidualFilter.phaseCutoff_shrinkage_at_scale hlam hχ
  change featureFilterDimension (k i) (hk i) φ = _
  rw [← hQ.tsum_eq, tsum_eq_sum (s := Finset.range (p+1)) (fun j hj => by
    have hj' : p < j := by simp only [Finset.mem_range, not_lt] at hj; omega
    rw [hzero j hj', zero_pow (by decide : 2 ≠ 0), mul_zero]), Finset.sum_range_succ, hp]
  congr 1
  · exact Finset.sum_congr rfl (fun j hj => by rw [hone j (Finset.mem_range.mp hj), one_pow, mul_one])
  · exact mul_comm _ _

private theorem spherical_layer_div_dimensionPower_tendsto
    (m : ℕ) (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => dim i m/(Fintype.card (ι i) : ℝ)^m) l (𝓝 ((m.factorial : ℝ)⁻¹)) := by
  have hh := (spherePolynomialLayer_dimension_ratio_tendsto ι m hd).div_const (m.factorial : ℝ)
  rw [one_div] at hh
  apply hh.congr
  intro i
  have hd0 : (0 : ℝ) < Fintype.card (ι i) := Nat.cast_pos.mpr Fintype.card_pos
  have hf : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  field_simp [hf, (pow_pos hd0 m).ne']

include ha hseries hΦ hkernel in
theorem spherical_phaseCutoff_filterDimension_scaled_tendsto (p : ℕ) {w : ℝ}
    (χ : ℝ → ℝ) (hχ : ResidualFilter.PhaseCutoffProfile w χ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => featureFilterDimension (k i) (hk i)
      (ResidualFilter.smoothedCutoff (deg i p) χ)/(Fintype.card (ι i) : ℝ)^p) l
      (𝓝 (w^2/(p.factorial : ℝ))) := by
  let d : I → ℝ := fun i => Fintype.card (ι i)
  have hd0 (i : I) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hdR : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hlo (j : ℕ) (hj : j ∈ Finset.range p) :
      Tendsto (fun i => dim i j/(d i)^p) l (𝓝 0) := by
    have hj' : (j : ℝ) < p := by exact_mod_cast Finset.mem_range.mp hj
    have hdecay : Tendsto (fun i => d i^(-((p : ℝ)-(j : ℝ)))) l (𝓝 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hj')).comp hdR
    have hh := (spherical_layer_div_dimensionPower_tendsto ι j hd).mul hdecay
    rw [mul_zero] at hh
    apply hh.congr
    intro i
    change dim i j/(d i)^j * d i^(-((p : ℝ)-(j : ℝ))) = _
    rw [neg_sub, Real.rpow_sub (hd0 i), Real.rpow_natCast, Real.rpow_natCast]
    field_simp [(pow_pos (hd0 i) j).ne', (pow_pos (hd0 i) p).ne']
  have hsum : Tendsto (fun i => ∑ j ∈ Finset.range p, dim i j/(d i)^p) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.range p) hlo
  have hhi := (spherical_layer_div_dimensionPower_tendsto ι p hd).const_mul (w^2)
  rw [← div_eq_mul_inv] at hhi
  have hall := hsum.add hhi
  rw [zero_add] at hall
  apply hall.congr'
  filter_upwards [spherical_phaseCutoff_filterDimension_eventually_eq ι H k hk a ha Φ hseries hΦ hkernel p χ hχ hd]
    with i hi
  rw [hi, add_div, Finset.sum_div]
  change _ + w^2 * (dim i p/d i^p) = _ + (w^2 * dim i p)/d i^p
  rw [mul_div_assoc]

include ha hseries hΦ hkernel in
theorem spherical_phaseCutoff_sequenceVariance_scaled_tendsto (p : ℕ) {w : ℝ}
    (χ : ℝ → ℝ) (hχ : ResidualFilter.PhaseCutoffProfile w χ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (n : I → ℕ) (hn : ∀ i, 0 < n i) {σ γ η : ℝ} (hη : 0 < η)
    (hSchedule : Tendsto (fun i => (n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) l (𝓝 η)) :
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^(γ-(p : ℝ)) *
      (σ^2/(n i : ℝ) * featureFilterDimension (k i) (hk i)
        (ResidualFilter.smoothedCutoff (deg i p) χ))) l
      (𝓝 (highDimensionalNoiseConstant σ η p * w^2)) := by
  have hQ := spherical_phaseCutoff_filterDimension_scaled_tendsto ι H k hk
    a ha Φ hseries hΦ hkernel p χ hχ hd
  have h := (hQ.const_mul (σ^2)).div hSchedule hη.ne'
  have hconst : σ^2*(w^2/(p.factorial : ℝ))/η = highDimensionalNoiseConstant σ η p * w^2 := by
    unfold highDimensionalNoiseConstant
    ring
  rw [hconst] at h
  apply h.congr
  intro i
  have hd0 : (0 : ℝ) < Fintype.card (ι i) := Nat.cast_pos.mpr Fintype.card_pos
  have hn0 : (0 : ℝ) < n i := Nat.cast_pos.mpr (hn i)
  let Q : ℝ := featureFilterDimension (k i) (hk i) (ResidualFilter.smoothedCutoff (deg i p) χ)
  change (σ^2*(Q/(Fintype.card (ι i) : ℝ)^p))/((n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) =
    (Fintype.card (ι i) : ℝ)^(γ-(p : ℝ))*(σ^2/(n i : ℝ)*Q)
  rw [Real.rpow_sub hd0, Real.rpow_natCast]
  field_simp [(pow_pos hd0 p).ne', (Real.rpow_pos_of_pos hd0 γ).ne', hn0.ne']

end
end KernelSeq
