import KernelSeq.SphereCoefficientBounds
import KernelSeq.SphereZonalMoments
import KernelSeq.SmoothPositivePowerMoments
import KernelSeq.SphereCoefficientDiagonal
import KernelSeq.SphereDimensionAsymptotics

/-!
# Actual fixed-degree spherical eigenvalue asymptotics

Smoothness of the original positive Φ series supplies all coefficient
moments internally. The genuine mixed-moment products give the extra d⁻¹
in the leading-term remainder and uniform bounds over higher degrees. The
values here are the same ones already proved to act on actual spherical L²
functions. Identifying the whole complementary spectrum is separate.
-/

namespace KernelSeq
open MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
noncomputable section

def zonalDegreeMomentConstant (a : ℕ → ℝ) (p : ℕ) : ℝ :=
  (2 : ℝ)^p * ∑' j, a j*(j+1 : ℝ)^p

def zonalDegreeRemainderConstant (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ)+1)^(m+1) * ∑' j, a j*(j+1 : ℝ)^(m+1)

section SingleDimension
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem summable_zonalSphereDegreeSeries_of_smooth
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (ell : ℕ) :
    Summable (fun j => a j*sphereMixedPowerCoefficient ι (j+ell) ell) := by
  have hs := summable_coeff_natPower_of_smooth_positive_series a ha Φ hseries hΦ ell
  have hmajor := ((hs.mul_left ((2 : ℝ)^ell)).div_const ((Fintype.card ι : ℝ)^ell))
  apply hmajor.of_nonneg_of_le
    (fun j => mul_nonneg (ha j) (sphereMixedPowerCoefficient_nonneg _ _))
  intro j
  have hh := mul_le_mul_of_nonneg_left (sphereMixedPowerCoefficient_uniform_degree_le (ι := ι) ell ell j le_rfl) (ha j)
  convert! hh using 1; ring

/-- Uniform over all degree values ell≥p, with the entire coefficient moment
proved from original smoothness rather than supplied as an extra premise. -/
theorem zonalSphereDegreeValue_uniform_upper
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (ell p : ℕ) (hp : p ≤ ell) :
    zonalSphereDegreeValue (ι := ι) a ell ≤ zonalDegreeMomentConstant a p / (Fintype.card ι : ℝ)^p := by
  have hs := summable_coeff_natPower_of_smooth_positive_series a ha Φ hseries hΦ p
  have hmajor := ((hs.mul_left ((2 : ℝ)^p)).div_const ((Fintype.card ι : ℝ)^p))
  have hh := (summable_zonalSphereDegreeSeries_of_smooth (ι := ι) a ha Φ hseries hΦ ell).tsum_le_tsum
    (fun j => ?_) hmajor
  · simpa only [tsum_div_const, tsum_mul_left, zonalSphereDegreeValue, zonalDegreeMomentConstant] using hh
  · have hh := mul_le_mul_of_nonneg_left (sphereMixedPowerCoefficient_uniform_degree_le (ι := ι) ell p j hp) (ha j)
    convert! hh using 1; ring

/-- The leading diagonal contribution has a true O(d⁻m⁻¹) remainder.
No eigenvalue asymptotic or coefficient-moment bound is an input. -/
theorem zonalSphereDegreeValue_leading_remainder
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (m : ℕ) :
    0 ≤ zonalSphereDegreeValue (ι := ι) a m - a m*sphereMixedPowerCoefficient ι (2*m) m ∧
      zonalSphereDegreeValue (ι := ι) a m - a m*sphereMixedPowerCoefficient ι (2*m) m ≤
        zonalDegreeRemainderConstant a m / (Fintype.card ι : ℝ)^(m+1) := by
  classical
  have hs := summable_zonalSphereDegreeSeries_of_smooth (ι := ι) a ha Φ hseries hΦ m
  let R : ℕ → ℝ := fun j => if j=m then 0 else a j*sphereMixedPowerCoefficient ι (j+m) m
  have hR0 (j : ℕ) : 0 ≤ R j := by
    dsimp only [R]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (ha j) (sphereMixedPowerCoefficient_nonneg _ _)
  have hR : Summable R := hs.of_nonneg_of_le hR0 (fun j => by
    dsimp only [R]
    split_ifs
    · exact mul_nonneg (ha j) (sphereMixedPowerCoefficient_nonneg _ _)
    · exact le_rfl)
  have hdecomp : zonalSphereDegreeValue (ι := ι) a m =
      a m*sphereMixedPowerCoefficient ι (2*m) m + ∑' j, R j := by
    simpa only [zonalSphereDegreeValue, R, ← two_mul] using hs.tsum_eq_add_tsum_ite m
  have hmoment := summable_coeff_natPower_of_smooth_positive_series a ha Φ hseries hΦ (m+1)
  have hmajor := ((hmoment.mul_left (((m : ℝ)+1)^(m+1))).div_const ((Fintype.card ι : ℝ)^(m+1)))
  have hpoint (j : ℕ) : R j ≤
      (((m : ℝ)+1)^(m+1)*(a j*(j+1 : ℝ)^(m+1))) / (Fintype.card ι : ℝ)^(m+1) := by
    dsimp only [R]
    split_ifs with hj
    · exact div_nonneg (mul_nonneg (by positivity) (mul_nonneg (ha j) (by positivity))) (by positivity)
    · have hh := mul_le_mul_of_nonneg_left
        (sphereMixedPowerCoefficient_off_diagonal_le_fixed_power (ι := ι) m j hj) (ha j)
      convert! hh using 1; ring
  have hbound := hR.tsum_le_tsum hpoint hmajor
  have hbound' : (∑' j, R j) ≤ zonalDegreeRemainderConstant a m / (Fintype.card ι : ℝ)^(m+1) := by
    simpa only [tsum_div_const, tsum_mul_left, zonalDegreeRemainderConstant] using hbound
  rw [hdecomp, add_sub_cancel_left]
  exact ⟨tsum_nonneg hR0, hbound'⟩

end SingleDimension

section DimensionLimit
variable {I : Type*} {l : Filter I}
    (ι : I → Type*) [∀ i, Fintype (ι i)] [∀ i, Nonempty (ι i)]

theorem zonalSphereDegreeValue_remainder_scaled_tendsto
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (m : ℕ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => (zonalSphereDegreeValue (ι := ι i) a m -
      a m*sphereMixedPowerCoefficient (ι i) (2*m) m)*(Fintype.card (ι i) : ℝ)^m) l (𝓝 0) := by
  have hdR : Tendsto (fun i => (Fintype.card (ι i) : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hlim : Tendsto (fun i => zonalDegreeRemainderConstant a m / (Fintype.card (ι i) : ℝ)) l (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hdR)
  apply squeeze_zero' (Eventually.of_forall fun i => mul_nonneg
    (zonalSphereDegreeValue_leading_remainder (ι := ι i) a ha Φ hseries hΦ m).1 (by positivity))
    (Eventually.of_forall fun i => ?_) hlim
  have hh := mul_le_mul_of_nonneg_right
    (zonalSphereDegreeValue_leading_remainder (ι := ι i) a ha Φ hseries hΦ m).2
    (by positivity : (0 : ℝ) ≤ (Fintype.card (ι i) : ℝ)^m)
  have hdP : (0 : ℝ) < (Fintype.card (ι i) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  convert! hh using 1
  rw [pow_succ]
  field_simp

theorem zonalSphereDegreeValue_scaled_tendsto
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (m : ℕ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => zonalSphereDegreeValue (ι := ι i) a m*(Fintype.card (ι i) : ℝ)^m) l
      (𝓝 (a m*(m.factorial : ℝ))) := by
  have hrem := zonalSphereDegreeValue_remainder_scaled_tendsto ι a ha Φ hseries hΦ m hd
  simp_rw [sphereMixedPowerCoefficient_diagonal] at hrem
  have hdiag := (degreeSphereMoment_dimension_ratio_tendsto ι m hd).const_mul (a m*(m.factorial : ℝ))
  have hh := hrem.add hdiag
  simpa only [sphereMixedPowerCoefficient_diagonal, mul_one, zero_add] using
    hh.congr (fun i => by ring)

/-- The original fixed-degree equivalent μ_d,m ~ a_m m! d⁻m for the actual
constructed degree values. The containing operator identification is proved
separately; no complete spherical-harmonic decomposition is claimed here. -/
theorem zonalSphereDegreeValue_ratio_tendsto
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (m : ℕ) (ham : 0 < a m)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => zonalSphereDegreeValue (ι := ι i) a m /
      (a m*(m.factorial : ℝ)*(Fintype.card (ι i) : ℝ)^(-(m : ℝ)))) l (𝓝 1) := by
  have hconst : (a m*(m.factorial : ℝ)) ≠ 0 := ne_of_gt (mul_pos ham (Nat.cast_pos.mpr m.factorial_pos))
  have hh := (zonalSphereDegreeValue_scaled_tendsto ι a ha Φ hseries hΦ m hd).div_const (a m*(m.factorial : ℝ))
  rw [div_self hconst] at hh
  apply hh.congr
  intro i
  have hdP : (0 : ℝ) < (Fintype.card (ι i) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [Real.rpow_neg hdP.le, Real.rpow_natCast]
  field_simp

end DimensionLimit
end
end KernelSeq
