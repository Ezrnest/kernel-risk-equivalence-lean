import KernelSeq.SphericalSpectralSums
import KernelSeq.SpherePolynomialLayerDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The spherical first effective dimension at high-dimensional scales

A single fixed degree above the regularization exponent contributes a
positive fraction of the inverse-regularization scale. The upper bound is
the actual covariance trace divided by regularization. No spectral counting
or leverage estimate is supplied as a premise.
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology ContDiff
noncomputable section

variable {I : Type*} {l : Filter I} (ι : I → Type*)
  [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
  (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
  (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
  (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))

include ha hseries hΦ in
theorem spherical_degreeTrace_tendsto (m : ℕ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => (Module.finrank ℝ (spherePolynomialLayer (ι i) m) : ℝ) *
      zonalSphereDegreeValue (ι := ι i) a m) l (𝓝 (a m)) := by
  have hD := spherePolynomialLayer_dimension_ratio_tendsto ι m hd
  have hμ := zonalSphereDegreeValue_scaled_tendsto ι a (fun j => (ha j).le) Φ hseries hΦ m hd
  have hfac : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hprod := (hD.mul hμ).div_const (m.factorial : ℝ)
  rw [one_mul, mul_div_cancel_right₀ _ hfac] at hprod
  apply hprod.congr
  intro i
  have hd0 : (0 : ℝ) < Fintype.card (ι i) := Nat.cast_pos.mpr Fintype.card_pos
  field_simp [hfac, (pow_pos hd0 m).ne']

variable (H : I → Type*) [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, CompleteSpace (H i)] [∀ i, TopologicalSpace.SeparableSpace (H i)]
  (k : ∀ i, KernelSphere (EuclideanSpace ℝ (ι i)) → H i)
  (hk : ∀ i, MemLp (k i) 2 uniformSphere)
  (hkernel : ∀ i x y, inner ℝ (k i x) (k i y) = zonalSphereKernel Φ x y)

include ha hseries hΦ hkernel in
/-- In particular, take `m=p+1` and the manuscript's exponent
`b=p+min(δ,s)/2`. The actual first effective dimension is Θ(dᵇ). -/
theorem spherical_effectiveDimension_isTheta_dimensionPower
    (lam : I → ℝ) (hlam : ∀ i, 0 < lam i) {b : ℝ} (m : ℕ) (hbm : b < m)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hLambda : lam =Θ[l] (fun i => (Fintype.card (ι i) : ℝ)^(-b))) :
    (fun i => featureEffectiveDimension (k i) (hk i) (lam i)) =Θ[l]
      (fun i => (Fintype.card (ι i) : ℝ)^b) := by
  let d : I → ℝ := fun i => Fintype.card (ι i)
  let N := fun i => featureEffectiveDimension (k i) (hk i) (lam i)
  let t : I → ℝ := fun i => zonalSphereDegreeValue (ι := ι i) a m
  let D : I → ℝ := fun i => Module.finrank ℝ (spherePolynomialLayer (ι i) m)
  have hd0 (i : I) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have ht0 (i : I) : 0 ≤ t i := zonalSphereDegreeValue_nonneg a (fun j => (ha j).le) m
  have hN0 (i : I) : 0 ≤ N i := featureEffectiveDimension_nonneg (k i) (hk i) (lam i) (hlam i)
  have htθ : t =Θ[l] (fun i => d i^(-(m : ℝ))) := by
    have h := zonalSphereDegreeValue_ratio_tendsto ι a (fun j => (ha j).le) Φ hseries hΦ m (ha m) hd
    have hc : 0 < a m*(m.factorial : ℝ) := mul_pos (ha m) (by positivity)
    exact (isTheta_of_div_tendsto_nhds_ne_zero h one_ne_zero).symm.trans
      ((isTheta_const_mul_left hc.ne').mpr (isTheta_refl _ _))
  have hLambdainv : (fun i => (lam i)⁻¹) =Θ[l] (fun i => d i^b) := by
    change lam =Θ[l] (fun i => d i^(-b)) at hLambda
    have he (i : I) : (d i^(-b))⁻¹ = d i^b := by
      rw [← Real.rpow_neg (hd0 i).le, neg_neg]
    simpa only [he] using hLambda.inv
  have hratio : Tendsto (fun i => t i/lam i) l (𝓝 0) := by
    have hProd := htθ.isBigO.mul hLambdainv.isBigO
    have he (i : I) : d i^(-(m : ℝ))*d i^b = d i^(-((m : ℝ)-b)) := by
      rw [← Real.rpow_add (hd0 i)]
      congr 1
      ring
    simp only [he, ← div_eq_mul_inv] at hProd
    exact hProd.trans_tendsto ((tendsto_rpow_neg_atTop (sub_pos.mpr hbm)).comp
      (tendsto_natCast_atTop_atTop.comp hd))
  have hL : ∀ᶠ i in l, a m/4 ≤ lam i*N i := by
    have hDT := spherical_degreeTrace_tendsto ι a ha Φ hseries hΦ m hd
    filter_upwards [hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hDT.eventually (lt_mem_nhds (by linarith [ha m] : a m/2 < a m))] with i hi hD
    have htLambda : t i ≤ lam i := le_of_lt ((div_lt_one (hlam i)).mp hi)
    have hterm : D i*(t i/(t i+lam i)) ≤ N i := by
      have hsum := hasSum_zonalSphere_effectiveDimension (k i) (hk i) a ha Φ hseries
        (hkernel i) hΦ (lam i) (hlam i)
      change _ ≤ featureEffectiveDimension (k i) (hk i) (lam i)
      rw [← hsum.tsum_eq]
      exact hsum.summable.le_tsum m (fun j _ => mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (zonalSphereDegreeValue_nonneg a (fun j => (ha j).le) j)
          (add_nonneg (zonalSphereDegreeValue_nonneg a (fun j => (ha j).le) j) (hlam i).le)))
    have hfac : (1 : ℝ)/2 ≤ lam i/(t i+lam i) := by
      apply (le_div_iff₀ (add_pos_of_nonneg_of_pos (ht0 i) (hlam i))).mpr
      linarith
    have hmid := mul_le_mul_of_nonneg_right hfac (mul_nonneg (show 0 ≤ D i by exact Nat.cast_nonneg _) (ht0 i))
    calc
      a m/4 ≤ 1/2*(D i*t i) := by
        change a m/2 < D i*t i at hD
        linarith
      _ ≤ lam i*(D i*(t i/(t i+lam i))) := by
        calc
          _ ≤ (lam i/(t i+lam i))*(D i*t i) := hmid
          _ = _ := by ring
      _ ≤ lam i*N i := mul_le_mul_of_nonneg_left hterm (hlam i).le
  have hθ : N =Θ[l] (fun i => (lam i)⁻¹) := by
    constructor
    · apply IsBigO.of_bound (Φ 1)
      exact Eventually.of_forall fun i => by
        have hB := featureEffectiveDimension_le_trace_div (k i) (hk i) (lam i) (hlam i)
        rw [zonalSphere_covarianceTrace_eq_profile_one (k i) (hk i) Φ (hkernel i), div_eq_mul_inv] at hB
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hN0 i), abs_of_pos (inv_pos.mpr (hlam i))] using hB
    · apply IsBigO.of_bound (4/(a m))
      filter_upwards [hL] with i hi
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hlam i)), abs_of_nonneg (hN0 i)]
      rw [inv_eq_one_div, div_le_iff₀ (hlam i)]
      calc
        1 = (4/a m)*(a m/4) := by field_simp [(ha m).ne']
        _ ≤ (4/a m)*(lam i*N i) := mul_le_mul_of_nonneg_left hi (div_nonneg (by norm_num) (ha m).le)
        _ = _ := by ring
  exact hθ.trans hLambdainv

end
end KernelSeq
