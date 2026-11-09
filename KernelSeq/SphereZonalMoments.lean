import KernelSeq.SpherePolynomialMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual zonal-kernel action on squarefree polynomial functions

The degree value is an actually summable scalar series. Summability is
proved from the original power-series convergence and the true spherical
moment identity; dominated convergence then identifies the full kernel
integral. No eigenvalue or harmonic-space certificate is a premise.
-/

namespace KernelSeq
open MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private def sphericalOnes : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)

omit [Fintype ι] [DecidableEq ι] in
private theorem sphericalOnes_ne_zero : sphericalOnes (ι := ι) ≠ 0 := by
  intro h
  have hh := congrArg (fun x : EuclideanSpace ℝ ι => x (Classical.arbitrary ι)) h
  change (1 : ℝ) = 0 at hh
  exact one_ne_zero hh

def sphericalPositivePole : KernelSphere (EuclideanSpace ℝ ι) :=
  ⟨NormedSpace.normalize sphericalOnes, mem_sphere_zero_iff_norm.mpr
    (NormedSpace.norm_normalize sphericalOnes_ne_zero)⟩

omit [DecidableEq ι] in
theorem sphericalPositivePole_coordinate_pos (i : ι) :
    0 < (sphericalPositivePole (ι := ι) : EuclideanSpace ℝ ι) i := by
  change 0 < (NormedSpace.normalize sphericalOnes) i
  simp only [NormedSpace.normalize, PiLp.smul_apply, smul_eq_mul, sphericalOnes, mul_one]
  exact inv_pos.mpr (norm_pos_iff.mpr sphericalOnes_ne_zero)

omit [DecidableEq ι] in
theorem sphereCoordinateProduct_positivePole_pos (s : Finset ι) :
    0 < sphereCoordinateProduct s (sphericalPositivePole (ι := ι)) :=
  Finset.prod_pos (fun i _ => sphericalPositivePole_coordinate_pos i)

/-- A finite bound for every actual polynomial-kernel coefficient. This
bound is used only for fixed-row convergence of the original Φ series. -/
theorem sphereMixedPowerCoefficient_le_positivePole (s : Finset ι) (j : ℕ) :
    sphereMixedPowerCoefficient ι (j+s.card) s.card ≤
      (sphereCoordinateProduct s (sphericalPositivePole (ι := ι)))⁻¹ := by
  let x := sphericalPositivePole (ι := ι)
  have hx : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hupper : (∫ y : KernelSphere (EuclideanSpace ℝ ι),
      sphereCoordinateProduct s y * inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)^j
      ∂uniformSphere) ≤ 1 := by
    have hh := integral_mono_ae
      (integrable_continuous_uniformSphere (by unfold sphereCoordinateProduct; fun_prop : Continuous (fun y : KernelSphere (EuclideanSpace ℝ ι) =>
        sphereCoordinateProduct s y * inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)^j)))
      (integrable_const (1 : ℝ)) (Eventually.of_forall fun y => ?_)
    · simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
    · have hy : ‖(y : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
      have hi : |inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)| ≤ 1 := by
        simpa only [hx, hy, one_mul] using abs_real_inner_le_norm (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)
      calc
        _ ≤ |sphereCoordinateProduct s y * inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)^j| := le_abs_self _
        _ = |sphereCoordinateProduct s y| * |inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)|^j := by
          rw [abs_mul, abs_pow]
        _ ≤ 1*1 := mul_le_mul (sphereCoordinateProduct_abs_le_one s y)
          (pow_le_one₀ (abs_nonneg _) hi) (by positivity) (by norm_num)
        _ = _ := one_mul _
  rw [integral_sphere_inner_power_mul_squarefree] at hupper
  simpa only [one_div] using (le_div_iff₀ (sphereCoordinateProduct_positivePole_pos s)).mpr hupper

def zonalSphereDegreeValue (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑' j, a j * sphereMixedPowerCoefficient ι (j+m) m

theorem summable_zonalSphereDegreeSeries
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (s : Finset ι) : Summable (fun j => a j * sphereMixedPowerCoefficient ι (j+s.card) s.card) := by
  have hs : Summable a := by
    simpa only [one_pow, mul_one] using (hseries 1 (by norm_num)).summable
  exact (hs.mul_right ((sphereCoordinateProduct s (sphericalPositivePole (ι := ι)))⁻¹)).of_nonneg_of_le
    (fun j => mul_nonneg (ha j) (sphereMixedPowerCoefficient_nonneg _ _))
    (fun j => mul_le_mul_of_nonneg_left (sphereMixedPowerCoefficient_le_positivePole s j) (ha j))

theorem summable_zonalSphereDegreeSeries_of_le_dimension
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (m : ℕ) (hmd : m ≤ Fintype.card ι) :
    Summable (fun j => a j * sphereMixedPowerCoefficient ι (j+m) m) := by
  obtain ⟨s, _, hcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (by simpa using hmd)
  simpa only [hcard] using summable_zonalSphereDegreeSeries a ha Φ hseries s

omit [DecidableEq ι] in
theorem zonalSphereDegreeValue_nonneg (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (m : ℕ) :
    0 ≤ zonalSphereDegreeValue (ι := ι) a m :=
  tsum_nonneg fun j => mul_nonneg (ha j) (sphereMixedPowerCoefficient_nonneg _ _)

/-- An actual positive original power coefficient contributes a strictly
positive degree eigenvalue; the desired estimate is proved from the series. -/
theorem zonalSphereDegreeValue_lower
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (m : ℕ) (hmd : m ≤ Fintype.card ι) :
    a m * sphereMixedPowerCoefficient ι (2*m) m ≤ zonalSphereDegreeValue (ι := ι) a m := by
  have hs := summable_zonalSphereDegreeSeries_of_le_dimension a ha Φ hseries m hmd
  have hh := hs.sum_le_tsum ({m} : Finset ℕ)
    (fun j _ => mul_nonneg (ha j) (sphereMixedPowerCoefficient_nonneg _ _))
  simpa only [Finset.sum_singleton, ← two_mul, zonalSphereDegreeValue] using hh

theorem zonalSphereDegreeValue_pos
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (m : ℕ) (hmd : m ≤ Fintype.card ι) (ham : 0 < a m) :
    0 < zonalSphereDegreeValue (ι := ι) a m :=
  (mul_pos ham (sphereMixedPowerCoefficient_even_pos m m le_rfl)).trans_le
    (zonalSphereDegreeValue_lower a ha Φ hseries m hmd)

theorem integral_zonalSphereKernel_mul_squarefree
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (s : Finset ι) (x : KernelSphere (EuclideanSpace ℝ ι)) :
    (∫ y : KernelSphere (EuclideanSpace ℝ ι), sphereCoordinateProduct s y * zonalSphereKernel Φ x y
      ∂uniformSphere) = zonalSphereDegreeValue (ι := ι) a s.card * sphereCoordinateProduct s x := by
  have hs : Summable a := by
    simpa only [one_pow, mul_one] using (hseries 1 (by norm_num)).summable
  have hcoeff := summable_zonalSphereDegreeSeries a ha Φ hseries s
  have hx : ‖(x : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hi (y : KernelSphere (EuclideanSpace ℝ ι)) :
      |inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)| ≤ 1 := by
    have hy : ‖(y : EuclideanSpace ℝ ι)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
    simpa only [hx, hy, one_mul] using abs_real_inner_le_norm (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)
  let F : ℕ → KernelSphere (EuclideanSpace ℝ ι) → ℝ := fun n y =>
    sphereCoordinateProduct s y * ∑ j ∈ Finset.range n, a j * inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)^j
  have hdom (n : ℕ) (y : KernelSphere (EuclideanSpace ℝ ι)) : ‖F n y‖ ≤ ∑' j, a j := by
    have hp : ‖∑ j ∈ Finset.range n, a j * inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)^j‖ ≤ ∑' j, a j := by
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_sum fun j _ => ?_).trans (hs.sum_le_tsum _ fun j _ => ha j)
      rw [norm_mul, Real.norm_of_nonneg (ha j), norm_pow, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (ha j) (pow_le_one₀ (abs_nonneg _) (hi y))
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans
      (mul_le_of_le_one_left (tsum_nonneg ha) (sphereCoordinateProduct_abs_le_one s y))
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := uniformSphere (E := EuclideanSpace ℝ ι)) (fun _ => ∑' j, a j)
    (fun n => (show Continuous (F n) by unfold F sphereCoordinateProduct; fun_prop).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (hdom n))
    (f := fun y => sphereCoordinateProduct s y * zonalSphereKernel Φ x y) (by
      apply Eventually.of_forall
      intro y
      have ht : inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι) ∈ Icc (-1 : ℝ) 1 :=
        abs_le.mp (hi y)
      exact tendsto_const_nhds.mul ((hseries _ ht).tendsto_sum_nat))
  have hpartial (n : ℕ) : (∫ y, F n y ∂uniformSphere) =
      (∑ j ∈ Finset.range n, a j * sphereMixedPowerCoefficient ι (j+s.card) s.card) * sphereCoordinateProduct s x := by
    dsimp only [F]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum]
    · apply Eq.trans ?_ (Finset.sum_mul _ _ _).symm
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = a j * ∫ y : KernelSphere (EuclideanSpace ℝ ι),
            sphereCoordinateProduct s y * inner ℝ (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι)^j
            ∂uniformSphere := by
          rw [← integral_const_mul]
          congr 1; ext y; ring
        _ = _ := by rw [integral_sphere_inner_power_mul_squarefree]; ring
    · intro j _
      exact integrable_continuous_uniformSphere (by unfold sphereCoordinateProduct; fun_prop)
  have hlim' := hcoeff.hasSum.tendsto_sum_nat.mul_const (sphereCoordinateProduct s x)
  rw [show (∑' j, a j * sphereMixedPowerCoefficient ι (j+s.card) s.card) =
    zonalSphereDegreeValue (ι := ι) a s.card from rfl] at hlim'
  have hh : Tendsto (fun n => ∫ y, F n y ∂uniformSphere) atTop
      (𝓝 (zonalSphereDegreeValue (ι := ι) a s.card * sphereCoordinateProduct s x)) := by
    simpa only [hpartial] using hlim'
  exact tendsto_nhds_unique hlim hh

end
end KernelSeq
