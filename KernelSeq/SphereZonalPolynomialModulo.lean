import KernelSeq.SpherePolynomialMomentsModulo
import KernelSeq.SpherePowerOperatorSeries
import KernelSeq.SphereZonalAsymptotics

/-!
# The actual full zonal covariance modulo lower polynomial degree

The genuine norm-convergent operator series and the proved scalar degree
series preserve the closed lower polynomial space. No harmonic action or
operator convergence is supplied as a premise.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped BigOperators ContDiff
noncomputable section

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem predictionCovariance_sphereSymLp_mod_polynomial_of_powerSeries
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)
    {m : ℕ} (s : Sym ι m) :
    predictionCovariance (featureEmbedding uniformSphere k hk) (sphereSymLp s)-
      zonalSphereDegreeValue (ι := ι) a m • sphereSymLp s ∈ spherePolynomialSpace ι (m-2) := by
  let E := Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))
  let v : E := sphereSymLp s
  let L := predictionCovariance (featureEmbedding uniformSphere k hk)
  let C := fun j => sphereMixedPowerCoefficient ι (j+m) m
  let W := spherePolynomialSpace ι (m-2)
  have hT := spherePowerPredictionOperator_series_hasSum k hk a ha Φ hseries hkernel
  have hTv : HasSum (fun j => a j • spherePowerPredictionOperator ι j v) (L v) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, smul_apply] using
      (ContinuousLinearMap.apply ℝ E v).hasSum hT
  have hC := summable_zonalSphereDegreeSeries_of_smooth (ι := ι) a ha Φ hseries hΦ m
  have hCv : HasSum (fun j => (a j*C j) • v) (zonalSphereDegreeValue (ι := ι) a m • v) :=
    hC.hasSum.smul_const v
  have hR : HasSum (fun j => a j • (spherePowerPredictionOperator ι j v-C j • v))
      (L v-zonalSphereDegreeValue (ι := ι) a m • v) := by
    simpa only [smul_sub, smul_smul] using hTv.sub hCv
  have hmem (j : ℕ) : spherePowerPredictionOperator ι j v-C j • v ∈ W :=
    predictionCovariance_sphereSymLp_mod_polynomial (sphereTensorFeature j)
      (sphereTensorFeature_memLp j) j (sphereTensorFeature_gram j) s
  exact W.closed_of_finiteDimensional.mem_of_tendsto hR.tendsto_sum_nat
    (Eventually.of_forall fun n => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j))

end
end KernelSeq
