import KernelSeq.PhaseCutoffFilter
import KernelSeq.SphereZonalAsymptotics
import KernelSeq.SphericalScaleBounds

/-!
# Actual spherical rows for the manuscript's smoothed cutoff
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology ContDiff
noncomputable section

/-- The degree-series value is positive even on a row where the corresponding
layer is empty. Smoothness supplies summability, and the diagonal coefficient
is positive in every nonzero ambient dimension. -/
theorem zonalSphereDegreeValue_pos_of_smooth
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j * t^j) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (m : ℕ) :
    0 < zonalSphereDegreeValue (ι := ι) a m := by
  have hsum := summable_zonalSphereDegreeSeries_of_smooth (ι := ι)
    a (fun j => (ha j).le) Φ hseries hΦ m
  have hle := hsum.sum_le_tsum ({m} : Finset ℕ)
    (fun j _ => mul_nonneg (ha j).le (sphereMixedPowerCoefficient_nonneg _ _))
  simp only [Finset.sum_singleton, ← two_mul] at hle
  exact (mul_pos (ha m) (sphereMixedPowerCoefficient_even_pos m m le_rfl)).trans_le hle

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H (KernelSphere (EuclideanSpace ℝ ι)) ℝ]
  {κ w : ℝ}

/-- The actual sphere design, exact degree-value regularization and exact
smooth cutoff. The common contract constant depends only on the profile. -/
def sphericalPhaseCutoffScaleModel
    (Φ : ℝ → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (n : ℕ) (hn : 0 < n)
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j * t^j) (Φ t))
    (p : ℕ) (χ : ℝ → ℝ) (hχ : ResidualFilter.PhaseCutoffProfile w χ) :
    SpectralScaleModel κ 1 (ResidualFilter.phaseCutoffContractConstant χ) :=
  let lam := zonalSphereDegreeValue (ι := ι) a p
  let hlam := zonalSphereDegreeValue_pos_of_smooth (ι := ι) a ha Φ hseries hΦ p
  sphericalScaleModel Φ hΦ.continuousOn hkernel hκ hdiag n hn f lam hlam
    (ResidualFilter.smoothedCutoff lam χ)
    (ResidualFilter.phaseCutoff_spectralFilter hχ)
    (ResidualFilter.phaseCutoff_contract hlam (sq_nonneg κ) hχ)

end
end KernelSeq
