import KernelSeq.SphericalPhaseCutoffModel
import KernelSeq.CanonicalGaussianSourceFamily

/-! The spherical applications use exactly the kernel and half-line profile
specified in the manuscript. -/

namespace KernelSeq
open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology
noncomputable section

def sphericalKernelBound (Φ : ℝ → ℝ) : ℝ := Real.sqrt (Φ 1)

theorem sphericalKernelBound_nonneg (Φ : ℝ → ℝ) : 0 ≤ sphericalKernelBound Φ :=
  Real.sqrt_nonneg _

theorem zonalProfile_one_pos (Φ : ℝ → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t)) : 0 < Φ 1 := by
  have h : HasSum a (Φ 1) := by simpa only [one_pow,mul_one] using hseries 1 (by norm_num)
  have hh := h.summable.sum_le_tsum ({0} : Finset ℕ) (fun j _ => (ha j).le)
  rw [Finset.sum_singleton,h.tsum_eq] at hh
  exact (ha 0).trans_le hh

theorem sphericalKernelBound_diag (Φ : ℝ → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t)) :
    Φ 1 = sphericalKernelBound Φ ^ 2 :=
  (Real.sq_sqrt (zonalProfile_one_pos Φ a ha hseries).le).symm

namespace ResidualFilter

/-- The value of the original half-line profile is unchanged at every
nonnegative argument. It is extended by zero to give a globally smooth
real representative for spectral calculus. -/
def phaseCutoffHalfLineExtension (χ : ℝ → ℝ) (u : ℝ) : ℝ := χ (max 0 u)

theorem phaseCutoffHalfLineExtension_eq {χ : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) :
    phaseCutoffHalfLineExtension χ u = χ u := by
  rw [phaseCutoffHalfLineExtension,max_eq_right hu]

theorem phaseCutoffHalfLineExtension_isProfile {χ : ℝ → ℝ} {w : ℝ}
    (hχ : ContDiffOn ℝ ∞ χ (Ici 0))
    (hmono : MonotoneOn χ (Ici 0))
    (hrange : ∀ u ≥ 0, χ u ∈ Icc (0 : ℝ) 1)
    (hbelow : ∀ u ∈ Icc (0 : ℝ) (1/2), χ u = 0)
    (hat : χ 1 = w) (habove : ∀ u ≥ 2, χ u = 1) :
    PhaseCutoffProfile w (phaseCutoffHalfLineExtension χ) := by
  have hb (u : ℝ) (hu : u ≤ 1/2) : phaseCutoffHalfLineExtension χ u = 0 :=
    hbelow (max 0 u) ⟨le_max_left _ _,max_le (by norm_num) hu⟩
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro u
    by_cases hu : 0 < u
    · have hne : Ici (0 : ℝ) ∈ 𝓝 u := Ici_mem_nhds hu
      apply (hχ.contDiffAt hne).congr_of_eventuallyEq
      filter_upwards [hne] with x hx
      exact phaseCutoffHalfLineExtension_eq hx
    · have hu' : u < 1/2 := (le_of_not_gt hu).trans_lt (by norm_num)
      apply (contDiff_const (c := (0 : ℝ))).contDiffAt.congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hu'] with x hx
      exact hb x (le_of_lt hx)
  · intro u v huv
    exact hmono (show max 0 u ∈ Ici (0 : ℝ) from le_max_left (0 : ℝ) u)
      (show max 0 v ∈ Ici (0 : ℝ) from le_max_left (0 : ℝ) v) (max_le_max le_rfl huv)
  · intro u
    exact hrange _ (le_max_left _ _)
  · exact hb
  · rw [phaseCutoffHalfLineExtension_eq (by norm_num : 0 ≤ (1 : ℝ)),hat]
  · intro u hu
    rw [phaseCutoffHalfLineExtension_eq (by linarith : 0 ≤ u)]
    exact habove u hu

theorem smoothedCutoff_halfLineExtension_eq {χ : ℝ → ℝ} {lam t : ℝ}
    (hlam : 0 < lam) (ht : 0 ≤ t) :
    smoothedCutoff lam (phaseCutoffHalfLineExtension χ) t = smoothedCutoff lam χ t := by
  unfold smoothedCutoff
  rw [phaseCutoffHalfLineExtension_eq (div_nonneg ht hlam.le)]

end ResidualFilter

section ActualMinimax
variable {ι H : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H (KernelSphere (EuclideanSpace ℝ ι)) ℝ]

/-- The actual minimax risk is independent of the filter and scale. -/
def sphericalGaussianMinimaxRisk
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (R σ : ℝ) : ℝ≥0∞ :=
  gaussianRangeMinimaxRisk (rkhsFeature (H := H)) (zonalSphereFeature_memLp Φ hΦ hkernel) σ n
    (featureSourceBall (rkhsFeature (H := H)) (zonalSphereFeature_memLp Φ hΦ hkernel) s hs R)

end ActualMinimax
end
end KernelSeq
