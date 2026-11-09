import KernelSeq.SphericalPhaseCutoffModel
import KernelSeq.HighDimensionalRidgeBounds

/-!
# The three comparison scales for the original spherical cutoff schedule
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology ContDiff
noncomputable section

universe uJ uI uH
variable {J : Type uJ} {l : Filter J} [NeBot l]
  (ι : J → Type uI) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
  (H : J → Type uH)
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
  [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
  [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]

/-- Actual retained cutoff at λ = μ_p supplies every original comparison
scale, uniformly over any family of targets in the literal source ball. -/
theorem spherical_phaseCutoff_original_scales
    {κ s R γ η w : ℝ}
    (Φ : ℝ → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hs : 0 < s) (hR : 0 < R) (hγ : s+1 ≤ γ) (hη : 0 < η)
    (n : J → ℕ) (hn : ∀ i, 0 < n i)
    (f : ∀ i, Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ (ι i))))
    (χ : ℝ → ℝ) (hχ : ResidualFilter.PhaseCutoffProfile w χ) (hw : 0 < w)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hnschedule : Tendsto (fun i => (n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) l (𝓝 η))
    (hsource : ∀ᶠ i in l, f i ∈ featureSourceBall (rkhsFeature (H := H i))
      (zonalSphereFeature_memLp Φ hΦ.continuousOn (hkernel i)) s hs.le R) :
    let model := fun i => sphericalPhaseCutoffScaleModel Φ hΦ (hkernel i) hκ hdiag
      (n i) (hn i) (f i) a ha hseries (highDimensionalDegree s γ) χ hχ
    (∀ᶠ i in l, 0 < (model i).Q) ∧
      Tendsto (fun i => (model i).compatibility) l (𝓝 0) ∧
      Tendsto (fun i => (model i).sourceBalance) l (𝓝 0) ∧
      Tendsto (fun i => (model i).expectationScale) l (𝓝 0) := by
  let p := highDimensionalDegree s γ
  let lam := fun i => zonalSphereDegreeValue (ι := ι i) a p
  have hl (i : J) : 0 < lam i := zonalSphereDegreeValue_pos_of_smooth a ha Φ hseries hΦ p
  let φ := fun i => ResidualFilter.smoothedCutoff (lam i) χ
  have hf (i : J) : ResidualFilter.SpectralFilter (κ^2) (φ i) :=
    ResidualFilter.phaseCutoff_spectralFilter hχ
  have hc (i : J) : ResidualFilter.Contract (lam i) (κ^2) 1
      (ResidualFilter.phaseCutoffContractConstant χ) (φ i) :=
    ResidualFilter.phaseCutoff_contract (hl i) (sq_nonneg κ) hχ
  have hp := highDimensionalDegree_bounds hs hγ
  have hdR : Tendsto (fun i => (Fintype.card (ι i) : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hreg := spherical_fixedDegree_isTheta ι Φ a (fun j => (ha j).le) hseries hΦ p (ha p) hd
  have hretain : ∃ q0 > 0, ∀ᶠ i in l, q0 ≤ ResidualFilter.shrinkage (φ i) (lam i) :=
    ⟨w, hw, Eventually.of_forall fun i => (ResidualFilter.phaseCutoff_shrinkage_at_scale (hl i) hχ).ge⟩
  exact spherical_retained_sourceBall_original_scales ι H Φ hΦ.continuousOn hkernel
    hκ hdiag n hn f lam hl φ hf hc a (fun j => (ha j).le) hseries p hp.1 hp.2.2.2
    (ha p) hs hR hdR (dimensionSample_isTheta hη hnschedule) hreg hretain hsource

end
end KernelSeq
