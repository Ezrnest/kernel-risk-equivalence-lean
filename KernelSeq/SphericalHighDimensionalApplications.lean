import KernelSeq.SphericalApplicationPrimitives
import KernelSeq.SphericalPhaseCutoffExpected
import KernelSeq.SphericalMinimaxLower
import KernelSeq.HighDimensionalMinimaxAssembly
import KernelSeq.SphericalRidgeUpper

/-!
# The original high-dimensional Pinsker constant and optimal KRR rate

The expected risk is the actual Gaussian regression risk. The minimax
quantity uses every measurable rule with values in the actual closed
prediction range. No spectral, scale, prior, or risk estimate is a premise.
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped ENNReal Topology ContDiff
noncomputable section

universe uI uι uH
variable {I : Type uI} {l : Filter I} [NeBot l]
    (ι : I → Type uι) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (H : I → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]
    (Φ : ℝ → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    {s γ R σ η : ℝ}
    (hs : 0 < s) (hγ : s+1 ≤ γ) (hR : 0 < R) (hσ : 0 < σ) (hη : 0 < η)
    (n : I → ℕ) (hn : ∀ i, 0 < n i)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hnschedule : Tendsto (fun i => (n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) l (𝓝 η))

def sphericalHighDimensionalPinskerModel (χ : ℝ → ℝ)
    (hχ : ResidualFilter.PhaseCutoffProfile (highDimensionalPinskerWeight a s γ R σ η) χ)
    (i : I) : SpectralScaleModel.{uH,uι} (sphericalKernelBound Φ) 1
      (ResidualFilter.phaseCutoffContractConstant χ) :=
  sphericalPhaseCutoffScaleModel Φ hΦ (hkernel i) (sphericalKernelBound_nonneg Φ)
    (sphericalKernelBound_diag Φ a ha hseries).le
    (n i) (hn i) 0 a ha hseries (highDimensionalDegree s γ) χ hχ

include hγ hR hη hd hnschedule in
set_option maxHeartbeats 1000000 in
/-- The normalized worst expected risk and the unrestricted minimax risk
have the original common constant. The actual spectral estimator attains
it, and the minimax rate is also the original sample-size power. -/
theorem rkhs_spherical_highDimensional_pinsker (χ : ℝ → ℝ)
    (hχ : ResidualFilter.PhaseCutoffProfile (highDimensionalPinskerWeight a s γ R σ η) χ) :
    let b := sphericalHighDimensionalPinskerModel ι H Φ hΦ hkernel a ha hseries n hn χ hχ
    let W := fun i => canonicalGaussianSourceWorstRisk (b i) s hs.le R hσ
    let M := fun i => (sphericalGaussianMinimaxRisk Φ hΦ.continuousOn (hkernel i) (n i) s hs.le R σ).toReal
    let ζ := highDimensionalRiskExponent s γ
    let C := highDimensionalPinskerConstant a s γ R σ η
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^ζ*W i) l (𝓝 C) ∧
      Tendsto (fun i => (Fintype.card (ι i) : ℝ)^ζ*M i) l (𝓝 C) ∧
      Tendsto (fun i => W i/M i) l (𝓝 1) ∧
      M =Θ[l] (fun i => (n i : ℝ)^(-ζ/γ)) := by
  intro b W M ζ C
  have hκ := sphericalKernelBound_nonneg Φ
  have hdiag := (sphericalKernelBound_diag Φ a ha hseries).le
  obtain ⟨hbdd,hW⟩ := spherical_phaseCutoff_expected_limit
    ι H Φ hΦ hkernel hκ hdiag a ha hseries hs hR hγ hη hσ n hn χ hχ hd hnschedule
  have hW' : Tendsto (fun i => (Fintype.card (ι i) : ℝ)^ζ*W i) l (𝓝 C) := hW
  have hC : 0 < C := highDimensionalPinskerConstant_pos ha hR hσ hη
  have hRM : ∀ᶠ i in l, M i ≤ W i := by
    filter_upwards [hbdd] with i hi
    have hWi := canonicalGaussianSourceWorstRisk_nonneg (b i) hs.le hσ hR.le hi
    have hle := gaussianSourceMinimaxRisk_le_canonicalWorstRisk (b i) hs.le hσ hi
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq (ENNReal.toReal_ofReal hWi)
  have hd0 (i : I) : (0 : ℝ) < Fintype.card (ι i) := Nat.cast_pos.mpr Fintype.card_pos
  have hM (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) (err : ℝ) (herr : 0 < err) :
      ∀ᶠ i in l, C*(1-ε)-err ≤ (Fintype.card (ι i) : ℝ)^ζ*M i := by
    have hh := rkhs_spherical_minimax_normalized_lower ι H Φ hΦ hkernel a ha hseries
      hs hγ hR hσ hη n hn hd hnschedule err herr
    filter_upwards [hh] with i hi
    have hc : C*(1-ε) ≤ C := mul_le_of_le_one_right hC.le (by linarith)
    exact (sub_le_sub_right hc _).trans hi
  obtain ⟨hm,hr,hmrate⟩ := highDimensionalMinimax_of_bounds
    (fun i => (Fintype.card (ι i) : ℝ)) W M hd0 hC hW' hRM hM
  have hsample := dimensionPower_isTheta_samplePower (by linarith : 0 < γ) hd0
    (fun i => Nat.cast_nonneg (n i)) (dimensionSample_isTheta hη hnschedule) (-ζ)
  exact ⟨hW',hm,hr,hmrate.trans hsample⟩

include hγ hR hη hd hnschedule in
set_option maxHeartbeats 1000000 in
/-- The original result for an arbitrary smooth half-line profile. Its
extension gives precisely the same filter on the population and empirical
nonnegative spectra. -/
theorem rkhs_spherical_highDimensional_pinsker_halfLine (χ : ℝ → ℝ)
    (hχ : ContDiffOn ℝ ∞ χ (Ici 0))
    (hmono : MonotoneOn χ (Ici 0))
    (hrange : ∀ u ≥ 0, χ u ∈ Icc (0 : ℝ) 1)
    (hbelow : ∀ u ∈ Icc (0 : ℝ) (1/2), χ u = 0)
    (hat : χ 1 = highDimensionalPinskerWeight a s γ R σ η)
    (habove : ∀ u ≥ 2, χ u = 1) :
    let χ' := ResidualFilter.phaseCutoffHalfLineExtension χ
    let hχ' := ResidualFilter.phaseCutoffHalfLineExtension_isProfile hχ hmono hrange hbelow hat habove
    let b := sphericalHighDimensionalPinskerModel ι H Φ hΦ hkernel a ha hseries n hn χ' hχ'
    let W := fun i => canonicalGaussianSourceWorstRisk (b i) s hs.le R hσ
    let M := fun i => (sphericalGaussianMinimaxRisk Φ hΦ.continuousOn (hkernel i) (n i) s hs.le R σ).toReal
    let ζ := highDimensionalRiskExponent s γ
    let C := highDimensionalPinskerConstant a s γ R σ η
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^ζ*W i) l (𝓝 C) ∧
      Tendsto (fun i => (Fintype.card (ι i) : ℝ)^ζ*M i) l (𝓝 C) ∧
      Tendsto (fun i => W i/M i) l (𝓝 1) ∧
      M =Θ[l] (fun i => (n i : ℝ)^(-ζ/γ)) := by
  intro χ' hχ'
  exact rkhs_spherical_highDimensional_pinsker ι H Φ hΦ hkernel a ha hseries
    hs hγ hR hσ hη n hn hd hnschedule χ' hχ'

include hγ hR hη hd hnschedule in
set_option maxHeartbeats 1000000 in
/-- The original KRR schedule and full range 0 < s <= 1 yield the minimax
rate, without assumptions on individual targets' degree energies. -/
theorem rkhs_spherical_highDimensional_krr (hs1 : s ≤ 1) (lam : I → ℝ)
    (hlam : ∀ i, 0 < lam i)
    (hreg : lam =Θ[l] (fun i => (Fintype.card (ι i) : ℝ)^(-highDimensionalRidgeExponent s γ))) :
    let b := sphericalRidgeScaleModel ι H Φ hΦ hkernel (sphericalKernelBound_nonneg Φ)
      (sphericalKernelBound_diag Φ a ha hseries).le n hn lam hlam
    let W := fun i => canonicalGaussianSourceWorstRisk (b i) s hs.le R hσ
    let M := fun i => (sphericalGaussianMinimaxRisk Φ hΦ.continuousOn (hkernel i) (n i) s hs.le R σ).toReal
    W =Θ[l] (fun i => (Fintype.card (ι i) : ℝ)^(-highDimensionalRiskExponent s γ)) ∧
      W =Θ[l] M := by
  intro b W M
  have hκ := sphericalKernelBound_nonneg Φ
  have hdiag := (sphericalKernelBound_diag Φ a ha hseries).le
  obtain ⟨hWM,hW⟩ := spherical_highDimensionalRidge_expected_upper ι H Φ hΦ hkernel hκ hdiag
    n hn lam hlam a ha hseries hs hs1 hγ hη hR hσ hd hnschedule hreg
  let w := highDimensionalPinskerWeight a s γ R σ η
  have hw : w ∈ Ioc (0 : ℝ) 1 := highDimensionalPinskerWeight_mem ha hR hσ hη
  have hχ := ResidualFilter.phaseCutoffProfile_isProfile hw.1.le hw.2
  have hm := (rkhs_spherical_highDimensional_pinsker ι H Φ hΦ hkernel a ha hseries
    hs hγ hR hσ hη n hn hd hnschedule (ResidualFilter.phaseCutoffProfile w) hχ).2.1
  have hC := highDimensionalPinskerConstant_pos (s := s) (γ := γ) ha hR hσ hη
  exact highDimensional_rate_of_minimax_le (fun _ => Nat.cast_pos.mpr Fintype.card_pos)
    hC hm (hWM.mono fun _ hi => hi.1) (hWM.mono fun _ hi => hi.2) hW

end
end KernelSeq
