import KernelSeq.SphericalSpectralDecomposition
import KernelSeq.SupportedEigenvalueBasis

/-!
# The actual positive spectrum of the zonal prediction operator

The supported polynomial basis classifies every positive spectral value.
A squarefree coordinate of an available degree realizes that degree value
in the selected positive singular spectrum.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped ContDiff
noncomputable section

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
  (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
  (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j * t^j) (Φ t))
  (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)

local notation "S" => featureEmbedding uniformSphere k hk

include ha hseries hkernel in
theorem spherical_positiveSpectrum_degree
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    (i : PredictionSingularIndex S) :
    ∃ j : ℕ, zonalSphereDegreeValue (ι := ι) a j = i.1.1 := by
  let hc := populationCovariance_feature_isCompact uniformSphere k hk
  let e := predictionSingularBasis S hc i
  have he : (e : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) ≠ 0 := by
    intro h
    have hn := (predictionSingularBasis S hc).orthonormal.norm_eq_one i
    change ‖(e : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))‖ = 1 at hn
    rw [h,norm_zero] at hn
    norm_num at hn
  obtain ⟨j,hj⟩ := predictionEigenvalue_occurs_in_supported_basis S
    (zonalSpherePredictionBasis k hk a ha Φ hseries hkernel)
    (fun j => zonalSphereDegreeValue (ι := ι) a j.1)
    (zonalSpherePredictionBasis_eigen k hk a ha Φ hseries hkernel hΦ)
    e.property he (predictionSingularBasis_eigen S hc i)
  exact ⟨j.1,hj⟩

include ha hseries hkernel in
theorem spherical_positiveSpectrum_contains_degree (m : ℕ) (hm : m ≤ Fintype.card ι) :
    ∃ i : PredictionSingularIndex S, i.1.1 = zonalSphereDegreeValue (ι := ι) a m := by
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (by simpa using hm)
  let si : SquarefreeSphereIndex ι m := ⟨s,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hs⟩⟩
  have he : normalizedSquarefreeSphereLp si ≠ 0 := by
    intro h
    have hn := (normalizedSquarefreeSphereLp_orthonormal (ι := ι) m).norm_eq_one si
    rw [h,norm_zero] at hn
    norm_num at hn
  exact predictionSingularIndex_occurs_of_positive_eigen S
    (populationCovariance_feature_isCompact uniformSphere k hk) he
    (zonalSphereDegreeValue_pos a (fun j => (ha j).le) Φ hseries m hm (ha m))
    (predictionCovariance_normalizedSquarefreeSphereLp_eigen k hk a
      (fun j => (ha j).le) Φ hseries hkernel si)

end
end KernelSeq
