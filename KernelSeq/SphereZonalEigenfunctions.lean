import KernelSeq.SphereZonalMoments
import KernelSeq.SphereMonomialBlock
import KernelSeq.PopulationCovariance
import KernelSeq.SphericalLeverage

/-!
# Actual polynomial eigenfunctions of the full zonal prediction operator

The original convergent positive Φ expansion is integrated against actual
squarefree functions. The resulting L² eigenfunction equation uses the real
canonical embedding and its actual adjoint pairing. No eigenvalue, block
invariance or kernel-integral operator identification is assumed.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped BigOperators
noncomputable section

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem predictionCovariance_squarefreeSphereLp_eigen
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)
    {m : ℕ} (s : SquarefreeSphereIndex ι m) :
    predictionCovariance (featureEmbedding uniformSphere k hk) (squarefreeSphereLp s) =
      zonalSphereDegreeValue (ι := ι) a m • squarefreeSphereLp s := by
  let S := featureEmbedding uniformSphere k hk
  have hpoint (x : KernelSphere (EuclideanSpace ℝ ι)) :
      inner ℝ (k x) (S.adjoint (squarefreeSphereLp s)) =
        zonalSphereDegreeValue (ι := ι) a m * sphereCoordinateProduct s.val x := by
    rw [featureEmbedding_adjoint_pairing]
    calc
      _ = ∫ y : KernelSphere (EuclideanSpace ℝ ι),
          sphereCoordinateProduct s.val y * zonalSphereKernel Φ x y ∂uniformSphere := by
        apply integral_congr_ae
        filter_upwards [(sphereCoordinateProduct_memLp s.val).coeFn_toLp] with y hy
        change (squarefreeSphereLp s) y = sphereCoordinateProduct s.val y at hy
        rw [hy, hkernel]
        unfold zonalSphereKernel
        rw [real_inner_comm (y : EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ ι)]
        ring
      _ = _ := by
        rw [integral_zonalSphereKernel_mul_squarefree a ha Φ hseries,
          squarefreeSphereIndex_card]
  change S (S.adjoint (squarefreeSphereLp s)) = _
  apply Lp.ext
  filter_upwards [featureEmbedding_ae uniformSphere k hk (S.adjoint (squarefreeSphereLp s)),
    Lp.coeFn_smul (zonalSphereDegreeValue (ι := ι) a m) (squarefreeSphereLp s),
    (sphereCoordinateProduct_memLp s.val).coeFn_toLp] with x hx hs hxF
  change S (S.adjoint (squarefreeSphereLp s)) x = _ at hx
  change (squarefreeSphereLp s) x = sphereCoordinateProduct s.val x at hxF
  rw [hx, hpoint, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hxF]

theorem predictionCovariance_normalizedSquarefreeSphereLp_eigen
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)
    {m : ℕ} (s : SquarefreeSphereIndex ι m) :
    predictionCovariance (featureEmbedding uniformSphere k hk) (normalizedSquarefreeSphereLp s) =
      zonalSphereDegreeValue (ι := ι) a m • normalizedSquarefreeSphereLp s := by
  unfold normalizedSquarefreeSphereLp
  rw [map_smul, predictionCovariance_squarefreeSphereLp_eigen k hk a ha Φ hseries hkernel s]
  simp only [smul_smul, mul_comm]

/-- The full genuinely constructed squarefree block is invariant, with one
actual common eigenvalue. This is not a claim that it exhausts all harmonics. -/
theorem predictionCovariance_squarefreeSphereBlock_eigen
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)
    (m : ℕ) (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))
    (hf : f ∈ squarefreeSphereBlock ι m) :
    predictionCovariance (featureEmbedding uniformSphere k hk) f =
      zonalSphereDegreeValue (ι := ι) a m • f := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
  rw [← hc, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold normalizedSquarefreeSphereLp
  rw [map_smul, map_smul, predictionCovariance_squarefreeSphereLp_eigen k hk a ha Φ hseries hkernel s]
  simp only [smul_smul]
  congr 1
  ring

/-- The constructed value is a genuine nonnegative bounded-operator
eigenvalue when the degree block is nonempty. -/
theorem zonalSphereDegreeValue_le_covariance_norm
    (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)
    (m : ℕ) (hmd : m ≤ Fintype.card ι) :
    zonalSphereDegreeValue (ι := ι) a m ≤
      ‖populationCovariance (featureEmbedding uniformSphere k hk)‖ := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (by simpa using hmd)
  let si : SquarefreeSphereIndex ι m := ⟨s, Finset.mem_powersetCard.mpr ⟨hs, hcard⟩⟩
  let S := featureEmbedding uniformSphere k hk
  have he := predictionCovariance_normalizedSquarefreeSphereLp_eigen k hk a ha Φ hseries hkernel si
  have hn := (normalizedSquarefreeSphereLp_orthonormal (ι := ι) m).norm_eq_one si
  have hh := (predictionCovariance S).le_opNorm (normalizedSquarefreeSphereLp si)
  rw [he, norm_smul, Real.norm_of_nonneg (zonalSphereDegreeValue_nonneg a ha m), hn, mul_one, mul_one] at hh
  have hnorm : ‖predictionCovariance S‖ = ‖populationCovariance S‖ := by
    rw [populationCovariance_norm]
    change ‖S.comp S.adjoint‖ = ‖S‖^2
    simpa only [pow_two, ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map] using
      S.adjoint.norm_adjoint_comp_self
  exact hh.trans_eq hnorm

section RKHS
variable [SecondCountableTopology H] [RKHS ℝ H (KernelSphere (EuclideanSpace ℝ ι)) ℝ]

theorem zonalSphereRKHS_squarefree_eigen
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    {m : ℕ} (s : SquarefreeSphereIndex ι m) :
    let k := rkhsFeature (H := H)
    let hk := zonalSphereFeature_memLp Φ hΦ hkernel
    predictionCovariance (featureEmbedding uniformSphere k hk) (squarefreeSphereLp s) =
      zonalSphereDegreeValue (ι := ι) a m • squarefreeSphereLp s := by
  dsimp only
  apply predictionCovariance_squarefreeSphereLp_eigen _ _ a ha Φ hseries
  intro x y
  rw [rkhsFeature_inner, rkhsFeature_apply, hkernel]

theorem zonalSphereRKHS_normalized_squarefree_eigen
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    {m : ℕ} (s : SquarefreeSphereIndex ι m) :
    let k := rkhsFeature (H := H)
    let hk := zonalSphereFeature_memLp Φ hΦ hkernel
    predictionCovariance (featureEmbedding uniformSphere k hk) (normalizedSquarefreeSphereLp s) =
      zonalSphereDegreeValue (ι := ι) a m • normalizedSquarefreeSphereLp s := by
  dsimp only
  apply predictionCovariance_normalizedSquarefreeSphereLp_eigen _ _ a ha Φ hseries
  intro x y
  rw [rkhsFeature_inner, rkhsFeature_apply, hkernel]


end RKHS
end
end KernelSeq
