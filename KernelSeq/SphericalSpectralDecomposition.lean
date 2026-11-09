import KernelSeq.HilbertFiltrationBasis
import KernelSeq.SpherePredictionRange
import KernelSeq.SpherePolynomialLayers
import KernelSeq.SphereZonalEigenfunctions
import KernelSeq.SphereZonalPolynomialModulo

/-!
# An actual spectral basis of the spherical prediction support

The polynomial filtration is transported into the genuine closed prediction
range. Density is a consequence of the actual positive-kernel moment series,
not a hypothesis of the spherical basis. Reindexing retains the actual
ambient layer dimensions, including empty layers and repeated eigenvalues.
-/

namespace KernelSeq
open MeasureTheory Set Submodule
open scoped BigOperators ContDiff
noncomputable section

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "SphereL2" => Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))

abbrev SpherePolynomialSpectralIndex (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :=
  Σ m : ℕ, Fin (Module.finrank ℝ (spherePolynomialLayer ι m))

section Transport
variable (S : H →L[ℝ] Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))

def spherePredictionFiltration (m : ℕ) : Submodule ℝ (PredictionRange S) :=
  (spherePolynomialSpace ι m).comap (PredictionRange S).subtype

instance spherePredictionFiltration_finiteDimensional (m : ℕ) :
    FiniteDimensional ℝ (spherePredictionFiltration S m) := by
  let G := PredictionRange S
  let U := spherePredictionFiltration S m
  have hle : U.map G.subtype ≤ spherePolynomialSpace ι m := by
    change Submodule.map G.subtype ((spherePolynomialSpace ι m).comap G.subtype) ≤ _
    rw [Submodule.map_comap_subtype]
    exact inf_le_right
  letI : FiniteDimensional ℝ (U.map G.subtype) := Submodule.finiteDimensional_of_le hle
  exact FiniteDimensional.of_injective (Submodule.equivSubtypeMap G U).toLinearMap
    (Submodule.equivSubtypeMap G U).injective

theorem spherePredictionFiltration_mono : Monotone (spherePredictionFiltration S) := by
  intro m n hmn x hx
  exact spherePolynomialSpace_mono hmn hx

theorem spherePolynomialSpace_le_polynomialSpan (m : ℕ) :
    spherePolynomialSpace ι m ≤ spherePolynomialSpan ι := by
  apply Submodule.span_le.mpr
  rintro f ⟨a, rfl⟩
  exact le_iSup (homogeneousSpherePolynomialSpace ι) a.1.val
    (Submodule.subset_span (Set.mem_range_self a.2))

private theorem filtration_le_range_of_eq
    (hG : PredictionRange S = (spherePolynomialSpan ι).topologicalClosure) (m : ℕ) :
    spherePolynomialSpace ι m ≤ PredictionRange S := by
  rw [hG]
  exact (spherePolynomialSpace_le_polynomialSpan m).trans (Submodule.le_topologicalClosure _)

/-- This transports an already-proved ambient closure equality into the
actual supported Hilbert space. -/
private theorem spherePredictionFiltration_dense_of_range_eq
    (hG : PredictionRange S = (spherePolynomialSpan ι).topologicalClosure) :
    (⨆ m, spherePredictionFiltration S m).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro x hx
  have hxo : (x : SphereL2) ∈ Submodule.orthogonal (spherePolynomialSpan ι) := by
    rw [spherePolynomialSpan, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro m
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    have hF : y ∈ spherePolynomialSpace ι m := homogeneousSpherePolynomialSpace_le_filtration le_rfl hy
    let yG : PredictionRange S := ⟨y, filtration_le_range_of_eq S hG m hF⟩
    have hyG : yG ∈ spherePredictionFiltration S m := hF
    exact (Submodule.mem_orthogonal _ x).mp hx yG (le_iSup (spherePredictionFiltration S) m hyG)
  have hxoG : (x : SphereL2) ∈ Submodule.orthogonal (PredictionRange S) := by
    have he : (PredictionRange S).orthogonal = (spherePolynomialSpan ι).orthogonal := by
      rw [hG, Submodule.orthogonal_closure]
    exact he.symm ▸ hxo
  have hzero : (x : SphereL2) = 0 :=
    (inner_self_eq_zero (𝕜 := ℝ)).mp (Submodule.inner_right_of_mem_orthogonal x.property hxoG)
  exact (Submodule.mem_bot ℝ).mpr (Subtype.ext hzero)

theorem spherePredictionFiltration_layer_eq_comap
    (hG : PredictionRange S = (spherePolynomialSpan ι).topologicalClosure) (m : ℕ) :
    hilbertFiltrationLayer (spherePredictionFiltration S) m =
      (spherePolynomialLayer ι m).comap (PredictionRange S).subtype := by
  cases m with
  | zero => rfl
  | succ m =>
    ext x
    change ((x : SphereL2) ∈ spherePolynomialSpace ι (m+1) ∧
      x ∈ Submodule.orthogonal (spherePredictionFiltration S m)) ↔
      ((x : SphereL2) ∈ spherePolynomialSpace ι (m+1) ∧
        (x : SphereL2) ∈ Submodule.orthogonal (spherePolynomialSpace ι m))
    constructor
    · intro hx
      refine ⟨hx.1, (Submodule.mem_orthogonal _ _).mpr ?_⟩
      intro y hy
      let yG : PredictionRange S := ⟨y, filtration_le_range_of_eq S hG m hy⟩
      exact (Submodule.mem_orthogonal _ x).mp hx.2 yG (show yG ∈ spherePredictionFiltration S m from hy)
    · intro hx
      refine ⟨hx.1, (Submodule.mem_orthogonal _ _).mpr ?_⟩
      intro y hy
      exact (Submodule.mem_orthogonal _ (x : SphereL2)).mp hx.2 (y : SphereL2) hy

theorem spherePredictionFiltration_layer_finrank
    (hG : PredictionRange S = (spherePolynomialSpan ι).topologicalClosure) (m : ℕ) :
    Module.finrank ℝ (hilbertFiltrationLayer (spherePredictionFiltration S) m) =
      Module.finrank ℝ (spherePolynomialLayer ι m) := by
  rw [spherePredictionFiltration_layer_eq_comap S hG]
  let G := PredictionRange S
  let W := spherePolynomialLayer ι m
  let U := W.comap G.subtype
  have hW : W ≤ G := (spherePolynomialLayer_le_filtration m).trans (filtration_le_range_of_eq S hG m)
  have hmap : U.map G.subtype = W := by
    change Submodule.map G.subtype (W.comap G.subtype) = W
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hW]
  exact ((Submodule.equivSubtypeMap G U).trans (LinearEquiv.ofEq _ _ hmap)).finrank_eq

private def spherePredictionIndexEquiv
    (hG : PredictionRange S = (spherePolynomialSpan ι).topologicalClosure) :
    SpherePolynomialSpectralIndex ι ≃
      Σ m : ℕ, Fin (Module.finrank ℝ (hilbertFiltrationLayer (spherePredictionFiltration S) m)) :=
  Equiv.sigmaCongrRight (fun m => finCongr (spherePredictionFiltration_layer_finrank S hG m).symm)

set_option maxHeartbeats 1800000 in
private def spherePredictionBasisOfRangeEq
    (hG : PredictionRange S = (spherePolynomialSpan ι).topologicalClosure) :
    HilbertBasis (SpherePolynomialSpectralIndex ι) ℝ (PredictionRange S) := by
  let b := hilbertFiltrationBasis (spherePredictionFiltration S) (spherePredictionFiltration_mono S)
    (spherePredictionFiltration_dense_of_range_eq S hG)
  let e := spherePredictionIndexEquiv S hG
  have hd : ⊤ ≤ (span ℝ (Set.range ((b : _ → PredictionRange S) ∘ e))).topologicalClosure := by
    rw [Set.range_comp, e.range_eq_univ, Set.image_univ, b.dense_span]
  exact HilbertBasis.mk (b.orthonormal.comp e e.injective) hd

set_option maxHeartbeats 1800000 in
private theorem spherePredictionBasisOfRangeEq_mem_layer
    (hG : PredictionRange S = (spherePolynomialSpan ι).topologicalClosure)
    (p : SpherePolynomialSpectralIndex ι) :
    (spherePredictionBasisOfRangeEq S hG p : SphereL2) ∈ spherePolynomialLayer ι p.1 := by
  let e := spherePredictionIndexEquiv S hG
  have hp := hilbertFiltrationBasis_mem_layer (spherePredictionFiltration S)
    (spherePredictionFiltration_mono S) (spherePredictionFiltration_dense_of_range_eq S hG) (e p)
  have he : (e p).1 = p.1 := rfl
  rw [he, spherePredictionFiltration_layer_eq_comap S hG] at hp
  unfold spherePredictionBasisOfRangeEq
  rw [HilbertBasis.coe_mk]
  exact hp

end Transport

section Zonal
variable [CompleteSpace H]

variable (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)

/-- A genuine Hilbert basis of the actual supported prediction range. Its
index records the actual dimension of each orthogonal polynomial layer. -/
def zonalSpherePredictionBasis : HilbertBasis (SpherePolynomialSpectralIndex ι) ℝ
    (PredictionRange (featureEmbedding uniformSphere k hk)) :=
  spherePredictionBasisOfRangeEq (featureEmbedding uniformSphere k hk)
    (sphere_predictionRange_eq_polynomialClosure k hk a ha Φ hseries hkernel)

theorem zonalSpherePredictionBasis_mem_layer (p : SpherePolynomialSpectralIndex ι) :
    (zonalSpherePredictionBasis k hk a ha Φ hseries hkernel p : SphereL2) ∈ spherePolynomialLayer ι p.1 :=
  spherePredictionBasisOfRangeEq_mem_layer _ _ p

/-- The constant layer is genuinely the old squarefree degree-zero block. -/
theorem spherePolynomialSpace_zero_eq_squarefree : spherePolynomialSpace ι 0 = squarefreeSphereBlock ι 0 := by
  symm
  apply Submodule.eq_of_le_of_finrank_le
    ((squarefreeSphereBlock_le_homogeneous 0).trans (homogeneousSpherePolynomialSpace_le_filtration le_rfl))
  have hh := spherePolynomialSpace_finrank_upper (ι := ι) 0
  have hsum : (∑ j : Fin (0+1), (Fintype.card ι+j.val-1).choose j.val) = 1 := by
    simp
  rw [hsum] at hh
  simpa only [squarefreeSphereBlock_finrank, Nat.choose_zero_right] using hh


variable (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
include ha hseries hkernel hΦ

set_option maxHeartbeats 1400000 in
theorem zonalSpherePrediction_preserves_filtration (m : ℕ) :
    ∀ f ∈ spherePolynomialSpace ι m,
      predictionCovariance (featureEmbedding uniformSphere k hk) f ∈ spherePolynomialSpace ι m := by
  let T : SphereL2 →L[ℝ] SphereL2 := predictionCovariance (featureEmbedding uniformSphere k hk)
  suffices hh : spherePolynomialSpace ι m ≤ (spherePolynomialSpace ι m).comap T.toLinearMap from
    fun _ hf => hh hf
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  change T (sphereSymLp s.2) ∈ spherePolynomialSpace ι m
  have hmod := predictionCovariance_sphereSymLp_mod_polynomial_of_powerSeries
    k hk a (fun j => (ha j).le) Φ hseries hΦ hkernel s.2
  have hdeg : s.1.val ≤ m := Nat.le_of_lt_succ s.1.isLt
  have hh := spherePolynomialSpace_mono (ι := ι) ((Nat.sub_le _ _).trans hdeg) hmod
  have hs : sphereSymLp s.2 ∈ spherePolynomialSpace ι m := Submodule.subset_span (Set.mem_range_self s)
  have hz := Submodule.add_mem _ hh (Submodule.smul_mem _ (zonalSphereDegreeValue (ι := ι) a s.1.val) hs)
  rw [sub_add_cancel] at hz
  exact hz

set_option maxHeartbeats 1600000 in
theorem zonalSpherePrediction_mod_predecessor (m : ℕ) :
    ∀ f ∈ spherePolynomialSpace ι (m+1),
      predictionCovariance (featureEmbedding uniformSphere k hk) f -
        zonalSphereDegreeValue (ι := ι) a (m+1) • f ∈ spherePolynomialSpace ι m := by
  let T : SphereL2 →L[ℝ] SphereL2 := predictionCovariance (featureEmbedding uniformSphere k hk)
  let c : ℝ := zonalSphereDegreeValue (ι := ι) a (m+1)
  let D : SphereL2 →ₗ[ℝ] SphereL2 := T.toLinearMap - c • LinearMap.id
  suffices hh : spherePolynomialSpace ι (m+1) ≤ (spherePolynomialSpace ι m).comap D from
    fun _ hf => hh hf
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  change T (sphereSymLp s.2) - c • sphereSymLp s.2 ∈ spherePolynomialSpace ι m
  by_cases hs : s.1.val ≤ m
  · have hv : sphereSymLp s.2 ∈ spherePolynomialSpace ι m :=
      homogeneousSpherePolynomialSpace_le_filtration hs (Submodule.subset_span (Set.mem_range_self s.2))
    exact Submodule.sub_mem _ (zonalSpherePrediction_preserves_filtration k hk a ha Φ hseries hkernel hΦ m _ hv)
      (Submodule.smul_mem _ _ hv)
  · have hdeg : s.1.val = m+1 := by have := s.1.isLt; omega
    have hmod := predictionCovariance_sphereSymLp_mod_polynomial_of_powerSeries
      k hk a (fun j => (ha j).le) Φ hseries hΦ hkernel s.2
    have hh := spherePolynomialSpace_mono (ι := ι) (show s.1.val-2 ≤ m by omega) hmod
    have hc : zonalSphereDegreeValue (ι := ι) a s.1.val = c :=
      congrArg (zonalSphereDegreeValue (ι := ι) a) hdeg
    rw [hc] at hh
    exact hh

/-- The actual full covariance acts by the genuine zonal degree value on
every orthogonal polynomial layer, not only on its squarefree subspace. -/
theorem zonalSpherePrediction_eigen_on_layer (m : ℕ) {f : SphereL2}
    (hf : f ∈ spherePolynomialLayer ι m) :
    predictionCovariance (featureEmbedding uniformSphere k hk) f =
      zonalSphereDegreeValue (ι := ι) a m • f := by
  cases m with
  | zero =>
    have hf' : f ∈ squarefreeSphereBlock ι 0 := by
      change f ∈ spherePolynomialSpace ι 0 at hf
      rwa [spherePolynomialSpace_zero_eq_squarefree] at hf
    exact predictionCovariance_squarefreeSphereBlock_eigen k hk a (fun j => (ha j).le) Φ hseries hkernel 0 f hf'
  | succ m =>
    exact symmetric_eigen_of_scalar_mod_lower _
      (predictionCovariance_isPositive (featureEmbedding uniformSphere k hk)).isSymmetric
      (spherePolynomialSpace ι m) (spherePolynomialSpace ι (m+1)) (zonalSphereDegreeValue (ι := ι) a (m+1))
      (zonalSpherePrediction_preserves_filtration k hk a ha Φ hseries hkernel hΦ m)
      (zonalSpherePrediction_mod_predecessor k hk a ha Φ hseries hkernel hΦ m) hf

/-- Every actual supported basis vector is an eigenvector with the value
indexed by its degree. Empty layers contribute no vectors. -/
theorem zonalSpherePredictionBasis_eigen (p : SpherePolynomialSpectralIndex ι) :
    predictionCovariance (featureEmbedding uniformSphere k hk)
      (zonalSpherePredictionBasis k hk a ha Φ hseries hkernel p : SphereL2) =
      zonalSphereDegreeValue (ι := ι) a p.1 •
        (zonalSpherePredictionBasis k hk a ha Φ hseries hkernel p : SphereL2) :=
  zonalSpherePrediction_eigen_on_layer k hk a ha Φ hseries hkernel hΦ p.1
    (zonalSpherePredictionBasis_mem_layer k hk a ha Φ hseries hkernel p)

end Zonal
end
end KernelSeq
