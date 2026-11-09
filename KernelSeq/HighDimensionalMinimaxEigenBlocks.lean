import KernelSeq.FiniteEigenFilterDimension
import KernelSeq.SphereZonalEigenfunctions

/-!
# Actual finite spherical blocks in the population spectral coordinates

Each constructed orthonormal degree block embeds into the selected positive
spectral coordinates, with its full dimension. The embedding follows from
the finite-dimensional nonzero eigenspace and its actual Hilbert basis.
-/

namespace KernelSeq
open MeasureTheory Set
noncomputable section

variable {H E J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype J]

private theorem nonempty_eigenspaceBasisSet_embedding_of_orthonormal
    (T : H →L[ℝ] H) (hc : IsCompactOperator T) {t : ℝ} (ht : t ≠ 0)
    (v : J → H) (hv : Orthonormal ℝ v) (heig : ∀ j, T (v j) = t • v j) :
    Nonempty (J ↪ eigenspaceBasisSet T t) := by
  classical
  let V := Module.End.eigenspace (T : Module.End ℝ H) t
  letI : FiniteDimensional ℝ V := T.finite_dimensional_eigenspace hc t ht
  let u (j : J) : V := ⟨v j, Module.End.mem_eigenspace_iff.mpr (heig j)⟩
  have hu : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    exact hv i j
  let b := eigenspaceHilbertBasis T t
  letI : Finite (eigenspaceBasisSet T t) := b.orthonormal.linearIndependent.finite
  letI : Fintype (eigenspaceBasisSet T t) := Fintype.ofFinite _
  have hcard : Module.finrank ℝ V = Fintype.card (eigenspaceBasisSet T t) :=
    Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis
  exact Function.Embedding.nonempty_of_card_le (hu.linearIndependent.fintype_card_le_finrank.trans_eq hcard)

/-- A finite orthonormal prediction eigensystem with a common positive
eigenvalue supplies that many genuine positive spectral coordinates. -/
theorem exists_prediction_index_embedding_of_orthonormal_block
    (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    (e : J → E) (he : Orthonormal ℝ e) {t : ℝ} (ht : 0 < t)
    (heig : ∀ j, (S.comp S.adjoint) (e j) = t • e j) :
    ∃ jmap : J → PredictionSingularIndex S, Function.Injective jmap ∧ ∀ j, (jmap j).1.1 = t := by
  let v := finitePredictionDomainVector S e (fun _ => t)
  have hv : Orthonormal ℝ v := finitePredictionDomainVector_orthonormal S e he _ (fun _ => ht) heig
  have hT (j : J) : (S.adjoint.comp S) (v j) = t • v j :=
    finitePredictionDomainVector_eigen S e (fun _ => t) heig j
  obtain ⟨f⟩ := nonempty_eigenspaceBasisSet_embedding_of_orthonormal (S.adjoint.comp S) hc ht.ne' v hv hT
  refine ⟨fun j => ⟨⟨t, f j⟩, ht⟩, ?_, fun _ => rfl⟩
  intro i j hij
  apply f.injective
  have h : (⟨t, f i⟩ : CompactSpectralIndex (S.adjoint.comp S)) = ⟨t, f j⟩ := congrArg Subtype.val hij
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

section Sphere
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [SecondCountableTopology H] [RKHS ℝ H (KernelSphere (EuclideanSpace ℝ ι)) ℝ]

theorem zonalSphere_exists_squarefree_prediction_index_embedding
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    (m : ℕ) (hmd : m ≤ Fintype.card ι) (ham : 0 < a m) :
    let k := rkhsFeature (H := H)
    let hk := zonalSphereFeature_memLp Φ hΦ hkernel
    ∃ jmap : SquarefreeSphereIndex ι m → PredictionSingularIndex (featureEmbedding uniformSphere k hk),
      Function.Injective jmap ∧ ∀ j, (jmap j).1.1 = zonalSphereDegreeValue (ι := ι) a m := by
  dsimp only
  apply exists_prediction_index_embedding_of_orthonormal_block _
    (populationCovariance_feature_isCompact uniformSphere _ _)
    (normalizedSquarefreeSphereLp (ι := ι) (m := m)) (normalizedSquarefreeSphereLp_orthonormal m)
    (zonalSphereDegreeValue_pos a ha Φ hseries m hmd ham)
  intro j
  exact zonalSphereRKHS_normalized_squarefree_eigen Φ hΦ hkernel a ha hseries j

end Sphere
end
end KernelSeq
