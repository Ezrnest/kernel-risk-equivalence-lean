import KernelSeq.SequenceBenchmark
import KernelSeq.CompactEmbedding

/-!
# A constructed supported polar isometry and prediction norm bridges

The isometry is synthesized from the actual positive singular systems, rather
than supplied as a polar factor hypothesis. It embeds the supported prediction
space into the original feature Hilbert space, without a separability or
closed-range assumption. Only the actual covariance is required compact.
-/

open Submodule

namespace KernelSeq

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem positiveDomainBasis_orthonormal (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) :
    Orthonormal ℝ (fun i : PredictionSingularIndex S => singularDomainBasis S hc i.1) :=
  (singularDomainBasis S hc).orthonormal.comp Subtype.val Subtype.val_injective

/-- The actual inverse polar map on the supported prediction space. -/
def supportedPolarIsometry (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) : PredictionRange S →ₗᵢ[ℝ] H :=
  (positiveDomainBasis_orthonormal S hc).orthogonalFamily.linearIsometry.comp
    (predictionSingularBasis S hc).repr.toLinearIsometry

@[simp]
theorem supportedPolarIsometry_basis (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (i : PredictionSingularIndex S) :
    supportedPolarIsometry S hc (predictionSingularBasis S hc i) = singularDomainBasis S hc i.1 := by
  classical
  change (positiveDomainBasis_orthonormal S hc).orthogonalFamily.linearIsometry
    ((predictionSingularBasis S hc).repr (predictionSingularBasis S hc i)) = _
  rw [HilbertBasis.repr_self, OrthogonalFamily.linearIsometry_apply_single]
  simp only [LinearIsometry.toSpanSingleton_apply, one_smul]

/-- The actual constructed square root acts on every eigenvector, including
zero eigenvectors and the unregularized case. -/
theorem compactRegularizedSqrt_eigen (T : H →L[ℝ] H) (hc : IsCompactOperator T)
    (hp : T.IsPositive) (lam : ℝ) {x : H} {t : ℝ} (hx : T x = t • x) :
    compactRegularizedSqrt T hc hp lam x = Real.sqrt (t + lam) • x := by
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖,
      |Real.sqrt (t + lam)| ≤ Real.sqrt (‖T‖ + lam) := by
    intro t ht
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith [ht.2])
  exact compactSpectralMultiplier_eigen T hc hp (fun t => Real.sqrt (t + lam))
    (Real.sqrt (‖T‖ + lam)) (Real.sqrt_nonneg _) hb hx

/-- The actual adjoint is `sqrt(S* S)` after the constructed supported polar
isometry; no polar-decomposition equality is assumed. -/
theorem adjoint_eq_sqrt_polar (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) :
    S.adjoint.comp (PredictionRange S).subtypeL =
      (compactRegularizedSqrt (S.adjoint.comp S) hc
        (ContinuousLinearMap.isPositive_adjoint_comp_self S) 0).comp
          (supportedPolarIsometry S hc).toContinuousLinearMap := by
  apply continuousLinearMap_eq_of_hilbertBasis (predictionSingularBasis S hc)
  intro i
  change S.adjoint (predictionSingularBasis S hc i : E) =
    compactRegularizedSqrt (S.adjoint.comp S) hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) 0
        (supportedPolarIsometry S hc (predictionSingularBasis S hc i))
  rw [predictionSingularBasis_adjoint, supportedPolarIsometry_basis]
  have he : (S.adjoint.comp S) (singularDomainBasis S hc i.1) =
      i.1.1 • singularDomainBasis S hc i.1 :=
    compactEigenbasis_eigen _ hc (ContinuousLinearMap.isPositive_adjoint_comp_self S).isSymmetric i.1
  symm
  simpa only [add_zero] using compactRegularizedSqrt_eigen _ hc _ 0 he

theorem adjoint_apply_eq_sqrt_polar (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (f : PredictionRange S) :
    S.adjoint (f : E) = compactRegularizedSqrt (S.adjoint.comp S) hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) 0 (supportedPolarIsometry S hc f) :=
  congrArg (fun A : PredictionRange S →L[ℝ] H => A f) (adjoint_eq_sqrt_polar S hc)

/-- The two actual image norms agree for every feature-space vector. -/
theorem norm_embedding_eq_norm_covariance_sqrt (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (z : H) :
    ‖S z‖ = ‖compactRegularizedSqrt (S.adjoint.comp S) hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) 0 z‖ := by
  let R := compactRegularizedSqrt (S.adjoint.comp S) hc
    (ContinuousLinearMap.isPositive_adjoint_comp_self S) 0
  have hR : R.adjoint.comp R = S.adjoint.comp S := by
    change R.adjoint * R = _
    rw [(compactRegularizedSqrt_isSelfAdjoint _ hc _ 0).adjoint_eq,
      compactRegularizedSqrt_sq _ hc _ 0 le_rfl]
    simp only [zero_smul, add_zero]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  rw [hR]

/-- The actual prediction/feature interaction norm bridge used in the
localized-interaction argument. The operator `G` is arbitrary and need not
commute with either covariance. -/
theorem prediction_interaction_norm_eq (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (G : H →L[ℝ] H) (f : PredictionRange S) :
    ‖S (G (S.adjoint (f : E)))‖ =
      ‖compactRegularizedSqrt (S.adjoint.comp S) hc
        (ContinuousLinearMap.isPositive_adjoint_comp_self S) 0
        (G (compactRegularizedSqrt (S.adjoint.comp S) hc
          (ContinuousLinearMap.isPositive_adjoint_comp_self S) 0 (supportedPolarIsometry S hc f)))‖ := by
  rw [norm_embedding_eq_norm_covariance_sqrt S hc, adjoint_apply_eq_sqrt_polar S hc]

/-- The actual prediction multiplier restricted to its invariant supported
space. Prediction covariance compactness is derived from domain covariance. -/
def supportedPredictionMultiplier (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |m t| ≤ K) :
    PredictionRange S →L[ℝ] PredictionRange S :=
  (compactSpectralMultiplier (S.comp S.adjoint)
    (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
    (ContinuousLinearMap.isPositive_self_comp_adjoint S) m K hK hm).restrict
      (fun _ hx => compactSpectralMultiplier_mem_predictionRange S
        (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc) m K hK hm hx)

@[simp]
theorem supportedPredictionMultiplier_basis (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |m t| ≤ K)
    (i : PredictionSingularIndex S) :
    supportedPredictionMultiplier S hc m K hK hm (predictionSingularBasis S hc i) =
      m i.1.1 • predictionSingularBasis S hc i := by
  apply Subtype.ext
  exact compactSpectralMultiplier_eigen _
    (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
    (ContinuousLinearMap.isPositive_self_comp_adjoint S) m K hK hm
    (predictionSingularBasis_eigen S hc i)

/-- Actual bounded spectral profiles intertwine through the constructed
isometry. The profile may be discontinuous and the two bounds may differ. -/
theorem supportedPolarIsometry_multiplier_intertwining (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (m : ℝ → ℝ)
    (KT KL : ℝ) (hKT : 0 ≤ KT) (hKL : 0 ≤ KL)
    (hmT : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.adjoint.comp S‖, |m t| ≤ KT)
    (hmL : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |m t| ≤ KL) :
    (supportedPolarIsometry S hc).toContinuousLinearMap.comp
        (supportedPredictionMultiplier S hc m KL hKL hmL) =
      (compactSpectralMultiplier (S.adjoint.comp S) hc
        (ContinuousLinearMap.isPositive_adjoint_comp_self S) m KT hKT hmT).comp
          (supportedPolarIsometry S hc).toContinuousLinearMap := by
  apply continuousLinearMap_eq_of_hilbertBasis (predictionSingularBasis S hc)
  intro i
  change supportedPolarIsometry S hc
      (supportedPredictionMultiplier S hc m KL hKL hmL (predictionSingularBasis S hc i)) =
    compactSpectralMultiplier (S.adjoint.comp S) hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) m KT hKT hmT
        (supportedPolarIsometry S hc (predictionSingularBasis S hc i))
  rw [supportedPredictionMultiplier_basis, map_smul, supportedPolarIsometry_basis]
  have he : (S.adjoint.comp S) (singularDomainBasis S hc i.1) =
      i.1.1 • singularDomainBasis S hc i.1 :=
    compactEigenbasis_eigen _ hc (ContinuousLinearMap.isPositive_adjoint_comp_self S).isSymmetric i.1
  exact (compactSpectralMultiplier_eigen _ hc _ m KT hKT hmT he).symm

theorem prediction_multiplier_norm_eq (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (m : ℝ → ℝ)
    (KT KL : ℝ) (hKT : 0 ≤ KT) (hKL : 0 ≤ KL)
    (hmT : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.adjoint.comp S‖, |m t| ≤ KT)
    (hmL : ∀ t ∈ Set.Icc (0 : ℝ) ‖S.comp S.adjoint‖, |m t| ≤ KL)
    (f : PredictionRange S) :
    ‖compactSpectralMultiplier (S.comp S.adjoint)
      (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) m KL hKL hmL (f : E)‖ =
    ‖compactSpectralMultiplier (S.adjoint.comp S) hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) m KT hKT hmT (supportedPolarIsometry S hc f)‖ := by
  have he := congrArg (fun A : PredictionRange S →L[ℝ] H => A f)
    (supportedPolarIsometry_multiplier_intertwining S hc m KT KL hKT hKL hmT hmL)
  change supportedPolarIsometry S hc (supportedPredictionMultiplier S hc m KL hKL hmL f) = _ at he
  calc
    _ = ‖supportedPredictionMultiplier S hc m KL hKL hmL f‖ := rfl
    _ = ‖supportedPolarIsometry S hc (supportedPredictionMultiplier S hc m KL hKL hmL f)‖ :=
      ((supportedPolarIsometry S hc).norm_map _).symm
    _ = _ := congrArg norm he

/-- The residual norm appearing in the localized prediction theorem is
exactly its feature-space spectral norm. -/
theorem prediction_residual_norm_eq (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (φ : ℝ → ℝ) {M : ℝ}
    (hMT : ‖S.adjoint.comp S‖ ≤ M) (hML : ‖S.comp S.adjoint‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (f : PredictionRange S) :
    ‖compactResidualOperator (S.comp S.adjoint)
      (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hML hf (f : E)‖ =
    ‖compactResidualOperator (S.adjoint.comp S) hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hMT hf (supportedPolarIsometry S hc f)‖ :=
  prediction_multiplier_norm_eq S hc (ResidualFilter.residual φ) 1 1 zero_le_one zero_le_one
    (fun _ ht => hf.residual_abs_le_one ⟨ht.1, ht.2.trans hMT⟩)
    (fun _ ht => hf.residual_abs_le_one ⟨ht.1, ht.2.trans hML⟩) f

/-- The same exact bridge for the manuscript's residual/source weight. -/
theorem prediction_residualWeight_norm_eq (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (φ : ℝ → ℝ) {M lam α : ℝ}
    (hlam : 0 < lam) (hα : 0 ≤ α)
    (hMT : ‖S.adjoint.comp S‖ ≤ M) (hML : ‖S.comp S.adjoint‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (f : PredictionRange S) :
    ‖compactResidualWeightOperator (S.comp S.adjoint)
      (isCompactOperator_comp_adjoint_of_adjoint_comp_self S hc)
      (ContinuousLinearMap.isPositive_self_comp_adjoint S) φ hlam hα hML hf (f : E)‖ =
    ‖compactResidualWeightOperator (S.adjoint.comp S) hc
      (ContinuousLinearMap.isPositive_adjoint_comp_self S) φ hlam hα hMT hf (supportedPolarIsometry S hc f)‖ :=
  prediction_multiplier_norm_eq S hc (residualWeight lam α φ) 2 2 (by norm_num) (by norm_num)
    (fun _ ht => ResidualFilter.residualWeight_abs_le_two hf hlam hα ⟨ht.1, ht.2.trans hMT⟩)
    (fun _ ht => ResidualFilter.residualWeight_abs_le_two hf hlam hα ⟨ht.1, ht.2.trans hML⟩) f

end
end KernelSeq
