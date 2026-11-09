import KernelSeq.PinskerSourceBias

/-!
# Genuine eigenvalue occurrence in any supported eigenbasis

A nonzero prediction eigenvector has a nonzero coefficient in the actual
supported Hilbert basis. Self-adjointness then identifies the corresponding
eigenvalue. This transfers spectral extrema between different actual
eigenbases without assuming a basis comparison or spectral enumeration.
-/

namespace KernelSeq

open MeasureTheory Set
noncomputable section

variable {H E J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem predictionEigenvalue_occurs_in_supported_basis
    (S : H →L[ℝ] E) (b : HilbertBasis J ℝ (PredictionRange S)) (t : J → ℝ)
    (hb : ∀ j, (S.comp S.adjoint) (b j : E) = t j • (b j : E))
    {v : E} (hv : v ∈ PredictionRange S) (hv0 : v ≠ 0) {u : ℝ}
    (heig : (S.comp S.adjoint) v = u • v) : ∃ j, t j = u := by
  have hcoeff : ∃ j, inner ℝ (b j : E) v ≠ 0 := by
    by_contra! hzero
    let vG : PredictionRange S := ⟨v,hv⟩
    have hs := b.hasSum_repr vG
    have he : (fun j => b.repr vG j • b j) = fun _ => 0 := by
      funext j
      rw [b.repr_apply_apply]
      change inner ℝ (b j : E) v • b j = 0
      rw [hzero j,zero_smul]
    rw [he] at hs
    exact hv0 (congrArg Subtype.val (hs.unique hasSum_zero))
  obtain ⟨j,hj⟩ := hcoeff
  have hh := (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric (b j : E) v
  change inner ℝ ((S.comp S.adjoint) (b j : E)) v =
    inner ℝ (b j : E) ((S.comp S.adjoint) v) at hh
  rw [hb,heig,inner_smul_left,inner_smul_right] at hh
  simp only [conj_trivial] at hh
  exact ⟨j,mul_right_cancel₀ hj hh⟩

theorem predictionSingularIndex_occurs_of_positive_eigen
    (S : H →L[ℝ] E) (hc : IsCompactOperator (S.adjoint.comp S))
    {v : E} (hv0 : v ≠ 0) {u : ℝ} (hu : 0 < u)
    (heig : (S.comp S.adjoint) v = u • v) :
    ∃ i : PredictionSingularIndex S, i.1.1 = u := by
  have hv : v ∈ PredictionRange S := by
    apply S.range.le_topologicalClosure
    refine ⟨u⁻¹ • S.adjoint v,?_⟩
    rw [map_smul]
    change u⁻¹ • (S.comp S.adjoint) v = v
    rw [heig,smul_smul,inv_mul_cancel₀ hu.ne',one_smul]
  exact predictionEigenvalue_occurs_in_supported_basis S (predictionSingularBasis S hc)
    (fun i => i.1.1) (predictionSingularBasis_eigen S hc) hv hv0 heig

section SourceBias
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem featureSequenceBias_le_of_spectral_weight_bound
    (k : X → H) (hk : MemLp k 2 μ) {s R M W : ℝ}
    (hs : 0 ≤ s) (hR : 0 ≤ R) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (φ : ℝ → ℝ) (hf : ResidualFilter.SpectralFilter M φ) (hW : 0 ≤ W)
    (hbound : ∀ i : PredictionSingularIndex (featureEmbedding μ k hk), featureSourceBiasWeight k hk s φ i ≤ W)
    {f : Lp ℝ 2 μ} (hsource : f ∈ featureSourceBall k hk s hs R) :
    featureSequenceBias k hk φ f ≤ R^2*W := by
  have hSup : featureSourceBiasSpectralSup k hk s φ ≤ W := by
    apply csSup_le (Set.insert_nonempty 0 _)
    rintro _ (rfl | ⟨i,rfl⟩)
    · exact hW
    · exact hbound i
  exact (featureSequenceBias_le_sourceBall_spectralSup k hk hs hR hM φ hf hsource).trans
    (mul_le_mul_of_nonneg_left hSup (sq_nonneg R))

theorem featureSequenceBias_attained_of_spectral_weight
    (k : X → H) (hk : MemLp k 2 μ) {s R W : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R)
    (φ : ℝ → ℝ) (i : PredictionSingularIndex (featureEmbedding μ k hk))
    (hi : featureSourceBiasWeight k hk s φ i = W) :
    ∃ f ∈ featureSourceBall k hk s hs R, featureSequenceBias k hk φ f = R^2*W := by
  refine ⟨featureSourceDirection k hk s hs R i,
    featureSourceDirection_mem_sourceBall k hk s hs hR i,?_⟩
  change featureSequenceBias k hk φ
    (predictionSourcePower (featureEmbedding μ k hk) (populationCovariance_feature_isCompact μ k hk)
      s hs (R • (predictionSingularBasis (featureEmbedding μ k hk)
        (populationCovariance_feature_isCompact μ k hk) i : Lp ℝ 2 μ))) = _
  rw [featureSequenceBias_source_direction k hk hs R φ i,hi]

end SourceBias
end
end KernelSeq
