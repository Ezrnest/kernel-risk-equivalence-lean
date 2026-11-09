import KernelSeq.SourceNormBounds

/-!
# Source balls on arbitrary actual finite positive eigensystems

The orthonormal vectors need not be selected members of the compact spectral
basis. Their true positive-eigenvector equations imply support in the actual
prediction range. Explicit inverse-power synthesis gives the exact source
ellipsoid and the containing norm bound, without a source-membership field.
-/

namespace KernelSeq
open MeasureTheory
open scoped BigOperators
noncomputable section

variable {H E ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]

def finiteEigenSourceEnergy (t : ι → ℝ) (s : ℝ) (θ : EuclideanSpace ℝ ι) : ℝ :=
  ∑ j, t j^(-s)*(θ j)^2

def finiteEigenSourceCoordinates (t : ι → ℝ) (s : ℝ) (θ : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι := WithLp.toLp 2 (fun j => t j^(-(s/2))*θ j)

omit [Fintype ι] in
theorem positive_prediction_eigen_mem_range (S : H →L[ℝ] E)
    {v : E} {t : ℝ} (ht : 0 < t) (heig : (S.comp S.adjoint) v = t • v) :
    v ∈ S.range := by
  refine ⟨t⁻¹ • S.adjoint v, ?_⟩
  rw [map_smul]
  change t⁻¹ • (S.comp S.adjoint) v = v
  rw [heig, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

omit [Fintype ι] in
theorem predictionSourcePower_eigen (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    {v : E} {t : ℝ} (heig : (S.comp S.adjoint) v = t • v) :
    predictionSourcePower S hc s hs v = t^(s/2) • v :=
  compactSpectralMultiplier_eigen _ _ _ _ _ _ _ heig

omit [Fintype ι] in
theorem predictionSourcePower_isSymmetric (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s) :
    (predictionSourcePower S hc s hs).IsSymmetric := by
  unfold predictionSourcePower compactSpectralMultiplier
  apply hilbertDiagonal_isSymmetric

omit [Fintype ι] in
theorem predictionSourcePower_eigen_coefficient (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (s : ℝ) (hs : 0 ≤ s)
    {v : E} {t : ℝ} (heig : (S.comp S.adjoint) v = t • v) (g : E) :
    inner ℝ v (predictionSourcePower S hc s hs g) = t^(s/2)*inner ℝ v g := by
  calc
    _ = inner ℝ (predictionSourcePower S hc s hs v) g :=
      (predictionSourcePower_isSymmetric S hc s hs v g).symm
    _ = _ := by
      rw [predictionSourcePower_eigen S hc s hs heig, inner_smul_left]
      rfl

theorem finiteEigenSourceCoordinates_norm_sq (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (s : ℝ) (θ : EuclideanSpace ℝ ι) :
    ‖finiteEigenSourceCoordinates t s θ‖^2 = finiteEigenSourceEnergy t s θ := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold finiteEigenSourceCoordinates finiteEigenSourceEnergy
  apply Finset.sum_congr rfl
  intro j _
  change (t j^(-(s/2))*θ j)^2 = _
  rw [mul_pow, ← Real.rpow_two, ← Real.rpow_mul (ht j).le]
  congr 2
  ring

theorem finiteEigenSynthesis_supported (S : H →L[ℝ] E) (e : ι → E)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, (S.comp S.adjoint) (e j) = t j • e j) (θ : EuclideanSpace ℝ ι) :
    FinitePredictionBayes.synthesis e θ ∈ PredictionRange S := by
  rw [FinitePredictionBayes.synthesis_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (S.range.le_topologicalClosure (positive_prediction_eigen_mem_range S (ht j) (heig j)))

theorem finiteEigenSourceCoordinates_power (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (e : ι → E)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, (S.comp S.adjoint) (e j) = t j • e j)
    (s : ℝ) (hs : 0 ≤ s) (θ : EuclideanSpace ℝ ι) :
    predictionSourcePower S hc s hs
      (FinitePredictionBayes.synthesis e (finiteEigenSourceCoordinates t s θ)) =
      FinitePredictionBayes.synthesis e θ := by
  classical
  rw [FinitePredictionBayes.synthesis_apply, map_sum, FinitePredictionBayes.synthesis_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, predictionSourcePower_eigen S hc s hs (heig j), smul_smul]
  change (t j^(-(s/2))*θ j*t j^(s/2)) • e j = θ j • e j
  have hp : t j^(-(s/2))*t j^(s/2) = 1 := by
    rw [← Real.rpow_add (ht j), neg_add_cancel, Real.rpow_zero]
  rw [show t j^(-(s/2))*θ j*t j^(s/2) =
    (t j^(-(s/2))*t j^(s/2))*θ j by ring, hp, one_mul]

theorem finiteEigenSynthesis_mem_sourceBall_of_energy (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (e : ι → E) (he : Orthonormal ℝ e)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, (S.comp S.adjoint) (e j) = t j • e j)
    {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) (θ : EuclideanSpace ℝ ι)
    (henergy : finiteEigenSourceEnergy t s θ ≤ R^2) :
    FinitePredictionBayes.synthesis e θ ∈ predictionSourceBall S hc s hs R := by
  refine ⟨FinitePredictionBayes.synthesis e (finiteEigenSourceCoordinates t s θ),
    finiteEigenSynthesis_supported S e t ht heig _, ?_,
    finiteEigenSourceCoordinates_power S hc e t ht heig s hs θ⟩
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  rw [FinitePredictionBayes.synthesis_norm_sq he, finiteEigenSourceCoordinates_norm_sq t ht]
  exact henergy

theorem finiteEigenSourceEnergy_le_of_mem_sourceBall (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (e : ι → E) (he : Orthonormal ℝ e)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, (S.comp S.adjoint) (e j) = t j • e j)
    {s R : ℝ} (hs : 0 ≤ s) (θ : EuclideanSpace ℝ ι)
    (hball : FinitePredictionBayes.synthesis e θ ∈ predictionSourceBall S hc s hs R) :
    finiteEigenSourceEnergy t s θ ≤ R^2 := by
  obtain ⟨g, _, hnorm, hpower⟩ := hball
  have hθ (j : ι) : θ j = t j^(s/2)*inner ℝ (e j) g := by
    calc
      θ j = FinitePredictionBayes.coefficients e (FinitePredictionBayes.synthesis e θ) j := by
        rw [FinitePredictionBayes.coefficients_synthesis he]
      _ = inner ℝ (e j) (predictionSourcePower S hc s hs g) := by rw [hpower]; rfl
      _ = _ := predictionSourcePower_eigen_coefficient S hc s hs (heig j) g
  have henergy : finiteEigenSourceEnergy t s θ = ‖FinitePredictionBayes.coefficients e g‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    unfold finiteEigenSourceEnergy
    apply Finset.sum_congr rfl
    intro j _
    rw [FinitePredictionBayes.coefficients_apply, hθ, mul_pow]
    have hpow : (t j^(s/2))^2 = t j^s := by
      rw [← Real.rpow_two, ← Real.rpow_mul (ht j).le]
      congr 1
      ring
    rw [hpow, ← mul_assoc, ← Real.rpow_add (ht j), neg_add_cancel, Real.rpow_zero, one_mul]
  rw [henergy]
  exact (FinitePredictionBayes.coefficients_norm_sq_le he g).trans
    (pow_le_pow_left₀ (norm_nonneg g) hnorm 2)

/-- Exact actual source-ball membership, with no chosen-basis assumption. -/
theorem finiteEigenSynthesis_mem_sourceBall_iff_energy (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (e : ι → E) (he : Orthonormal ℝ e)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, (S.comp S.adjoint) (e j) = t j • e j)
    {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) (θ : EuclideanSpace ℝ ι) :
    FinitePredictionBayes.synthesis e θ ∈ predictionSourceBall S hc s hs R ↔
      finiteEigenSourceEnergy t s θ ≤ R^2 :=
  ⟨finiteEigenSourceEnergy_le_of_mem_sourceBall S hc e he t ht heig hs θ,
    finiteEigenSynthesis_mem_sourceBall_of_energy S hc e he t ht heig hs hR θ⟩

theorem finiteEigenSynthesis_norm_sq_le_sourceEnergy (S : H →L[ℝ] E)
    (hc : IsCompactOperator (S.adjoint.comp S)) (e : ι → E) (he : Orthonormal ℝ e)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, (S.comp S.adjoint) (e j) = t j • e j)
    {M s : ℝ} (hM : ‖S.comp S.adjoint‖ ≤ M) (hs : 0 ≤ s) (θ : EuclideanSpace ℝ ι) :
    ‖FinitePredictionBayes.synthesis e θ‖^2 ≤ (1+M)^s*finiteEigenSourceEnergy t s θ := by
  have hn := predictionSourcePower_apply_norm_le S hc s hs hM
    (FinitePredictionBayes.synthesis e (finiteEigenSourceCoordinates t s θ))
  rw [finiteEigenSourceCoordinates_power S hc e t ht heig] at hn
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow, FinitePredictionBayes.synthesis_norm_sq he (finiteEigenSourceCoordinates t s θ),
    finiteEigenSourceCoordinates_norm_sq t ht] at hsq
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hp : ((1+M)^(s/2))^2 = (1+M)^s := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by linarith : 0 ≤ 1+M)]
    congr 1
    ring
  rwa [hp] at hsq

section Feature
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem finiteEigenSynthesis_mem_featureSourceBall_iff_energy
    (k : X → H) (hk : MemLp k 2 μ) (e : ι → Lp ℝ 2 μ) (he : Orthonormal ℝ e)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, predictionCovariance (featureEmbedding μ k hk) (e j) = t j • e j)
    {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) (θ : EuclideanSpace ℝ ι) :
    FinitePredictionBayes.synthesis e θ ∈ featureSourceBall k hk s hs R ↔
      finiteEigenSourceEnergy t s θ ≤ R^2 :=
  finiteEigenSynthesis_mem_sourceBall_iff_energy _ (populationCovariance_feature_isCompact μ k hk)
    e he t ht heig hs hR θ

theorem finiteEigenSynthesis_norm_sq_le_featureSourceEnergy
    (k : X → H) (hk : MemLp k 2 μ) (e : ι → Lp ℝ 2 μ) (he : Orthonormal ℝ e)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, predictionCovariance (featureEmbedding μ k hk) (e j) = t j • e j)
    {κ s : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ) (hs : 0 ≤ s)
    (θ : EuclideanSpace ℝ ι) :
    ‖FinitePredictionBayes.synthesis e θ‖^2 ≤ (1+κ^2)^s*finiteEigenSourceEnergy t s θ :=
  finiteEigenSynthesis_norm_sq_le_sourceEnergy _ (populationCovariance_feature_isCompact μ k hk)
    e he t ht heig (feature_prediction_covariance_norm_le k hk hκ hbound) hs θ

end Feature
end
end KernelSeq
