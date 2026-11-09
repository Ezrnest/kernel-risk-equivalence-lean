import KernelSeq.FiniteEigenSourceBall
import KernelSeq.ActualVarianceTransfer
import KernelSeq.SchattenCompression

/-!
# Actual filter dimension dominates any finite positive prediction eigensystem

The domain singular vectors are explicitly `mu^(-1/2) S* e`. Their
orthonormality and covariance eigenrelations follow from the true prediction
eigenrelations. The finite energy bound is then applied to the constructed
population Hilbert--Schmidt shrinkage operator, whose energy is exactly the
actual filter dimension. No trace bound is supplied as a premise.
-/

namespace KernelSeq
open MeasureTheory
open scoped BigOperators
noncomputable section

variable {H E ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def finitePredictionDomainVector (S : H →L[ℝ] E) (e : ι → E) (t : ι → ℝ) (j : ι) : H :=
  (Real.sqrt (t j))⁻¹ • S.adjoint (e j)

theorem finitePredictionDomainVector_orthonormal (S : H →L[ℝ] E)
    (e : ι → E) (he : Orthonormal ℝ e) (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, (S.comp S.adjoint) (e j) = t j • e j) :
    Orthonormal ℝ (finitePredictionDomainVector S e t) := by
  classical
  have hinner (i j : ι) : inner ℝ (S.adjoint (e i)) (S.adjoint (e j)) =
      t j*inner ℝ (e i) (e j) := by
    rw [← S.adjoint.adjoint_inner_right, ContinuousLinearMap.adjoint_adjoint]
    change inner ℝ (e i) ((S.comp S.adjoint) (e j)) = _
    rw [heig, inner_smul_right]
  rw [orthonormal_iff_ite]
  intro i j
  unfold finitePredictionDomainVector
  rw [inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  rw [hinner]
  by_cases hij : i = j
  · subst j
    simp only [real_inner_self_eq_norm_sq, he.norm_eq_one, one_pow, mul_one, ite_true]
    have hsqrt : Real.sqrt (t i) ≠ 0 := (Real.sqrt_pos.mpr (ht i)).ne'
    field_simp
    simpa using (Real.sq_sqrt (ht i).le).symm
  · rw [he.inner_eq_zero hij, if_neg hij]
    simp

theorem finitePredictionDomainVector_eigen (S : H →L[ℝ] E) (e : ι → E) (t : ι → ℝ)
    (heig : ∀ j, (S.comp S.adjoint) (e j) = t j • e j) (j : ι) :
    (S.adjoint.comp S) (finitePredictionDomainVector S e t j) =
      t j • finitePredictionDomainVector S e t j := by
  have he : S (S.adjoint (e j)) = t j • e j := heig j
  change S.adjoint (S ((Real.sqrt (t j))⁻¹ • S.adjoint (e j))) =
    t j • ((Real.sqrt (t j))⁻¹ • S.adjoint (e j))
  rw [map_smul, map_smul, he, map_smul, smul_smul, smul_smul]
  congr 1
  ring

section Feature
variable {X J : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [TopologicalSpace.SeparableSpace H] [Fintype J]

/-- The finite actual prediction-eigenvalue sum is bounded by the actual
population variance dimension. Multiplicities are retained by the arbitrary
finite orthonormal family. -/
theorem finitePredictionEigen_shrinkage_sum_le_filterDimension
    (k : X → H) (hk : MemLp k 2 μ) (e : J → Lp ℝ 2 μ) (he : Orthonormal ℝ e)
    (t : J → ℝ) (ht : ∀ j, 0 < t j)
    (heig : ∀ j, predictionCovariance (featureEmbedding μ k hk) (e j) = t j • e j)
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    (∑ j, (ResidualFilter.shrinkage φ (t j))^2) ≤ featureFilterDimension k hk φ := by
  classical
  let S := featureEmbedding μ k hk
  let v := finitePredictionDomainVector S e t
  let b := featureCovarianceBasis k hk
  let c := populationShrinkageHSColumns k hk φ hlam hM hf h
  have hv : Orthonormal ℝ v := finitePredictionDomainVector_orthonormal S e he t ht heig
  have hT (j : J) : populationCovariance S (v j) = t j • v j :=
    finitePredictionDomainVector_eigen S e t heig j
  have hq (j : J) : hilbertSchmidtOperator b c (v j) =
      ResidualFilter.shrinkage φ (t j) • v j := by
    rw [show hilbertSchmidtOperator b c = compactShrinkageOperator (populationCovariance S)
      (populationCovariance_feature_isCompact μ k hk) (populationCovariance_isPositive S) φ hM hf from
        hilbertSchmidtOperator_populationShrinkageHSColumns k hk φ hlam hM hf h]
    exact compactSpectralMultiplier_eigen _ _ _ _ _ _ _ (hT j)
  have hh := hs_orthonormal_power_sum_le b c (p := 2) (by norm_num) v hv Finset.univ
  norm_num only [show (2 : ℝ)/2 = 1 by norm_num, Real.rpow_one] at hh
  rw [(hasSum_hsSquaredSingularValues b c).tsum_eq] at hh
  change (∑ j, ‖hilbertSchmidtOperator b c (v j)‖^2) ≤ ‖c‖^2 at hh
  simp_rw [hq, norm_smul, hv.norm_eq_one, mul_one, Real.norm_eq_abs, sq_abs] at hh
  exact hh.trans_eq (populationShrinkageHSColumns_norm_sq k hk φ hlam hM hf h)

end Feature
end
end KernelSeq
