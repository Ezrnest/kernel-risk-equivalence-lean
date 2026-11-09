import KernelSeq.FinitePredictionBayes
import KernelSeq.SourceBall

/-!
# Exact source membership on actual finite population eigenspaces

The inverse-power source vector is explicitly synthesized. Both directions
of the ellipsoid criterion use the genuine operator source ball, not a
replacement definition of the function class.
-/

namespace KernelSeq
open MeasureTheory Submodule
open scoped BigOperators
noncomputable section

variable {X H ι : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ] [Fintype ι]

def finiteSourceEnergy (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (s : ℝ)
    (θ : EuclideanSpace ℝ ι) : ℝ := ∑ j, (jmap j).1.1^(-s) * (θ j)^2

def finiteSourceCoordinates (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (s : ℝ)
    (θ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun j => (jmap j).1.1^(-(s/2)) * θ j)

omit [IsProbabilityMeasure μ] in
theorem finiteSourceCoordinates_norm_sq (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (s : ℝ)
    (θ : EuclideanSpace ℝ ι) : ‖finiteSourceCoordinates k hk jmap s θ‖^2 =
      finiteSourceEnergy k hk jmap s θ := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold finiteSourceCoordinates finiteSourceEnergy
  apply Finset.sum_congr rfl
  intro j _
  change ((jmap j).1.1^(-(s/2)) * θ j)^2 = _
  rw [mul_pow, ← Real.rpow_two, ← Real.rpow_mul (jmap j).2.le]
  congr 2
  ring

theorem finitePredictionSynthesis_supported (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk))
    (θ : EuclideanSpace ℝ ι) :
    FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ ∈
      PredictionRange (featureEmbedding μ k hk) := by
  rw [FinitePredictionBayes.synthesis_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (predictionSingularBasis (featureEmbedding μ k hk)
      (populationCovariance_feature_isCompact μ k hk) (jmap j)).property

theorem finiteSourceCoordinates_power (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk))
    (s : ℝ) (hs : 0 ≤ s) (θ : EuclideanSpace ℝ ι) :
    predictionSourcePower (featureEmbedding μ k hk) (populationCovariance_feature_isCompact μ k hk) s hs
      (FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap)
        (finiteSourceCoordinates k hk jmap s θ)) =
      FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ := by
  classical
  let S := featureEmbedding μ k hk
  let hc := populationCovariance_feature_isCompact μ k hk
  let b := predictionSingularBasis S hc
  have hsup := finitePredictionSynthesis_supported k hk jmap (finiteSourceCoordinates k hk jmap s θ)
  have hout := predictionSourcePower_mem_predictionRange S hc s hs hsup
  have hf := finitePredictionSynthesis_supported k hk jmap θ
  have heq : (⟨_,hout⟩ : PredictionRange S) = ⟨_,hf⟩ := by
    apply b.repr.injective
    ext i
    simp only [HilbertBasis.repr_apply_apply, Submodule.coe_inner]
    rw [predictionSourcePower_coefficient]
    simp only [FinitePredictionBayes.synthesis_apply, inner_sum, inner_smul_right,
      Finset.mul_sum, finiteSourceCoordinates]
    apply Finset.sum_congr rfl
    intro j _
    change i.1.1 ^ (s/2) * ((jmap j).1.1 ^ (-(s/2)) * θ j *
      inner ℝ (b i : Lp ℝ 2 μ) (b (jmap j) : Lp ℝ 2 μ)) =
      θ j * inner ℝ (b i : Lp ℝ 2 μ) (b (jmap j) : Lp ℝ 2 μ)
    by_cases hij : i = jmap j
    · rw [hij]
      have hp : (jmap j).1.1^(s/2) * (jmap j).1.1^(-(s/2)) = 1 := by
        rw [← Real.rpow_add (jmap j).2, add_neg_cancel, Real.rpow_zero]
      calc
        _ = ((jmap j).1.1^(s/2) * (jmap j).1.1^(-(s/2))) *
          (θ j * inner ℝ (b (jmap j) : Lp ℝ 2 μ) (b (jmap j) : Lp ℝ 2 μ)) := by ring
        _ = _ := by rw [hp, one_mul]
    · have ho : inner ℝ (b i : Lp ℝ 2 μ) (b (jmap j) : Lp ℝ 2 μ) = 0 :=
        (b.orthonormal.comp_linearIsometry (Submodule.subtypeₗᵢ _)).2 hij
      rw [ho]
      ring
  exact congrArg Subtype.val heq

/-- An explicit inverse-power source vector proves the forward membership
criterion. It is in the actual closed prediction range. -/
theorem finiteSynthesis_mem_sourceBall_of_energy (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) (θ : EuclideanSpace ℝ ι)
    (henergy : finiteSourceEnergy k hk jmap s θ ≤ R^2) :
    FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ ∈
      featureSourceBall k hk s hs R := by
  let g := FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap)
    (finiteSourceCoordinates k hk jmap s θ)
  refine ⟨g, finitePredictionSynthesis_supported k hk jmap _, ?_, finiteSourceCoordinates_power k hk jmap s hs θ⟩
  apply (sq_le_sq₀ (norm_nonneg _) hR).mp
  rw [FinitePredictionBayes.synthesis_norm_sq (finitePredictionFunction_orthonormal k hk jmap hj),
    finiteSourceCoordinates_norm_sq]
  exact henergy

theorem finiteSourceEnergy_le_of_mem_sourceBall (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    {s R : ℝ} (hs : 0 ≤ s) (_hR : 0 ≤ R) (θ : EuclideanSpace ℝ ι)
    (hball : FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ ∈
      featureSourceBall k hk s hs R) :
    finiteSourceEnergy k hk jmap s θ ≤ R^2 := by
  obtain ⟨g, _hg, hnorm, hpower⟩ := hball
  let e := finitePredictionFunction k hk jmap
  have he : Orthonormal ℝ e := finitePredictionFunction_orthonormal k hk jmap hj
  have hθ (j : ι) : θ j = (jmap j).1.1^(s/2) * inner ℝ (e j) g := by
    calc
      θ j = FinitePredictionBayes.coefficients e (FinitePredictionBayes.synthesis e θ) j := by
        rw [FinitePredictionBayes.coefficients_synthesis he]
      _ = inner ℝ (e j) (predictionSourcePower (featureEmbedding μ k hk)
          (populationCovariance_feature_isCompact μ k hk) s hs g) := by rw [hpower]; rfl
      _ = _ := predictionSourcePower_coefficient _ _ _ _ _ _
  have henergy : finiteSourceEnergy k hk jmap s θ = ‖FinitePredictionBayes.coefficients e g‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    unfold finiteSourceEnergy
    apply Finset.sum_congr rfl
    intro j _
    rw [FinitePredictionBayes.coefficients_apply, hθ, mul_pow]
    have hpow : ((jmap j).1.1^(s/2))^2 = (jmap j).1.1^s := by
      rw [← Real.rpow_two, ← Real.rpow_mul (jmap j).2.le]
      congr 1
      ring
    rw [hpow, ← mul_assoc, ← Real.rpow_add (jmap j).2, neg_add_cancel, Real.rpow_zero, one_mul]
  rw [henergy]
  exact (FinitePredictionBayes.coefficients_norm_sq_le he g).trans
    (pow_le_pow_left₀ (norm_nonneg g) hnorm 2)

/-- Exact equivalence with the original operator-defined source ball,
on any actual finite set of distinct positive population eigendirections. -/
theorem finiteSynthesis_mem_sourceBall_iff_energy (k : X → H) (hk : MemLp k 2 μ)
    (jmap : ι → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    {s R : ℝ} (hs : 0 ≤ s) (hR : 0 ≤ R) (θ : EuclideanSpace ℝ ι) :
    FinitePredictionBayes.synthesis (finitePredictionFunction k hk jmap) θ ∈
        featureSourceBall k hk s hs R ↔ finiteSourceEnergy k hk jmap s θ ≤ R^2 :=
  ⟨finiteSourceEnergy_le_of_mem_sourceBall k hk jmap hj hs hR θ,
    finiteSynthesis_mem_sourceBall_of_energy k hk jmap hj hs hR θ⟩

end
end KernelSeq
