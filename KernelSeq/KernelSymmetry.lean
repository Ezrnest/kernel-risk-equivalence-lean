import KernelSeq.RKHSFeature
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Genuine Hilbert symmetries from invariant feature Gram matrices

An index permutation preserving the actual Gram matrix acts isometrically
on finite feature combinations. A dense linear extension constructs an
actual Hilbert-space unitary; its existence is not a model certificate.
-/

namespace KernelSeq
open Set Submodule
noncomputable section

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem denseRange_featureCombination (k : X → H)
    (hdense : (span ℝ (range k)).topologicalClosure = ⊤) :
    DenseRange (Finsupp.linearCombination ℝ k) := by
  rw [DenseRange, dense_iff_closure_eq]
  change closure ((LinearMap.range (Finsupp.linearCombination ℝ k) : Submodule ℝ H) : Set H) = univ
  rw [← Submodule.topologicalClosure_coe, Finsupp.range_linearCombination, hdense]
  rfl

omit [CompleteSpace H] in
private theorem featureCombination_norm (k : X → H) (r : X ≃ X)
    (hgram : ∀ x y, inner ℝ (k (r x)) (k (r y)) = inner ℝ (k x) (k y))
    (c : X →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ (k ∘ r) c‖ = ‖Finsupp.linearCombination ℝ k c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [← real_inner_self_eq_norm_sq, Finsupp.linearCombination_apply,
    Finsupp.sum_inner, Finsupp.inner_sum, real_inner_smul_left, real_inner_smul_right,
    Function.comp_apply, hgram]

/-- The actual unitary extending the feature permutation. -/
def featureSymmetry (k : X → H) (hdense : (span ℝ (range k)).topologicalClosure = ⊤)
    (r : X ≃ X)
    (hgram : ∀ x y, inner ℝ (k (r x)) (k (r y)) = inner ℝ (k x) (k y)) : H ≃ₗᵢ[ℝ] H :=
  (Finsupp.domLCongr (R := ℝ) (M := ℝ) r).extendOfIsometry
    (Finsupp.linearCombination ℝ k) (Finsupp.linearCombination ℝ k)
    (denseRange_featureCombination k hdense) (denseRange_featureCombination k hdense)
    (fun c => by
      change ‖Finsupp.linearCombination ℝ k (Finsupp.equivMapDomain r c)‖ = _
      rw [Finsupp.linearCombination_equivMapDomain]
      exact featureCombination_norm k r hgram c)

@[simp] theorem featureSymmetry_apply (k : X → H)
    (hdense : (span ℝ (range k)).topologicalClosure = ⊤) (r : X ≃ X)
    (hgram : ∀ x y, inner ℝ (k (r x)) (k (r y)) = inner ℝ (k x) (k y)) (x : X) :
    featureSymmetry k hdense r hgram (k x) = k (r x) := by
  have hh := LinearEquiv.extendOfIsometry_eq (Finsupp.domLCongr (R := ℝ) (M := ℝ) r)
    (Finsupp.linearCombination ℝ k) (Finsupp.linearCombination ℝ k)
    (denseRange_featureCombination k hdense) (denseRange_featureCombination k hdense)
    (fun c => by
      change ‖Finsupp.linearCombination ℝ k (Finsupp.equivMapDomain r c)‖ = _
      rw [Finsupp.linearCombination_equivMapDomain]
      exact featureCombination_norm k r hgram c) (Finsupp.single x 1)
  simpa only [featureSymmetry, Finsupp.domLCongr_single,
    Finsupp.linearCombination_single, one_smul] using hh

variable [RKHS ℝ H X ℝ]

/-- Density of actual canonical scalar kernel sections. -/
theorem rkhsFeature_denseSpan :
    (span ℝ (range (rkhsFeature (X := X) (H := H)))).topologicalClosure = ⊤ := by
  refine Submodule.orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr fun f hf => ?_)
  apply DFunLike.ext f 0
  intro x
  have hh := Submodule.inner_right_of_mem_orthogonal
    (subset_closure (Submodule.subset_span (mem_range_self x))) hf
  simpa only [rkhsFeature_inner, RKHS.coe_zero, Pi.zero_apply] using hh

end
end KernelSeq
