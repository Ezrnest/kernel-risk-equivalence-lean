import KernelFoundations.OperatorComparison
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

/-!
# Actual regularized operator normalization

The continuous functional calculus in this Mathlib version is available for
operators on complex Hilbert spaces. The real-Hilbert conjugation mechanism is
in `OperatorComparison`; a real square-root construction or complexification
bridge is not established here.
-/

namespace KernelFoundations

section Conjugation

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Loewner order is preserved by adjoint conjugation over either scalar field. -/
theorem loewner_adjoint_conjugation (A B : F →L[𝕜] F) (R : E →L[𝕜] F)
    (hAB : A ≤ B) :
    R.adjoint.comp (A.comp R) ≤ R.adjoint.comp (B.comp R) := by
  change (B - A).IsPositive at hAB
  change (R.adjoint.comp (B.comp R) - R.adjoint.comp (A.comp R)).IsPositive
  convert hAB.adjoint_conj R using 1
  ext x
  simp

end Conjugation

section RealRoot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- With a self-adjoint invertible root already given, normalization can be
undone algebraically; this lemma does not postulate a perturbation factorization. -/
theorem inverse_root_factorization_real (R C : E →L[ℝ] E)
    (hR : IsSelfAdjoint R) (hu : IsUnit R) :
    R.adjoint.comp ((Ring.inverse R * C * Ring.inverse R).comp R) = C := by
  have hRadj : R.adjoint = R := hR
  change R.adjoint * ((Ring.inverse R * C * Ring.inverse R) * R) = C
  rw [hRadj]
  calc
    R * (Ring.inverse R * C * Ring.inverse R * R) =
        (R * Ring.inverse R) * C * (Ring.inverse R * R) := by simp only [mul_assoc]
    _ = C := by rw [Ring.mul_inverse_cancel R hu, Ring.inverse_mul_cancel R hu]; simp

/-- Real-Hilbert relative comparison for the square of an actual invertible
self-adjoint operator. Square-root existence for a general positive operator is
not assumed or established by this theorem. -/
theorem invertible_root_relative_comparison_real (R B : E →L[ℝ] E)
    (hR : IsSelfAdjoint R) (hu : IsUnit R) (x : E) :
    let δ := ‖Ring.inverse R * (B - R * R) * Ring.inverse R‖
    (1 - δ) * inner ℝ x ((R * R) x) ≤ inner ℝ x (B x) ∧
      inner ℝ x (B x) ≤ (1 + δ) * inner ℝ x ((R * R) x) := by
  dsimp only
  apply relative_quadratic_form_comparison (R * R) B R
    (Ring.inverse R * (B - R * R) * Ring.inverse R) le_rfl
  · exact (inverse_root_factorization_real R (B - R * R) hR hu).symm
  · intro y
    have hRadj : R.adjoint = R := hR
    simpa only [hRadj, RCLike.re_to_real, ContinuousLinearMap.mul_def] using
      (R.apply_norm_sq_eq_inner_adjoint_right y).symm

end RealRoot

section CStar

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Relative Loewner comparison with the normalized perturbation constructed
using the actual CFC inverse square root. There are no factorization hypotheses. -/
theorem cfc_relative_loewner_comparison (a b : A) (ha : IsStrictlyPositive a)
    (hb : IsSelfAdjoint b) :
    let δ := ‖CFC.conjSqrt (Ring.inverse a) (b - a)‖
    (1 - δ) • a ≤ b ∧ b ≤ (1 + δ) • a := by
  dsimp only
  let d := CFC.conjSqrt (Ring.inverse a) (b - a)
  have hd : IsSelfAdjoint d := by
    exact (hb.sub (IsSelfAdjoint.of_nonneg ha.nonneg)).conjugate_self
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _))
  have hconj : CFC.conjSqrt a d = b - a :=
    CFC.conjSqrt_conjSqrt_ringInverse a (b - a) ha
  have hscalar (r : ℝ) : CFC.conjSqrt a (algebraMap ℝ A r) = r • a := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, CFC.conjSqrt_one a ha.nonneg]
  have hlo := CFC.conjSqrt_le_conjSqrt (c := a) hd.neg_algebraMap_norm_le_self
  have hhi := CFC.conjSqrt_le_conjSqrt (c := a) hd.le_algebraMap_norm_self
  rw [map_neg, hscalar, hconj] at hlo
  rw [hscalar, hconj] at hhi
  change (1 - ‖d‖) • a ≤ b ∧ b ≤ (1 + ‖d‖) • a
  constructor
  · calc
      (1 - ‖d‖) • a = a + -(‖d‖ • a) := by rw [sub_smul, one_smul, sub_eq_add_neg]
      _ ≤ a + (b - a) := add_le_add le_rfl hlo
      _ = b := by abel
  · calc
      b = a + (b - a) := by abel
      _ ≤ a + ‖d‖ • a := add_le_add le_rfl hhi
      _ = (1 + ‖d‖) • a := by rw [add_smul, one_smul]

/-- The usual half/three-halves consequence with an actual CFC normalization. -/
theorem cfc_relative_loewner_half_comparison (a b : A) (ha : IsStrictlyPositive a)
    (hb : IsSelfAdjoint b)
    (hδ : ‖CFC.conjSqrt (Ring.inverse a) (b - a)‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) • a ≤ b ∧ b ≤ (3 / 2 : ℝ) • a := by
  have h := cfc_relative_loewner_comparison a b ha hb
  constructor
  · exact (smul_le_smul_of_nonneg_right (by linarith) ha.nonneg).trans h.1
  · exact h.2.trans (smul_le_smul_of_nonneg_right (by linarith) ha.nonneg)

end CStar

section ComplexHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 400000 in
/-- Regularized Loewner comparison on a complex Hilbert space, with
`T + lam I` and its inverse square root constructed by Mathlib. -/
theorem regularized_covariance_loewner_comparison_complex
    (T TX : E →L[ℂ] E) (hT : 0 ≤ T) (hTX : IsSelfAdjoint TX)
    (lam : ℝ) (hlam : 0 < lam) :
    let a := T + lam • (1 : E →L[ℂ] E)
    let b := TX + lam • (1 : E →L[ℂ] E)
    let δ := ‖CFC.conjSqrt (Ring.inverse a) (b - a)‖
    (1 - δ) • a ≤ b ∧ b ≤ (1 + δ) • a := by
  have hreg : IsStrictlyPositive (T + lam • (1 : E →L[ℂ] E)) :=
    IsStrictlyPositive.nonneg_add hT (IsStrictlyPositive.smul hlam isStrictlyPositive_one)
  exact cfc_relative_loewner_comparison _ _ hreg
    (hTX.add (show IsSelfAdjoint (lam • (1 : E →L[ℂ] E)) from by simp [IsSelfAdjoint]))

end ComplexHilbert

end KernelFoundations
