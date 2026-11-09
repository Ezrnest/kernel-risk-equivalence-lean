import KernelSeq.SchattenTriangle
import KernelSeq.SingularSystem

/-!
# Adjoint invariance of actual Schatten quantities

The adjoint's positive singular system supplies actual orthonormal vectors in
the original domain. The proved spectral Jensen/Bessel energy bound compares
the two power sums; applying it twice gives equality. Neither a spectral
multiplicity certificate nor a full Schatten Banach-ideal structure is used.
-/

open scoped BigOperators

namespace KernelSeq

noncomputable section

variable {ι η H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Zero covariance eigenvalues contribute zero to every positive power.
The reduction includes an arbitrary-dimensional kernel and needs no
countability assumption on either Hilbert space. -/
theorem hsSingularPower_eq_positive (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 0 < p) :
    (∑' i : HSSingularIndex b c, i.1 ^ (p / 2)) =
      ∑' i : PositiveSpectralIndex (hsSingularCovariance b c), i.1.1 ^ (p / 2) := by
  symm
  apply tsum_subtype_eq_of_support_subset
    (s := {i : HSSingularIndex b c | 0 < i.1})
    (f := fun i : HSSingularIndex b c => i.1 ^ (p / 2))
  intro i hi
  by_contra hn
  have hz : i.1 = 0 := le_antisymm (le_of_not_gt hn) (hsSingularValue_nonneg b c i)
  exact hi (by
    change i.1 ^ (p / 2) = 0
    rw [hz, Real.zero_rpow (by linarith : p / 2 ≠ 0)])

/-- The actual adjoint singular power sum is bounded by the original one,
through its genuine normalized image singular vectors. -/
theorem hsAdjoint_singularPower_le (b : HilbertBasis ι ℝ H) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    (∑' j : HSSingularIndex e (hsAdjointColumns b e c), j.1 ^ (p / 2)) ≤
      ∑' i : HSSingularIndex b c, i.1 ^ (p / 2) := by
  classical
  let d := hsAdjointColumns b e c
  let S := hilbertSchmidtOperator e d
  have hc : IsCompactOperator (S.adjoint.comp S) := hsSingularCovariance_isCompact e d
  let v : PredictionSingularIndex S → H := fun j => (predictionSingularBasis S hc j : H)
  have hv : Orthonormal ℝ v :=
    (predictionSingularBasis S hc).orthonormal.comp_linearIsometry (PredictionRange S).subtypeₗᵢ
  have hA : S.adjoint = hilbertSchmidtOperator b c := by
    dsimp only [S, d]
    rw [hilbertSchmidtOperator_adjoint, ContinuousLinearMap.adjoint_adjoint]
  have himage (j : PredictionSingularIndex S) : ‖hilbertSchmidtOperator b c (v j)‖ ^ 2 = j.1.1 := by
    rw [← hA]
    change ‖S.adjoint (predictionSingularBasis S hc j : H)‖ ^ 2 = _
    rw [predictionSingularBasis_adjoint, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), (singularDomainBasis S hc).orthonormal.norm_eq_one,
      mul_one, Real.sq_sqrt j.2.le]
  rw [hsSingularPower_eq_positive e d (by linarith : 0 < p)]
  change (∑' j : PredictionSingularIndex S, j.1.1 ^ (p / 2)) ≤ _
  apply Real.tsum_le_of_sum_le (fun j => Real.rpow_nonneg j.2.le _)
  intro s
  have he := hs_orthonormal_power_sum_le b c hp v hv s
  simpa only [himage] using he

theorem hsSchattenNorm_adjointColumns_le (b : HilbertBasis ι ℝ H) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm e (hsAdjointColumns b e c) p ≤ hsSchattenNorm b c p :=
  Real.rpow_le_rpow
    (tsum_nonneg (fun j => Real.rpow_nonneg (hsSingularValue_nonneg e (hsAdjointColumns b e c) j) _))
    (hsAdjoint_singularPower_le b e c hp) (one_div_nonneg.mpr (by linarith : 0 ≤ p))

/-- Adjoint invariance of the actual Schatten quantity for all `p ≥ 2`, with
the actual adjoint columns and arbitrary domain/codomain Hilbert bases. -/
theorem hsSchattenNorm_adjointColumns (b : HilbertBasis ι ℝ H) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm e (hsAdjointColumns b e c) p = hsSchattenNorm b c p := by
  apply le_antisymm (hsSchattenNorm_adjointColumns_le b e c hp)
  have hback := hsSchattenNorm_adjointColumns_le e b (hsAdjointColumns b e c) hp
  have heq : hilbertSchmidtOperator b (hsAdjointColumns e b (hsAdjointColumns b e c)) =
      hilbertSchmidtOperator b c := by
    rw [hilbertSchmidtOperator_adjoint, hilbertSchmidtOperator_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  rw [hsSchattenNorm_reconstruction_eq b b _ _ heq p] at hback
  exact hback

theorem hsAdjoint_singularPower_eq (b : HilbertBasis ι ℝ H) (e : HilbertBasis η ℝ E)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    (∑' j : HSSingularIndex e (hsAdjointColumns b e c), j.1 ^ (p / 2)) =
      ∑' i : HSSingularIndex b c, i.1 ^ (p / 2) := by
  have hp0 : 0 < p := by linarith
  rw [← hsSchattenNorm_rpow e _ hp0, ← hsSchattenNorm_rpow b c hp0,
    hsSchattenNorm_adjointColumns b e c hp]

/-- An arbitrary HS reconstruction of the actual adjoint has the same
Schatten norm. Adjoint columns need not be the canonical chosen ones. -/
theorem hsSchattenNorm_adjoint_reconstruction_eq (b : HilbertBasis ι ℝ H)
    (e : HilbertBasis η ℝ E) (c : HilbertSchmidtColumns ι E) (d : HilbertSchmidtColumns η H)
    (hadj : hilbertSchmidtOperator e d = (hilbertSchmidtOperator b c).adjoint)
    {p : ℝ} (hp : 2 ≤ p) : hsSchattenNorm e d p = hsSchattenNorm b c p := by
  calc
    _ = hsSchattenNorm e (hsAdjointColumns b e c) p :=
      hsSchattenNorm_reconstruction_eq e e _ _
        (hadj.trans (hilbertSchmidtOperator_adjoint b e c).symm) p
    _ = _ := hsSchattenNorm_adjointColumns b e c hp

section RightIdeal

variable {κ F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- The full actual right ideal bound follows from the constructed adjoint
columns and the proved left ideal bound. No Schatten ideal axiom is used. -/
theorem hsSchattenNorm_rightComposition_le (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ F) (e : HilbertBasis η ℝ E) (B : F →L[ℝ] H)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm d (hsRightComposition b d e B c) p ≤ hsSchattenNorm b c p * ‖B‖ := by
  rw [hsRightComposition, hsSchattenNorm_adjointColumns e d _ hp]
  calc
    _ ≤ ‖B.adjoint‖ * hsSchattenNorm e (hsAdjointColumns b e c) p :=
      hsSchattenNorm_leftComposition_le e B.adjoint (hsAdjointColumns b e c) hp
    _ = _ := by rw [hsSchattenNorm_adjointColumns b e c hp, LinearIsometryEquiv.norm_map]; ring

theorem hsSchattenNorm_rightContraction_le (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ F) (e : HilbertBasis η ℝ E) (B : F →L[ℝ] H) (hB : ‖B‖ ≤ 1)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm d (hsRightComposition b d e B c) p ≤ hsSchattenNorm b c p := by
  calc
    _ ≤ hsSchattenNorm b c p * ‖B‖ := hsSchattenNorm_rightComposition_le b d e B c hp
    _ ≤ hsSchattenNorm b c p * 1 := mul_le_mul_of_nonneg_left hB (hsSchattenNorm_nonneg b c p)
    _ = _ := mul_one _

/-- A basis-independent reconstruction of `A B` satisfies the same true
right ideal bound, irrespective of the column construction chosen. -/
theorem hsSchattenNorm_right_reconstruction_le (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ F) (e : HilbertBasis η ℝ E) (B : F →L[ℝ] H)
    (c : HilbertSchmidtColumns ι E) (z : HilbertSchmidtColumns κ E)
    (hz : hilbertSchmidtOperator d z = (hilbertSchmidtOperator b c).comp B)
    {p : ℝ} (hp : 2 ≤ p) : hsSchattenNorm d z p ≤ hsSchattenNorm b c p * ‖B‖ := by
  rw [hsSchattenNorm_reconstruction_eq d d z (hsRightComposition b d e B c)
    (hz.trans (hilbertSchmidtOperator_rightComposition b d e B c).symm) p]
  exact hsSchattenNorm_rightComposition_le b d e B c hp

/-- The actual two-sided ideal estimate on HS-represented operators. This
includes arbitrary bounded factors and all real `p ≥ 2`. -/
theorem hsSchattenNorm_twoSidedComposition_le (b : HilbertBasis ι ℝ H)
    (d : HilbertBasis κ ℝ F) (e : HilbertBasis η ℝ E)
    (B : F →L[ℝ] H) (Q : E →L[ℝ] G) (c : HilbertSchmidtColumns ι E)
    {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm d (hsLeftComposition Q (hsRightComposition b d e B c)) p ≤
      ‖Q‖ * hsSchattenNorm b c p * ‖B‖ := by
  calc
    _ ≤ ‖Q‖ * hsSchattenNorm d (hsRightComposition b d e B c) p :=
      hsSchattenNorm_leftComposition_le d Q _ hp
    _ ≤ ‖Q‖ * (hsSchattenNorm b c p * ‖B‖) := mul_le_mul_of_nonneg_left
      (hsSchattenNorm_rightComposition_le b d e B c hp) (norm_nonneg Q)
    _ = _ := by ring

end RightIdeal

end
end KernelSeq
