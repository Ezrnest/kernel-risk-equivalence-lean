import KernelSeq.SchattenCompression
import Mathlib.Analysis.MeanInequalities

/-!
# The Schatten triangle inequality on actual HS operators, p at least two

The proved spectral Jensen/Bessel bound and scalar finite Minkowski inequality
give the triangle inequality directly. No Schatten norm or Banach-space
structure is assumed as a premise, and the ambient Hilbert spaces are arbitrary.
-/

open Filter Topology

namespace KernelSeq

variable {ι H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem norm_sq_rpow_half (x : E) (p : ℝ) : (‖x‖ ^ 2) ^ (p / 2) = ‖x‖ ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
  congr 1
  ring

/-- The finite orthonormal-coordinate Lp norm is dominated by the actual
Schatten quantity. The input family can be unrelated to the singular basis. -/
theorem hs_orthonormal_lp_le (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E)
    {p : ℝ} (hp : 2 ≤ p) {J : Type*} (v : J → H) (hv : Orthonormal ℝ v) (s : Finset J) :
    (∑ j ∈ s, ‖hilbertSchmidtOperator b c (v j)‖ ^ p) ^ (1 / p) ≤ hsSchattenNorm b c p := by
  have he := hs_orthonormal_power_sum_le b c hp v hv s
  simp_rw [norm_sq_rpow_half] at he
  exact Real.rpow_le_rpow (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) _)) he
    (one_div_nonneg.mpr (by linarith : 0 ≤ p))

/-- A uniform bound on finite parts of the actual singular-basis Lp energy
controls the full Schatten quantity, using genuine power-sum convergence. -/
theorem hsSchattenNorm_le_of_singular_finite_lp_bound
    (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E) {p C : ℝ} (hp : 2 ≤ p)
    (hbound : ∀ s : Finset (HSSingularIndex b c),
      (∑ j ∈ s, ‖hilbertSchmidtOperator b c (hsSingularBasis b c j)‖ ^ p) ^ (1 / p) ≤ C) :
    hsSchattenNorm b c p ≤ C := by
  classical
  have hlim : Tendsto (fun s : Finset (HSSingularIndex b c) =>
      (∑ j ∈ s, j.1 ^ (p / 2)) ^ (1 / p)) atTop (𝓝 (hsSchattenNorm b c p)) :=
    (summable_hsSingularPower b c hp).hasSum.rpow_const
      (Or.inr (one_div_nonneg.mpr (by linarith : 0 ≤ p)))
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro s
  have he := hbound s
  simp_rw [← norm_sq_rpow_half, hsSingularBasis_image_norm_sq] at he
  exact he

/-- The actual Schatten triangle inequality for all p≥2 on HS operators.
This proof uses scalar Minkowski and the actual compact spectral theorem. -/
theorem hsSchattenNorm_add_le (b : HilbertBasis ι ℝ H)
    (c d : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (c + d) p ≤ hsSchattenNorm b c p + hsSchattenNorm b d p := by
  classical
  apply hsSchattenNorm_le_of_singular_finite_lp_bound b (c + d) hp
  intro s
  let v := hsSingularBasis b (c + d)
  have hp0 : 0 ≤ p := by linarith
  calc
    _ ≤ (∑ j ∈ s, (‖hilbertSchmidtOperator b c (v j)‖ +
        ‖hilbertSchmidtOperator b d (v j)‖) ^ p) ^ (1 / p) := by
      apply Real.rpow_le_rpow
        (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))
        (Finset.sum_le_sum (fun j _ => ?_)) (one_div_nonneg.mpr hp0)
      exact Real.rpow_le_rpow (norm_nonneg _) (by
        simpa only [map_add, _root_.add_apply] using
          norm_add_le (hilbertSchmidtOperator b c (v j)) (hilbertSchmidtOperator b d (v j))) hp0
    _ ≤ (∑ j ∈ s, ‖hilbertSchmidtOperator b c (v j)‖ ^ p) ^ (1 / p) +
        (∑ j ∈ s, ‖hilbertSchmidtOperator b d (v j)‖ ^ p) ^ (1 / p) :=
      Real.Lp_add_le_of_nonneg s (by linarith)
        (fun j _ => norm_nonneg _) (fun j _ => norm_nonneg _)
    _ ≤ _ := add_le_add (hs_orthonormal_lp_le b c hp v v.orthonormal s)
      (hs_orthonormal_lp_le b d hp v v.orthonormal s)

theorem hsSchattenNorm_nonneg (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (p : ℝ) : 0 ≤ hsSchattenNorm b c p :=
  Real.rpow_nonneg (tsum_nonneg (fun i => Real.rpow_nonneg (hsSingularValue_nonneg b c i) _)) _

/-- Exact positive scalar homogeneity of a finite coordinate Lp norm. -/
theorem finite_lp_mul_of_nonneg {J : Type*} (s : Finset J) (f : J → ℝ)
    (hf : ∀ j, 0 ≤ f j) {K p : ℝ} (hK : 0 ≤ K) (hp : 0 < p) :
    (∑ j ∈ s, (K * f j) ^ p) ^ (1 / p) = K * (∑ j ∈ s, f j ^ p) ^ (1 / p) := by
  simp_rw [Real.mul_rpow hK (hf _)]
  rw [← Finset.mul_sum, Real.mul_rpow (Real.rpow_nonneg hK _)
    (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (hf j) _)), ← Real.rpow_mul hK,
    mul_one_div_cancel hp.ne', Real.rpow_one]

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- The full left ideal bound in actual Schatten p≥2, obtained from finite
orthonormal energies rather than assumed as an ideal norm property. -/
theorem hsSchattenNorm_leftComposition_le (b : HilbertBasis ι ℝ H)
    (Q : E →L[ℝ] G) (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (hsLeftComposition Q c) p ≤ ‖Q‖ * hsSchattenNorm b c p := by
  classical
  apply hsSchattenNorm_le_of_singular_finite_lp_bound b _ hp
  intro s
  let v := hsSingularBasis b (hsLeftComposition Q c)
  have hp0 : 0 < p := by linarith
  calc
    _ ≤ (∑ j ∈ s, (‖Q‖ * ‖hilbertSchmidtOperator b c (v j)‖) ^ p) ^ (1 / p) := by
      apply Real.rpow_le_rpow
        (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))
        (Finset.sum_le_sum (fun j _ => ?_)) (one_div_nonneg.mpr hp0.le)
      apply Real.rpow_le_rpow (norm_nonneg _) _ hp0.le
      simpa only [hilbertSchmidtOperator_leftComposition, ContinuousLinearMap.comp_apply] using
        Q.le_opNorm (hilbertSchmidtOperator b c (v j))
    _ = ‖Q‖ * (∑ j ∈ s, ‖hilbertSchmidtOperator b c (v j)‖ ^ p) ^ (1 / p) :=
      finite_lp_mul_of_nonneg s _ (fun _ => norm_nonneg _) (norm_nonneg Q) hp0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs_orthonormal_lp_le b c hp v v.orthonormal s) (norm_nonneg Q)

/-- Upper scalar homogeneity, with no nonzero-scalar assumption. -/
theorem hsSchattenNorm_smul_le (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (a : ℝ) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (a • c) p ≤ |a| * hsSchattenNorm b c p := by
  classical
  apply hsSchattenNorm_le_of_singular_finite_lp_bound b _ hp
  intro s
  let v := hsSingularBasis b (a • c)
  have hp0 : 0 < p := by linarith
  calc
    _ = (∑ j ∈ s, (|a| * ‖hilbertSchmidtOperator b c (v j)‖) ^ p) ^ (1 / p) := by
      simp only [v, map_smul, _root_.smul_apply, norm_smul, Real.norm_eq_abs]
    _ = |a| * (∑ j ∈ s, ‖hilbertSchmidtOperator b c (v j)‖ ^ p) ^ (1 / p) :=
      finite_lp_mul_of_nonneg s _ (fun _ => norm_nonneg _) (abs_nonneg a) hp0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hs_orthonormal_lp_le b c hp v v.orthonormal s) (abs_nonneg a)

theorem hsSchattenNorm_zero (b : HilbertBasis ι ℝ H) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (0 : HilbertSchmidtColumns ι E) p = 0 := by
  have h := hsSchattenNorm_smul_le b (0 : HilbertSchmidtColumns ι E) 0 hp
  simp only [zero_smul, abs_zero, zero_mul] at h
  exact le_antisymm h (hsSchattenNorm_nonneg _ _ _)

/-- Exact scalar homogeneity in the actual Schatten quantity. -/
theorem hsSchattenNorm_smul (b : HilbertBasis ι ℝ H)
    (c : HilbertSchmidtColumns ι E) (a : ℝ) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (a • c) p = |a| * hsSchattenNorm b c p := by
  apply le_antisymm (hsSchattenNorm_smul_le b c a hp)
  by_cases ha : a = 0
  · simp only [ha, abs_zero, zero_mul, zero_smul, hsSchattenNorm_zero b hp]
    exact le_rfl
  · have h := hsSchattenNorm_smul_le b (a • c) a⁻¹ hp
    rw [inv_smul_smul₀ ha, abs_inv] at h
    have hm := mul_le_mul_of_nonneg_left h (abs_nonneg a)
    simpa only [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr ha), one_mul] using hm

end KernelSeq
