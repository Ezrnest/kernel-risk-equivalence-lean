import KernelSeq.LipschitzFourierLpTransference
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual finite polynomial Schatten moment continuity

Pointwise convergence of finitely many scalar Fourier multipliers implies
convergence of the actual matrix-polynomial Lp moments. The HS reconstruction,
measurability and eventual uniform dominating constant are derived internally.
No polynomial or integral convergence certificate is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ν ι H : Type*} [Fintype ν] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def weightedTrigColumns (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ)
    (X Y : ν → H →L[ℝ] H) (a : ν → ℝ) (θ : ℝ × ℝ) : HilbertSchmidtColumns ι H :=
  ∑ i, ((a i * Real.cos (integerPlanePhase (k i) θ)) • finiteOperatorColumns b (X i) +
    (a i * Real.sin (integerPlanePhase (k i) θ)) • finiteOperatorColumns b (Y i))

omit [CompleteSpace H] in
theorem weightedTrigColumns_eq (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ)
    (X Y : ν → H →L[ℝ] H) (a : ν → ℝ) (θ : ℝ × ℝ) :
    weightedTrigColumns b k X Y a θ = finiteOperatorColumns b
      (realMatrixTrigPolynomial k (fun i => a i • X i) (fun i => a i • Y i) θ) := by
  ext j
  simp only [weightedTrigColumns, realMatrixTrigPolynomial, finiteOperatorColumns_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    _root_.sum_apply, add_apply, smul_apply, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_comm]

omit [CompleteSpace H] in
theorem weightedTrigColumns_continuous (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ)
    (X Y : ν → H →L[ℝ] H) (a : ν → ℝ) :
    Continuous (weightedTrigColumns b k X Y a) := by
  unfold weightedTrigColumns integerPlanePhase
  fun_prop

omit [CompleteSpace H] in
theorem weightedTrigColumns_tendsto {J : Type*} {l : Filter J}
    (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ) (X Y : ν → H →L[ℝ] H)
    (a : J → ν → ℝ) (a₀ : ν → ℝ)
    (ha : ∀ i, Tendsto (fun j => a j i) l (𝓝 (a₀ i))) (θ : ℝ × ℝ) :
    Tendsto (fun j => weightedTrigColumns b k X Y (a j) θ) l
      (𝓝 (weightedTrigColumns b k X Y a₀ θ)) := by
  unfold weightedTrigColumns
  exact tendsto_finsetSum _ fun i _ =>
    (((ha i).mul_const _).smul tendsto_const_nhds).add
      (((ha i).mul_const _).smul tendsto_const_nhds)

omit [CompleteSpace H] in
theorem weightedTrigColumns_norm_le (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ)
    (X Y : ν → H →L[ℝ] H) (a B : ν → ℝ) (hB : ∀ i, |a i| ≤ B i) (θ : ℝ × ℝ) :
    ‖weightedTrigColumns b k X Y a θ‖ ≤
      ∑ i, B i * (‖finiteOperatorColumns b (X i)‖ + ‖finiteOperatorColumns b (Y i)‖) := by
  unfold weightedTrigColumns
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hBi : 0 ≤ B i := (abs_nonneg _).trans (hB i)
  have hc : |a i * Real.cos (integerPlanePhase (k i) θ)| ≤ B i := by
    rw [abs_mul]
    exact (mul_le_mul (hB i) (Real.abs_cos_le_one _) (abs_nonneg _) hBi).trans_eq (mul_one _)
  have hs : |a i * Real.sin (integerPlanePhase (k i) θ)| ≤ B i := by
    rw [abs_mul]
    exact (mul_le_mul (hB i) (Real.abs_sin_le_one _) (abs_nonneg _) hBi).trans_eq (mul_one _)
  calc
    _ ≤ |a i * Real.cos (integerPlanePhase (k i) θ)| * ‖finiteOperatorColumns b (X i)‖ +
        |a i * Real.sin (integerPlanePhase (k i) θ)| * ‖finiteOperatorColumns b (Y i)‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
        ((a i * Real.cos (integerPlanePhase (k i) θ)) • finiteOperatorColumns b (X i))
        ((a i * Real.sin (integerPlanePhase (k i) θ)) • finiteOperatorColumns b (Y i))
    _ ≤ B i * ‖finiteOperatorColumns b (X i)‖ + B i * ‖finiteOperatorColumns b (Y i)‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
    _ = _ := by ring

/-- Actual Lp moment convergence for every countably generated parameter
filter, including the step-count and nonzero-step-size limits used by the walk. -/
theorem weightedTrigPolynomial_schattenMoment_tendsto {J : Type*} {l : Filter J}
    [l.IsCountablyGenerated] (b : HilbertBasis ι ℝ H) (k : ν → ℤ × ℤ)
    (X Y : ν → H →L[ℝ] H) (a : J → ν → ℝ) (a₀ : ν → ℝ)
    (ha : ∀ i, Tendsto (fun j => a j i) l (𝓝 (a₀ i))) {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun j => ∫ θ, hsSchattenNorm b (finiteOperatorColumns b
      (realMatrixTrigPolynomial k (fun i => a j i • X i) (fun i => a j i • Y i) θ)) p ^ p
        ∂fourierSquareMeasure) l
      (𝓝 (∫ θ, hsSchattenNorm b (finiteOperatorColumns b
        (realMatrixTrigPolynomial k (fun i => a₀ i • X i) (fun i => a₀ i • Y i) θ)) p ^ p
          ∂fourierSquareMeasure)) := by
  simp_rw [← weightedTrigColumns_eq]
  apply tendsto_integral_filter_of_norm_le_const
  · apply Eventually.of_forall
    intro j
    have hc := (hsSchattenNorm_continuous b hp).comp (weightedTrigColumns_continuous b k X Y (a j))
    exact (hc.rpow_const (fun _ => Or.inr (by linarith : 0 ≤ p))).aestronglyMeasurable
  · let B := fun i => |a₀ i| + 1
    let M := ∑ i, B i * (‖finiteOperatorColumns b (X i)‖ + ‖finiteOperatorColumns b (Y i)‖)
    have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => by dsimp only [B]; positivity
    have he : ∀ᶠ j in l, ∀ i, |a j i| ≤ B i := by
      apply Filter.eventually_all.mpr
      intro i
      have ht := (ha i).abs
      exact (ht.eventually (gt_mem_nhds (by dsimp only [B]; linarith))).mono fun _ h => h.le
    refine ⟨M ^ p, he.mono fun j hj => Eventually.of_forall fun θ => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hsSchattenNorm_nonneg b _ p) p)]
    exact Real.rpow_le_rpow (hsSchattenNorm_nonneg b _ p)
      ((hsSchattenNorm_le_hsNorm b _ hp).trans (weightedTrigColumns_norm_le b k X Y (a j) B hj θ))
      (by linarith)
  · apply Eventually.of_forall
    intro θ
    exact (((hsSchattenNorm_continuous b hp).continuousAt.tendsto).comp
      (weightedTrigColumns_tendsto b k X Y a a₀ ha θ)).rpow_const
        (Or.inr (by linarith : 0 ≤ p))

end
end KernelSeq
