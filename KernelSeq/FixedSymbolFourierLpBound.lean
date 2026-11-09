import KernelSeq.FixedPlanarRieszLp
import KernelSeq.FinitePolynomialLinearity

/-!
# The actual fixed-symbol Fourier bound

Absolutely summable genuine rotation weights combine the proved anisotropic
Riesz bounds. Actual finite partial symbols converge to the fixed smooth even
symbol, and genuine polynomial moment continuity passes to the limit. No
Walsh, Riesz, Fourier or Lipschitz multiplier estimate is an input.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelSeq
noncomputable section

/-- A genuine universal constant from the actual summable rotation weights. -/
def fixedSymbolFourierConstant : ℝ := 133 * ∑' n : ℕ, |fixedSymbolRieszWeight n|

theorem fixedSymbolFourierConstant_nonneg : 0 ≤ fixedSymbolFourierConstant :=
  mul_nonneg (by norm_num) (tsum_nonneg fun _ => abs_nonneg _)

universe uν uι uH

/-- The fixed smooth even Fourier estimate has an actual constructor. The
constant is universal; every finite matrix, polynomial and dyadic exponent is
quantified by the original proposition. -/
theorem fixedEvenFourierLpBound_proved :
    FixedEvenFourierLpBound.{uν, uι, uH} fixedSymbolFourierConstant where
  constant_nonneg := fixedSymbolFourierConstant_nonneg
  bound := by
    intro ν ι _ _ H _ _ _ b k X Y m
    let q := dyadicSchattenExponent m
    have hq : 2 ≤ q := dyadicSchattenExponent_ge_two m
    have hq0 : 0 < q := by linarith
    let F₀ := weightedTrigColumns b k X Y (fun _ => 1)
    let I₀ := hsSchattenLpNorm b fourierSquareMeasure F₀ q
    let W := ∑' n : ℕ, |fixedSymbolRieszWeight n|
    let M := weightedTrigColumnsHSBound b X Y
    let F := fun n : ℕ => weightedTrigColumns b k X Y
      (fun j => fixedPlanarRieszAverage n (((k j).1 : ℝ), ((k j).2 : ℝ)))
    let a := fun N : ℕ => fun j => fixedPlanarRieszPartialSymbol N (((k j).1 : ℝ), ((k j).2 : ℝ))
    let P := fun N : ℕ => weightedTrigColumns b k X Y (a N)
    have hI₀ : 0 ≤ I₀ := hsSchattenLpNorm_nonneg b F₀ q
    have hfactor : 0 ≤ 133 * q * I₀ := by positivity
    have hmodal (n : ℕ) : hsSchattenLpNorm b fourierSquareMeasure (F n) q ≤ 133 * q * I₀ := by
      exact fixedPlanarRieszAverage_schattenLpNorm_le b k X Y n m
    have hFbound (n : ℕ) (θ : ℝ × ℝ) : ‖F n θ‖ ≤ M :=
      weightedTrigColumns_norm_le_unit b k X Y _
        (fun j => fixedPlanarRieszAverage_abs_le_one n _) θ
    have hPnorm (N : ℕ) : hsSchattenLpNorm b fourierSquareMeasure (P N) q ≤
        fixedSymbolFourierConstant * q * I₀ := by
      have heq : P N = ∑ n ∈ Finset.range N, fixedSymbolRieszWeight n • F n := by
        funext θ
        simp only [P, a, fixedPlanarRieszPartialSymbol, Finset.sum_apply, Pi.smul_apply]
        exact weightedTrigColumns_weighted_sum (Finset.range N) b k X Y θ
          (fun n j => fixedPlanarRieszAverage n (((k j).1 : ℝ), ((k j).2 : ℝ))) fixedSymbolRieszWeight
      rw [heq]
      have hs := hsSchattenLpNorm_sum_le_of_bound (μ := fourierSquareMeasure) b
        (Finset.range N) (fun n => fixedSymbolRieszWeight n • F n)
        (fun n => |fixedSymbolRieszWeight n| * M) hq
        (fun n => by
          have hc : Continuous (fun θ : ℝ × ℝ => fixedSymbolRieszWeight n •
              weightedTrigColumns b k X Y
                (fun j => fixedPlanarRieszAverage n (((k j).1 : ℝ), ((k j).2 : ℝ))) θ) :=
            continuous_const.smul (weightedTrigColumns_continuous b k X Y _)
          have he : (fixedSymbolRieszWeight n • F n) =
              (fun θ : ℝ × ℝ => fixedSymbolRieszWeight n •
                weightedTrigColumns b k X Y
                  (fun j => fixedPlanarRieszAverage n (((k j).1 : ℝ), ((k j).2 : ℝ))) θ) := by
            funext θ
            rfl
          rw [he]
          exact hc.stronglyMeasurable)
        (fun n θ => by
          change ‖fixedSymbolRieszWeight n • F n θ‖ ≤ _
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hFbound n θ) (abs_nonneg _))
      refine hs.trans ?_
      calc
        _ ≤ ∑ n ∈ Finset.range N, |fixedSymbolRieszWeight n| * (133 * q * I₀) := by
          apply Finset.sum_le_sum
          intro n _
          rw [hsSchattenLpNorm_smul b _ _ hq]
          exact mul_le_mul_of_nonneg_left (hmodal n) (abs_nonneg _)
        _ = (∑ n ∈ Finset.range N, |fixedSymbolRieszWeight n|) * (133 * q * I₀) :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ W * (133 * q * I₀) := mul_le_mul_of_nonneg_right
          (fixedSymbolRieszWeight_abs_summable.sum_le_tsum _ (fun _ _ => abs_nonneg _)) hfactor
        _ = _ := by unfold fixedSymbolFourierConstant; dsimp only [W]; ring
    have hnormpow (G : (ℝ × ℝ) → HilbertSchmidtColumns ι H) :
        hsSchattenLpNorm b fourierSquareMeasure G q ^ q =
          ∫ θ, hsSchattenNorm b (G θ) q ^ q ∂fourierSquareMeasure := by
      unfold hsSchattenLpNorm
      exact Real.rpow_inv_rpow (integral_nonneg fun θ =>
        Real.rpow_nonneg (hsSchattenNorm_nonneg b _ q) q) hq0.ne'
    have hpartial (N : ℕ) : (∫ θ, hsSchattenNorm b (P N θ) q ^ q ∂fourierSquareMeasure) ≤
        (fixedSymbolFourierConstant * q) ^ q *
          (∫ θ, hsSchattenNorm b (F₀ θ) q ^ q ∂fourierSquareMeasure) := by
      have h := Real.rpow_le_rpow (hsSchattenLpNorm_nonneg b (P N) q) (hPnorm N) hq0.le
      change hsSchattenLpNorm b fourierSquareMeasure (P N) q ^ q ≤
        (fixedSymbolFourierConstant * q * hsSchattenLpNorm b fourierSquareMeasure F₀ q) ^ q at h
      rwa [Real.mul_rpow (mul_nonneg fixedSymbolFourierConstant_nonneg hq0.le) hI₀,
        hnormpow, hnormpow] at h
    have hlim := weightedTrigPolynomial_schattenMoment_tendsto b k X Y a
      (fun j => lipschitzEvenSymbol ((k j).1 : ℝ) ((k j).2 : ℝ))
      (fun j => fixedPlanarRieszPartialSymbol_tendsto (((k j).1 : ℝ), ((k j).2 : ℝ))) hq
    simp_rw [← weightedTrigColumns_eq] at hlim
    have hfinal := le_of_tendsto hlim (Eventually.of_forall hpartial)
    simpa only [fixedEvenFourierPolynomial, weightedTrigColumns_eq, one_smul,
      F₀, q, dyadicSchattenExponent] using hfinal

universe u

/-- The actual finite dyadic Lipschitz theorem needed by the manuscript,
with its universal constant and no external analytic proof parameter. -/
theorem finiteDyadicLipschitzSchur_proved :
    FiniteDyadicLipschitzSchur.{u, u, u, u} (2 * fixedSymbolFourierConstant) :=
  finiteDyadicLipschitzSchur_of_fixedEvenFourierLp fixedEvenFourierLpBound_proved

end
end KernelSeq
