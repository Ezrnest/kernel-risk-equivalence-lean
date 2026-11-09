import KernelSeq.ContinuousCompactCalculus
import Mathlib.Topology.Algebra.InfiniteSum.Order
import KernelSeq.CovarianceMoments
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Actual exponential and second-order matrix Bernstein bounds

The exponential is `NormedSpace.exp` in the Banach algebra of bounded real
operators. Its spectral action is derived from the convergent exponential
series; no exponential functional-calculus identity is an assumption.
The final results are single-operator moment bounds, not an independent-sum
trace exponential estimate or a proof of matrix Bernstein concentration.
-/

open MeasureTheory Filter
open scoped BigOperators

namespace KernelSeq

noncomputable section

/-- Exact exponential quadratic remainder coefficient, with value `θ²/2` at radius zero. -/
def matrixExpRemainderCoefficient (θ R : ℝ) : ℝ :=
  if R = 0 then θ ^ 2 / 2 else (Real.exp (θ * R) - 1 - θ * R) / R ^ 2

@[simp] theorem matrixExpRemainderCoefficient_zero (θ : ℝ) :
    matrixExpRemainderCoefficient θ 0 = θ ^ 2 / 2 := by simp [matrixExpRemainderCoefficient]

theorem matrixExpRemainderCoefficient_of_ne_zero (θ : ℝ) {R : ℝ} (hR : R ≠ 0) :
    matrixExpRemainderCoefficient θ R = (Real.exp (θ * R) - 1 - θ * R) / R ^ 2 := by
  simp only [matrixExpRemainderCoefficient, if_neg hR]

@[simp] theorem matrixExpRemainderCoefficient_zero_parameter (R : ℝ) :
    matrixExpRemainderCoefficient 0 R = 0 := by simp [matrixExpRemainderCoefficient]

theorem matrixExpRemainderCoefficient_nonneg (θ R : ℝ) : 0 ≤ matrixExpRemainderCoefficient θ R := by
  unfold matrixExpRemainderCoefficient
  split_ifs
  · positivity
  · exact div_nonneg (by linarith [Real.add_one_le_exp (θ * R)]) (sq_nonneg R)

theorem exp_remainder_hasSum (z : ℝ) :
    HasSum (fun k : ℕ => z ^ (k + 2) / ((k + 2).factorial : ℝ))
      (Real.exp z - 1 - z) := by
  have h := NormedSpace.expSeries_div_hasSum_exp z
  rw [← Real.exp_eq_exp_ℝ] at h
  have ht := (hasSum_nat_add_iff' 2).mpr h
  simpa [Finset.sum_range_succ, Nat.factorial, sub_sub] using ht

theorem scalar_exp_remainder_le {θ R y : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hy : |y| ≤ R) :
    Real.exp (θ * y) ≤ 1 + θ * y + matrixExpRemainderCoefficient θ R * y ^ 2 := by
  by_cases hR0 : R = 0
  · subst R
    have hy0 : y = 0 := abs_eq_zero.mp (le_antisymm hy (abs_nonneg _))
    subst y
    simp [matrixExpRemainderCoefficient]
  have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
  have hterm (k : ℕ) :
      R ^ 2 * ((θ * y) ^ (k + 2) / ((k + 2).factorial : ℝ)) ≤
        y ^ 2 * ((θ * R) ^ (k + 2) / ((k + 2).factorial : ℝ)) := by
    have hpow : y ^ k ≤ R ^ k := (le_abs_self _).trans (by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hy k)
    have hmul := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (mul_nonneg (pow_nonneg hθ (k + 2)) (sq_nonneg y)) (sq_nonneg R))
    have hnum : R ^ 2 * (θ * y) ^ (k + 2) ≤ y ^ 2 * (θ * R) ^ (k + 2) := by
      simp only [mul_pow, pow_add] at hmul ⊢
      nlinarith [hmul]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hnum
      (Nat.cast_nonneg (Nat.factorial (k + 2)) : (0 : ℝ) ≤ _)
  have hs := hasSum_le hterm ((exp_remainder_hasSum (θ * y)).mul_left (R ^ 2))
    ((exp_remainder_hasSum (θ * R)).mul_left (y ^ 2))
  rw [matrixExpRemainderCoefficient, if_neg hR0]
  have hden : 0 < R ^ 2 := sq_pos_of_pos hRp
  have hs' := div_le_div_of_nonneg_right hs hden.le
  have hleft : (R ^ 2 * (Real.exp (θ * y) - 1 - θ * y)) / R ^ 2 =
      Real.exp (θ * y) - 1 - θ * y := by field_simp
  have hright : (y ^ 2 * (Real.exp (θ * R) - 1 - θ * R)) / R ^ 2 =
      (Real.exp (θ * R) - 1 - θ * R) / R ^ 2 * y ^ 2 := by ring
  rw [hleft, hright] at hs'
  linarith


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Powers act on an actual eigenvector by the corresponding scalar powers. -/
theorem operator_pow_eigen (Y : H →L[ℝ] H) {x : H} {y : ℝ}
    (hx : Y x = y • x) (n : ℕ) : (Y ^ n) x = y ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hx, smul_smul, pow_succ']
    congr 1
    ring

/-- The genuine operator exponential has the expected action on every eigenvector. -/
theorem operator_exp_eigen (Y : H →L[ℝ] H) {x : H} {y : ℝ}
    (hx : Y x = y • x) : (NormedSpace.exp Y) x = Real.exp y • x := by
  have hs := (ContinuousLinearMap.apply ℝ H x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Y)
  have hr := (NormedSpace.expSeries_div_hasSum_exp y).smul_const x
  rw [← Real.exp_eq_exp_ℝ] at hr
  apply hs.unique
  convert hr using 1
  funext n
  change ((n.factorial : ℝ)⁻¹ • Y ^ n) x = (y ^ n / n.factorial) • x
  simp only [smul_apply, operator_pow_eigen Y hx n, smul_smul, div_eq_mul_inv, mul_comm]

/-- The exact spectral action of `exp (θ Y)` on a compact selfadjoint eigenbasis. -/
theorem compact_operator_exp_eigen (Y : H →L[ℝ] H) (hc : IsCompactOperator Y)
    (hY : Y.IsSymmetric) (θ : ℝ) (i : CompactSpectralIndex Y) :
    NormedSpace.exp (θ • Y) (compactEigenbasis Y hc hY i) =
      Real.exp (θ * i.1) • compactEigenbasis Y hc hY i := by
  apply operator_exp_eigen
  simp only [smul_apply, compactEigenbasis_eigen, smul_smul]


omit [CompleteSpace H] in
/-- An actual bounded diagonal operator is positive when all its real eigenvalues are nonnegative. -/
theorem operator_nonneg_of_hilbertBasis_eigen {ι : Type*} (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H) (w : ι → ℝ) (heigen : ∀ i, A (b i) = w i • b i)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ A := by
  have hbound (i : ι) : ‖w i‖ ≤ ‖A‖ := by
    have hi := A.le_opNorm (b i)
    simpa only [heigen, norm_smul, b.orthonormal.norm_eq_one, mul_one] using hi
  have heq : A = hilbertDiagonal b w ‖A‖ (norm_nonneg _) hbound := by
    apply continuousLinearMap_eq_of_hilbertBasis b
    intro i
    rw [heigen, hilbertDiagonal_eigen]
  rw [heq]
  exact hilbertDiagonal_nonneg b w ‖A‖ (norm_nonneg _) hbound hw

/-- Positivity of the actual compact selfadjoint exponential, for every real parameter. -/
theorem compact_operator_exp_nonneg (Y : H →L[ℝ] H) (hc : IsCompactOperator Y)
    (hY : Y.IsSymmetric) (θ : ℝ) : 0 ≤ NormedSpace.exp (θ • Y) :=
  operator_nonneg_of_hilbertBasis_eigen (compactEigenbasis Y hc hY) _
    (fun i : CompactSpectralIndex Y => Real.exp (θ * i.1))
    (compact_operator_exp_eigen Y hc hY θ) (fun _ => (Real.exp_pos _).le)

/-- The true exponential norm bound, derived from the actual selfadjoint spectrum. -/
theorem compact_operator_exp_norm_le (Y : H →L[ℝ] H) (hc : IsCompactOperator Y)
    (hY : Y.IsSymmetric) {θ R : ℝ} (hθ : 0 ≤ θ) (hR : ‖Y‖ ≤ R) :
    ‖NormedSpace.exp (θ • Y)‖ ≤ Real.exp (θ * R) := by
  let b := compactEigenbasis Y hc hY
  have hbound (i : CompactSpectralIndex Y) : ‖Real.exp (θ * i.1)‖ ≤ Real.exp (θ * R) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((le_abs_self i.1).trans ((compactEigenvalue_norm_le Y hc hY i).trans hR)) hθ)
  have heq : NormedSpace.exp (θ • Y) = hilbertDiagonal b
      (fun i : CompactSpectralIndex Y => Real.exp (θ * i.1)) (Real.exp (θ * R))
      (Real.exp_pos _).le hbound := by
    apply continuousLinearMap_eq_of_hilbertBasis b
    intro i
    rw [hilbertDiagonal_eigen]
    exact compact_operator_exp_eigen Y hc hY θ i
  rw [heq]
  exact hilbertDiagonal_norm_le b _ _ _ _

/-- Finite dimensionality supplies compactness; it is not a separate certificate. -/
theorem finite_operator_exp_norm_le [FiniteDimensional ℝ H] (Y : H →L[ℝ] H)
    (hY : Y.IsSymmetric) {θ R : ℝ} (hθ : 0 ≤ θ) (hR : ‖Y‖ ≤ R) :
    ‖NormedSpace.exp (θ • Y)‖ ≤ Real.exp (θ * R) :=
  compact_operator_exp_norm_le Y (isCompactOperator_of_locallyCompactSpace_dom Y) hY hθ hR


/-- Genuine second-order Loewner bound for the actual exponential of a compact
selfadjoint operator. The coefficient has its true `R = 0` extension. -/
theorem compact_operator_exp_remainder_le (Y : H →L[ℝ] H) (hc : IsCompactOperator Y)
    (hY : Y.IsSymmetric) {θ R : ℝ} (hθ : 0 ≤ θ) (hR : ‖Y‖ ≤ R) :
    NormedSpace.exp (θ • Y) ≤
      1 + θ • Y + matrixExpRemainderCoefficient θ R • (Y * Y) := by
  let b := compactEigenbasis Y hc hY
  apply (ContinuousLinearMap.le_def _ _).mpr
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
  apply operator_nonneg_of_hilbertBasis_eigen b _
    (fun i : CompactSpectralIndex Y => 1 + θ * i.1 +
      matrixExpRemainderCoefficient θ R * i.1 ^ 2 - Real.exp (θ * i.1))
  · intro i
    simp only [sub_apply, add_apply, one_apply_eq_self, smul_apply, mul_apply_eq_comp,
      compactEigenbasis_eigen, map_smul, smul_smul, compact_operator_exp_eigen, b]
    module
  · intro i
    have hi : |i.1| ≤ R := (compactEigenvalue_norm_le Y hc hY i).trans hR
    have hr0 : 0 ≤ R := (norm_nonneg Y).trans hR
    linarith [scalar_exp_remainder_le hθ hr0 hi]

/-- The finite-dimensional matrix exponential inequality, without an additional compactness premise. -/
theorem finite_operator_exp_remainder_le [FiniteDimensional ℝ H] (Y : H →L[ℝ] H)
    (hY : IsSelfAdjoint Y) {θ R : ℝ} (hθ : 0 ≤ θ) (hR : ‖Y‖ ≤ R) :
    NormedSpace.exp (θ • Y) ≤
      1 + θ • Y + matrixExpRemainderCoefficient θ R • (Y * Y) :=
  compact_operator_exp_remainder_le Y (isCompactOperator_of_locallyCompactSpace_dom Y)
    hY.isSymmetric hθ hR



/-- The actual operator exponential dominates its affine first-order truncation. -/
theorem compact_one_add_operator_le_exp (Y : H →L[ℝ] H) (hc : IsCompactOperator Y)
    (hY : Y.IsSymmetric) : 1 + Y ≤ NormedSpace.exp Y := by
  let b := compactEigenbasis Y hc hY
  apply (ContinuousLinearMap.le_def _ _).mpr
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
  apply operator_nonneg_of_hilbertBasis_eigen b _
    (fun i : CompactSpectralIndex Y => Real.exp i.1 - 1 - i.1)
  · intro i
    have he := operator_exp_eigen Y (compactEigenbasis_eigen Y hc hY i)
    simp only [sub_apply, add_apply, one_apply_eq_self, compactEigenbasis_eigen, he, b]
    module
  · intro i
    linarith [Real.add_one_le_exp i.1]

/-- Finite real selfadjoint matrices need no separate spectral or compactness certificate. -/
theorem finite_one_add_operator_le_exp [FiniteDimensional ℝ H] (Y : H →L[ℝ] H)
    (hY : Y.IsSymmetric) : 1 + Y ≤ NormedSpace.exp Y :=
  compact_one_add_operator_le_exp Y (isCompactOperator_of_locallyCompactSpace_dom Y) hY


section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [FiniteDimensional ℝ H]

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
/-- Bounded measurable operator fields are genuinely Bochner integrable. -/
theorem integrable_operator_of_ae_norm_bound (Y : Ω → H →L[ℝ] H)
    (hYm : AEStronglyMeasurable Y P) {R : ℝ} (hR : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R) :
    Integrable Y P := (integrable_const R).mono' hYm hR

/-- The actual matrix exponential is integrable, from the true spectral norm bound. -/
theorem integrable_operator_exp_of_ae_norm_bound (Y : Ω → H →L[ℝ] H)
    (hYm : AEStronglyMeasurable Y P) (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω))
    {θ R : ℝ} (hθ : 0 ≤ θ) (hR : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R) :
    Integrable (fun ω => NormedSpace.exp (θ • Y ω)) P := by
  have hcont : Continuous (NormedSpace.exp : (H →L[ℝ] H) → H →L[ℝ] H) :=
    continuous_iff_continuousAt.mpr fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).continuousAt
  have hmeas := hcont.comp_aestronglyMeasurable
    ((continuous_const_smul θ).comp_aestronglyMeasurable hYm)
  apply (integrable_const (Real.exp (θ * R))).mono' hmeas
  filter_upwards [hY, hR] with ω hYω hRω
  exact finite_operator_exp_norm_le (Y ω) hYω.isSymmetric hθ hRω

/-- The centered exponential-moment bound uses actual Bochner expectations and
Loewner order. Centering removes the linear term after integration. -/
theorem integral_operator_exp_le_one_add_variance (Y : Ω → H →L[ℝ] H)
    (hYm : AEStronglyMeasurable Y P) (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω))
    {θ R : ℝ} (hθ : 0 ≤ θ) (hR : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R)
    (hmean : (∫ ω, Y ω ∂P) = 0) :
    (∫ ω, NormedSpace.exp (θ • Y ω) ∂P : H →L[ℝ] H) ≤
      1 + matrixExpRemainderCoefficient θ R • (∫ ω, Y ω * Y ω ∂P) := by
  have hYi := integrable_operator_of_ae_norm_bound Y hYm hR
  have hY2 := integrable_operator_square_of_bound Y hYi hR
  have hEi := integrable_operator_exp_of_ae_norm_bound Y hYm hY hθ hR
  have hlin := hYi.smul θ
  have hquad := hY2.smul (matrixExpRemainderCoefficient θ R)
  have hconst : Integrable (fun _ : Ω => (1 : H →L[ℝ] H)) P := integrable_const _
  have hm := integral_operator_mono (fun ω => NormedSpace.exp (θ • Y ω))
    (fun ω => 1 + θ • Y ω + matrixExpRemainderCoefficient θ R • (Y ω * Y ω))
    hEi ((hconst.add hlin).add hquad) (by
      filter_upwards [hY, hR] with ω hYω hRω
      exact finite_operator_exp_remainder_le (Y ω) hYω hθ hRω)
  have heq : (∫ ω, 1 + θ • Y ω +
      matrixExpRemainderCoefficient θ R • (Y ω * Y ω) ∂P : H →L[ℝ] H) =
      1 + matrixExpRemainderCoefficient θ R • (∫ ω, Y ω * Y ω ∂P) := by
    have hsum := integral_add (hconst.add hlin) hquad
    have hsumlin := integral_add hconst hlin
    simp only [Pi.add_apply, Pi.smul_apply] at hsum hsumlin
    rw [hsum, hsumlin, integral_smul, integral_smul, hmean]
    simp
  exact hm.trans_eq heq

/-- A genuine Loewner variance majorant can be substituted after expectation. -/
theorem integral_operator_exp_le_one_add_majorant (Y : Ω → H →L[ℝ] H)
    (hYm : AEStronglyMeasurable Y P) (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω))
    {θ R : ℝ} (hθ : 0 ≤ θ) (hR : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R)
    (hmean : (∫ ω, Y ω ∂P) = 0) (W : H →L[ℝ] H)
    (hW : (∫ ω, Y ω * Y ω ∂P : H →L[ℝ] H) ≤ W) :
    (∫ ω, NormedSpace.exp (θ • Y ω) ∂P : H →L[ℝ] H) ≤
      1 + matrixExpRemainderCoefficient θ R • W := by
  apply (integral_operator_exp_le_one_add_variance Y hYm hY hθ hR hmean).trans
  apply (ContinuousLinearMap.le_def _ _).mpr
  have heq : (1 + matrixExpRemainderCoefficient θ R • W) -
      (1 + matrixExpRemainderCoefficient θ R • (∫ ω, Y ω * Y ω ∂P)) =
      matrixExpRemainderCoefficient θ R • (W - ∫ ω, Y ω * Y ω ∂P) := by module
  rw [heq]
  exact ((ContinuousLinearMap.le_def _ _).mp hW).smul_of_nonneg
    (matrixExpRemainderCoefficient_nonneg θ R)


/-- The familiar matrix exponential-moment estimate with a true variance majorant.
Positivity of the majorant follows from the actual second moment and Loewner bound;
no logarithmic concavity, trace exponential inequality, or concentration result is assumed. -/
theorem integral_operator_exp_le_exp_majorant (Y : Ω → H →L[ℝ] H)
    (hYm : AEStronglyMeasurable Y P) (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω))
    {θ R : ℝ} (hθ : 0 ≤ θ) (hR : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R)
    (hmean : (∫ ω, Y ω ∂P) = 0) (W : H →L[ℝ] H)
    (hW : (∫ ω, Y ω * Y ω ∂P : H →L[ℝ] H) ≤ W) :
    (∫ ω, NormedSpace.exp (θ • Y ω) ∂P : H →L[ℝ] H) ≤
      NormedSpace.exp (matrixExpRemainderCoefficient θ R • W) := by
  have hYi := integrable_operator_of_ae_norm_bound Y hYm hR
  have hY2 := integrable_operator_square_of_bound Y hYi hR
  have hvar : (∫ ω, Y ω * Y ω ∂P : H →L[ℝ] H).IsPositive :=
    integral_operator_isPositive _ hY2 (hY.mono fun ω hω =>
      operator_square_isPositive_of_isSelfAdjoint (Y ω) hω)
  have hWpos : W.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive W).mp
    (((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hvar).trans hW)
  exact (integral_operator_exp_le_one_add_majorant Y hYm hY hθ hR hmean W hW).trans
    (finite_one_add_operator_le_exp _
      (hWpos.smul_of_nonneg (matrixExpRemainderCoefficient_nonneg θ R)).isSymmetric)

end Expectation
end
end KernelSeq
