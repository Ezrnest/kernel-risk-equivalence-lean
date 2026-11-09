import KernelSeq.RectangularTriangularSchur
import KernelSeq.ChiStepRepresentation

/-!
# Actual chi Schur bounds from strict steps

The actual derivative of the removable manuscript chi has L1 mass one.
Its genuine strict-step representation is integrated in the actual finite
HS column Hilbert space. The resulting dyadic bound is linear in p. Diagonal
removal uses a linear combination of two strict steps, without composing two
p-dependent estimates or assuming a pinching contraction or HMS theorem.
-/

open MeasureTheory Filter
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {ι κ H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Finite
variable [Fintype ι] [Fintype κ]

omit [CompleteSpace E] in
/-- Actual finite constant Schur matrices act by scalar multiplication. -/
theorem finiteMatrixSchurColumns_const (a : HilbertBasis κ ℝ E) (r : ℝ)
    (c : HilbertSchmidtColumns ι E) : finiteMatrixSchurColumns a (fun _ _ => r) c = r • c := by
  simpa only [mul_one, finiteMatrixSchurColumns_one] using
    finiteMatrixSchurColumns_smul a (fun _ _ => 1) r c

omit [CompleteSpace E] in
/-- Actual finite Schur columns respect subtraction in the scalar kernel. -/
theorem finiteMatrixSchurColumns_sub (a : HilbertBasis κ ℝ E) (M N : κ → ι → ℝ)
    (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a (fun i j => M i j - N i j) c =
      finiteMatrixSchurColumns a M c - finiteMatrixSchurColumns a N c := by
  ext j
  simp only [finiteMatrixSchurColumns_apply, sub_mul, sub_smul, Finset.sum_sub_distrib,
    lp.coeFn_sub, Pi.sub_apply]

omit [Fintype ι] in
/-- Negation leaves the actual Schatten quantity unchanged. -/
theorem hsSchattenNorm_neg_eq (b : HilbertBasis ι ℝ H) (c : HilbertSchmidtColumns ι E)
    {p : ℝ} (hp : 2 ≤ p) : hsSchattenNorm b (-c) p = hsSchattenNorm b c p := by
  simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using hsSchattenNorm_smul b c (-1) hp

omit [Fintype ι] in
/-- The actual Schatten triangle estimate for a difference of two HS families. -/
theorem hsSchattenNorm_sub_le_add (b : HilbertBasis ι ℝ H) (c d : HilbertSchmidtColumns ι E)
    {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (c - d) p ≤ hsSchattenNorm b c p + hsSchattenNorm b d p := by
  simpa only [sub_eq_add_neg, hsSchattenNorm_neg_eq b d hp] using hsSchattenNorm_add_le b c (-d) hp

/-- Every scalar coordinate of the actual derivative-weighted step is
integrable, derived from the genuine chi derivative L1 theorem. -/
theorem integrable_chiStepEntry (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (s t : ℝ) :
    Integrable (fun r : ℝ => if t + r < s then deriv (interactionChi α) r else 0) := by
  have hm : MeasurableSet {r : ℝ | t + r < s} :=
    measurableSet_lt (measurable_const.add measurable_id) measurable_const
  have heq : (fun r : ℝ => if t + r < s then deriv (interactionChi α) r else 0) =
      {r : ℝ | t + r < s}.indicator (deriv (interactionChi α)) := by
    funext r
    rfl
  rw [heq]
  exact (interactionChi_deriv_integrable hα0 hα1).indicator hm

/-- Actual finite HS columns of the derivative-weighted threshold step. -/
def chiStepIntegralColumns (a : HilbertBasis κ ℝ E) (α : ℝ)
    (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E) (r : ℝ) : HilbertSchmidtColumns ι E :=
  finiteMatrixSchurColumns a (fun i j => if y j + r < x i then deriv (interactionChi α) r else 0) c

omit [CompleteSpace E] in
/-- Genuine HS Bochner integrability of the chi step columns, not an
operator-valued measurability or integrability premise. -/
theorem integrable_chiStepIntegralColumns (a : HilbertBasis κ ℝ E) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E) :
    Integrable (chiStepIntegralColumns a α x y c) :=
  integrable_finiteMatrixSchurColumns a _ (fun i j => integrable_chiStepEntry α hα0 hα1 (x i) (y j)) c

omit [CompleteSpace E] in
/-- The actual weighted columns factor into the genuine derivative and the
actual strict-threshold matrix, with equality at every r. -/
theorem chiStepIntegralColumns_eq_smul (a : HilbertBasis κ ℝ E) (α : ℝ)
    (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E) (r : ℝ) :
    chiStepIntegralColumns a α x y c r = deriv (interactionChi α) r •
      finiteMatrixSchurColumns a (fun i j => if y j + r < x i then 1 else 0) c := by
  rw [chiStepIntegralColumns, ← finiteMatrixSchurColumns_smul]
  congr 1
  funext i j
  split_ifs <;> simp

/-- The actual integrated chi step has the uniform dyadic bound `p/2`, since
the derived derivative L1 mass is exactly one. -/
theorem chiStepIntegralColumns_integral_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ)
    (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (∫ r : ℝ, chiStepIntegralColumns a α x y c r) ((2 : ℝ) ^ (m + 1)) ≤
      ((2 : ℝ) ^ (m + 1) / 2) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  let p := (2 : ℝ) ^ (m + 1)
  have hp : 2 ≤ p := by
    simpa only [p, pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 1)
  have hd : Integrable (fun r : ℝ => |deriv (interactionChi α) r|) := by
    simpa only [Real.norm_eq_abs] using (interactionChi_deriv_integrable hα0 hα1).norm
  have hbound : ∀ᵐ r : ℝ, hsSchattenNorm b (chiStepIntegralColumns a α x y c r) p ≤
      |deriv (interactionChi α) r| * (p / 2 * hsSchattenNorm b c p) := by
    apply Eventually.of_forall
    intro r
    rw [chiStepIntegralColumns_eq_smul, hsSchattenNorm_smul b _ _ hp]
    exact mul_le_mul_of_nonneg_left (finiteRectangularThresholdStep_dyadic_le b a x y r m c) (abs_nonneg _)
  have hi := hsSchattenNorm_integral_le_of_ae_bound b hp _
    (integrable_chiStepIntegralColumns a α hα0 hα1 x y c) _ (hd.mul_const _) hbound
  rw [integral_mul_const] at hi
  have hmass : (∫ r : ℝ, |deriv (interactionChi α) r|) = 1 := by
    simpa only [Real.norm_eq_abs] using interactionChi_deriv_norm_integral_eq_one hα0 hα1
  rw [hmass, one_mul] at hi
  exact hi

/-- Actual finite Schur columns satisfy the actual chi integral identity.
This reconstructs the operator-valued representation from scalar coordinates. -/
theorem finite_chi_columns_eq_integral (a : HilbertBasis κ ℝ E)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ)
    (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a (fun i j => interactionChi α (x i - y j)) c =
      -c + ∫ r : ℝ, chiStepIntegralColumns a α x y c r := by
  have hker : (fun i j => interactionChi α (x i - y j)) =
      (fun i j => -1 + ∫ r : ℝ, if y j + r < x i then deriv (interactionChi α) r else 0) := by
    funext i j
    rw [interactionChi_step_representation_indicator hα0 hα1]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun r => by
      change (if r < x i - y j then deriv (interactionChi α) r else 0) =
        (if y j + r < x i then deriv (interactionChi α) r else 0)
      simp only [show (r < x i - y j) ↔ y j + r < x i by constructor <;> intro h <;> linarith]
  rw [hker, finiteMatrixSchurColumns_add, finiteMatrixSchurColumns_const,
    ← integral_finiteMatrixSchurColumns a _ (fun i j => integrable_chiStepEntry α hα0 hα1 (x i) (y j)) c,
    neg_one_smul]
  rfl

/-- The actual chi translation kernel has a genuine dyadic bound `1+p/2`,
with no chi regularity or HMS certificate. -/
theorem finite_chi_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ)
    (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => interactionChi α (x i - y j)) c) ((2 : ℝ) ^ (m + 1)) ≤
      (1 + (2 : ℝ) ^ (m + 1) / 2) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  have hp : 2 ≤ (2 : ℝ) ^ (m + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 1)
  rw [finite_chi_columns_eq_integral a α hα0 hα1 x y c]
  calc
    _ ≤ hsSchattenNorm b (-c) ((2 : ℝ) ^ (m + 1)) +
        hsSchattenNorm b (∫ r : ℝ, chiStepIntegralColumns a α x y c r) ((2 : ℝ) ^ (m + 1)) :=
      hsSchattenNorm_add_le b _ _ hp
    _ ≤ hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) +
        ((2 : ℝ) ^ (m + 1) / 2) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
      rw [hsSchattenNorm_neg_eq b c hp]
      exact add_le_add le_rfl (chiStepIntegralColumns_integral_dyadic_le b a α hα0 hα1 x y m c)
    _ = _ := by ring

/-- Equality of two scalar labels is the identity kernel minus the two
strict comparison kernels, with equality handled explicitly. -/
theorem equalGridIndicator_eq_strictSteps (s t : ℝ) :
    (if s = t then (1 : ℝ) else 0) =
      1 - (if t < s then 1 else 0) - (if -t < -s then 1 else 0) := by
  split_ifs <;> norm_num at * <;> grind

/-- An actual equal-grid block matrix has a dyadic linear bound, derived by
adding two strict-step estimates, without a pinching norm certificate. -/
theorem finite_equalGridIndicator_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (x : κ → ℝ) (y : ι → ℝ) (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => if x i = y j then 1 else 0) c) ((2 : ℝ) ^ (m + 1)) ≤
      (1 + (2 : ℝ) ^ (m + 1)) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  have hp : 2 ≤ (2 : ℝ) ^ (m + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 1)
  have hker : (fun i j => if x i = y j then (1 : ℝ) else 0) =
      (fun i j => (1 - (if y j < x i then 1 else 0)) - (if -y j < -x i then 1 else 0)) := by
    funext i j
    exact equalGridIndicator_eq_strictSteps (x i) (y j)
  rw [hker, finiteMatrixSchurColumns_sub, finiteMatrixSchurColumns_sub,
    finiteMatrixSchurColumns_const, one_smul]
  calc
    _ ≤ (hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) +
        hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => if y j < x i then 1 else 0) c) ((2 : ℝ) ^ (m + 1))) +
        hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => if -y j < -x i then 1 else 0) c) ((2 : ℝ) ^ (m + 1)) :=
      (hsSchattenNorm_sub_le_add b _ _ hp).trans
        (add_le_add (hsSchattenNorm_sub_le_add b _ _ hp) le_rfl)
    _ ≤ (hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) +
        ((2 : ℝ) ^ (m + 1) / 2) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1))) +
        ((2 : ℝ) ^ (m + 1) / 2) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) :=
      add_le_add (add_le_add le_rfl (finiteRectangularStrictStep_dyadic_le b a x y m c))
        (finiteRectangularStrictStep_dyadic_le b a (fun i => -x i) (fun j => -y j) m c)
    _ = _ := by ring

/-- The actual zero-diagonal manuscript chi has dyadic bound `3p` on every
finite real rectangular grid. All scalar regularity, strict-step, integral and
block estimates are proved; no HMS or chi multiplier certificate is assumed. -/
theorem finite_chiOffDiagonal_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ)
    (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => interactionChiOffDiagonal α (x i) (y j)) c) ((2 : ℝ) ^ (m + 1)) ≤
      3 * (2 : ℝ) ^ (m + 1) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  let p := (2 : ℝ) ^ (m + 1)
  have hp : 2 ≤ p := by
    simpa only [p, pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 1)
  have hker : (fun i j => interactionChiOffDiagonal α (x i) (y j)) =
      (fun i j => interactionChi α (x i - y j) - interactionChi α 0 * (if x i = y j then 1 else 0)) := by
    funext i j
    by_cases h : x i = y j <;> simp [interactionChiOffDiagonal, h]
  rw [hker, finiteMatrixSchurColumns_sub, finiteMatrixSchurColumns_smul]
  calc
    _ ≤ hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => interactionChi α (x i - y j)) c) p +
        hsSchattenNorm b (interactionChi α 0 • finiteMatrixSchurColumns a (fun i j => if x i = y j then 1 else 0) c) p :=
      hsSchattenNorm_sub_le_add b _ _ hp
    _ = hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => interactionChi α (x i - y j)) c) p +
        |interactionChi α 0| * hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => if x i = y j then 1 else 0) c) p := by
      rw [hsSchattenNorm_smul b _ _ hp]
    _ ≤ (1 + p / 2) * hsSchattenNorm b c p + 1 * ((1 + p) * hsSchattenNorm b c p) :=
      add_le_add (finite_chi_dyadic_le b a α hα0 hα1 x y m c)
        (mul_le_mul (interactionChi_abs_le_one hα0.le (by linarith : α ≤ 2) 0)
          (finite_equalGridIndicator_dyadic_le b a x y m c) (hsSchattenNorm_nonneg b _ p) (by norm_num))
    _ = (2 + 3 * p / 2) * hsSchattenNorm b c p := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : 2 + 3 * p / 2 ≤ 3 * p) (hsSchattenNorm_nonneg b c p)

end Finite

/-- The actual zero-diagonal chi grid is bounded by one, with no HMS symbol
certificate. This supplies the genuine bounded HS Schur construction. -/
theorem chiOffDiagonal_grid_norm_le (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x : κ → ℝ) (y : ι → ℝ) (i : κ) (j : ι) :
    ‖interactionChiOffDiagonal α (x i) (y j)‖ ≤ 1 := by
  unfold interactionChiOffDiagonal
  split_ifs
  · norm_num
  · exact interactionChi_abs_le_one hα0.le (by linarith : α ≤ 2) _

/-- The actual infinite HS chi DOI has the same proved dyadic `3p` bound.
Finite compression, HS construction and pointwise Schatten inheritance are
all proved upstream. No finite leaf, HMS theorem, separability or multiplier
bound is an assumption. -/
theorem infinite_chiOffDiagonal_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (x : κ → ℝ) (y : ι → ℝ)
    (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (hsSchurMultiplier a (fun i j => interactionChiOffDiagonal α (x i) (y j))
      1 zero_le_one (chiOffDiagonal_grid_norm_le α hα0 hα1 x y) c) ((2 : ℝ) ^ (m + 1)) ≤
      3 * (2 : ℝ) ^ (m + 1) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  have hp : 2 ≤ (2 : ℝ) ^ (m + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 1)
  apply hsSchur_schatten_bound_of_finite b a _ 1 zero_le_one _ hp (by positivity)
  intro s t d
  rw [← finiteMatrixSchurColumns_eq (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
    (fun (i : t) (j : s) => interactionChiOffDiagonal α (x i) (y j)) 1 zero_le_one
    (fun i j => chiOffDiagonal_grid_norm_le α hα0 hα1 x y i j) d]
  exact finite_chiOffDiagonal_dyadic_le (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
    α hα0 hα1 (fun i : t => x i) (fun j : s => y j) m d

end
end KernelSeq
