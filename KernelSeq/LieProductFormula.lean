import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual Banach-algebra Lie--Trotter product formula

Near-identity powers and a noncommutative telescoping expansion control the
accumulated error. Both exponential steps have the same actual derivative at
zero, so their local difference is `o(t)`. No product-formula certificate,
commutativity, normalized unit norm, or finite dimensionality is assumed.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace KernelSeq

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- A near-identity power bound that retains the actual norm of the unit. -/
theorem norm_pow_le_norm_one_mul_one_add (A : 𝔸) (k : ℕ) :
    ‖A ^ k‖ ≤ ‖(1 : 𝔸)‖ * (1 + ‖A - 1‖) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hid : A ^ (k + 1) = A ^ k + (A - 1) * A ^ k := by
      rw [pow_succ']
      noncomm_ring
    rw [hid]
    calc
      ‖A ^ k + (A - 1) * A ^ k‖ ≤ ‖A ^ k‖ + ‖A - 1‖ * ‖A ^ k‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
      _ = (1 + ‖A - 1‖) * ‖A ^ k‖ := by ring
      _ ≤ (1 + ‖A - 1‖) * (‖(1 : 𝔸)‖ * (1 + ‖A - 1‖) ^ k) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by rw [pow_succ]; ring

/-- The exact noncommutative telescoping expansion of a power difference. -/
theorem pow_sub_pow_eq_sum_noncomm (A B : 𝔸) (n : ℕ) :
    A ^ n - B ^ n = ∑ k ∈ Finset.range n,
      A ^ k * (A - B) * B ^ (n - 1 - k) := by
  have ht := Finset.sum_range_sub (fun k => A ^ k * B ^ (n - k)) n
  calc
    A ^ n - B ^ n = ∑ k ∈ Finset.range n,
      (A ^ (k + 1) * B ^ (n - (k + 1)) - A ^ k * B ^ (n - k)) := by simpa using ht.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have h1 : n - (k + 1) = n - 1 - k := by omega
      have h2 : n - k = (n - 1 - k) + 1 := by omega
      rw [h1, h2, pow_succ A k, pow_succ' B (n - 1 - k)]
      noncomm_ring

/-- Uniform prefix-power bounds give a noncommutative Lipschitz estimate for powers. -/
theorem norm_pow_sub_pow_le_of_prefix_bounds (A B : 𝔸) (n : ℕ) (M : ℝ)
    (hA : ∀ k ≤ n, ‖A ^ k‖ ≤ M) (hB : ∀ k ≤ n, ‖B ^ k‖ ≤ M) :
    ‖A ^ n - B ^ n‖ ≤ (n : ℝ) * M ^ 2 * ‖A - B‖ := by
  have hM : 0 ≤ M := (norm_nonneg (A ^ 0)).trans (hA 0 (Nat.zero_le _))
  rw [pow_sub_pow_eq_sum_noncomm]
  calc
    ‖∑ k ∈ Finset.range n, A ^ k * (A - B) * B ^ (n - 1 - k)‖ ≤
      ∑ k ∈ Finset.range n, M ^ 2 * ‖A - B‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk0 : k ≤ n := (Finset.mem_range.mp hk).le
        have hk1 : n - 1 - k ≤ n := by omega
        calc
          ‖A ^ k * (A - B) * B ^ (n - 1 - k)‖ ≤
              (‖A ^ k‖ * ‖A - B‖) * ‖B ^ (n - 1 - k)‖ := by
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (M * ‖A - B‖) * M := by
            gcongr
            · exact hA k hk0
            · exact hB (n - 1 - k) hk1
          _ = _ := by ring
    _ = _ := by simp; ring


/-- Exponential form of the near-identity prefix bound, still without normalized unit. -/
theorem norm_pow_le_norm_one_mul_exp (A : 𝔸) (k : ℕ) :
    ‖A ^ k‖ ≤ ‖(1 : 𝔸)‖ * Real.exp ((k : ℝ) * ‖A - 1‖) := by
  calc
    ‖A ^ k‖ ≤ ‖(1 : 𝔸)‖ * (1 + ‖A - 1‖) ^ k := norm_pow_le_norm_one_mul_one_add A k
    _ ≤ ‖(1 : 𝔸)‖ * (Real.exp ‖A - 1‖) ^ k := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ‖A - 1‖]) k
    _ = _ := by rw [Real.exp_nat_mul]

/-- A step of size `c/n` has uniformly bounded prefix powers through the `n`th step. -/
theorem norm_prefix_pow_le_of_norm_sub_one (A : 𝔸) {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    {c : ℝ} (hc : 0 ≤ c) (hA : ‖A - 1‖ ≤ c / (n : ℝ)) :
    ‖A ^ k‖ ≤ ‖(1 : 𝔸)‖ * Real.exp c := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hstep : (k : ℝ) * ‖A - 1‖ ≤ c := by
    calc
      (k : ℝ) * ‖A - 1‖ ≤ (k : ℝ) * (c / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg k)
      _ ≤ (n : ℝ) * (c / (n : ℝ)) := mul_le_mul_of_nonneg_right hk' (div_nonneg hc hn'.le)
      _ = c := by field_simp
  exact (norm_pow_le_norm_one_mul_exp A k).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hstep) (norm_nonneg _))


section BanachAlgebra

variable [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- One actual Lie splitting step, in its original noncommuting order. -/
def lieStep (A B : 𝔸) (t : ℝ) : 𝔸 :=
  NormedSpace.exp (t • A) * NormedSpace.exp (t • B)

/-- The exact single exponential for the same infinitesimal generator. -/
def lieExactStep (A B : 𝔸) (t : ℝ) : 𝔸 := NormedSpace.exp (t • (A + B))

omit [CompleteSpace 𝔸] in
@[simp] theorem lieStep_zero (A B : 𝔸) : lieStep A B 0 = 1 := by
  simp [lieStep, NormedSpace.exp_zero]

omit [CompleteSpace 𝔸] in
@[simp] theorem lieExactStep_zero (A B : 𝔸) : lieExactStep A B 0 = 1 := by
  simp [lieExactStep, NormedSpace.exp_zero]

/-- The actual first derivative of the product step. -/
theorem lieStep_hasDerivAt_zero (A B : 𝔸) : HasDerivAt (lieStep A B) (A + B) 0 := by
  have hA := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
  have hB := hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0
  convert hA.mul hB using 1 <;> first | rfl | simp [NormedSpace.exp_zero]

theorem lieExactStep_hasDerivAt_zero (A B : 𝔸) : HasDerivAt (lieExactStep A B) (A + B) 0 := by
  convert hasDerivAt_exp_smul_const (𝕂 := ℝ) (A + B) 0 using 1 <;>
    first | rfl | simp [NormedSpace.exp_zero]

/-- The local consistency error is derived from the genuine exponential derivatives. -/
theorem lieStep_error_hasDerivAt_zero (A B : 𝔸) :
    HasDerivAt (fun t => lieStep A B t - lieExactStep A B t) 0 0 := by
  convert (lieStep_hasDerivAt_zero A B).sub (lieExactStep_hasDerivAt_zero A B) using 1 <;>
    first | rfl | simp

/-- Multiplying the real local error at `1/n` by `n` still gives a vanishing quantity. -/
theorem lieStep_weighted_error_tendsto_zero (A B : 𝔸) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ‖lieStep A B (n : ℝ)⁻¹ - lieExactStep A B (n : ℝ)⁻¹‖) atTop (𝓝 0) := by
  have h := hasDerivAt_iff_tendsto.mp (lieStep_error_hasDerivAt_zero A B)
  have ht := h.comp (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  convert ht using 1
  funext n
  simp only [Function.comp_apply, sub_zero, lieStep_zero, lieExactStep_zero, sub_self,
    smul_zero, norm_inv, Real.norm_natCast, inv_inv]


/-- The actual product and exact steps have uniformly bounded powers through the `n`th prefix.
The bound retains the actual norm of the unit, so normalized unit norm is unnecessary. -/
theorem lieStep_uniform_prefix_norms (A B : 𝔸) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n : ℕ in atTop, ∀ k ≤ n,
      ‖lieStep A B (n : ℝ)⁻¹ ^ k‖ ≤ M ∧ ‖lieExactStep A B (n : ℝ)⁻¹ ^ k‖ ≤ M := by
  obtain ⟨cP, hcP, hP⟩ := (lieStep_hasDerivAt_zero A B).isBigO_sub.exists_pos
  obtain ⟨cQ, hcQ, hQ⟩ := (lieExactStep_hasDerivAt_zero A B).isBigO_sub.exists_pos
  let c := max cP cQ
  have hc : 0 ≤ c := hcP.le.trans (le_max_left _ _)
  refine ⟨‖(1 : 𝔸)‖ * Real.exp c, mul_nonneg (norm_nonneg _) (Real.exp_pos _).le, ?_⟩
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop 1, hi.eventually hP.bound, hi.eventually hQ.bound]
    with n hn hPn hQn k hk
  have hPn' : ‖lieStep A B (n : ℝ)⁻¹ - 1‖ ≤ c / (n : ℝ) := by
    simp only [lieStep_zero, sub_zero, norm_inv, Real.norm_natCast] at hPn
    exact hPn.trans (by dsimp [c]; rw [div_eq_mul_inv]; gcongr; exact le_max_left _ _)
  have hQn' : ‖lieExactStep A B (n : ℝ)⁻¹ - 1‖ ≤ c / (n : ℝ) := by
    simp only [lieExactStep_zero, sub_zero, norm_inv, Real.norm_natCast] at hQn
    exact hQn.trans (by dsimp [c]; rw [div_eq_mul_inv]; gcongr; exact le_max_right _ _)
  exact ⟨norm_prefix_pow_le_of_norm_sub_one _ hn hk hc hPn',
    norm_prefix_pow_le_of_norm_sub_one _ hn hk hc hQn'⟩

/-- Repeating the exact step `n` times is exactly the exponential of `A+B`. -/
theorem lieExactStep_pow (A B : 𝔸) {n : ℕ} (hn : 0 < n) :
    lieExactStep A B (n : ℝ)⁻¹ ^ n = NormedSpace.exp (A + B) := by
  letI : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  rw [lieExactStep, ← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul]

/-- The actual noncommutative Lie--Trotter product formula in any complete real normed algebra. -/
theorem lie_trotter_product_formula (A B : 𝔸) :
    Tendsto (fun n : ℕ => (NormedSpace.exp ((n : ℝ)⁻¹ • A) *
      NormedSpace.exp ((n : ℝ)⁻¹ • B)) ^ n) atTop (𝓝 (NormedSpace.exp (A + B))) := by
  obtain ⟨M, _, hM⟩ := lieStep_uniform_prefix_norms A B
  have herr := lieStep_weighted_error_tendsto_zero A B
  have hlim : Tendsto (fun n : ℕ => M ^ 2 * ((n : ℝ) *
      ‖lieStep A B (n : ℝ)⁻¹ - lieExactStep A B (n : ℝ)⁻¹‖)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := M ^ 2)).mul herr
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1, hM] with n hn hMn
  change ‖lieStep A B (n : ℝ)⁻¹ ^ n - NormedSpace.exp (A + B)‖ ≤ _
  rw [← lieExactStep_pow A B hn]
  exact (norm_pow_sub_pow_le_of_prefix_bounds _ _ n M
    (fun k hk => (hMn k hk).1) (fun k hk => (hMn k hk).2)).trans_eq (by ring)


/-- Time-parameter form, with the coefficient exactly `t/n` in each exponential. -/
theorem lie_trotter_product_formula_smul (A B : 𝔸) (t : ℝ) :
    Tendsto (fun n : ℕ => (NormedSpace.exp ((t / (n : ℝ)) • A) *
      NormedSpace.exp ((t / (n : ℝ)) • B)) ^ n) atTop
        (𝓝 (NormedSpace.exp (t • (A + B)))) := by
  simpa only [smul_smul, smul_add, div_eq_mul_inv, mul_comm] using
    lie_trotter_product_formula (t • A) (t • B)

end BanachAlgebra
end
end KernelSeq
