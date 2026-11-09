import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Ring
import KernelSeq.EmpiricalCovariance

/-!
# Prediction risk with fixed design and noise moments

The finite-sample bias–variance decomposition. The noise moment
identities are explicit inputs under a fixed measure. Their derivation after
conditioning on all designs is in `ConditionalNoise`; the random-coefficient
conditional energy formula is in `ConditionalRisk`.
-/

open MeasureTheory
open scoped BigOperators

namespace KernelSeq

variable {Ω E ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
  {P : Measure Ω}

/-- Expansion into scalar noise products and deterministic vector inner products. -/
theorem noise_inner_expansion (ε : ι → ℝ) (a b : ι → E) :
    inner ℝ (∑ i, ε i • a i) (∑ j, ε j • b j) =
      ∑ i, ∑ j, (ε i * ε j) * inner ℝ (a i) (b j) := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

/-- Integrated second-moment formula, without any independence assumption. -/
theorem integral_noise_inner (ε : ι → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 2 P) (a b : ι → E) :
    (∫ ω, inner ℝ (∑ i, ε i ω • a i) (∑ j, ε j ω • b j) ∂P) =
      ∑ i, ∑ j, (∫ ω, ε i ω * ε j ω ∂P) * inner ℝ (a i) (b j) := by
  have hint (i j : ι) : Integrable
      (fun ω => (ε i ω * ε j ω) * inner ℝ (a i) (b j)) P :=
    ((hε i).integrable_mul (hε j)).mul_const _
  simp_rw [noise_inner_expansion]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_mul_const _ _

/-- The squared norm is integrable under the displayed scalar second moments. -/
theorem integrable_noise_norm_sq (ε : ι → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 2 P) (a : ι → E) :
    Integrable (fun ω => ‖∑ i, ε i ω • a i‖ ^ 2) P := by
  have hint (i j : ι) : Integrable
      (fun ω => (ε i ω * ε j ω) * inner ℝ (a i) (a j)) P :=
    ((hε i).integrable_mul (hε j)).mul_const _
  have hsum := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hint i j))
  simpa only [← noise_inner_expansion, real_inner_self_eq_norm_sq] using hsum

/-- Diagonal noise covariance yields the sum of squared prediction directions. -/
theorem integral_noise_norm_sq_of_diagonal [DecidableEq ι] (ε : ι → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 2 P) (a : ι → E) (σ : ℝ)
    (hcov : ∀ i j, (∫ ω, ε i ω * ε j ω ∂P) = if i = j then σ ^ 2 else 0) :
    (∫ ω, ‖∑ i, ε i ω • a i‖ ^ 2 ∂P) = σ ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
  classical
  have h := integral_noise_inner ε hε a a
  simp only [real_inner_self_eq_norm_sq] at h
  rw [h]
  simp [hcov, ← Finset.mul_sum]

/-- Integrability of the cross term with a fixed bias vector. -/
theorem integrable_inner_noise [IsFiniteMeasure P] (ε : ι → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 2 P) (a : ι → E) (r : E) :
    Integrable (fun ω => inner ℝ r (∑ i, ε i ω • a i)) P := by
  simp_rw [inner_sum, inner_smul_right]
  exact integrable_finsetSum _ (fun i _ => ((hε i).integrable (by norm_num)).mul_const _)

/-- Centered noise makes the deterministic-bias cross term vanish. -/
theorem integral_inner_noise_zero [IsFiniteMeasure P] (ε : ι → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 2 P) (a : ι → E) (r : E)
    (hmean : ∀ i, (∫ ω, ε i ω ∂P) = 0) :
    (∫ ω, inner ℝ r (∑ i, ε i ω • a i) ∂P) = 0 := by
  simp_rw [inner_sum, inner_smul_right]
  rw [integral_finsetSum _
    (fun i _ => ((hε i).integrable (by norm_num)).mul_const _)]
  simp [integral_mul_const, hmean]

/-- Exact bias/variance identity under centered diagonal noise moments.
No Gaussian distribution or fourth moments are required. -/
theorem integral_norm_bias_add_noise [IsProbabilityMeasure P] [DecidableEq ι]
    (ε : ι → Ω → ℝ) (hε : ∀ i, MemLp (ε i) 2 P)
    (a : ι → E) (r : E) (σ : ℝ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂P) = 0)
    (hcov : ∀ i j, (∫ ω, ε i ω * ε j ω ∂P) = if i = j then σ ^ 2 else 0) :
    (∫ ω, ‖r + ∑ i, ε i ω • a i‖ ^ 2 ∂P) =
      ‖r‖ ^ 2 + σ ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
  have hlin := integrable_inner_noise ε hε a r
  have hc : Integrable (fun _ : Ω => ‖r‖ ^ 2) P := integrable_const _
  simp_rw [norm_add_sq_real]
  calc
    (∫ ω, ‖r‖ ^ 2 + 2 * inner ℝ r (∑ i, ε i ω • a i) +
        ‖∑ i, ε i ω • a i‖ ^ 2 ∂P) =
        (∫ ω, ‖r‖ ^ 2 + 2 * inner ℝ r (∑ i, ε i ω • a i) ∂P) +
          ∫ ω, ‖∑ i, ε i ω • a i‖ ^ 2 ∂P :=
      integral_add (hc.add (hlin.const_mul 2)) (integrable_noise_norm_sq ε hε a)
    _ = ((∫ _ω : Ω, ‖r‖ ^ 2 ∂P) +
        ∫ ω, 2 * inner ℝ r (∑ i, ε i ω • a i) ∂P) +
          ∫ ω, ‖∑ i, ε i ω • a i‖ ^ 2 ∂P := by
      congr 1
      exact integral_add hc (hlin.const_mul 2)
    _ = _ := by
      rw [integral_const_mul, integral_inner_noise_zero ε hε a r hmean,
        integral_noise_norm_sq_of_diagonal ε hε a σ hcov]
      simp

section Prediction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual sample representer splits into a mean and scalar noise directions. -/
theorem prediction_mean_noise_decomposition {n : ℕ} (x : Fin n → H)
    (m ε : Fin n → ℝ) (A : H →L[ℝ] E) (f : E) :
    A (empiricalRepresenter x (fun i => m i + ε i)) - f =
      (A (empiricalRepresenter x m) - f) +
        ∑ i, ε i • ((n : ℝ)⁻¹ • A (x i)) := by
  simp only [empiricalRepresenter, add_smul, Finset.sum_add_distrib,
    smul_add, map_add, map_smul, map_sum, Finset.smul_sum, smul_smul]
  have hswap : ∑ i, ((n : ℝ)⁻¹ * ε i) • A (x i) =
      ∑ i, (ε i * (n : ℝ)⁻¹) • A (x i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  rw [hswap]
  abel

/-- The fixed-design risk formula for a bounded linear prediction rule.
The conditional noise-moment derivation from the full observation law remains
upstream, as does identifying `A` with the spectral prediction operator. -/
theorem fixed_design_prediction_risk [IsProbabilityMeasure P] {n : ℕ}
    (x : Fin n → H) (m : Fin n → ℝ) (ε : Fin n → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 2 P) (A : H →L[ℝ] E) (f : E) (σ : ℝ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂P) = 0)
    (hcov : ∀ i j, (∫ ω, ε i ω * ε j ω ∂P) = if i = j then σ ^ 2 else 0) :
    (∫ ω, ‖A (empiricalRepresenter x (fun i => m i + ε i ω)) - f‖ ^ 2 ∂P) =
      ‖A (empiricalRepresenter x m) - f‖ ^ 2 +
        σ ^ 2 / (n : ℝ) ^ 2 * ∑ i, ‖A (x i)‖ ^ 2 := by
  simp_rw [prediction_mean_noise_decomposition]
  rw [integral_norm_bias_add_noise ε hε _ _ σ hmean hcov]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, mul_pow, inv_pow,
    ← Finset.mul_sum]
  ring

end Prediction

end KernelSeq
