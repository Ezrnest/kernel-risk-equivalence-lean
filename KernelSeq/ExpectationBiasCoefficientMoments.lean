import KernelSeq.ExpectationGoodMoments

/-!
# Integrating the actual bias-transfer coefficient forms

The RHS amplitude, the deterministic cutoff and the covariance deviation
enter the multiplicative bias coefficient through an affine sum. These
identities and bounds supply the genuine coefficient second moments used
by the original-scale bias transfer, including zero target energy.
-/

open MeasureTheory

namespace KernelSeq

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem memLp_bias_affine_coefficient [IsFiniteMeasure P] {U δ : Ω → ℝ}
    (hU : MemLp U 2 P) (hδ : MemLp δ 2 P) (C τ : ℝ) :
    MemLp (fun ω => U ω + C * (τ + δ ω / τ)) 2 P := by
  have hd : MemLp (fun ω => δ ω / τ) 2 P := by
    simpa only [div_eq_mul_inv] using hδ.mul_const τ⁻¹
  exact hU.add (((memLp_const τ).add hd).const_mul C)

/-- Three genuine square moments bound the affine coefficient. -/
theorem integral_bias_affine_coefficient_sq_le [IsFiniteMeasure P]
    (hmass : P.real Set.univ ≤ 1) {U δ : Ω → ℝ}
    (hU : MemLp U 2 P) (hδ : MemLp δ 2 P) (C τ : ℝ) :
    (∫ ω, (U ω + C * (τ + δ ω / τ)) ^ 2 ∂P) ≤
      3 * ((∫ ω, U ω ^ 2 ∂P) + C ^ 2 * τ ^ 2 +
        C ^ 2 / τ ^ 2 * (∫ ω, δ ω ^ 2 ∂P)) := by
  have hu := memLp_bias_affine_coefficient hU hδ C τ
  have h1 := hU.integrable_sq
  have h2 : Integrable (fun _ : Ω => C ^ 2 * τ ^ 2) P := integrable_const _
  have h3 : Integrable (fun ω => C ^ 2 / τ ^ 2 * δ ω ^ 2) P :=
    hδ.integrable_sq.const_mul _
  have he1 := integral_add (h1.add h2) h3
  have he2 := integral_add h1 h2
  dsimp only [Pi.add_apply] at he1 he2
  have hpoint (ω : Ω) :
      (U ω + C * (τ + δ ω / τ)) ^ 2 ≤
        3 * (U ω ^ 2 + C ^ 2 * τ ^ 2 + C ^ 2 / τ ^ 2 * δ ω ^ 2) := by
    have hh : C ^ 2 / τ ^ 2 * δ ω ^ 2 = (C * (δ ω / τ)) ^ 2 := by ring
    rw [hh]
    nlinarith [sq_nonneg (U ω - C * τ), sq_nonneg (U ω - C * (δ ω / τ)),
      sq_nonneg (C * τ - C * (δ ω / τ))]
  calc
    _ ≤ ∫ ω, 3 * (U ω ^ 2 + C ^ 2 * τ ^ 2 + C ^ 2 / τ ^ 2 * δ ω ^ 2) ∂P :=
      integral_mono hu.integrable_sq (((h1.add h2).add h3).const_mul 3) hpoint
    _ = 3 * ((∫ ω, U ω ^ 2 ∂P) + P.real Set.univ * (C ^ 2 * τ ^ 2) +
        C ^ 2 / τ ^ 2 * (∫ ω, δ ω ^ 2 ∂P)) := by
      rw [integral_const_mul, he1, he2]
      simp only [integral_const_mul, integral_const, smul_eq_mul]
      ring
    _ ≤ _ := by
      have hh := mul_le_of_le_one_left (by positivity : 0 ≤ C ^ 2 * τ ^ 2) hmass
      linarith

/-- Exact normalization of the additive source coefficient's square moment. -/
theorem integral_bias_source_coefficient_sq {E : Ω → ℝ} (C τ W : ℝ)
    {V : ℝ} (hV : 0 < V) :
    (∫ ω, ((C * E ω / τ * W) / Real.sqrt V) ^ 2 ∂P) =
      (C ^ 2 * W ^ 2 / (τ ^ 2 * V)) * (∫ ω, E ω ^ 2 ∂P) := by
  have he (ω : Ω) : ((C * E ω / τ * W) / Real.sqrt V) ^ 2 =
      (C ^ 2 * W ^ 2 / (τ ^ 2 * V)) * E ω ^ 2 := by
    rw [div_pow, Real.sq_sqrt hV.le]
    ring
  simp_rw [he]
  exact integral_const_mul _ _

end KernelSeq
