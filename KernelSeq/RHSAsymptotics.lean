import KernelSeq.RHSFluctuation
import KernelSeq.GoodEvents

/-!
# Stochastic negligibility of the actual empirical right-hand side

The `o_P` bound for the empirical right-hand-side fluctuation, with a
general bounded normalizer. The residual may vanish, and the inverse-norm
scaling uses Lean's
zero-inverse convention, and the unscaled fluctuation is then zero a.s.
The spectral residual identity and construction of the inverse square root
remain separate obligations.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace KernelSeq

/-- A vanishing integral second-moment bound implies convergence in measure.
This works with arbitrary measures and filters; it needs no event measurability. -/
theorem tendstoInMeasure_zero_of_second_moment_bound
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {l : Filter ι} (z : ι → Ω → E) (a : ι → ℝ)
    (hz : ∀ i, MemLp (z i) 2 P)
    (hbound : ∀ᶠ i in l, (∫ ω, ‖z i ω‖ ^ 2 ∂P) ≤ a i)
    (ha : Tendsto a l (𝓝 0)) :
    TendstoInMeasure P z l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [sub_zero]
  have hlim : Tendsto (fun i => ENNReal.ofReal (a i / ε ^ 2)) l (𝓝 0) := by
    simpa only [zero_div, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (ha.div_const (ε ^ 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hlim (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hbound] with i hi
  have hint := (memLp_two_iff_integrable_sq_norm (hz i).1).mp (hz i)
  have hm := (hint.div_const (ε ^ 2)).measure_le_integral
    (Eventually.of_forall (fun ω => div_nonneg (sq_nonneg ‖z i ω‖) (sq_nonneg ε)))
    (s := {ω | ε ≤ ‖z i ω‖}) (fun ω hω => by
      rw [le_div_iff₀ (sq_pos_of_pos hε)]
      change ε ≤ ‖z i ω‖ at hω
      nlinarith [norm_nonneg (z i ω)])
  refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  exact div_le_div_of_nonneg_right hi (sq_nonneg ε)

variable {ι X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The actual right-hand-side fluctuation is square integrable. -/
theorem memLp_rhsFluctuation {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (f : Lp ℝ 2 μ) (h : H) (R : H →L[ℝ] H)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, ‖R (k y)‖ ^ 2 ≤ L) :
    MemLp (fun ω => R (rhsFluctuation k hk f h (fun i => x i ω))) 2 P := by
  apply (memLp_normalized_rhs hn x hlaw k hk
    (f - featureEmbedding μ k hk h) R hL).ae_eq
  filter_upwards [rhsFluctuation_eq_residual_ae x hlaw k hk f h] with ω hω
  exact congrArg R hω.symm

variable [MeasurableSpace H] [BorelSpace H]

/-- Normalize by the residual norm without imposing a positive lower bound.
If the residual is zero, the scaled vector is zero by definition. -/
theorem integral_scaled_rhsFluctuation_sq_le {n : ℕ} (hn : 0 < n)
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (f : Lp ℝ 2 μ) (h : H) (R : H →L[ℝ] H)
    {L : ℝ} (hLnonneg : 0 ≤ L) (hL : ∀ᵐ y ∂μ, ‖R (k y)‖ ^ 2 ≤ L) :
    (∫ ω, ‖‖f - featureEmbedding μ k hk h‖⁻¹ •
      R (rhsFluctuation k hk f h (fun i => x i ω))‖ ^ 2 ∂P) ≤ L / (n : ℝ) := by
  simp_rw [norm_smul, Real.norm_eq_abs, mul_pow]
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left
    (integral_rhsFluctuation_sq_le hn x hlaw hindep k hk f h R hL)
    (sq_nonneg _)).trans ?_
  by_cases hr : ‖f - featureEmbedding μ k hk h‖ = 0
  · simp only [hr, inv_zero, abs_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
    exact div_nonneg hLnonneg (Nat.cast_nonneg n)
  · have habs : |‖f - featureEmbedding μ k hk h‖⁻¹| =
        ‖f - featureEmbedding μ k hk h‖⁻¹ := abs_of_nonneg (by positivity)
    rw [habs]
    exact le_of_eq (by field_simp)

omit [IsProbabilityMeasure P] [MeasurableSpace H] [BorelSpace H] in
/-- Zero population residual also forces the actual fluctuation to vanish a.s.;
the scaling convention therefore does not conceal a residual-free error. -/
theorem rhsFluctuation_eq_zero_ae_of_residual_zero {n : ℕ}
    (x : Fin n → Ω → X) (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (f : Lp ℝ 2 μ) (h : H)
    (hr : f - featureEmbedding μ k hk h = 0) :
    (fun ω => rhsFluctuation k hk f h (fun i => x i ω)) =ᵐ[P] 0 := by
  filter_upwards [rhsFluctuation_eq_residual_ae x hlaw k hk f h] with ω hω
  rw [hω, hr]
  simp [empiricalRepresenter]

/-- The actual empirical-minus-population right-hand side is negligible
relative to its `L²` residual when leverage divided by sample size tends to zero.
The sample law and pairwise independence are proved inputs at every index. -/
theorem rhsFluctuation_div_residual_tendstoInMeasure
    {l : Filter ι} (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (x : (i : ι) → Fin (n i) → Ω → X)
    (hlaw : ∀ i j, MeasurePreserving (x i j) P μ)
    (hindep : ∀ i, Pairwise (fun j k => IndepFun (x i j) (x i k) P))
    (k : X → H) (hk : MemLp k 2 μ) (f : ι → Lp ℝ 2 μ) (h : ι → H)
    (R : ι → H →L[ℝ] H) (L : ι → ℝ) (hLnonneg : ∀ i, 0 ≤ L i)
    (hL : ∀ i, ∀ᵐ y ∂μ, ‖R i (k y)‖ ^ 2 ≤ L i)
    (hrate : Tendsto (fun i => L i / (n i : ℝ)) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω => ‖f i - featureEmbedding μ k hk (h i)‖⁻¹ •
      R i (rhsFluctuation k hk (f i) (h i) (fun j => x i j ω))) l (fun _ => 0) := by
  apply tendstoInMeasure_zero_of_second_moment_bound _
    (fun i => L i / (n i : ℝ)) _ _ hrate
  · intro i
    exact (memLp_rhsFluctuation (hn i) (x i) (hlaw i) k hk (f i) (h i)
      (R i) (hL i)).const_smul _
  · exact Eventually.of_forall fun i => integral_scaled_rhsFluctuation_sq_le
      (hn i) (x i) (hlaw i) (hindep i) k hk (f i) (h i) (R i) (hLnonneg i) (hL i)

end KernelSeq
