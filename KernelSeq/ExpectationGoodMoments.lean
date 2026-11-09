import KernelSeq.BiasTransfer
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Genuine L²-to-L¹ risk transfer on good events

Bochner integral bounds for risk on the good-design event. A restricted
probability measure has mass at most one, so square moments control all
linear terms. Young's inequality controls the mixed coefficient term.
The population bias may be zero and the positive variance may tend to zero.
The actual sampled-model operator bounds are connected in later modules.
-/

open MeasureTheory Filter Topology

namespace KernelSeq
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Cauchy--Schwarz on a measure of mass at most one, with true L² input. -/
theorem integral_abs_le_sqrt_second_moment [IsFiniteMeasure P]
    (hmass : P.real Set.univ ≤ 1) {u : Ω → ℝ} (hu : MemLp u 2 P) :
    (∫ ω, |u ω| ∂P) ≤ Real.sqrt (∫ ω, u ω ^ 2 ∂P) := by
  have h := integral_mul_norm_le_Lp_mul_Lq
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    (by simpa using hu) (by simpa using (memLp_const (μ := P) (p := 2) (1 : ℝ)))
  simp only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs,
    one_pow, integral_const, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] at h
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.sqrt_le_one.mpr hmass) (Real.sqrt_nonneg (∫ ω, u ω ^ 2 ∂P)))

/-- Actual Cauchy--Schwarz for the mixed covariance/effective-dimension
term. No independence between the two factors is required. -/
theorem integral_abs_mul_le_sqrt_second_moments {u v : Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P) :
    (∫ ω, |u ω| * |v ω| ∂P) ≤
      Real.sqrt (∫ ω, u ω ^ 2 ∂P) * Real.sqrt (∫ ω, v ω ^ 2 ∂P) := by
  have h := integral_mul_norm_le_Lp_mul_Lq
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    (by simpa using hu) (by simpa using hv)
  simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using h

/-- A polynomial majorant eliminates the coefficient product pointwise. -/
theorem relativeRiskBound_le_second_moment_envelope {u c V : ℝ}
    (hV : 0 < V) :
    relativeRiskBound u c V ≤
      2 * |u| + 2 * u ^ 2 + |c / Real.sqrt V| + 2 * (c / Real.sqrt V) ^ 2 := by
  have hs : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  have hcs : c ^ 2 / V = (c / Real.sqrt V) ^ 2 := by rw [div_pow, hs]
  have huc : (1 + u) * c / Real.sqrt V = c / Real.sqrt V + u * (c / Real.sqrt V) := by ring
  unfold relativeRiskBound
  rw [hcs, huc]
  nlinarith [le_abs_self u, le_abs_self (c / Real.sqrt V),
    sq_nonneg (u - c / Real.sqrt V)]

/-- All terms of the actual risk envelope are integrable from the two L²
coefficients; the product term uses true Hölder with exponents two. -/
theorem integrable_relativeRiskBound [IsFiniteMeasure P]
    {u c : Ω → ℝ} {V : ℝ} (hV : 0 < V)
    (hu : MemLp u 2 P) (hc : MemLp c 2 P) :
    Integrable (fun ω => relativeRiskBound (u ω) (c ω) V) P := by
  have hz : MemLp (fun ω => c ω / Real.sqrt V) 2 P := by
    simpa only [div_eq_mul_inv] using hc.mul_const (Real.sqrt V)⁻¹
  have huz : Integrable (fun ω => u ω * (c ω / Real.sqrt V)) P :=
    memLp_one_iff_integrable.mp (hz.mul hu)
  have hi := ((((hu.integrable (by norm_num)).const_mul 2).add hu.integrable_sq).add
    ((hz.integrable (by norm_num)).add huz)).add hz.integrable_sq
  apply hi.congr
  filter_upwards [] with ω
  dsimp only [Pi.add_apply]
  unfold relativeRiskBound
  rw [div_pow, Real.sq_sqrt hV.le]
  ring

/-- An explicit finite-moment bound for the actual scalar risk envelope.
Neither a strictly positive bias nor a lower bound on the variance is used. -/
theorem integral_relativeRiskBound_le [IsFiniteMeasure P]
    (hmass : P.real Set.univ ≤ 1) {u c : Ω → ℝ} {V : ℝ} (hV : 0 < V)
    (hu : MemLp u 2 P) (hc : MemLp c 2 P) :
    (∫ ω, relativeRiskBound (u ω) (c ω) V ∂P) ≤
      2 * Real.sqrt (∫ ω, u ω ^ 2 ∂P) + 2 * (∫ ω, u ω ^ 2 ∂P) +
      Real.sqrt (∫ ω, (c ω / Real.sqrt V) ^ 2 ∂P) +
      2 * (∫ ω, (c ω / Real.sqrt V) ^ 2 ∂P) := by
  have hz : MemLp (fun ω => c ω / Real.sqrt V) 2 P := by
    simpa only [div_eq_mul_inv] using hc.mul_const (Real.sqrt V)⁻¹
  have he : Integrable (fun ω => 2 * |u ω| + 2 * u ω ^ 2 +
      |c ω / Real.sqrt V| + 2 * (c ω / Real.sqrt V) ^ 2) P :=
    ((((hu.integrable (by norm_num)).abs.const_mul 2).add
      (hu.integrable_sq.const_mul 2)).add
      (hz.integrable (by norm_num)).abs).add (hz.integrable_sq.const_mul 2)
  have hr := integrable_relativeRiskBound hV hu hc
  have hm := integral_mono hr he (fun ω => relativeRiskBound_le_second_moment_envelope hV)
  have hu1 := integral_abs_le_sqrt_second_moment hmass hu
  have hz1 := integral_abs_le_sqrt_second_moment hmass hz
  have heq : (∫ ω, 2 * |u ω| + 2 * u ω ^ 2 +
      |c ω / Real.sqrt V| + 2 * (c ω / Real.sqrt V) ^ 2 ∂P) =
      2 * (∫ ω, |u ω| ∂P) + 2 * (∫ ω, u ω ^ 2 ∂P) +
      (∫ ω, |c ω / Real.sqrt V| ∂P) + 2 * (∫ ω, (c ω / Real.sqrt V) ^ 2 ∂P) := by
    have h₁ := (hu.integrable (by norm_num)).abs.const_mul 2
    have h₂ := hu.integrable_sq.const_mul 2
    have h₃ := (hz.integrable (by norm_num)).abs
    have h₄ := hz.integrable_sq.const_mul 2
    have he₁ := integral_add ((h₁.add h₂).add h₃) h₄
    have he₂ := integral_add (h₁.add h₂) h₃
    have he₃ := integral_add h₁ h₂
    dsimp only [Pi.add_apply] at he₁ he₂ he₃
    rw [he₁, he₂, he₃]
    simp only [integral_const_mul]
  rw [heq] at hm
  linarith

/-- Genuine L¹ bias transfer from a vector perturbation and its two L²
coefficient moments. The integrability of the actual energy is derived. -/
theorem integral_bias_relative_risk_le [IsFiniteMeasure P]
    (hmass : P.real Set.univ ≤ 1) {E : Type*} [NormedAddCommGroup E]
    (r : E) (e : Ω → E) (he : AEStronglyMeasurable e P)
    {u c : Ω → ℝ} {V : ℝ} (hV : 0 < V)
    (hu : MemLp u 2 P) (hc : MemLp c 2 P)
    (hun : ∀ᵐ ω ∂P, 0 ≤ u ω) (hcn : ∀ᵐ ω ∂P, 0 ≤ c ω)
    (herr : ∀ᵐ ω ∂P, ‖e ω‖ ≤ u ω * ‖r‖ + c ω) :
    (∫ ω, |‖r - e ω‖ ^ 2 - ‖r‖ ^ 2| / (‖r‖ ^ 2 + V) ∂P) ≤
      2 * Real.sqrt (∫ ω, u ω ^ 2 ∂P) + 2 * (∫ ω, u ω ^ 2 ∂P) +
      Real.sqrt (∫ ω, (c ω / Real.sqrt V) ^ 2 ∂P) +
      2 * (∫ ω, (c ω / Real.sqrt V) ^ 2 ∂P) := by
  have hb : ∀ᵐ ω ∂P,
      |‖r - e ω‖ ^ 2 - ‖r‖ ^ 2| / (‖r‖ ^ 2 + V) ≤ relativeRiskBound (u ω) (c ω) V := by
    filter_upwards [hun, hcn, herr] with ω huω hcω heω
    exact bias_relative_risk_bound r (e ω) _ _ _ huω hcω hV heω
  have hi := integrable_relativeRiskBound hV hu hc
  have hm : AEStronglyMeasurable
      (fun ω => |‖r - e ω‖ ^ 2 - ‖r‖ ^ 2| / (‖r‖ ^ 2 + V)) P := by
    have hme := (((aestronglyMeasurable_const :
      AEStronglyMeasurable (fun _ : Ω => r) P).sub he).norm.pow 2).sub
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => ‖r‖ ^ 2) P)
    apply (hme.norm.const_smul (‖r‖ ^ 2 + V)⁻¹).congr
    filter_upwards [] with ω
    simp only [Real.norm_eq_abs, Pi.smul_apply, Pi.sub_apply, Pi.pow_apply,
      smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hin : Integrable (fun ω => |‖r - e ω‖ ^ 2 - ‖r‖ ^ 2| / (‖r‖ ^ 2 + V)) P := by
    apply hi.mono' hm
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ |‖r - e ω‖ ^ 2 - ‖r‖ ^ 2| / (‖r‖ ^ 2 + V))] using hω
  exact (integral_mono_ae hin hi hb).trans (integral_relativeRiskBound_le hmass hV hu hc)

/-- The preceding theorem on any good event of a probability space.
L² hypotheses concern the restricted measure only, so no control on bad
designs is required for this part of the argument. -/
theorem setIntegral_bias_relative_risk_le [IsProbabilityMeasure P]
    (G : Set Ω) {E : Type*} [NormedAddCommGroup E]
    (r : E) (e : Ω → E) (he : AEStronglyMeasurable e (P.restrict G))
    {u c : Ω → ℝ} {V : ℝ} (hV : 0 < V)
    (hu : MemLp u 2 (P.restrict G)) (hc : MemLp c 2 (P.restrict G))
    (hun : ∀ᵐ ω ∂P.restrict G, 0 ≤ u ω) (hcn : ∀ᵐ ω ∂P.restrict G, 0 ≤ c ω)
    (herr : ∀ᵐ ω ∂P.restrict G, ‖e ω‖ ≤ u ω * ‖r‖ + c ω) :
    (∫ ω in G, |‖r - e ω‖ ^ 2 - ‖r‖ ^ 2| / (‖r‖ ^ 2 + V) ∂P) ≤
      2 * Real.sqrt (∫ ω in G, u ω ^ 2 ∂P) + 2 * (∫ ω in G, u ω ^ 2 ∂P) +
      Real.sqrt (∫ ω in G, (c ω / Real.sqrt V) ^ 2 ∂P) +
      2 * (∫ ω in G, (c ω / Real.sqrt V) ^ 2 ∂P) := by
  apply integral_bias_relative_risk_le (P := P.restrict G) _ r e he hV hu hc hun hcn herr
  simpa only [Measure.real, Measure.restrict_apply_univ] using
    (measureReal_le_one (μ := P) (s := G))

/-- Vanishing second moments imply the actual normalized L¹ bias error
vanishes along any filter; no positivity or boundedness of `r i` is imposed. -/
theorem tendsto_setIntegral_bias_relative_risk_of_second_moments
    {I : Type*} {l : Filter I} [IsProbabilityMeasure P]
    {E : Type*} [NormedAddCommGroup E] (G : I → Set Ω) (r : I → E) (e : I → Ω → E)
    (he : ∀ i, AEStronglyMeasurable (e i) (P.restrict (G i)))
    (u c : I → Ω → ℝ) (V : I → ℝ) (hV : ∀ i, 0 < V i)
    (hu : ∀ i, MemLp (u i) 2 (P.restrict (G i)))
    (hc : ∀ i, MemLp (c i) 2 (P.restrict (G i)))
    (hun : ∀ i, ∀ᵐ ω ∂P.restrict (G i), 0 ≤ u i ω)
    (hcn : ∀ i, ∀ᵐ ω ∂P.restrict (G i), 0 ≤ c i ω)
    (herr : ∀ i, ∀ᵐ ω ∂P.restrict (G i), ‖e i ω‖ ≤ u i ω * ‖r i‖ + c i ω)
    (hU : Tendsto (fun i => ∫ ω in G i, u i ω ^ 2 ∂P) l (𝓝 0))
    (hC : Tendsto (fun i => ∫ ω in G i, (c i ω / Real.sqrt (V i)) ^ 2 ∂P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω in G i,
      |‖r i - e i ω‖ ^ 2 - ‖r i‖ ^ 2| / (‖r i‖ ^ 2 + V i) ∂P) l (𝓝 0) := by
  have hlim := (((hU.sqrt.const_mul 2).add (hU.const_mul 2)).add hC.sqrt).add (hC.const_mul 2)
  simp only [Real.sqrt_zero, mul_zero, add_zero] at hlim
  apply squeeze_zero (fun i => integral_nonneg fun ω =>
    div_nonneg (abs_nonneg _) (add_nonneg (sq_nonneg _) (hV i).le)) _ hlim
  intro i
  exact setIntegral_bias_relative_risk_le (G i) (r i) (e i) (he i) (hV i)
    (hu i) (hc i) (hun i) (hcn i) (herr i)

end
end KernelSeq
