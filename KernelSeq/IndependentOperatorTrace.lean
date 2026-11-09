import KernelSeq.FiniteOperatorTrace
import KernelSeq.MatrixBernsteinExp
import KernelSeq.GoldenThompson
import Mathlib.Probability.Independence.Integration

/-!
# Genuine independence and one-step operator trace moments

Independent integrable bounded-operator fields have an integrable actual
product and a factored Bochner integral, by Mathlib's proved bilinear
independence theorem. Continuous actual exponential transforms preserve
independence. Finite prefix sums use only AE measurability.

The generic one-step trace-MGF inequality displays the general trace-exponential
comparison it uses. The final actual version invokes the independently proved
Golden--Thompson theorem: all integrability, factorization and moment bounds
follow from raw independence, centering, boundedness and variance assumptions,
with no trace-MGF or Golden--Thompson certificate as an input.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace KernelSeq

noncomputable section

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {P : Measure Ω}

local instance independentOperatorTraceMeasurableSpace : MeasurableSpace (H →L[ℝ] H) :=
  borel (H →L[ℝ] H)
local instance independentOperatorTraceBorelSpace : BorelSpace (H →L[ℝ] H) := ⟨rfl⟩

omit [CompleteSpace H] in
/-- Independence and individual Bochner integrability imply integrability of
the actual noncommuting operator product. -/
theorem integrable_operator_mul_of_indep {U V : Ω → H →L[ℝ] H}
    (hUV : IndepFun U V P) (hU : Integrable U P) (hV : Integrable V P) :
    Integrable (fun ω => U ω * V ω) P :=
  hUV.integrable_bilin hU hV (ContinuousLinearMap.mul ℝ (H →L[ℝ] H))

/-- The actual Bochner expectation of an independent operator product factors
in the given order. No commutativity hypothesis is used. -/
theorem integral_operator_mul_of_indep {U V : Ω → H →L[ℝ] H}
    (hUV : IndepFun U V P) (hU : Integrable U P) (hV : Integrable V P) :
    (∫ ω, U ω * V ω ∂P : H →L[ℝ] H) = (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P) :=
  hUV.integral_bilin (𝕜 := ℝ) hU hV (ContinuousLinearMap.mul ℝ (H →L[ℝ] H))

/-- The actual exponential, composed with real scalar multiplication, is
continuous in the actual operator norm. -/
theorem operator_exp_smul_continuous (θ : ℝ) :
    Continuous (fun A : H →L[ℝ] H => NormedSpace.exp (θ • A)) := by
  have hcont : Continuous (NormedSpace.exp : (H →L[ℝ] H) → H →L[ℝ] H) :=
    continuous_iff_continuousAt.mpr fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).continuousAt
  exact hcont.comp (continuous_const_smul θ)

/-- Genuine independence of actual operator exponential transforms. -/
theorem indepFun_operator_exp_smul {U V : Ω → H →L[ℝ] H}
    (hUV : IndepFun U V P) (θ ψ : ℝ) :
    IndepFun (fun ω => NormedSpace.exp (θ • U ω)) (fun ω => NormedSpace.exp (ψ • V ω)) P :=
  hUV.comp (operator_exp_smul_continuous θ).measurable (operator_exp_smul_continuous ψ).measurable

omit [CompleteSpace H] in
/-- A finite partial sum of independent operator fields is independent of a
new field. AE strong measurability is sufficient. -/
theorem indepFun_operator_finsetSum_of_notMem [FiniteDimensional ℝ H] {J : Type*}
    (Y : J → Ω → H →L[ℝ] H) (hY : iIndepFun Y P)
    (hYm : ∀ i, AEStronglyMeasurable (Y i) P) {s : Finset J} {j : J} (hj : j ∉ s) :
    IndepFun (fun ω => ∑ i ∈ s, Y i ω) (Y j) P := by
  simpa only [Finset.sum_fn] using hY.indepFun_finsetSum_of_notMem₀
    (fun i => (hYm i).aemeasurable) hj

section FiniteTrace

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace H] in
/-- The independent actual trace product is integrable. -/
theorem integrable_trace_operator_mul_of_indep (b : HilbertBasis ι ℝ H)
    {U V : Ω → H →L[ℝ] H} (hUV : IndepFun U V P)
    (hU : Integrable U P) (hV : Integrable V P) :
    Integrable (fun ω => basisTrace b (U ω * V ω)) P :=
  integrable_finiteBasisTrace b _ (integrable_operator_mul_of_indep hUV hU hV)

/-- The actual independent trace product expectation is the trace of the
ordered product of actual expectations. -/
theorem integral_trace_operator_mul_of_indep (b : HilbertBasis ι ℝ H)
    {U V : Ω → H →L[ℝ] H} (hUV : IndepFun U V P)
    (hU : Integrable U P) (hV : Integrable V P) :
    (∫ ω, basisTrace b (U ω * V ω) ∂P) =
      basisTrace b ((∫ ω, U ω ∂P) * (∫ ω, V ω ∂P)) := by
  rw [← finiteBasisTrace_integral b _ (integrable_operator_mul_of_indep hUV hU hV),
    integral_operator_mul_of_indep hUV hU hV]

variable [IsProbabilityMeasure P] [FiniteDimensional ℝ H]

/-- A genuine one-step matrix trace-MGF bound. The input `hGT` is the general
Golden--Thompson trace inequality; the raw randomness assumptions determine
all moment and product bounds appearing in the conclusion. -/
theorem integral_trace_exp_add_le_one_step
    (b : HilbertBasis ι ℝ H)
    (hGT : ∀ X Y : H →L[ℝ] H, IsSelfAdjoint X → IsSelfAdjoint Y →
      basisTrace b (NormedSpace.exp (X + Y)) ≤ basisTrace b (NormedSpace.exp X * NormedSpace.exp Y))
    (S Y : Ω → H →L[ℝ] H) (hSY : IndepFun S Y P)
    (hSm : AEStronglyMeasurable S P) (hYm : AEStronglyMeasurable Y P)
    (hS : ∀ᵐ ω ∂P, IsSelfAdjoint (S ω)) (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω))
    {θ R C : ℝ} (hθ : 0 ≤ θ)
    (hR : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R) (hC : ∀ᵐ ω ∂P, ‖S ω‖ ≤ C)
    (hmean : (∫ ω, Y ω ∂P) = 0) (W : H →L[ℝ] H)
    (hW : (∫ ω, Y ω * Y ω ∂P : H →L[ℝ] H) ≤ W) :
    (∫ ω, basisTrace b (NormedSpace.exp (θ • (S ω + Y ω))) ∂P) ≤
      (∫ ω, basisTrace b (NormedSpace.exp (θ • S ω)) ∂P) +
        matrixExpRemainderCoefficient θ R *
          basisTrace b ((∫ ω, NormedSpace.exp (θ • S ω) ∂P) * W) := by
  have hES := integrable_operator_exp_of_ae_norm_bound S hSm hS hθ hC
  have hEY := integrable_operator_exp_of_ae_norm_bound Y hYm hY hθ hR
  have hSum : ∀ᵐ ω ∂P, IsSelfAdjoint (S ω + Y ω) := by
    filter_upwards [hS, hY] with ω hSω hYω
    exact hSω.add hYω
  have hSumBound : ∀ᵐ ω ∂P, ‖S ω + Y ω‖ ≤ C + R := by
    filter_upwards [hC, hR] with ω hCω hRω
    exact (norm_add_le _ _).trans (add_le_add hCω hRω)
  have hESum := integrable_operator_exp_of_ae_norm_bound (fun ω => S ω + Y ω)
    (hSm.add hYm) hSum hθ hSumBound
  have hExpInd := indepFun_operator_exp_smul hSY θ θ
  have hProd := integrable_operator_mul_of_indep hExpInd hES hEY
  have hGTae : ∀ᵐ ω ∂P, basisTrace b (NormedSpace.exp (θ • (S ω + Y ω))) ≤
      basisTrace b (NormedSpace.exp (θ • S ω) * NormedSpace.exp (θ • Y ω)) := by
    filter_upwards [hS, hY] with ω hSω hYω
    simpa only [smul_add] using hGT (θ • S ω) (θ • Y ω)
      ((IsSelfAdjoint.all θ).smul hSω) ((IsSelfAdjoint.all θ).smul hYω)
  have hESpos : (∫ ω, NormedSpace.exp (θ • S ω) ∂P : H →L[ℝ] H).IsPositive := by
    apply integral_operator_isPositive _ hES
    filter_upwards [hS] with ω hSω
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (compact_operator_exp_nonneg (S ω) (isCompactOperator_of_locallyCompactSpace_dom (S ω)) hSω.isSymmetric θ)
  have hYmajor := integral_operator_exp_le_one_add_majorant Y hYm hY hθ hR hmean W hW
  calc
    _ ≤ ∫ ω, basisTrace b (NormedSpace.exp (θ • S ω) * NormedSpace.exp (θ • Y ω)) ∂P :=
      integral_mono_ae (integrable_finiteBasisTrace b _ hESum) (integrable_finiteBasisTrace b _ hProd) hGTae
    _ = basisTrace b ((∫ ω, NormedSpace.exp (θ • S ω) ∂P) * (∫ ω, NormedSpace.exp (θ • Y ω) ∂P)) :=
      integral_trace_operator_mul_of_indep b hExpInd hES hEY
    _ ≤ basisTrace b ((∫ ω, NormedSpace.exp (θ • S ω) ∂P) *
        (1 + matrixExpRemainderCoefficient θ R • W)) :=
      finiteBasisTrace_mul_mono b _ _ _ hESpos hYmajor
    _ = _ := by
      rw [mul_add, mul_one, mul_smul_comm]
      simp only [← finiteBasisTraceCLM_apply, map_add, map_smul, smul_eq_mul]
      rw [finiteBasisTraceCLM_apply, finiteBasisTraceCLM_apply,
        finiteBasisTrace_integral b _ hES]
      simp only [finiteBasisTraceCLM_apply]

/-- The actual one-step trace-MGF inequality, now using the locally proved
Golden--Thompson theorem. Only raw probabilistic and variance-majorant premises
remain; no trace comparison or moment conclusion is an assumption. -/
theorem integral_trace_exp_add_le_one_step_actual
    (b : HilbertBasis ι ℝ H)
    (S Y : Ω → H →L[ℝ] H) (hSY : IndepFun S Y P)
    (hSm : AEStronglyMeasurable S P) (hYm : AEStronglyMeasurable Y P)
    (hS : ∀ᵐ ω ∂P, IsSelfAdjoint (S ω)) (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω))
    {θ R C : ℝ} (hθ : 0 ≤ θ)
    (hR : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R) (hC : ∀ᵐ ω ∂P, ‖S ω‖ ≤ C)
    (hmean : (∫ ω, Y ω ∂P) = 0) (W : H →L[ℝ] H)
    (hW : (∫ ω, Y ω * Y ω ∂P : H →L[ℝ] H) ≤ W) :
    (∫ ω, basisTrace b (NormedSpace.exp (θ • (S ω + Y ω))) ∂P) ≤
      (∫ ω, basisTrace b (NormedSpace.exp (θ • S ω)) ∂P) +
        matrixExpRemainderCoefficient θ R *
          basisTrace b ((∫ ω, NormedSpace.exp (θ • S ω) ∂P) * W) :=
  integral_trace_exp_add_le_one_step b (finiteBasisTrace_exp_add_le b) S Y hSY hSm hYm hS hY
    hθ hR hC hmean W hW

end FiniteTrace
end
end KernelSeq
