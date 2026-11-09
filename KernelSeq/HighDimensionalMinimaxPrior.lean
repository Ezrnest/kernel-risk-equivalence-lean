import KernelSeq.FiniteGaussianMinimaxLower
import KernelSeq.GaussianPriorOutsideMoment
import KernelSeq.PinskerMinimaxAssembly

/-!
# Finite Gaussian priors with a fixed shaved source budget

The weighted Gaussian mean is the prescribed source budget. Coordinate
source weights give an actual concentration bound. The finite Gaussian
regression comparison and source-ball clipping then give a real lower
bound on the full prediction-range minimax risk.
-/

namespace KernelSeq
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal
noncomputable section

def finiteGaussianShavingConstant (κ s R : ℝ) : ℝ :=
  2*((1+κ^2)^(s/2)*R)^2 + 2*(1+κ^2)^s*Real.sqrt (2*Real.exp (2*R^2))

variable {X H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} [IsProbabilityMeasure μ] [Fintype J] [DecidableEq J]

theorem finiteGaussian_minimax_sourceBall_lower_exponential
    (k : X → H) (hk : MemLp k 2 μ)
    (jmap : J → PredictionSingularIndex (featureEmbedding μ k hk)) (hj : Function.Injective jmap)
    {κ s R σ ε B : ℝ} (hκ : 0 ≤ κ) (hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ κ)
    (hs : 0 ≤ s) (hR : 0 < R) (hσ : 0 < σ) (n : ℕ)
    (v : J → ℝ) (hv : ∀ j, 0 < v j)
    (hε : 0 < ε) (hε1 : ε < 1) (hB : 0 < B) (hBsmall : B ≤ 1/4)
    (hweight : ∀ j, (jmap j).1.1^(-s)*v j ≤ B)
    (hmean : (∑ j, (jmap j).1.1^(-s)*v j) = (1-ε)*R^2) :
    (∑ j, ((v j)⁻¹ + (n : ℝ)*(σ^2)⁻¹)⁻¹) ≤
      (gaussianRangeMinimaxRisk k hk σ n (featureSourceBall k hk s hs R)).toReal +
        finiteGaussianShavingConstant κ s R*Real.exp (-priorShavingExponent ε R/(2*B)) := by
  classical
  let w := fun j => (jmap j).1.1^(-s)
  let P := multivariateGaussian (0 : EuclideanSpace ℝ J) (Matrix.diagonal v)
  let Q := gaussianPriorEnergy w
  let C := {θ | Q θ ≤ R^2}
  let E := {θ | R^2 < Q θ}
  let T := (1+κ^2)^(s/2)*R
  let K := (1+κ^2)^s
  let x := Real.exp (-priorShavingExponent ε R/(2*B))
  have hv0 : ∀ j, 0 ≤ v j := fun j => (hv j).le
  have hw : ∀ j, 0 ≤ w j := fun j => Real.rpow_nonneg (jmap j).2.le _
  have hQI : Integrable Q P := gaussianPriorEnergy_integrable v w
  have hpos : 0 < P C := by
    by_contra! hn
    have hz : P C = 0 := le_antisymm hn bot_le
    have hae : ∀ᵐ θ ∂P, R^2 ≤ Q θ := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with θ hθ
      exact (not_le.mp hθ).le
    have hi := integral_mono_ae (integrable_const (R^2)) hQI hae
    rw [integral_const, probReal_univ, one_smul] at hi
    have he : (∫ θ, Q θ ∂P) = (1-ε)*R^2 :=
      (integral_gaussianPriorEnergy v w hv0).trans hmean
    rw [he] at hi
    nlinarith [mul_pos hε (sq_pos_of_pos hR)]
  have hSlo : (1-ε)*R^2/2 ≤ ∑ j, w j*v j := by
    change (1-ε)*R^2/2 ≤ ∑ j, (jmap j).1.1^(-s)*v j
    rw [hmean]
    nlinarith [mul_nonneg (sub_nonneg.mpr hε1.le) (sq_nonneg R)]
  have hShi : (∑ j, w j*v j) ≤ (1-ε/2)*R^2 := by
    change (∑ j, (jmap j).1.1^(-s)*v j) ≤ _
    rw [hmean]
    nlinarith [mul_nonneg hε.le (sq_nonneg R)]
  have ht := gaussianPriorEnergy_outside_tail v w hv0 hw hε hε1 hR hB hweight hSlo hShi
  have hm := gaussianPriorEnergy_outside_moment_le v w hv0 hw hε hε1 hR hB hBsmall hweight hSlo hShi
  have hprob : P.real E ≤ x := by
    have ht' := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at ht'
    refine ht'.trans (Real.exp_le_exp.mpr ?_)
    rw [show -priorShavingExponent ε R/(2*B) = (-priorShavingExponent ε R/B)/2 by ring]
    have hn := div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (priorShavingExponent_pos hε hε1 hR).le) hB.le
    linarith
  have hmoment : (∫ θ in E, Q θ ∂P) ≤ Real.sqrt (2*Real.exp (2*R^2))*x := hm
  have hE : Cᶜ = E := by
    ext θ
    exact not_le (a := Q θ) (b := R^2)
  have hrem : (∫⁻ θ in Cᶜ, ENNReal.ofReal (2*T^2+2*K*Q θ) ∂P) ≤
      ENNReal.ofReal (finiteGaussianShavingConstant κ s R*x) := by
    rw [hE]
    have hi : Integrable (fun θ => 2*T^2+2*K*Q θ) P :=
      (integrable_const _).add (hQI.const_mul _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn]
    · apply ENNReal.ofReal_le_ofReal
      rw [integral_add (integrable_const _) (hQI.const_mul _).integrableOn,
        integral_const, integral_const_mul]
      simp only [measureReal_restrict_apply_univ, smul_eq_mul]
      have hp := mul_le_mul_of_nonneg_left hprob (by positivity : 0 ≤ 2*T^2)
      have hq := mul_le_mul_of_nonneg_left hmoment (by dsimp [K]; positivity : 0 ≤ 2*K)
      change P.real E*(2*T^2)+2*K*(∫ θ in E, Q θ ∂P) ≤
        (2*T^2+2*K*Real.sqrt (2*Real.exp (2*R^2)))*x
      nlinarith only [hp, hq]
    · exact Eventually.of_forall fun θ => by
        have hq := gaussianPriorEnergy_nonneg w hw θ
        change 0 ≤ 2*T^2+2*K*Q θ
        dsimp [K, Q]
        positivity
  have hb := finiteGaussian_minimax_sourceBall_lower k hk jmap hj hκ hbound hs hR hσ n v hv hpos
  have hreal := real_le_toReal_add_of_ofReal_le
    (show 0 ≤ finiteGaussianShavingConstant κ s R*x by unfold finiteGaussianShavingConstant; dsimp [x]; positivity)
    (gaussianRangeMinimaxRisk_sourceBall_lt_top k hk hκ hbound hs hR.le σ n).ne
    (hb.trans (add_le_add le_rfl hrem))
  exact hreal

end
end KernelSeq
