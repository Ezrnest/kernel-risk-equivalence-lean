import KernelSeq.TriangularRiskModel

/-!
# Actual model facts uniform across row-dependent spaces

Every statement is instantiated separately in the row's own RKHS and design
measure. These are derived model identities, not additional array hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace KernelSeq.TriangularRiskModel
noncomputable section

universe uH uX uΩ
variable {κ ρ A : ℝ} (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A)

theorem feature_stronglyMeasurable : StronglyMeasurable m.feature :=
  rkhsFeature_stronglyMeasurable m.kernel_measurable

theorem feature_bound (y : m.X) : ‖m.feature y‖ ≤ κ :=
  rkhsFeature_norm_le κ m.kappa_nonneg m.diagonal_bound y

theorem feature_sq_bound : ∀ᵐ y ∂m.μ, ‖m.feature y‖ ^ 2 ≤ κ ^ 2 :=
  Eventually.of_forall fun y => pow_le_pow_left₀ (norm_nonneg _) (m.feature_bound y) 2

theorem leverage_ae : ∀ᵐ y ∂m.μ, normalizedLeverage m.feature m.feature_memLp m.lam y ≤ m.L :=
  normalizedLeverage_ae_le_essentialSup m.feature m.feature_memLp m.lambda_pos m.feature_sq_bound

theorem L_nonneg : 0 ≤ m.L :=
  featureLeverageEssentialSup_nonneg m.feature m.feature_memLp m.lambda_pos m.feature_sq_bound

theorem N_nonneg : 0 ≤ m.N :=
  featureEffectiveDimension_nonneg m.feature m.feature_memLp m.lam m.lambda_pos

theorem Q_nonneg : 0 ≤ m.Q := featureFilterDimension_nonneg _ _ _
theorem r_nonneg : 0 ≤ m.r := featureCovarianceRetention_nonneg _ _ _
theorem r_le_one : m.r ≤ 1 := featureCovarianceRetention_le_one _ _ _ m.lambda_pos

theorem r_le_N : m.r ≤ m.N :=
  featureCovarianceRetention_le_effectiveDimension m.feature m.feature_memLp m.lam m.lambda_pos

theorem N_le_L : m.N ≤ m.L :=
  featureEffectiveDimension_le_essentialSup m.feature m.feature_memLp m.lambda_pos m.feature_sq_bound

theorem Q_le_retention : m.Q ≤ A ^ 2 * m.r * m.N :=
  featureFilterDimension_le_retention m.feature m.feature_memLp m.φ m.lambda_pos
    m.population_bound m.spectral_filter m.filter_contract

theorem Q_le_L : m.Q ≤ A ^ 2 * m.L :=
  (featureFilterDimension_le_effectiveDimension m.feature m.feature_memLp m.φ m.lambda_pos
    m.population_bound m.spectral_filter m.filter_contract).trans
      (mul_le_mul_of_nonneg_left m.N_le_L (sq_nonneg A))

theorem r_pos (hQ : 0 < m.Q) : 0 < m.r :=
  featureCovarianceRetention_pos_of_filterDimension_pos m.feature m.feature_memLp m.φ
    m.lambda_pos m.population_bound m.spectral_filter m.filter_contract hQ

theorem L_pos (hQ : 0 < m.Q) : 0 < m.L := (m.r_pos hQ).trans_le (m.r_le_N.trans m.N_le_L)
theorem N_pos (hQ : 0 < m.Q) : 0 < m.N := (m.r_pos hQ).trans_le m.r_le_N

theorem v_nonneg : 0 ≤ m.v := div_nonneg
  (mul_nonneg m.L_nonneg (zero_le_one.trans (one_le_dimensionLog m.N_nonneg))) (Nat.cast_nonneg _)

theorem v_pos (hQ : 0 < m.Q) : 0 < m.v := div_pos
  (mul_pos (m.L_pos hQ) (zero_lt_one.trans_le (one_le_dimensionLog m.N_nonneg)))
  (Nat.cast_pos.mpr m.sample_pos)

theorem S_nonneg : 0 ≤ m.S := featureSequenceSourceEnergy_nonneg _ _ m.lambda_pos _
theorem gamma_nonneg : 0 ≤ m.gamma := originalBiasGamma_nonneg _ _ _
theorem compatibility_nonneg (hQ : 0 < m.Q) : 0 ≤ m.compatibility :=
  mul_nonneg (div_nonneg m.N_nonneg hQ.le) (Real.sqrt_nonneg _)

theorem sourceBalance_nonneg (hQ : 0 < m.Q) : 0 ≤ m.sourceBalance :=
  div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) m.S_nonneg) (sq_nonneg _)) hQ.le

theorem expectationH_pos (hQ : 0 < m.Q) : 0 < m.expectationH :=
  div_pos (Nat.cast_pos.mpr m.sample_pos) (mul_pos m.lambda_pos hQ)

theorem alpha_pos : 0 < m.alpha := residualComparisonOrder_pos m.filter_contract.rho_pos
theorem alpha_le_one : m.alpha ≤ 1 := residualComparisonOrder_le_one _
theorem alpha_half_le : m.alpha / 2 ≤ ρ := residualComparisonOrder_half_le _
include m in
theorem A_nonneg : 0 ≤ A := (m.filter_contract).constant_nonneg m.lambda_pos (sq_nonneg κ)

theorem design_independent : iIndepFun m.design m.P :=
  m.independent_pairs.comp (fun _ => Prod.fst) (fun _ => measurable_fst)

theorem goodEvent_measurable : MeasurableSet m.goodEvent :=
  measurableSet_le (stronglyMeasurable_actualCovarianceDeviation m.feature m.feature_memLp m.lam m.design
    (fun j => m.feature_stronglyMeasurable.comp_measurable (m.design_law j).measurable)).measurable
      measurable_const

theorem bias_integrable : Integrable m.bias m.P :=
  integrable_actualEmpiricalBiasEnergy m.sample_pos m.design m.design_law m.feature m.feature_memLp
    m.feature_stronglyMeasurable κ m.kappa_nonneg m.feature_bound m.empirical_bound m.φ
    m.lambda_pos m.spectral_filter m.filter_contract m.f

theorem lambda_sq_Q_bound : m.lam ^ 2 * m.Q ≤ A ^ 2 * κ ^ 4 :=
  lambda_sq_mul_featureFilterDimension_le_sq_bound m.feature m.feature_memLp m.φ κ
    m.feature_sq_bound m.lambda_pos m.population_bound m.spectral_filter m.filter_contract

end
end KernelSeq.TriangularRiskModel
