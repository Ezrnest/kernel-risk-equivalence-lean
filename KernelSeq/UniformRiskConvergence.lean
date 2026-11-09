import KernelSeq.UniformFilters
import KernelSeq.ExpectationRiskAssembly

/-!
# Uniform risk convergence with changing sample spaces

Uniform convergence in probability is the supremum of the separate row-law
tail probabilities. It is not the probability of a simultaneous supremum
event, and no common sample space or common probability law is required.
The generic assembly lemmas consume genuine common scalar bounds; the
actual triangular-model theorems supply those finite bounds separately.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace KernelSeq
noncomputable section

universe uI uΘ uΩ
variable {I : Type uI} {Θ : Type uΘ} {Ω : I → Θ → Type uΩ}
  [∀ i θ, MeasurableSpace (Ω i θ)] {l : Filter I}

/-- The correct uniform tail, permitting a different underlying sample
space and law at each row and parameter. No supremum of random variables
on an artificial common probability space occurs. -/
def uniformRiskTail (P : ∀ i θ, Measure (Ω i θ))
    (e : ∀ i θ, Ω i θ → ℝ) (ε : ℝ) (i : I) : ℝ≥0∞ :=
  ⨆ θ, P i θ {ω | ε < |e i θ ω|}

def UniformRiskInProbability (P : ∀ i θ, Measure (Ω i θ))
    (e : ∀ i θ, Ω i θ → ℝ) (l : Filter I) : Prop :=
  ∀ ε > 0, Tendsto (uniformRiskTail P e ε) l (𝓝 0)

/-- Exact product-filter interpretation of uniform convergence in
probability. The tail probabilities remain separate for each parameter. -/
theorem uniformRiskInProbability_iff_product (P : ∀ i θ, Measure (Ω i θ))
    (e : ∀ i θ, Ω i θ → ℝ) :
    UniformRiskInProbability P e l ↔ ∀ ε > 0,
      Tendsto (fun p : I × Θ => P p.1 p.2 {ω | ε < |e p.1 p.2 ω|})
        (uniformFamilyFilter l Θ) (𝓝 0) := by
  constructor
  · intro h ε hε
    exact (uniform_ennreal_tendsto_zero_iff_iSup _).mpr (h ε hε)
  · intro h ε hε
    exact (uniform_ennreal_tendsto_zero_iff_iSup _).mp (h ε hε)

/-- The epsilon-delta formulation has one common row threshold for all
parameters, while allowing all probability spaces to change. -/
theorem uniformRiskInProbability_iff_eventual (P : ∀ i θ, Measure (Ω i θ))
    (e : ∀ i θ, Ω i θ → ℝ) :
    UniformRiskInProbability P e l ↔ ∀ ε > 0, ∀ δ : ℝ≥0∞, 0 < δ →
      ∀ᶠ i in l, ∀ θ, P i θ {ω | ε < |e i θ ω|} ≤ δ := by
  constructor
  · intro h ε hε δ hδ
    exact (ENNReal.tendsto_nhds_zero.mp (h ε hε) δ hδ).mono fun i hi θ =>
      (le_iSup _ θ).trans hi
  · intro h ε hε
    apply ENNReal.tendsto_nhds_zero.mpr
    intro δ hδ
    exact (h ε hε δ hδ).mono fun _ hi => iSup_le hi

/-- Actual common nonasymptotic tail bounds tending to zero imply the
uniform probability conclusion, without assuming that conclusion. -/
theorem uniformRiskInProbability_of_tail_bound (P : ∀ i θ, Measure (Ω i θ))
    (e : ∀ i θ, Ω i θ → ℝ) (b : ℝ → I → ℝ≥0∞)
    (hb : ∀ ε > 0, Tendsto (b ε) l (𝓝 0))
    (hbound : ∀ ε > 0, ∀ᶠ i in l, ∀ θ, P i θ {ω | ε < |e i θ ω|} ≤ b ε i) :
    UniformRiskInProbability P e l := by
  intro ε hε
  exact iSup_ennreal_tendsto_zero_of_uniform_bound _ _ (hbound ε hε) (hb ε hε)

/-- Every diagonal inherits the probability conclusion under its own
changing row law. There is no coupling or common-space hypothesis. -/
theorem UniformRiskInProbability.diagonal {P : ∀ i θ, Measure (Ω i θ)}
    {e : ∀ i θ, Ω i θ → ℝ} (h : UniformRiskInProbability P e l) (θ : I → Θ) :
    ∀ ε > 0, Tendsto (fun i => P i (θ i) {ω | ε < |e i (θ i) ω|}) l (𝓝 0) := by
  intro ε hε
  exact uniformFamilyFilter_tendsto_diagonal
    (f := fun i θ => P i θ {ω | ε < |e i θ ω|})
    ((uniformRiskInProbability_iff_product P e).mp h ε hε) θ

/-- Exact diagonal characterization, not merely a pointwise-in-parameter
statement. The selection is allowed to change with every row. -/
theorem uniformRiskInProbability_iff_diagonal [Nonempty Θ]
    (P : ∀ i θ, Measure (Ω i θ)) (e : ∀ i θ, Ω i θ → ℝ) :
    UniformRiskInProbability P e l ↔ ∀ θ : I → Θ, ∀ ε > 0,
      Tendsto (fun i => P i (θ i) {ω | ε < |e i (θ i) ω|}) l (𝓝 0) := by
  constructor
  · intro h θ
    exact h.diagonal θ
  · intro h
    apply (uniformRiskInProbability_iff_eventual P e).mpr
    intro ε hε δ hδ
    apply (eventually_forall_iff_diagonal _).mpr
    intro θ
    exact ENNReal.tendsto_nhds_zero.mp (h θ ε hε) δ hδ

/-- Strict exceedances and the usual non-strict `TendstoInMeasure`
threshold give the same uniform notion. The proof uses ε/2 and event
inclusion, without exchanging any probability and parameter supremum. -/
theorem uniformRiskInProbability_iff_nonstrict (P : ∀ i θ, Measure (Ω i θ))
    (e : ∀ i θ, Ω i θ → ℝ) :
    UniformRiskInProbability P e l ↔ ∀ ε > 0,
      Tendsto (fun i => ⨆ θ, P i θ {ω | ε ≤ |e i θ ω|}) l (𝓝 0) := by
  constructor
  · intro h ε hε
    apply iSup_ennreal_tendsto_zero_of_uniform_bound
      (fun i θ => P i θ {ω | ε ≤ |e i θ ω|}) (uniformRiskTail P e (ε / 2))
      (Eventually.of_forall fun i θ => ?_) (h (ε / 2) (by linarith))
    exact (measure_mono (fun ω hω => (by linarith : ε / 2 < ε).trans_le hω)).trans
      (le_iSup (fun θ => P i θ {ω | ε / 2 < |e i θ ω|}) θ)
  · intro h ε hε
    apply iSup_ennreal_tendsto_zero_of_uniform_bound
      (fun i θ => P i θ {ω | ε < |e i θ ω|})
      (fun i => ⨆ θ, P i θ {ω | ε ≤ |e i θ ω|})
      (Eventually.of_forall fun i θ => ?_) (h ε hε)
    have hsub : {ω : Ω i θ | ε < |e i θ ω|} ⊆ {ω | ε ≤ |e i θ ω|} := by
      intro ω hω
      change ε < |e i θ ω| at hω
      change ε ≤ |e i θ ω|
      exact hω.le
    exact (measure_mono hsub).trans
      (le_iSup (fun θ => P i θ {ω | ε ≤ |e i θ ω|}) θ)

/-- True uniform expectation-risk assembly from a common bound on the
normalized conditional L1 error. All losses are integrable under their own
laws; no common probability space, positive bias, or denominator lower
bound independent of row and parameter is imposed. -/
theorem uniform_expected_risk_ratio_of_L1_bound [Nonempty Θ]
    (P : ∀ i θ, Measure (Ω i θ)) [∀ i θ, IsProbabilityMeasure (P i θ)]
    (R : ∀ i θ, Ω i θ → ℝ) (D : I → Θ → ℝ)
    (hR : ∀ i θ, Integrable (R i θ) (P i θ))
    (hD : ∀ᶠ i in l, ∀ θ, 0 < D i θ) (b : I → ℝ)
    (hb : Tendsto b l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ θ,
      (∫ ω, |R i θ ω - D i θ| ∂P i θ) / D i θ ≤ b i) :
    Tendsto (fun i => sSup (Set.range (fun θ =>
      |(∫ ω, R i θ ω ∂P i θ) / D i θ - 1|))) l (𝓝 0) ∧
    Tendsto (fun p : I × Θ => (∫ ω, R p.1 p.2 ω ∂P p.1 p.2) / D p.1 p.2)
      (uniformFamilyFilter l Θ) (𝓝 1) := by
  have he : ∀ᶠ i in l, ∀ θ,
      |(∫ ω, R i θ ω ∂P i θ) / D i θ - 1| ≤ b i := by
    filter_upwards [hD, hbound] with i hiD hib θ
    have hh := integral_risk_ratio_error_le (R i θ) (D i θ) (hR i θ) (hiD θ)
    rw [integral_div] at hh
    exact hh.trans (hib θ)
  refine ⟨sSup_tendsto_zero_of_uniform_bound _ b
    (Eventually.of_forall fun _ _ => abs_nonneg _) he hb, ?_⟩
  apply (tendsto_uniformFamilyFilter_iff
    (fun i θ => (∫ ω, R i θ ω ∂P i θ) / D i θ) 1).mpr
  intro ε hε
  filter_upwards [he, hb.eventually (gt_mem_nhds hε)] with i hi hbi θ
  simpa only [Real.dist_eq] using (hi θ).trans_lt hbi

/-- Single-law Markov bound after a genuine good/bad event split. This
uses the restricted integral on the good event, so it adds no expectation
scale to the conditional-in-probability argument. -/
theorem measure_relative_risk_exceedance_le_good_bad
    {S : Type*} [MeasurableSpace S] {ν : Measure S} [IsProbabilityMeasure ν]
    (R : S → ℝ) (D : ℝ) (hR : Integrable R ν) (hD : 0 < D)
    (G : Set S) (hG : MeasurableSet G) {ε : ℝ} (hε : 0 < ε) :
    ν {ω | ε < |R ω - D| / D} ≤ ν Gᶜ +
      ENNReal.ofReal ((∫ ω in G, |R ω - D| / D ∂ν) / ε) := by
  let f := fun ω => |R ω - D| / D
  have hf : Integrable f ν := by
    simpa only [f, Real.norm_eq_abs, Pi.sub_apply] using
      (hR.sub (integrable_const D)).norm.div_const D
  have hfi : Integrable (fun ω => f ω / ε) (ν.restrict G) := hf.restrict.div_const ε
  have hmark := hfi.measure_le_integral
    (Eventually.of_forall fun ω => div_nonneg (div_nonneg (abs_nonneg _) hD.le) hε.le)
    (s := {ω | ε < f ω}) (fun _ hω => (le_div_iff₀ hε).mpr (by simpa using hω.le))
  rw [Measure.restrict_apply' hG, integral_div] at hmark
  have hsub : {ω | ε < f ω} ⊆ Gᶜ ∪ ({ω | ε < f ω} ∩ G) := by
    intro ω hω
    by_cases hωG : ω ∈ G
    · exact Or.inr ⟨hω, hωG⟩
    · exact Or.inl hωG
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl hmark))

/-- The same actual bound in the risk-ratio convention of the manuscript. -/
theorem measure_risk_ratio_exceedance_le_good_bad
    {S : Type*} [MeasurableSpace S] {ν : Measure S} [IsProbabilityMeasure ν]
    (R : S → ℝ) (D : ℝ) (hR : Integrable R ν) (hD : 0 < D)
    (G : Set S) (hG : MeasurableSet G) {ε : ℝ} (hε : 0 < ε) :
    ν {ω | ε < |R ω / D - 1|} ≤ ν Gᶜ +
      ENNReal.ofReal ((∫ ω in G, |R ω - D| / D ∂ν) / ε) := by
  have he : (fun ω => |R ω / D - 1|) = (fun ω => |R ω - D| / D) := by
    funext ω
    rw [show R ω / D - 1 = (R ω - D) / D by field_simp, abs_div, abs_of_pos hD]
  have hset : {ω | ε < |R ω / D - 1|} = {ω | ε < |R ω - D| / D} := by
    ext ω
    change ε < |R ω / D - 1| ↔ ε < |R ω - D| / D
    rw [congrFun he ω]
  rw [hset]
  exact measure_relative_risk_exceedance_le_good_bad R D hR hD G hG hε

/-- Uniform conditional-oP from actual common good-event L1 bounds and
bad-event probabilities, with changing row sample spaces and laws. There
is no bad-risk-expectation bound or logarithmic expectation condition in
this implication. The two finite bounds are supplied by the actual model. -/
theorem uniform_risk_in_probability_of_good_bad_bounds
    (P : ∀ i θ, Measure (Ω i θ)) [∀ i θ, IsProbabilityMeasure (P i θ)]
    (R : ∀ i θ, Ω i θ → ℝ) (D : I → Θ → ℝ)
    (hR : ∀ i θ, Integrable (R i θ) (P i θ))
    (hD : ∀ᶠ i in l, ∀ θ, 0 < D i θ)
    (G : ∀ i θ, Set (Ω i θ)) (hG : ∀ i θ, MeasurableSet (G i θ))
    (bGood : I → ℝ) (bBad : I → ℝ≥0∞)
    (hGood : Tendsto bGood l (𝓝 0)) (hBad : Tendsto bBad l (𝓝 0))
    (hgood : ∀ᶠ i in l, ∀ θ,
      (∫ ω in G i θ, |R i θ ω - D i θ| / D i θ ∂P i θ) ≤ bGood i)
    (hbad : ∀ᶠ i in l, ∀ θ, P i θ (G i θ)ᶜ ≤ bBad i) :
    UniformRiskInProbability P (fun i θ ω => R i θ ω / D i θ - 1) l := by
  apply uniformRiskInProbability_of_tail_bound P _
    (fun ε i => bBad i + ENNReal.ofReal (bGood i / ε))
  · intro ε hε
    have ht := hBad.add (ENNReal.tendsto_ofReal (hGood.div_const ε))
    simpa only [zero_div, ENNReal.ofReal_zero, add_zero] using ht
  · intro ε hε
    filter_upwards [hD, hgood, hbad] with i hiD hiGood hiBad θ
    exact (measure_risk_ratio_exceedance_le_good_bad (R i θ) (D i θ) (hR i θ)
      (hiD θ) (G i θ) (hG i θ) hε).trans
      (add_le_add (hiBad θ) (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (hiGood θ) hε.le)))

/-- The diagonal/triangular conditional probability step under arbitrary
row laws and spaces. Its two scalar limits are the already-proved good
L1 comparison and bad probability; no bad-risk expectation or additional
logarithmic expectation condition is needed. -/
theorem risk_ratio_probability_of_good_bad_L1
    {J : Type*} {l : Filter J} {S : J → Type*} [∀ i, MeasurableSpace (S i)]
    (P : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (P i)]
    (R : ∀ i, S i → ℝ) (D : J → ℝ)
    (hR : ∀ i, Integrable (R i) (P i)) (hD : ∀ᶠ i in l, 0 < D i)
    (G : ∀ i, Set (S i)) (hG : ∀ i, MeasurableSet (G i))
    (hgood : Tendsto (fun i => ∫ ω in G i, |R i ω - D i| / D i ∂P i) l (𝓝 0))
    (hbad : Tendsto (fun i => (P i).real (G i)ᶜ) l (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun i => P i {ω | ε < |R i ω / D i - 1|}) l (𝓝 0) := by
  intro ε hε
  have ht := (ENNReal.tendsto_ofReal hbad).add
    (ENNReal.tendsto_ofReal (hgood.div_const ε))
  simp only [ENNReal.ofReal_zero, zero_div, add_zero] at ht
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  filter_upwards [hD, ENNReal.tendsto_nhds_zero.mp ht δ hδ] with i hiD hit
  have he : ENNReal.ofReal ((P i).real (G i)ᶜ) = P i (G i)ᶜ :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  exact (measure_risk_ratio_exceedance_le_good_bad (R i) (D i) (hR i) hiD
    (G i) (hG i) hε).trans (by rwa [he] at hit)

/-- Genuine expectation assembly for changing row sample spaces and laws.
This is the variable-law version of the scalar good/bad integral assembly;
its finite inequalities are applied inside each actual row separately. -/
theorem risk_expectation_from_good_bad_rows
    {J : Type*} {l : Filter J} {S : J → Type*} [∀ i, MeasurableSpace (S i)]
    (P : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (P i)]
    (R : ∀ i, S i → ℝ) (D : J → ℝ)
    (hR : ∀ i, Integrable (R i) (P i)) (hRn : ∀ i, 0 ≤ᵐ[P i] R i)
    (hD : ∀ᶠ i in l, 0 < D i) (G : ∀ i, Set (S i)) (hG : ∀ i, MeasurableSet (G i))
    (hgood : Tendsto (fun i => ∫ ω in G i, |R i ω - D i| / D i ∂P i) l (𝓝 0))
    (hbad : Tendsto (fun i => ∫ ω in (G i)ᶜ, R i ω / D i ∂P i) l (𝓝 0))
    (hprob : Tendsto (fun i => (P i).real (G i)ᶜ) l (𝓝 0)) :
    Tendsto (fun i => (∫ ω, R i ω ∂P i) / D i) l (𝓝 1) ∧
      Tendsto (fun i => ∫ ω, |R i ω - D i| / D i ∂P i) l (𝓝 0) := by
  have hL1 : Tendsto (fun i => ∫ ω, |R i ω - D i| / D i ∂P i) l (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa only [zero_add] using (hgood.add hbad).add hprob)
    · filter_upwards [hD] with i hiD
      exact integral_nonneg fun _ => div_nonneg (abs_nonneg _) hiD.le
    · filter_upwards [hD] with i hiD
      exact integral_normalized_abs_risk_le_good_bad (R i) (D i) (G i) (hG i)
        (hR i) (hRn i) hiD
  refine ⟨?_, hL1⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hL1
  filter_upwards [hD] with i hiD
  simpa only [Real.norm_eq_abs] using integral_risk_ratio_error_le (R i) (D i) (hR i) hiD

end
end KernelSeq
