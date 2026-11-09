import KernelSeq.IndependentOperatorTrace
import KernelSeq.MatrixMgfRecurrence
import KernelSeq.MatrixLaplaceBernstein

/-!
# Actual independent matrix Bernstein with a common variance proxy

The trace-exponential remainder recursion is derived from genuine independence,
Golden--Thompson, and the one-increment exponential bound. Each increment has
the same actual Loewner second-moment majorant `W`. No trace-moment or
matrix-concentration certificate is a hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {Ω ι H : Type*} [MeasurableSpace Ω] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {P : Measure Ω} [IsProbabilityMeasure P]

local instance commonVarianceOperatorMeasurableSpace : MeasurableSpace (H →L[ℝ] H) :=
  borel (H →L[ℝ] H)
local instance commonVarianceOperatorBorelSpace : BorelSpace (H →L[ℝ] H) := ⟨rfl⟩

/-- The actual centered trace-exponential moment. For mean-zero fields it is
also the integral of `trace(exp(θS) - I - θS)`. -/
def centeredTraceExpMoment (b : HilbertBasis ι ℝ H) (P : Measure Ω)
    (θ : ℝ) (S : Ω → H →L[ℝ] H) : ℝ :=
  basisTrace b ((∫ ω, NormedSpace.exp (θ • S ω) ∂P) - 1)

omit [IsProbabilityMeasure P] in
theorem centeredTraceExpMoment_eq_trace_integral (b : HilbertBasis ι ℝ H)
    (θ : ℝ) (S : Ω → H →L[ℝ] H)
    (hE : Integrable (fun ω => NormedSpace.exp (θ • S ω)) P) :
    centeredTraceExpMoment b P θ S =
      (∫ ω, basisTrace b (NormedSpace.exp (θ • S ω)) ∂P) - basisTrace b 1 := by
  rw [centeredTraceExpMoment, ← finiteBasisTraceCLM_apply, map_sub]
  rw [finiteBasisTraceCLM_apply, finiteBasisTraceCLM_apply, finiteBasisTrace_integral b _ hE]

variable [FiniteDimensional ℝ H]

/-- Centering and the actual affine lower exponential bound give positivity
of the genuine integrated exponential remainder. -/
theorem integral_operator_exp_sub_one_isPositive
    (S : Ω → H →L[ℝ] H) (θ : ℝ)
    (hSi : Integrable S P) (hEi : Integrable (fun ω => NormedSpace.exp (θ • S ω)) P)
    (hS : ∀ᵐ ω ∂P, IsSelfAdjoint (S ω)) (hmean : (∫ ω, S ω ∂P) = 0) :
    ((∫ ω, NormedSpace.exp (θ • S ω) ∂P : H →L[ℝ] H) - 1).IsPositive := by
  have hc : Integrable (fun _ : Ω => (1 : H →L[ℝ] H)) P := integrable_const _
  have hlin := hSi.smul θ
  have hle := integral_operator_mono
    (fun ω => 1 + θ • S ω) (fun ω => NormedSpace.exp (θ • S ω))
    (hc.add hlin) hEi (hS.mono fun ω hω =>
      finite_one_add_operator_le_exp _ (((IsSelfAdjoint.all θ).smul hω).isSymmetric))
  have heq : (∫ ω, 1 + θ • S ω ∂P : H →L[ℝ] H) = 1 := by
    have hsum := integral_add hc hlin
    simp only [Pi.smul_apply] at hsum
    rw [hsum, integral_smul, hmean]
    simp
  rw [heq] at hle
  exact (ContinuousLinearMap.le_def _ _).mp hle

omit [FiniteDimensional ℝ H] in
/-- For a truly centered field this is exactly the integral of the actual
exponential remainder, including its linear term. -/
theorem centeredTraceExpMoment_eq_integral_remainder
    (b : HilbertBasis ι ℝ H) (S : Ω → H →L[ℝ] H) (θ : ℝ)
    (hSi : Integrable S P) (hEi : Integrable (fun ω => NormedSpace.exp (θ • S ω)) P)
    (hmean : (∫ ω, S ω ∂P) = 0) :
    centeredTraceExpMoment b P θ S =
      ∫ ω, basisTrace b (NormedSpace.exp (θ • S ω) - 1 - θ • S ω) ∂P := by
  have hc : Integrable (fun _ : Ω => (1 : H →L[ℝ] H)) P := integrable_const _
  have hlin := hSi.smul θ
  have hrem := (hEi.sub hc).sub hlin
  have htrace := finiteBasisTrace_integral b _ hrem
  simp only [Pi.sub_apply, Pi.smul_apply] at htrace
  rw [centeredTraceExpMoment, ← htrace]
  congr 1
  have hsub := integral_sub (hEi.sub hc) hlin
  have hsub' := integral_sub hEi hc
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsub'
  rw [hsub, hsub', integral_const, integral_smul, hmean]
  simp

/-- The one-step intrinsic trace-remainder recursion, with the actual
integrated positive remainder providing the weighted trace estimate. -/
theorem centeredTraceExpMoment_add_le
    (b : HilbertBasis ι ℝ H) (S Y : Ω → H →L[ℝ] H)
    (hSY : IndepFun S Y P)
    (hSm : AEStronglyMeasurable S P) (hYm : AEStronglyMeasurable Y P)
    (hS : ∀ᵐ ω ∂P, IsSelfAdjoint (S ω)) (hY : ∀ᵐ ω ∂P, IsSelfAdjoint (Y ω))
    {θ R C : ℝ} (hθ : 0 ≤ θ)
    (hR : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ R) (hC : ∀ᵐ ω ∂P, ‖S ω‖ ≤ C)
    (hSmean : (∫ ω, S ω ∂P) = 0) (hmean : (∫ ω, Y ω ∂P) = 0)
    (W : H →L[ℝ] H) (hWp : W.IsPositive)
    (hW : (∫ ω, Y ω * Y ω ∂P : H →L[ℝ] H) ≤ W) :
    centeredTraceExpMoment b P θ (fun ω => S ω + Y ω) ≤
      (1 + matrixExpRemainderCoefficient θ R * ‖W‖) * centeredTraceExpMoment b P θ S +
        matrixExpRemainderCoefficient θ R * basisTrace b W := by
  have hSi := integrable_operator_of_ae_norm_bound S hSm hC
  have hEi := integrable_operator_exp_of_ae_norm_bound S hSm hS hθ hC
  have hSumS : ∀ᵐ ω ∂P, IsSelfAdjoint (S ω + Y ω) := by
    filter_upwards [hS, hY] with ω hSω hYω
    exact hSω.add hYω
  have hSumC : ∀ᵐ ω ∂P, ‖S ω + Y ω‖ ≤ C + R := by
    filter_upwards [hC, hR] with ω hCω hRω
    exact (norm_add_le _ _).trans (add_le_add hCω hRω)
  have hSumE := integrable_operator_exp_of_ae_norm_bound (fun ω => S ω + Y ω)
    (hSm.add hYm) hSumS hθ hSumC
  let Z : H →L[ℝ] H := (∫ ω, NormedSpace.exp (θ • S ω) ∂P) - 1
  have hZ : Z.IsPositive := integral_operator_exp_sub_one_isPositive S θ hSi hEi hS hSmean
  have hweight := finiteBasisTrace_weighted_le_norm b Z W hZ hWp.isSymmetric.isSelfAdjoint
  have htrace : basisTrace b ((∫ ω, NormedSpace.exp (θ • S ω) ∂P) * W) ≤
      ‖W‖ * centeredTraceExpMoment b P θ S + basisTrace b W := by
    have heq : (∫ ω, NormedSpace.exp (θ • S ω) ∂P : H →L[ℝ] H) * W = Z * W + W := by
      dsimp only [Z]
      noncomm_ring
    rw [heq, ← finiteBasisTraceCLM_apply, map_add]
    simpa only [finiteBasisTraceCLM_apply, centeredTraceExpMoment, Z] using add_le_add hweight (le_refl (basisTrace b W))
  have hstep := integral_trace_exp_add_le_one_step_actual b S Y hSY hSm hYm hS hY
    hθ hR hC hmean W hW
  rw [centeredTraceExpMoment_eq_trace_integral b θ _ hSumE,
    centeredTraceExpMoment_eq_trace_integral b θ S hEi]
  have hmul := mul_le_mul_of_nonneg_left htrace (matrixExpRemainderCoefficient_nonneg θ R)
  rw [centeredTraceExpMoment_eq_trace_integral b θ S hEi] at hmul
  nlinarith

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
private theorem commonVariance_sum_integrable {J : Type*}
    (Y : J → Ω → H →L[ℝ] H) (hYm : ∀ i, AEStronglyMeasurable (Y i) P)
    {R : ℝ} (hR : ∀ i, ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ R) (s : Finset J) :
    Integrable (fun ω => ∑ i ∈ s, Y i ω) P := by
  exact integrable_finsetSum (μ := P) (ε' := H →L[ℝ] H) s (f := Y)
    (fun i _ => integrable_operator_of_ae_norm_bound (Y i) (hYm i) (hR i))

omit [IsProbabilityMeasure P] [FiniteDimensional ℝ H] in
private theorem commonVariance_sum_selfadj {J : Type*}
    (Y : J → Ω → H →L[ℝ] H) (hY : ∀ i, ∀ᵐ ω ∂P, IsSelfAdjoint (Y i ω)) (s : Finset J) :
    ∀ᵐ ω ∂P, IsSelfAdjoint (∑ i ∈ s, Y i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    filter_upwards [hY i, ih] with ω hiω hsω
    simpa only [Finset.sum_insert hi] using hiω.add hsω

omit [CompleteSpace H] [IsProbabilityMeasure P] [FiniteDimensional ℝ H] in
private theorem commonVariance_sum_norm {J : Type*}
    (Y : J → Ω → H →L[ℝ] H) {R : ℝ}
    (hR : ∀ i, ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ R) (s : Finset J) :
    ∀ᵐ ω ∂P, ‖∑ i ∈ s, Y i ω‖ ≤ (s.card : ℝ) * R := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    filter_upwards [hR i, ih] with ω hiω hsω
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    exact (norm_add_le _ _).trans (by nlinarith)

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
private theorem commonVariance_sum_mean {J : Type*}
    (Y : J → Ω → H →L[ℝ] H) (hYm : ∀ i, AEStronglyMeasurable (Y i) P)
    {R : ℝ} (hR : ∀ i, ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ R)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = 0) (s : Finset J) :
    (∫ ω, ∑ i ∈ s, Y i ω ∂P) = 0 := by
  rw [integral_finsetSum s (fun i _ => integrable_operator_of_ae_norm_bound (Y i) (hYm i) (hR i))]
  simp only [hmean, Finset.sum_const_zero]

/-- The genuine one-sided trace-remainder moment of an independent finite sum.
The common positive proxy need not be an exact variance. -/
theorem commonVariance_trace_exp_remainder_le {J : Type*}
    (b : HilbertBasis ι ℝ H) (Y : J → Ω → H →L[ℝ] H)
    (hYm : ∀ i, AEStronglyMeasurable (Y i) P) (hind : iIndepFun Y P)
    (hY : ∀ i, ∀ᵐ ω ∂P, IsSelfAdjoint (Y i ω))
    {R : ℝ} (hR : ∀ i, ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ R)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = 0)
    (W : H →L[ℝ] H) (hWp : W.IsPositive) (hWnorm : 0 < ‖W‖)
    (hW : ∀ i, (∫ ω, Y i ω * Y i ω ∂P : H →L[ℝ] H) ≤ W)
    {θ : ℝ} (hθ : 0 ≤ θ) (s : Finset J) :
    centeredTraceExpMoment b P θ (fun ω => ∑ i ∈ s, Y i ω) ≤
      (basisTrace b W / ‖W‖) *
        (Real.exp (matrixExpRemainderCoefficient θ R * ((s.card : ℝ) * ‖W‖)) - 1) := by
  classical
  let u : Finset J → ℝ := fun t => centeredTraceExpMoment b P θ (fun ω => ∑ i ∈ t, Y i ω)
  let a := matrixExpRemainderCoefficient θ R * ‖W‖
  let d := basisTrace b W / ‖W‖
  have ha : 0 ≤ a := mul_nonneg (matrixExpRemainderCoefficient_nonneg θ R) (norm_nonneg W)
  have hd : 0 ≤ d := div_nonneg (finiteBasisTrace_nonneg b W hWp) (norm_nonneg W)
  have hzero : u ∅ ≤ 0 := by
    simp [u, centeredTraceExpMoment, NormedSpace.exp_zero]
    rw [← finiteBasisTraceCLM_apply, map_zero]
  have hstep : ∀ t i, i ∉ t → u (insert i t) ≤ (1 + a) * u t + a * d := by
    intro t i hi
    have hsum : (fun ω => ∑ j ∈ insert i t, Y j ω) =
        (fun ω => (∑ j ∈ t, Y j ω) + Y i ω) := by
      funext ω
      rw [Finset.sum_insert hi, add_comm]
    have hSi := commonVariance_sum_integrable Y hYm hR t
    have hineq := centeredTraceExpMoment_add_le b (fun ω => ∑ j ∈ t, Y j ω) (Y i)
      (indepFun_operator_finsetSum_of_notMem Y hind hYm hi)
      hSi.aestronglyMeasurable (hYm i) (commonVariance_sum_selfadj Y hY t) (hY i)
      hθ (hR i) (commonVariance_sum_norm Y hR t)
      (commonVariance_sum_mean Y hYm hR hmean t) (hmean i) W hWp (hW i)
    have had : a * d = matrixExpRemainderCoefficient θ R * basisTrace b W := by
      dsimp only [a, d]
      field_simp [hWnorm.ne']
    dsimp only [u]
    rw [hsum, had]
    exact hineq
  have hr := mgf_finset_recurrence_exp ha hd u hzero hstep s
  have hexp : (s.card : ℝ) * a =
      matrixExpRemainderCoefficient θ R * ((s.card : ℝ) * ‖W‖) := by dsimp only [a]; ring
  simpa only [hexp, u, d] using hr

omit [FiniteDimensional ℝ H] in
/-- Exact decomposition of the actual symmetric Laplace potential into the
two genuine one-sided trace remainders. -/
theorem integral_matrixLaplacePotential_eq_centeredTraceExpMoments
    (b : HilbertBasis ι ℝ H) (S : Ω → H →L[ℝ] H) (θ : ℝ)
    (hplus : Integrable (fun ω => NormedSpace.exp (θ • S ω)) P)
    (hminus : Integrable (fun ω => NormedSpace.exp ((-θ) • S ω)) P) :
    (∫ ω, matrixLaplacePotential b θ (S ω) ∂P) =
      centeredTraceExpMoment b P θ S + centeredTraceExpMoment b P θ (fun ω => -S ω) := by
  have hneg : (fun ω => NormedSpace.exp (θ • -S ω)) =
      (fun ω => NormedSpace.exp ((-θ) • S ω)) := by
    funext ω
    rw [smul_neg, neg_smul]
  have hnegI : Integrable (fun ω => NormedSpace.exp (θ • -S ω)) P := by
    rwa [hneg]
  rw [centeredTraceExpMoment_eq_trace_integral b θ S hplus,
    centeredTraceExpMoment_eq_trace_integral b θ _ hnegI]
  have hid : (fun ω => matrixLaplacePotential b θ (S ω)) =
      (fun ω => basisTrace b (NormedSpace.exp (θ • S ω)) +
        basisTrace b (NormedSpace.exp ((-θ) • S ω)) - 2 * basisTrace b 1) := by
    funext ω
    simp only [matrixLaplacePotential, ← finiteBasisTraceCLM_apply,
      map_sub, map_add, map_smul, smul_eq_mul]
  have hsub := integral_sub ((integrable_finiteBasisTrace b _ hplus).add
    (integrable_finiteBasisTrace b _ hminus)) (integrable_const (2 * basisTrace b 1))
  have hadd := integral_add (integrable_finiteBasisTrace b _ hplus) (integrable_finiteBasisTrace b _ hminus)
  simp only [Pi.add_apply] at hsub
  rw [hid, hsub, hadd]
  simp only [integral_const, probReal_univ, one_smul]
  simp only [smul_neg, neg_smul]
  ring

/-- The actual two-sided trace-potential bound. Both signs are treated as
genuinely independent transformed families with the same second moments. -/
theorem commonVariance_matrixLaplacePotential_moment_le {J : Type*}
    (b : HilbertBasis ι ℝ H) (Y : J → Ω → H →L[ℝ] H)
    (hYm : ∀ i, AEStronglyMeasurable (Y i) P) (hind : iIndepFun Y P)
    (hY : ∀ i, ∀ᵐ ω ∂P, IsSelfAdjoint (Y i ω))
    {R : ℝ} (hR : ∀ i, ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ R)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = 0)
    (W : H →L[ℝ] H) (hWp : W.IsPositive) (hWnorm : 0 < ‖W‖)
    (hW : ∀ i, (∫ ω, Y i ω * Y i ω ∂P : H →L[ℝ] H) ≤ W)
    {θ : ℝ} (hθ : 0 ≤ θ) (s : Finset J) :
    (∫ ω, matrixLaplacePotential b θ (∑ i ∈ s, Y i ω) ∂P) ≤
      2 * (basisTrace b W / ‖W‖) *
        (Real.exp (matrixExpRemainderCoefficient θ R * ((s.card : ℝ) * ‖W‖)) - 1) := by
  let Z : J → Ω → H →L[ℝ] H := fun i ω => -Y i ω
  have hZm : ∀ i, AEStronglyMeasurable (Z i) P := fun i => (hYm i).neg
  have hindZ : iIndepFun Z P := hind.comp (fun _ => fun A : H →L[ℝ] H => -A)
    (fun _ => measurable_neg)
  have hZ : ∀ i, ∀ᵐ ω ∂P, IsSelfAdjoint (Z i ω) := fun i =>
    (hY i).mono (fun _ h => h.neg)
  have hZR : ∀ i, ∀ᵐ ω ∂P, ‖Z i ω‖ ≤ R := fun i => by simpa only [Z, norm_neg] using hR i
  have hZmean : ∀ i, (∫ ω, Z i ω ∂P) = 0 := fun i => by
    simp only [Z, integral_neg, hmean i, neg_zero]
  have hZW : ∀ i, (∫ ω, Z i ω * Z i ω ∂P : H →L[ℝ] H) ≤ W := fun i => by
    simpa only [Z, neg_mul_neg] using hW i
  have hp := commonVariance_trace_exp_remainder_le b Y hYm hind hY hR hmean W hWp hWnorm hW hθ s
  have hm := commonVariance_trace_exp_remainder_le b Z hZm hindZ hZ hZR hZmean W hWp hWnorm hZW hθ s
  have hSi := commonVariance_sum_integrable Y hYm hR s
  have hSp := commonVariance_sum_selfadj Y hY s
  have hSn := commonVariance_sum_norm Y hR s
  have hplus := integrable_operator_exp_of_ae_norm_bound _ hSi.aestronglyMeasurable hSp hθ hSn
  have hminus : Integrable (fun ω => NormedSpace.exp ((-θ) • (∑ i ∈ s, Y i ω))) P := by
    have hmE := integrable_operator_exp_of_ae_norm_bound (fun ω => -(∑ i ∈ s, Y i ω))
      hSi.aestronglyMeasurable.neg (hSp.mono (fun _ h => h.neg)) hθ
      (hSn.mono (fun ω h => by simpa only [norm_neg] using h))
    simpa only [smul_neg, neg_smul] using hmE
  rw [integral_matrixLaplacePotential_eq_centeredTraceExpMoments b _ θ hplus hminus]
  have hsum : (fun ω => ∑ i ∈ s, Z i ω) = (fun ω => -(∑ i ∈ s, Y i ω)) := by
    funext ω
    simp only [Z, Finset.sum_neg_distrib]
  rw [hsum] at hm
  linarith

omit [FiniteDimensional ℝ H] in
/-- A genuine common second-moment majorant of a nonempty family is positive;
this is derived from the actual integrated selfadjoint square. -/
theorem commonVariance_proxy_isPositive {n : ℕ} (hn : 0 < n)
    (Y : Fin n → Ω → H →L[ℝ] H)
    (hYm : ∀ i, AEStronglyMeasurable (Y i) P)
    (hY : ∀ i, ∀ᵐ ω ∂P, IsSelfAdjoint (Y i ω))
    {R : ℝ} (hR : ∀ i, ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ R)
    (W : H →L[ℝ] H)
    (hW : ∀ i, (∫ ω, Y i ω * Y i ω ∂P : H →L[ℝ] H) ≤ W) : W.IsPositive := by
  let i : Fin n := ⟨0, hn⟩
  have hYi := integrable_operator_of_ae_norm_bound (Y i) (hYm i) (hR i)
  have hY2 := integrable_operator_square_of_bound (Y i) hYi (hR i)
  have hp := integral_operator_isPositive _ hY2 ((hY i).mono (fun ω hω =>
    operator_square_isPositive_of_isSelfAdjoint (Y i ω) hω))
  exact (ContinuousLinearMap.nonneg_iff_isPositive W).mp
    (((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp).trans (hW i))

/-- Actual finite independent selfadjoint matrix Bernstein with a common
per-increment variance proxy. All integrability and trace-moment bounds are
derived from the raw measurable bounded centered independent increments. -/
theorem finite_commonVariance_bernstein
    (b : HilbertBasis ι ℝ H) {n : ℕ} (hn : 0 < n)
    (Y : Fin n → Ω → H →L[ℝ] H)
    (hYm : ∀ i, AEStronglyMeasurable (Y i) P) (hind : iIndepFun Y P)
    (hY : ∀ i, ∀ᵐ ω ∂P, IsSelfAdjoint (Y i ω))
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ i, ∀ᵐ ω ∂P, ‖Y i ω‖ ≤ R)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = 0)
    (W : H →L[ℝ] H) (hWnorm : 0 < ‖W‖)
    (hW : ∀ i, (∫ ω, Y i ω * Y i ω ∂P : H →L[ℝ] H) ≤ W)
    (t : ℝ) (ht : Real.sqrt ((n : ℝ) * ‖W‖) + R / 3 ≤ t) :
    P {ω | t ≤ ‖∑ i, Y i ω‖} ≤
      ENNReal.ofReal (8 * (basisTrace b W / ‖W‖) *
        Real.exp (-(t ^ 2) / (2 * ((n : ℝ) * ‖W‖ + R * t / 3)))) := by
  have hWp := commonVariance_proxy_isPositive hn Y hYm hY hR W hW
  have hv : 0 < (n : ℝ) * ‖W‖ := mul_pos (Nat.cast_pos.mpr hn) hWnorm
  have hd : 0 ≤ basisTrace b W / ‖W‖ :=
    div_nonneg (finiteBasisTrace_nonneg b W hWp) (norm_nonneg W)
  let θ := t / ((n : ℝ) * ‖W‖ + R * t / 3)
  have ht0 : 0 < t := by
    have hs := Real.sqrt_pos.mpr hv
    linarith
  have hθ : 0 ≤ θ := le_of_lt (div_pos ht0 (by positivity))
  have hSi := commonVariance_sum_integrable Y hYm hR Finset.univ
  have hSp := commonVariance_sum_selfadj Y hY Finset.univ
  have hSn := commonVariance_sum_norm Y hR Finset.univ
  have hplus := integrable_operator_exp_of_ae_norm_bound _ hSi.aestronglyMeasurable hSp hθ hSn
  have hminus : Integrable (fun ω => NormedSpace.exp ((-θ) • (∑ i, Y i ω))) P := by
    have hmE := integrable_operator_exp_of_ae_norm_bound (fun ω => -(∑ i, Y i ω))
      hSi.aestronglyMeasurable.neg (hSp.mono (fun _ h => h.neg)) hθ
      (hSn.mono (fun ω h => by simpa only [norm_neg] using h))
    simpa only [smul_neg, neg_smul] using hmE
  have hm := commonVariance_matrixLaplacePotential_moment_le b Y hYm hind hY hR hmean
    W hWp hWnorm hW hθ Finset.univ
  simp only [Finset.card_univ, Fintype.card_fin] at hm
  exact matrixLaplace_bernstein_of_trace_moment b _ hSp hv hR0 hd ht hplus hminus hm

end
end KernelSeq
