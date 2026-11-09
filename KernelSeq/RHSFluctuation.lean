import KernelSeq.HilbertMoments
import KernelSeq.PopulationCovariance
import KernelSeq.EmpiricalCovariance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Actual sampled right-hand-side fluctuations

Second-moment and Markov bounds for the difference between the
feature-weighted empirical representer and its population counterpart. The
normalizing bounded operator is arbitrary: identifying it with the real
regularized inverse square root and identifying the spectral residual remain
upstream. No Gaussian noise, fourth moments, or finite-dimensional ambient
space is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace KernelSeq

variable {X Ω H : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure X} {P : Measure Ω}

/-- Centering decreases the second moment, with the exact variance identity. -/
theorem integral_norm_sq_centered [IsProbabilityMeasure μ] {u : X → H}
    (hu : MemLp u 2 μ) :
    (∫ x, ‖u x - ∫ y, u y ∂μ‖ ^ 2 ∂μ) =
      (∫ x, ‖u x‖ ^ 2 ∂μ) - ‖∫ y, u y ∂μ‖ ^ 2 := by
  have hi := hu.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hs := (memLp_two_iff_integrable_sq_norm hu.1).mp hu
  have hc : Integrable (fun _ : X => ‖∫ y, u y ∂μ‖ ^ 2) μ := integrable_const _
  have hh := hi.const_inner (𝕜 := ℝ) (∫ y, u y ∂μ)
  have hexp (x : X) : ‖u x - ∫ y, u y ∂μ‖ ^ 2 =
      ‖u x‖ ^ 2 + ‖∫ y, u y ∂μ‖ ^ 2 -
        2 * inner ℝ (∫ y, u y ∂μ) (u x) := by
    rw [norm_sub_sq_real, real_inner_comm]
    ring
  simp_rw [hexp]
  have hsub := integral_sub (hs.add hc) (hh.const_mul 2)
  have hadd := integral_add hs hc
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd,
    integral_const_mul, integral_inner hi, real_inner_self_eq_norm_sq]
  simp
  ring

/-- The scalar `L²` representative has exactly its Hilbert-space squared norm. -/
theorem integral_sq_L2 (r : Lp ℝ 2 μ) : (∫ x, r x ^ 2 ∂μ) = ‖r‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change (∫ x, r x ^ 2 ∂μ) = ∫ x, inner ℝ (r x) (r x) ∂μ
  simp

omit [CompleteSpace H] in
/-- A leverage bound makes the normalized, residual-weighted feature square integrable. -/
theorem memLp_normalized_residual_feature (k : X → H) (hk : MemLp k 2 μ)
    (r : Lp ℝ 2 μ) (R : H →L[ℝ] H) {L : ℝ}
    (hL : ∀ᵐ x ∂μ, ‖R (k x)‖ ^ 2 ≤ L) :
    MemLp (fun x => r x • R (k x)) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun x => r x • R (k x)) μ :=
    (Lp.aestronglyMeasurable r).smul (R.continuous.comp_aestronglyMeasurable hk.1)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  apply ((Lp.memLp r).integrable_sq.const_mul L).mono' (hmeas.norm.pow 2)
  filter_upwards [hL] with x hx
  calc
    ‖‖r x • R (k x)‖ ^ 2‖ = r x ^ 2 * ‖R (k x)‖ ^ 2 := by
      simp [norm_smul, mul_pow]
    _ ≤ r x ^ 2 * L := mul_le_mul_of_nonneg_left hx (sq_nonneg _)
    _ = L * r x ^ 2 := mul_comm _ _

/-- The actual normalized feature has the correct population mean. -/
theorem integral_normalized_residual_feature (k : X → H) (hk : MemLp k 2 μ)
    (r : Lp ℝ 2 μ) (R : H →L[ℝ] H) :
    (∫ x, r x • R (k x) ∂μ) = R ((featureEmbedding μ k hk).adjoint r) := by
  rw [featureEmbedding_adjoint_eq_integral, ← R.integral_comp_comm
    (integrable_feature_smul k hk r)]
  simp only [map_smul]

/-- Exact centered sample average behind the manuscript's `Z_λ`. -/
theorem normalized_rhs_as_centered_average {n : ℕ} (hn : 0 < n)
    (k : X → H) (hk : MemLp k 2 μ) (r : Lp ℝ 2 μ) (R : H →L[ℝ] H)
    (x : Fin n → X) :
    R (empiricalRepresenter (fun i => k (x i)) (fun i => r (x i)) -
        (featureEmbedding μ k hk).adjoint r) =
      (n : ℝ)⁻¹ • ∑ i, (r (x i) • R (k (x i)) -
        ∫ y, r y • R (k y) ∂μ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [integral_normalized_residual_feature k hk r R]
  simp only [empiricalRepresenter, map_sub, map_smul, map_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_sub]
  simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn0]

/-- Averages of actual iid pullbacks have at most `1/n` of the uncentered moment.
Only pairwise independence, together with the common sample law, is needed. -/
theorem integral_norm_sq_centered_sample_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [MeasurableSpace H] [BorelSpace H]
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (u : X → H) (hu : MemLp u 2 μ) :
    (∫ ω, ‖(n : ℝ)⁻¹ • ∑ i, (u (x i ω) - ∫ y, u y ∂μ)‖ ^ 2 ∂P) ≤
      (n : ℝ)⁻¹ * ∫ y, ‖u y‖ ^ 2 ∂μ := by
  let v : X → H := fun y => u y - ∫ z, u z ∂μ
  have hv : MemLp v 2 μ := hu.sub (memLp_const _)
  have hvmean : (∫ y, v y ∂μ) = 0 := by
    rw [show v = (fun y => u y - ∫ z, u z ∂μ) from rfl,
      integral_sub (hu.integrable (by norm_num)) (integrable_const _)]
    simp
  have hcomp (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (i : Fin n) :
      (∫ ω, f (x i ω) ∂P) = ∫ y, f y ∂μ := by
    have h := integral_map (hlaw i).aemeasurable (by rwa [(hlaw i).map_eq])
    rw [(hlaw i).map_eq] at h
    exact h.symm
  have hmean (i : Fin n) : (∫ ω, v (x i ω) ∂P) = 0 := by
    have h := integral_map (hlaw i).aemeasurable
      (show AEStronglyMeasurable v (Measure.map (x i) P) by
        simpa only [(hlaw i).map_eq] using hv.1)
    rw [(hlaw i).map_eq, hvmean] at h
    exact h.symm
  have hind : Pairwise (fun i j => IndepFun (v ∘ x i) (v ∘ x j) P) := by
    intro i j hij
    apply (hindep hij).comp₀ (hlaw i).aemeasurable (hlaw j).aemeasurable
    · rw [(hlaw i).map_eq]
      exact hv.1.aemeasurable
    · rw [(hlaw j).map_eq]
      exact hv.1.aemeasurable
  have hs := integral_norm_sq_average_of_indep (fun i => v ∘ x i)
    (fun i => hv.comp_measurePreserving (hlaw i)) hind hmean
  simp only [Function.comp_apply] at hs
  change (∫ ω, ‖(n : ℝ)⁻¹ • ∑ i, v (x i ω)‖ ^ 2 ∂P) ≤ _
  rw [hs]
  simp_rw [hcomp (fun y => ‖v y‖ ^ 2) (hv.1.norm.pow 2)]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ∫ y, ‖v y‖ ^ 2 ∂μ) =
    (n : ℝ)⁻¹ * ∫ y, ‖v y‖ ^ 2 ∂μ by field_simp]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change (∫ y, ‖u y - ∫ z, u z ∂μ‖ ^ 2 ∂μ) ≤ _
  rw [integral_norm_sq_centered hu]
  exact sub_le_self _ (sq_nonneg _)

/-- Second-moment bound for the actual normalized empirical representer.
The leverage assumption is a.e., so exceptional design points do not strengthen
the model. The residual is an arbitrary `L²` function. -/
theorem integral_normalized_rhs_sq_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [MeasurableSpace H] [BorelSpace H]
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (r : Lp ℝ 2 μ) (R : H →L[ℝ] H)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, ‖R (k y)‖ ^ 2 ≤ L) :
    (∫ ω, ‖R (empiricalRepresenter (fun i => k (x i ω)) (fun i => r (x i ω)) -
        (featureEmbedding μ k hk).adjoint r)‖ ^ 2 ∂P) ≤
      L / (n : ℝ) * ‖r‖ ^ 2 := by
  simp_rw [normalized_rhs_as_centered_average hn k hk r R]
  have hu := memLp_normalized_residual_feature k hk r R hL
  refine (integral_norm_sq_centered_sample_le hn x hlaw hindep _ hu).trans ?_
  have hmoment : (∫ y, ‖r y • R (k y)‖ ^ 2 ∂μ) ≤ L * ‖r‖ ^ 2 := by
    rw [← integral_sq_L2 r, ← integral_const_mul]
    apply integral_mono_ae
      ((memLp_two_iff_integrable_sq_norm hu.1).mp hu)
      ((Lp.memLp r).integrable_sq.const_mul L)
    filter_upwards [hL] with y hy
    calc
      ‖r y • R (k y)‖ ^ 2 = r y ^ 2 * ‖R (k y)‖ ^ 2 := by
        simp [norm_smul, mul_pow]
      _ ≤ r y ^ 2 * L := mul_le_mul_of_nonneg_left hy (sq_nonneg _)
      _ = L * r y ^ 2 := mul_comm _ _
  calc
    (n : ℝ)⁻¹ * ∫ y, ‖r y • R (k y)‖ ^ 2 ∂μ ≤
        (n : ℝ)⁻¹ * (L * ‖r‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = _ := by ring

/-- The random empirical fluctuation has a genuine finite second moment. -/
theorem memLp_normalized_rhs [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (r : Lp ℝ 2 μ) (R : H →L[ℝ] H)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, ‖R (k y)‖ ^ 2 ≤ L) :
    MemLp (fun ω => R (empiricalRepresenter (fun i => k (x i ω))
      (fun i => r (x i ω)) - (featureEmbedding μ k hk).adjoint r)) 2 P := by
  have hu := memLp_normalized_residual_feature k hk r R hL
  have hv : MemLp (fun y => r y • R (k y) - ∫ z, r z • R (k z) ∂μ) 2 μ :=
    hu.sub (memLp_const _)
  have hs := (memLp_finsetSum' Finset.univ (fun i _ =>
    hv.comp_measurePreserving (hlaw i))).const_smul (n : ℝ)⁻¹
  simp_rw [normalized_rhs_as_centered_average hn k hk r R]
  convert hs using 1
  funext ω
  simp only [Pi.smul_apply, Finset.sum_apply, Function.comp_apply]

/-- Explicit Markov bound for the normalized fluctuation at any positive threshold. -/
theorem measure_normalized_rhs_ge_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [MeasurableSpace H] [BorelSpace H]
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (r : Lp ℝ 2 μ) (R : H →L[ℝ] H)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, ‖R (k y)‖ ^ 2 ≤ L)
    {t : ℝ} (ht : 0 < t) :
    P {ω | t ≤ ‖R (empiricalRepresenter (fun i => k (x i ω)) (fun i => r (x i ω)) -
        (featureEmbedding μ k hk).adjoint r)‖} ≤
      ENNReal.ofReal (L / (n : ℝ) * ‖r‖ ^ 2 / t ^ 2) := by
  let z : Ω → H := fun ω => R (empiricalRepresenter (fun i => k (x i ω))
    (fun i => r (x i ω)) - (featureEmbedding μ k hk).adjoint r)
  have hz := memLp_normalized_rhs hn x hlaw k hk r R hL
  change MemLp z 2 P at hz
  have hi := (memLp_two_iff_integrable_sq_norm hz.1).mp hz
  have hm := (hi.div_const (t ^ 2)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (sq_nonneg ‖z ω‖) (sq_nonneg t)))
    (s := {ω | t ≤ ‖z ω‖}) (fun ω hω => by
      rw [le_div_iff₀ (sq_pos_of_pos ht)]
      change t ≤ ‖z ω‖ at hω
      nlinarith [norm_nonneg (z ω)])
  refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (integral_normalized_rhs_sq_le hn x hlaw hindep k hk r R hL) (sq_nonneg t)

/-- The paper's actual empirical-minus-population right-hand side, before
identifying the population residual with a spectral multiplier. -/
noncomputable def rhsFluctuation (k : X → H) (hk : MemLp k 2 μ)
    (f : Lp ℝ 2 μ) (h : H) {n : ℕ} (x : Fin n → X) : H :=
  empiricalRepresenter (fun i => k (x i)) (fun i => f (x i)) -
    empiricalCovariance (fun i => k (x i)) h -
    ((featureEmbedding μ k hk).adjoint f -
      populationCovariance (featureEmbedding μ k hk) h)

/-- Evaluations of `L²` representatives agree at all sampled designs a.s.
This identifies `Z_λ` with the fluctuation for the population residual. -/
theorem rhsFluctuation_eq_residual_ae {n : ℕ} (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (k : X → H) (hk : MemLp k 2 μ) (f : Lp ℝ 2 μ) (h : H) :
    (fun ω => rhsFluctuation k hk f h (fun i => x i ω)) =ᵐ[P]
      (fun ω => empiricalRepresenter (fun i => k (x i ω))
        (fun i => (f - featureEmbedding μ k hk h) (x i ω)) -
        (featureEmbedding μ k hk).adjoint (f - featureEmbedding μ k hk h)) := by
  have hr : ∀ᵐ y ∂μ, (f - featureEmbedding μ k hk h) y =
      f y - inner ℝ (k y) h := by
    filter_upwards [Lp.coeFn_sub f (featureEmbedding μ k hk h),
      featureEmbedding_ae μ k hk h] with y hy hy'
    simpa only [Pi.sub_apply, hy'] using hy
  have hx : ∀ i, ∀ᵐ ω ∂P, (f - featureEmbedding μ k hk h) (x i ω) =
      f (x i ω) - inner ℝ (k (x i ω)) h :=
    fun i => (hlaw i).quasiMeasurePreserving.ae hr
  filter_upwards [ae_all_iff.mpr hx] with ω hω
  dsimp only [rhsFluctuation]
  rw [empiricalRepresenter_sub_covariance, map_sub]
  congr 1
  · congr 1
    funext i
    exact (hω i).symm

/-- The full actual `Z_λ` second-moment estimate, with residual `f - S h`.
Only the later spectral choice of `h` and inverse square root is left open. -/
theorem integral_rhsFluctuation_sq_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [MeasurableSpace H] [BorelSpace H]
    {n : ℕ} (hn : 0 < n) (x : Fin n → Ω → X)
    (hlaw : ∀ i, MeasurePreserving (x i) P μ)
    (hindep : Pairwise (fun i j => IndepFun (x i) (x j) P))
    (k : X → H) (hk : MemLp k 2 μ) (f : Lp ℝ 2 μ) (h : H) (R : H →L[ℝ] H)
    {L : ℝ} (hL : ∀ᵐ y ∂μ, ‖R (k y)‖ ^ 2 ≤ L) :
    (∫ ω, ‖R (rhsFluctuation k hk f h (fun i => x i ω))‖ ^ 2 ∂P) ≤
      L / (n : ℝ) * ‖f - featureEmbedding μ k hk h‖ ^ 2 := by
  calc
    _ = ∫ ω, ‖R (empiricalRepresenter (fun i => k (x i ω))
        (fun i => (f - featureEmbedding μ k hk h) (x i ω)) -
        (featureEmbedding μ k hk).adjoint (f - featureEmbedding μ k hk h))‖ ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [rhsFluctuation_eq_residual_ae x hlaw k hk f h] with ω hω
      rw [hω]
    _ ≤ _ := integral_normalized_rhs_sq_le hn x hlaw hindep k hk _ R hL

end KernelSeq
