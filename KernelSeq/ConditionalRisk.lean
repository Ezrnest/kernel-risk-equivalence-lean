import KernelSeq.NoiseRisk
import KernelSeq.ConditionalNoise
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Conditional prediction risk with random design coefficients

The coefficients and bias are measurable for the design sigma-algebra, while
noise is not assumed independent of its own design. Conditional moments can be
supplied by `observation_pair_conditional_noise_moments_of_positive_variance`.
The bounded-coefficient theorem below proves all product integrability from
actual L² noise and bias, without conditional laws or finite-dimensional Hilbert
spaces. Uniform coefficient bounds are explicit at the finite-sample level.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators MeasureTheory

namespace KernelSeq

variable {Ω E ι : Type*} {m₀ : MeasurableSpace Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
  {P : Measure Ω}

/-- Conditional expectation commutes with a finite pointwise sum. -/
theorem condExp_sum_fun (m : MeasurableSpace Ω) (F : ι → Ω → ℝ)
    (hF : ∀ i, Integrable (F i) P) :
    P[(fun ω => ∑ i, F i ω) | m] =ᵐ[P] (fun ω => ∑ i, (P[F i | m]) ω) := by
  have hs := condExp_finsetSum (s := Finset.univ) (fun i _ => hF i) m
  have hsum : ∑ i, F i = (fun ω => ∑ i, F i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  have hsum' : ∑ i, P[F i | m] = (fun ω => ∑ i, (P[F i | m]) ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hsum, hsum'] at hs
  exact hs

/-- Pointwise expansion with the design-dependent vectors evaluated at a
fixed observation. This is ordinary Hilbert algebra, not a moment certificate. -/
theorem conditional_noise_energy_expansion (ε : ι → ℝ) (a : ι → E) (r : E) :
    ‖r + ∑ i, ε i • a i‖ ^ 2 = ‖r‖ ^ 2 +
      (∑ i, ε i * (2 * inner ℝ r (a i))) +
      ∑ i, ∑ j, (ε i * ε j) * inner ℝ (a i) (a j) := by
  rw [norm_add_sq_real, ← real_inner_self_eq_norm_sq (∑ i, ε i • a i),
    noise_inner_expansion, inner_sum, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_smul_right]
  ring

/-- Conditional energy from explicit integrable scalar products. These are
unconditional integrability premises, not the desired conditional energy. -/
theorem conditional_noise_energy_of_integrable_products [IsProbabilityMeasure P]
    [DecidableEq ι] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (ε : ι → Ω → ℝ) (a : ι → Ω → E) (r : Ω → E) (σ : ℝ)
    (hε : ∀ i, Integrable (ε i) P)
    (hr : StronglyMeasurable[m] r) (ha : ∀ i, StronglyMeasurable[m] (a i))
    (hB : Integrable (fun ω => ‖r ω‖ ^ 2) P)
    (hLin : ∀ i, Integrable (fun ω => ε i ω * (2 * inner ℝ (r ω) (a i ω))) P)
    (hQuad : ∀ i j, Integrable
      (fun ω => (ε i ω * ε j ω) * inner ℝ (a i ω) (a j ω)) P)
    (hProd : ∀ i j, Integrable (fun ω => ε i ω * ε j ω) P)
    (hmean : ∀ i, P[ε i | m] =ᵐ[P] (fun _ => 0))
    (hcov : ∀ i j, P[(fun ω => ε i ω * ε j ω) | m] =ᵐ[P]
      (fun _ => if i = j then σ ^ 2 else 0)) :
    P[(fun ω => ‖r ω + ∑ i, ε i ω • a i ω‖ ^ 2) | m] =ᵐ[P]
      (fun ω => ‖r ω‖ ^ 2 + σ ^ 2 * ∑ i, ‖a i ω‖ ^ 2) := by
  let B := fun ω => ‖r ω‖ ^ 2
  let L := fun i ω => ε i ω * (2 * inner ℝ (r ω) (a i ω))
  let Q := fun i j ω => (ε i ω * ε j ω) * inner ℝ (a i ω) (a j ω)
  have hLzero (i : ι) : P[L i | m] =ᵐ[P] (fun _ => 0) := by
    have hc : StronglyMeasurable[m] (fun ω => 2 * inner ℝ (r ω) (a i ω)) :=
      (hr.inner (𝕜 := ℝ) (ha i)).const_mul 2
    have hpull := condExp_mul_of_stronglyMeasurable_right hc (hLin i) (hε i)
    filter_upwards [hpull, hmean i] with ω hp hz
    simpa only [L, Pi.mul_def, hz, zero_mul] using hp
  have hQmoment (i j : ι) : P[Q i j | m] =ᵐ[P]
      (fun ω => (if i = j then σ ^ 2 else 0) * inner ℝ (a i ω) (a j ω)) := by
    have hc := (ha i).inner (𝕜 := ℝ) (ha j)
    have hpull := condExp_mul_of_stronglyMeasurable_right hc (hQuad i j) (hProd i j)
    filter_upwards [hpull, hcov i j] with ω hp hcω
    simpa only [Q, Pi.mul_def, hcω] using hp
  have hLsum : P[(fun ω => ∑ i, L i ω) | m] =ᵐ[P] (fun _ => 0) := by
    filter_upwards [condExp_sum_fun m L hLin, ae_all_iff.mpr hLzero] with ω hs hz
    simpa only [hz, Finset.sum_const_zero] using hs
  have hQrow (i : ι) : P[(fun ω => ∑ j, Q i j ω) | m] =ᵐ[P]
      (fun ω => σ ^ 2 * ‖a i ω‖ ^ 2) := by
    filter_upwards [condExp_sum_fun m (Q i) (hQuad i), ae_all_iff.mpr (hQmoment i)] with ω hs hq
    rw [hs]
    simp only [hq, ite_mul, zero_mul]
    simp
  have hQsum : P[(fun ω => ∑ i, ∑ j, Q i j ω) | m] =ᵐ[P]
      (fun ω => σ ^ 2 * ∑ i, ‖a i ω‖ ^ 2) := by
    filter_upwards [condExp_sum_fun m (fun i ω => ∑ j, Q i j ω)
      (fun i => integrable_finsetSum _ (fun j _ => hQuad i j)),
      ae_all_iff.mpr hQrow] with ω hs hq
    simpa only [hq, Finset.mul_sum] using hs
  have hLInt : Integrable (fun ω => ∑ i, L i ω) P :=
    integrable_finsetSum _ (fun i _ => hLin i)
  have hQInt : Integrable (fun ω => ∑ i, ∑ j, Q i j ω) P :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hQuad i j))
  have hBCE : P[B | m] = B := condExp_of_stronglyMeasurable hm (hr.norm.pow 2) hB
  have hfirst := condExp_add hB hLInt m
  have hsecond := condExp_add (hB.add hLInt) hQInt m
  simp only [Pi.add_def] at hfirst hsecond
  have henergy : (fun ω => ‖r ω + ∑ i, ε i ω • a i ω‖ ^ 2) =
      (fun ω => B ω + (∑ i, L i ω) + ∑ i, ∑ j, Q i j ω) := by
    funext ω
    exact conditional_noise_energy_expansion (fun i => ε i ω) (fun i => a i ω) (r ω)
  rw [henergy]
  filter_upwards [hfirst, hsecond, hLsum, hQsum] with ω h₁ h₂ hL hQ
  rw [hBCE] at h₁
  dsimp only [B] at h₁
  linarith

/-- Inner products with an almost-everywhere bounded vector preserve L²
integrability of the other vector. -/
theorem memLp_inner_of_bounded_right {r a : Ω → E}
    (hr : MemLp r 2 P) (ha : AEStronglyMeasurable a P) {C : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖a ω‖ ≤ C) :
    MemLp (fun ω => inner ℝ (r ω) (a ω)) 2 P := by
  apply (hr.norm.mul_const C).mono' (hr.1.inner (𝕜 := ℝ) ha)
  filter_upwards [hbound] with ω hω
  exact (norm_inner_le_norm (𝕜 := ℝ) (r ω) (a ω)).trans
    (mul_le_mul_of_nonneg_left hω (norm_nonneg _))

/-- A genuine conditional bias/variance formula with random design-dependent
coefficients. All product and energy integrability is derived from L² bias and
noise and explicit almost-everywhere coefficient bounds. No all-design energy
expectation or conditional law is assumed. -/
theorem conditional_noise_energy_of_bounded_coefficients [IsProbabilityMeasure P]
    [DecidableEq ι] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (ε : ι → Ω → ℝ) (a : ι → Ω → E) (r : Ω → E) (σ : ℝ)
    (hε : ∀ i, MemLp (ε i) 2 P) (hrLp : MemLp r 2 P)
    (hr : StronglyMeasurable[m] r) (ha : ∀ i, StronglyMeasurable[m] (a i))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (habound : ∀ i, ∀ᵐ ω ∂P, ‖a i ω‖ ≤ C i)
    (hmean : ∀ i, P[ε i | m] =ᵐ[P] (fun _ => 0))
    (hcov : ∀ i j, P[(fun ω => ε i ω * ε j ω) | m] =ᵐ[P]
      (fun _ => if i = j then σ ^ 2 else 0)) :
    Integrable (fun ω => ‖r ω + ∑ i, ε i ω • a i ω‖ ^ 2) P ∧
    P[(fun ω => ‖r ω + ∑ i, ε i ω • a i ω‖ ^ 2) | m] =ᵐ[P]
      (fun ω => ‖r ω‖ ^ 2 + σ ^ 2 * ∑ i, ‖a i ω‖ ^ 2) := by
  have hB : Integrable (fun ω => ‖r ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hrLp.1).mp hrLp
  have hameas (i : ι) : AEStronglyMeasurable[m₀] (a i) P :=
    ((ha i).mono hm).aestronglyMeasurable
  have hLin (i : ι) : Integrable (fun ω => ε i ω * (2 * inner ℝ (r ω) (a i ω))) P :=
    (hε i).integrable_mul
      ((memLp_inner_of_bounded_right hrLp (hameas i) (habound i)).const_mul 2)
  have hProd (i j : ι) : Integrable (fun ω => ε i ω * ε j ω) P :=
    (hε i).integrable_mul (hε j)
  have hQuad (i j : ι) : Integrable
      (fun ω => (ε i ω * ε j ω) * inner ℝ (a i ω) (a j ω)) P := by
    apply (hProd i j).mul_bdd ((hameas i).inner (𝕜 := ℝ) (hameas j))
    filter_upwards [habound i, habound j] with ω hi hj
    exact (norm_inner_le_norm (𝕜 := ℝ) (a i ω) (a j ω)).trans
      (mul_le_mul hi hj (norm_nonneg _) (hC i))
  constructor
  · have hsum := (hB.add (integrable_finsetSum Finset.univ (fun i _ => hLin i))).add
      (integrable_finsetSum Finset.univ
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hQuad i j)))
    apply hsum.congr
    exact Eventually.of_forall (fun ω =>
      (conditional_noise_energy_expansion (fun i => ε i ω) (fun i => a i ω) (r ω)).symm)
  · exact conditional_noise_energy_of_integrable_products m hm ε a r σ
      (fun i => (hε i).integrable (by norm_num)) hr ha hB hLin hQuad hProd hmean hcov

/-- Source-model conditional risk: independent full observation pairs and their
own-design first and positive second noise moments imply the actual all-design
energy formula. The noise L² premise is derived, rather than additionally
assumed. Bias L² and design-measurable bounded coefficient vectors remain
explicit finite-sample analytic premises. -/
theorem observation_pair_conditional_risk [IsProbabilityMeasure P]
    [DecidableEq ι] {X : Type*} [MeasurableSpace X]
    (Z : ι → Ω → X × ℝ) (f : X → ℝ) (σ : ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hf : Measurable f) (hσ : 0 < σ)
    (hind : iIndepFun Z P)
    (hmean : ∀ i, P[observationNoise (Z i) f | observationDesignSigma (Z i)] =ᵐ[P]
      (fun _ => 0))
    (hsecond : ∀ i, P[(fun ω => observationNoise (Z i) f ω ^ 2) |
      observationDesignSigma (Z i)] =ᵐ[P] (fun _ => σ ^ 2))
    (a : ι → Ω → E) (r : Ω → E) (hrLp : MemLp r 2 P)
    (hr : StronglyMeasurable[⨆ i, observationDesignSigma (Z i)] r)
    (ha : ∀ i, StronglyMeasurable[⨆ j, observationDesignSigma (Z j)] (a i))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (habound : ∀ i, ∀ᵐ ω ∂P, ‖a i ω‖ ≤ C i) :
    Integrable (fun ω => ‖r ω + ∑ i, observationNoise (Z i) f ω • a i ω‖ ^ 2) P ∧
    P[(fun ω => ‖r ω + ∑ i, observationNoise (Z i) f ω • a i ω‖ ^ 2) |
      ⨆ i, observationDesignSigma (Z i)] =ᵐ[P]
      (fun ω => ‖r ω‖ ^ 2 + σ ^ 2 * ∑ i, ‖a i ω‖ ^ 2) := by
  have hm : (⨆ i, observationDesignSigma (Z i)) ≤ m₀ :=
    iSup_le (fun i => (hZ i).fst.comap_le)
  have hε (i : ι) : MemLp (observationNoise (Z i) f) 2 P :=
    memLp_observationNoise_of_positive_conditional_second_moment
      (Z i) f σ (hZ i) hf hσ (hsecond i)
  obtain ⟨hmeanAll, hcovAll⟩ :=
    observation_pair_conditional_noise_moments_of_positive_variance
      Z f σ hZ hf hσ hind hmean hsecond
  exact conditional_noise_energy_of_bounded_coefficients _ hm
    (fun i => observationNoise (Z i) f) a r σ hε hrLp hr ha C hC habound hmeanAll hcovAll

end KernelSeq
