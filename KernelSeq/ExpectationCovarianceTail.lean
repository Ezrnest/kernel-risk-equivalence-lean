import KernelSeq.ExpectationCovarianceLeaveOneOut
/-!
# Actual fixed-threshold covariance and leave-one-out exponential tails

The genuine locally proved Bernstein theorem supplies every concentration
input. A deterministic intrinsic-log smallness condition is later derived
from original variance compatibility; no retention lower bound is imposed.
-/
open Filter Topology MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
namespace KernelSeq
noncomputable section

/-- An explicit fixed-threshold inversion, uniform over vanishing retention. -/
theorem expectation_fixedThreshold_bernstein_le {m n L r ell : ℝ}
    (hm : 0 ≤ m) (hmn : m ≤ n) (hn : 0 < n) (hL : 0 < L)
    (hr1 : r ≤ 1) (hell : 1 ≤ ell)
    (hsmall : L*ell/n ≤ 1/65536) :
    bernsteinThreshold (m*L*r) (2*L) (ell+n/(65536*L)) ≤ n/8 := by
  let s := ell+n/(65536*L)
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have hLe : L*ell ≤ n/65536 := by
    have hh := (div_le_iff₀ hn).mp hsmall
    nlinarith
  have hz : L*(n/(65536*L)) = n/65536 := by field_simp
  have hLs : L*s ≤ n/32768 := by dsimp only [s]; rw [mul_add, hz]; linarith
  have hvar : m*L*r ≤ n*L :=
    (mul_le_of_le_one_right (mul_nonneg hm hL.le) hr1).trans
      (mul_le_mul_of_nonneg_right hmn hL.le)
  have hv : m*L*r*s ≤ n^2/32768 := by
    calc
      _ ≤ n*L*s := mul_le_mul_of_nonneg_right hvar hs
      _ = n*(L*s) := by ring
      _ ≤ n*(n/32768) := mul_le_mul_of_nonneg_left hLs hn.le
      _ = _ := by ring
  have hroot : Real.sqrt (m*L*r*s) ≤ n/128 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg n]
  change 2*Real.sqrt (m*L*r*s)+2*(2*L)*s ≤ n/8
  nlinarith

variable {X H Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} {P : Measure Ω}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

/-- The actual fixed-quarter bad-design tail. All finite Bernstein inputs are
supplied by the existing proved constructor. -/
theorem actual_bad_design_exponential_tail (k : X → H) (hk : MemLp k 2 μ)
    {lam L : ℝ} (hlam : 0<lam) {n : ℕ} (hn : 0<n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (hind : iIndepFun x P)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hr : 0<featureCovarianceRetention k hk lam)
    (hsmall : L*intrinsicDimensionLog (featureEffectiveDimension k hk lam)
      (featureCovarianceRetention k hk lam)/(n:ℝ) ≤ 1/65536) :
    P {ω | 1/4 < actualCovarianceDeviation k hk lam (fun j => x j ω)} ≤
      ENNReal.ofReal (8*Real.exp (-(n:ℝ)/(65536*L))) := by
  let r := featureCovarianceRetention k hk lam
  let N := featureEffectiveDimension k hk lam
  let ell := intrinsicDimensionLog N r
  have hnR : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hLpos : 0<L := hr.trans_le (by
    rw [← bernsteinFeature_covariance_norm k hk lam]
    exact populationCovariance_norm_le_feature_bound _ (bernsteinFeature_memLp k hk lam) hL)
  have hN : 0≤N := featureEffectiveDimension_nonneg k hk lam hlam
  have hell : 1≤ell := one_le_dimensionLog (div_nonneg hN hr.le)
  let z := (n:ℝ)/(65536*L)
  have hz : 0≤z := by dsimp only [z]; positivity
  have ht := expectation_fixedThreshold_bernstein_le hnR.le le_rfl hnR hLpos
    (featureCovarianceRetention_le_one k hk lam hlam) hell hsmall
  have htail := normalized_covariance_bernstein_tail k hk lam hlam
    (finiteSpectralBernstein_proved _ P) hn x hlaw hind hL hr z hz
  rw [neg_div]
  apply (measure_mono (t := {ω | bernsteinThreshold ((n:ℝ)*L*r) (2*L) (ell+z)/(n:ℝ) <
      actualCovarianceDeviation k hk lam (fun j => x j ω)}) ?_).trans htail
  intro ω hω
  change 1/4 < actualCovarianceDeviation k hk lam (fun j => x j ω) at hω
  have htn : bernsteinThreshold ((n:ℝ)*L*r) (2*L) (ell+z)/(n:ℝ) ≤ 1/8 := by
    exact (div_le_iff₀ hnR).mpr (by simpa only [r, z, div_eq_mul_inv, mul_comm, one_mul] using ht)
  exact htn.trans_lt (by linarith)

/-- The genuine leave-one-out tail, with the original `1/n` normalization.
The one-sample case is an empty event; all larger cases use the actual
independent `succAbove` sample and the proved covariance Bernstein bound. -/
theorem leaveOneOutCovarianceBad_exponential_tail (k : X → H) (hk : MemLp k 2 μ)
    {lam L : ℝ} (hlam : 0<lam) {n : ℕ} (hn : 0<n) (i : Fin n) (x : Fin n → Ω → X)
    (hlaw : ∀ j, MeasurePreserving (x j) P μ) (hind : iIndepFun x P)
    (hL : ∀ᵐ y ∂μ, normalizedLeverage k hk lam y ≤ L)
    (hr : 0<featureCovarianceRetention k hk lam)
    (hsmall : L*intrinsicDimensionLog (featureEffectiveDimension k hk lam)
      (featureCovarianceRetention k hk lam)/(n:ℝ) ≤ 1/65536) :
    P (leaveOneOutCovarianceBad k hk lam i x) ≤
      ENNReal.ofReal (8*Real.exp (-(n:ℝ)/(65536*L))) := by
  classical
  cases n with
  | zero => omega
  | succ m =>
    by_cases hm : m=0
    · subst m
      have hz (ω : Ω) : leaveOneOutCovariance k hk lam i (fun j => x j ω) = 0 := by
        rw [leaveOneOutCovariance_succAbove]
        simp
      have he : leaveOneOutCovarianceBad k hk lam i x = ∅ := by
        ext ω
        simp only [leaveOneOutCovarianceBad, Set.mem_setOf_eq, hz, norm_zero,
          Set.mem_empty_iff_false]
        norm_num
      rw [he, measure_empty]
      exact bot_le
    · have hmpos : 0<m := Nat.pos_of_ne_zero hm
      let u := bernsteinFeature k hk lam
      let hu := bernsteinFeature_memLp k hk lam
      let r := featureCovarianceRetention k hk lam
      let N := featureEffectiveDimension k hk lam
      let ell := intrinsicDimensionLog N r
      let nR : ℝ := (m+1:ℕ)
      let z := nR/(65536*L)
      let t := bernsteinThreshold ((m:ℝ)*L*r) (2*L) (ell+z)
      let xs := fun j : Fin m => x (i.succAbove j)
      have hnR : 0<nR := Nat.cast_pos.mpr hn
      have hmR : 0<(m:ℝ) := Nat.cast_pos.mpr hmpos
      have hLpos : 0<L := hr.trans_le (by
        rw [← bernsteinFeature_covariance_norm k hk lam]
        exact populationCovariance_norm_le_feature_bound u hu hL)
      have hcn : ‖populationCovariance (featureEmbedding μ u hu)‖ = r :=
        bernsteinFeature_covariance_norm k hk lam
      have hv : 0<(m:ℝ)*L*r := by positivity
      have hN : 0≤N := featureEffectiveDimension_nonneg k hk lam hlam
      have hd : 0≤N/r := div_nonneg hN hr.le
      have hell : 1≤ell := one_le_dimensionLog hd
      have hz : 0≤z := by dsimp only [z]; positivity
      have hR : 0≤2*L := by positivity
      have ht : Real.sqrt (((m:ℝ)*L)*‖populationCovariance (featureEmbedding μ u hu)‖)+
          (2*L)/3 ≤ t := by
        rw [hcn]
        exact bernsteinThreshold_admissible hv.le hR (by linarith)
      have htail := infinite_covariance_sum_tail u hu (finiteSpectralBernstein_proved _ P)
        hmpos xs (fun j => hlaw _) (iIndepFun.precomp Fin.succAbove_right_injective hind)
        hL (by rwa [hcn]) t ht
      rw [integral_bernsteinFeature_norm_sq k hk lam hlam, hcn] at htail
      have hexp := intrinsicBernstein_expression_le hd hv hR hz
      have htail' : P {ω | t < ‖∑ j : Fin m, centeredRankOne u hu (xs j ω)‖} ≤
          ENNReal.ofReal (8*Real.exp (-z)) :=
        htail.trans (ENNReal.ofReal_le_ofReal hexp)
      have hmn : (m:ℝ)≤nR := by dsimp only [nR]; push_cast; linarith
      have htbound : t≤nR/8 := expectation_fixedThreshold_bernstein_le hmR.le hmn hnR hLpos
        (featureCovarianceRetention_le_one k hk lam hlam) hell hsmall
      rw [neg_div]
      apply (measure_mono (t := {ω | t < ‖∑ j : Fin m, centeredRankOne u hu (xs j ω)‖}) ?_).trans htail'
      intro ω hω
      have he : ‖leaveOneOutCovariance k hk lam i (fun j => x j ω)‖ =
          ‖∑ j : Fin m, centeredRankOne u hu (xs j ω)‖/nR := by
        rw [leaveOneOutCovariance_succAbove]
        have hmadd : 0≤(m:ℝ)+1 := by positivity
        simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hmadd,
          div_eq_mul_inv, nR, Nat.cast_add, Nat.cast_one, normalizedCovarianceIncrement, u, xs,
          mul_comm]
      change 1/8 < ‖leaveOneOutCovariance k hk lam i (fun j => x j ω)‖ at hω
      rw [he] at hω
      exact htbound.trans_lt (by
        have hh := (lt_div_iff₀ hnR).mp hω
        nlinarith)


end
end KernelSeq
