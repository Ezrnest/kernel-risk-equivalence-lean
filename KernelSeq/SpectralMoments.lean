import KernelSeq.SpectralCounting
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual fractional spectral moments

Polynomial and exponential spectrum assumptions will supply these moments
internally. The moment bound is a quantitative tool for verifying the original
three scales; it does not replace the spectrum assumptions in an application.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelSeq
noncomputable section

/-- A regularized weight is bounded by every fractional power with exponent
in `(0,1]`, including the zero spectral endpoint. -/
theorem regularized_weight_le_fractional_power {t lam p : ℝ}
    (ht : 0 ≤ t) (hlam : 0 < lam) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    t / (t + lam) ≤ lam ^ (-p) * t ^ p := by
  have hw := ResidualFilter.regularized_weight_mem hlam ht
  have hdiv : t / (t + lam) ≤ t / lam :=
    div_le_div_of_nonneg_left ht hlam (by linarith)
  calc
    _ ≤ (t / (t + lam)) ^ p := Real.self_le_rpow_of_le_one hw.1 hw.2 hp1
    _ ≤ (t / lam) ^ p := Real.rpow_le_rpow hw.1 hdiv hp
    _ = _ := by rw [Real.div_rpow ht hlam.le, Real.rpow_neg hlam.le]; ring

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

def featureSpectralMoment (k : X → H) (hk : MemLp k 2 μ) (p : ℝ) : ℝ :=
  ∑' i : PredictionSingularIndex (featureEmbedding μ k hk), i.1.1 ^ p

omit [TopologicalSpace.SeparableSpace H] in
theorem featureEffectiveDimension_eq_positive_sequence
    (k : X → H) (hk : MemLp k 2 μ) (lam : ℝ) :
    featureEffectiveDimension k hk lam =
      ∑' i : PredictionSingularIndex (featureEmbedding μ k hk), i.1.1 / (i.1.1 + lam) := by
  unfold featureEffectiveDimension
  symm
  apply tsum_subtype_eq_of_support_subset
    (s := {i : FeatureCovarianceIndex k hk | 0 < i.1})
    (f := fun i : FeatureCovarianceIndex k hk => i.1 / (i.1 + lam))
  intro i hi
  have ht := compactEigenvalue_nonneg _ (populationCovariance_feature_isCompact μ k hk)
    (populationCovariance_isPositive (featureEmbedding μ k hk)) i
  by_contra hnot
  have hz : i.1 = 0 := le_antisymm (le_of_not_gt hnot) ht
  exact hi (by simp only [hz, zero_div])

theorem featureEffectiveDimension_le_fractional_moment
    (k : X → H) (hk : MemLp k 2 μ) {lam p : ℝ} (hlam : 0 < lam)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsum : Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) => i.1.1 ^ p)) :
    featureEffectiveDimension k hk lam ≤ lam ^ (-p) * featureSpectralMoment k hk p := by
  rw [featureEffectiveDimension_eq_positive_sequence]
  have hs : Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) =>
      i.1.1 / (i.1.1 + lam)) :=
    (summable_featureEffectiveDimension k hk lam hlam).subtype _
  have hle := hs.tsum_le_tsum (fun i => regularized_weight_le_fractional_power i.2.le hlam hp hp1)
    (hsum.mul_left (lam ^ (-p)))
  simpa only [tsum_mul_left, featureSpectralMoment] using hle

/-- An enumeration is a relabeling of the actual positive spectrum, including
every multiplicity; it is not a freely supplied surrogate eigenvalue sequence. -/
abbrev FeatureSpectrumEnumeration (k : X → H) (hk : MemLp k 2 μ) :=
  ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk)

def enumeratedEigenvalue (k : X → H) (hk : MemLp k 2 μ)
    (e : FeatureSpectrumEnumeration k hk) (j : ℕ) : ℝ := (e j).1.1

omit [TopologicalSpace.SeparableSpace H] [IsProbabilityMeasure μ] in
theorem featureSpectralMoment_eq_enumerated
    (k : X → H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk) (p : ℝ) :
    featureSpectralMoment k hk p = ∑' j : ℕ, enumeratedEigenvalue k hk e j ^ p :=
  (e.tsum_eq (fun i => i.1.1 ^ p)).symm

/-- The genuine summable p-series constant used for a polynomial upper
spectral envelope. It is independent of the actual model and target. -/
def polynomialMomentConstant (β p : ℝ) : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) ^ (-β * p)

theorem summable_polynomial_moment {β p : ℝ} (hpβ : 1 < β * p) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-β * p)) := by
  have hs : Summable (fun j : ℕ => (j : ℝ) ^ (-β * p)) :=
    Real.summable_nat_rpow.mpr (by nlinarith)
  simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs

private theorem polynomial_envelope_rpow {C β p : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    (C * ((j : ℝ) + 1) ^ (-β)) ^ p = C ^ p * ((j : ℝ) + 1) ^ (-β * p) := by
  rw [Real.mul_rpow hC (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_mul (by positivity : 0 ≤ (j : ℝ) + 1)]

theorem summable_moment_of_polynomial_upper {w : ℕ → ℝ} {C β p : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hC : 0 ≤ C) (hp : 0 ≤ p) (hpβ : 1 < β * p)
    (hupper : ∀ j, w j ≤ C * ((j : ℝ) + 1) ^ (-β)) :
    Summable (fun j => w j ^ p) := by
  apply ((summable_polynomial_moment hpβ).mul_left (C ^ p)).of_nonneg_of_le
    (fun j => Real.rpow_nonneg (hw j) _)
  intro j
  have hle := Real.rpow_le_rpow (hw j) (hupper j) hp
  rw [polynomial_envelope_rpow hC j] at hle
  exact hle

theorem moment_le_polynomial_constant {w : ℕ → ℝ} {C β p : ℝ}
    (hw : ∀ j, 0 ≤ w j) (hC : 0 ≤ C) (hp : 0 ≤ p) (hpβ : 1 < β * p)
    (hupper : ∀ j, w j ≤ C * ((j : ℝ) + 1) ^ (-β)) :
    (∑' j, w j ^ p) ≤ C ^ p * polynomialMomentConstant β p := by
  have hpoint (j : ℕ) : w j ^ p ≤ C ^ p * ((j : ℝ) + 1) ^ (-β * p) := by
    rw [← polynomial_envelope_rpow hC j]
    exact Real.rpow_le_rpow (hw j) (hupper j) hp
  have hle := (summable_moment_of_polynomial_upper hw hC hp hpβ hupper).tsum_le_tsum
    hpoint ((summable_polynomial_moment hpβ).mul_left (C ^ p))
  simpa only [tsum_mul_left, polynomialMomentConstant] using hle

end
end KernelSeq
