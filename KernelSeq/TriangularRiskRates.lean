import KernelSeq.TriangularRiskTails
import KernelSeq.UniformGoodBias
import KernelSeq.UniformGoodVariance
import KernelSeq.UniformBadRisk

/-!
# Common deterministic risk envelopes for actual varying rows

The constants depend only on the original common bounds and the positive
noise lower bound. The envelopes vanish on any filter where the original
scalar assumptions hold, including the uniform family filter.
-/

open Filter Topology

namespace KernelSeq
noncomputable section

universe uH uX uΩ
variable {κ ρ A : ℝ}

def triangularGoodEnvelope (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A) (s0 : ℝ) : ℝ :=
  uniformBiasRiskConstant (residualComparisonOrder ρ) ρ A s0 *
    uniformBiasErrorRate (m.L / (m.n : ℝ) + m.cutoff ^ 2 + m.v / m.cutoff ^ 2)
      (m.sourceBalance / m.cutoff ^ 2) +
    uniformVarianceRiskConstant ρ A * (m.compatibility + m.compatibility ^ 2)

def triangularBadEnvelope (m : TriangularRiskModel.{uH, uX, uΩ} κ ρ A) (s0 : ℝ) : ℝ :=
  uniformBadRiskConstant A κ s0 * (1 + m.expectationH) ^ 3 * (1 + m.sourceBalance) *
    Real.exp (-(1 / 65536 : ℝ) * (m.n : ℝ) / m.L)

variable {J : Type*} {l : Filter J}

theorem triangular_good_envelope_tendsto_zero [NeBot l]
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A) (s0 : ℝ)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hc : Tendsto (fun i => (m i).compatibility) l (𝓝 0))
    (hz : Tendsto (fun i => (m i).sourceBalance) l (𝓝 0)) :
    Tendsto (fun i => triangularGoodEnvelope (m i) s0) l (𝓝 0) := by
  obtain ⟨ht, hs⟩ := triangular_good_scalar_limits m hQ hc hz
  have hrate := ((ht.sqrt.add ht).add hs.sqrt).add hs
  simp only [Real.sqrt_zero, add_zero] at hrate
  have hb := hrate.const_mul (uniformBiasRiskConstant (residualComparisonOrder ρ) ρ A s0)
  have hv := (hc.add (hc.pow 2)).const_mul (uniformVarianceRiskConstant ρ A)
  simpa only [triangularGoodEnvelope, uniformBiasErrorRate, mul_zero,
    zero_pow (by norm_num : 2 ≠ 0), add_zero] using hb.add hv

theorem triangular_bad_envelope_tendsto_zero
    (m : J → TriangularRiskModel.{uH, uX, uΩ} κ ρ A) (s0 : ℝ)
    (hQ : ∀ᶠ i in l, 0 < (m i).Q)
    (hz : Tendsto (fun i => (m i).sourceBalance) l (𝓝 0))
    (he : Tendsto (fun i => (m i).expectationScale) l (𝓝 0)) :
    Tendsto (fun i => triangularBadEnvelope (m i) s0) l (𝓝 0) := by
  have ht := triangular_expectation_polynomial_tail m hQ he (p := (3 : ℝ)) (by norm_num)
  simp only [Real.rpow_ofNat] at ht
  have hz' := hz.const_add 1
  simp only [add_zero] at hz'
  have hu := (ht.mul hz').const_mul (uniformBadRiskConstant A κ s0)
  simp only [zero_mul, mul_zero] at hu
  apply hu.congr'
  exact Eventually.of_forall fun i => by unfold triangularBadEnvelope; ring

end
end KernelSeq
