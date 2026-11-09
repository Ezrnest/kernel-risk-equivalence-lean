import KernelSeq.PinskerSpectralSum
import KernelSeq.WeightedACIntegration

/-!
# The complete spectral-sum rule for the actual population spectrum

The spectral-sum rule uses exact counting, weighted
a.e. derivative integrability, and endpoint hypotheses. Summability and both
integral representations are conclusions. The endpoint limits are retained
in this manuscript-facing statement; the signed-Fubini proof actually derives
the integral equality without needing those additional limits.
-/

namespace KernelSeq

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

/-- A stronger generic version of the complete rule: the original two
weighted derivative assumptions already imply the required weighted primitive
integrability and the integral identity. -/
theorem pinsker_spectral_sum_complete {w : ℕ → ℝ}
    (hs : Summable w) (hw : ∀ j, 0 ≤ w j) {γ D η : ℝ}
    (hγ : 0 < γ) (hη : 0 < η)
    (hcount : Tendsto (fun t => t ^ γ * spectralCounting w t) (𝓝[>] 0) (𝓝 D))
    (G : ℝ → ℝ) (hG0 : G 0 = 0)
    (hac : ∀ R, 0 ≤ R → AbsolutelyContinuousOnInterval G 0 R)
    (hnear : IntegrableOn (fun u => u ^ (-γ - η) * |deriv G u|) (Ioc (0 : ℝ) 1))
    (hfar : IntegrableOn (fun u => u ^ (-γ + η) * |deriv G u|) (Ioi (1 : ℝ))) :
    (∀ lam, 0 < lam → Summable (fun j => G (w j / lam))) ∧
      IntegrableOn (fun u => G u * u ^ (-γ - 1)) (Ioi (0 : ℝ)) ∧
      (∫ u in Ioi (0 : ℝ), u ^ (-γ) * deriv G u) =
        γ * ∫ u in Ioi (0 : ℝ), G u * u ^ (-γ - 1) ∧
      Tendsto (fun lam => lam ^ γ * ∑' j, G (w j / lam)) (𝓝[>] 0)
        (𝓝 ((D * γ) * ∫ u in Ioi (0 : ℝ), G u * u ^ (-γ - 1))) := by
  have hi := integrable_weighted_deriv_of_two_weights hη.le hnear hfar
  have hIBP := weighted_ac_integrable_and_integral G hG0 hac hγ hi
  obtain ⟨C, _, hC⟩ := spectralCounting_global_power_bound hs hw hγ.le hcount
  have hsG : ∀ lam, 0 < lam → Summable (fun j => G (w j / lam)) := by
    intro lam hlam
    exact (hasSum_spectral_values_of_integrable_count_deriv hs hw hlam G hG0 hac
      (integrable_count_deriv_of_power_bound hlam hC hi)).summable
  have hlim := pinsker_spectral_sum_tendsto_derivative hs hw hγ hη hcount G hG0 hac hnear hfar
  rw [hIBP.2] at hlim
  exact ⟨hsG, hIBP.1, hIBP.2, by simpa only [mul_assoc] using hlim⟩

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The manuscript's exact spectral-sum rule, with actual covariance
eigenvalues and multiplicities. The original `N(t) ~ D*t^(-1/beta)` is stated
as its ratio limit. There is no spectral-sum, domination or integration-by-
parts certificate among the hypotheses. -/
theorem feature_pinsker_spectral_sum
    (k : X → H) (hk : MemLp k 2 μ)
    (e : ℕ ≃ PredictionSingularIndex (featureEmbedding μ k hk))
    {β D η : ℝ} (hβ : 1 < β) (hD : 0 < D)
    (hη : η ∈ Ioo (0 : ℝ) (min (1 / β) (1 - 1 / β)))
    (hcount : Tendsto
      (fun t => (featureSpectralCount k hk t : ℝ) / (D * t ^ (-(1 / β))))
      (𝓝[>] 0) (𝓝 1))
    (G : ℝ → ℝ) (hG0 : G 0 = 0)
    (hac : ∀ R, 0 ≤ R → AbsolutelyContinuousOnInterval G 0 R)
    (hnear : IntegrableOn (fun u => u ^ (-(1 / β) - η) * |deriv G u|) (Ioc (0 : ℝ) 1))
    (hfar : IntegrableOn (fun u => u ^ (-(1 / β) + η) * |deriv G u|) (Ioi (1 : ℝ)))
    (_hzero : Tendsto (fun u => u ^ (-(1 / β)) * G u) (𝓝[>] 0) (𝓝 0))
    (_hinfty : Tendsto (fun u => u ^ (-(1 / β)) * G u) atTop (𝓝 0)) :
    (∀ lam, 0 < lam → Summable (fun j => G ((e j).1.1 / lam))) ∧
      IntegrableOn (fun u => G u * u ^ (-(1 / β) - 1)) (Ioi (0 : ℝ)) ∧
      (D * ∫ u in Ioi (0 : ℝ), u ^ (-(1 / β)) * deriv G u) =
        (D / β) * ∫ u in Ioi (0 : ℝ), G u * u ^ (-(1 / β) - 1) ∧
      Tendsto (fun lam => lam ^ (1 / β) * ∑' j, G ((e j).1.1 / lam)) (𝓝[>] 0)
        (𝓝 (D * ∫ u in Ioi (0 : ℝ), u ^ (-(1 / β)) * deriv G u)) ∧
      Tendsto (fun lam => lam ^ (1 / β) * ∑' j, G ((e j).1.1 / lam)) (𝓝[>] 0)
        (𝓝 ((D / β) * ∫ u in Ioi (0 : ℝ), G u * u ^ (-(1 / β) - 1))) := by
  have hβ0 : 0 < β := by linarith
  have hγ : 0 < 1 / β := one_div_pos.mpr hβ0
  have hbase := integrable_weighted_deriv_of_two_weights hη.1.le hnear hfar
  have hIBP := weighted_ac_integrable_and_integral G hG0 hac hγ hbase
  have hcountNorm : Tendsto (fun t => t ^ (1 / β) * (featureSpectralCount k hk t : ℝ))
      (𝓝[>] 0) (𝓝 D) :=
    (exact_counting_limit_iff_ratio (fun t => (featureSpectralCount k hk t : ℝ)) hD.ne').mpr hcount
  have hlim := feature_spectral_sum_tendsto_derivative k hk e hγ hη.1
    hcountNorm G hG0 hac hnear hfar
  have hcounts : Tendsto
      (fun t => t ^ (1 / β) * spectralCounting (fun j => (e j).1.1) t)
      (𝓝[>] 0) (𝓝 D) := by
    apply hcountNorm.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [spectralCounting_eq_featureSpectralCount k hk e ht]
  have hs := summable_enumerated_covariance_eigenvalues k hk e
  have hw : ∀ j, 0 ≤ (e j).1.1 := fun j => (e j).2.le
  obtain ⟨C, _, hC⟩ := spectralCounting_global_power_bound hs hw hγ.le hcounts
  have hsG : ∀ lam, 0 < lam → Summable (fun j => G ((e j).1.1 / lam)) := by
    intro lam hlam
    exact (hasSum_spectral_values_of_integrable_count_deriv hs hw hlam G hG0 hac
      (integrable_count_deriv_of_power_bound hlam hC hbase)).summable
  have heq : (D * ∫ u in Ioi (0 : ℝ), u ^ (-(1 / β)) * deriv G u) =
      (D / β) * ∫ u in Ioi (0 : ℝ), G u * u ^ (-(1 / β) - 1) := by
    rw [hIBP.2]
    ring
  exact ⟨hsG, hIBP.1, heq, hlim, heq ▸ hlim⟩

end
end KernelSeq
