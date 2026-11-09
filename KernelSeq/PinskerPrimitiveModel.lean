import KernelSeq.CanonicalPinskerUpperBound

/-!
# Pinsker applications from the original primitive RKHS assumptions

The auxiliary deterministic model is constructed from the kernel, its
measurability and diagonal bound. An arbitrary old target, regularization or
filter witness is not a public application assumption.
-/

namespace KernelSeq
open MeasureTheory Filter Topology
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H X ℝ]
  (μ : Measure X) [IsProbabilityMeasure μ]
  {κ s : ℝ}
  (hkernel : Measurable (fun p : X × X => rkhsKernel (H := H) p.1 p.2))
  (hκ : 0 ≤ κ) (hdiag : ∀ x, rkhsKernel (H := H) x x ≤ κ^2) (hs : 1 ≤ s)

def pinskerPrimitiveModel : SpectralScaleModel κ (ResidualFilter.pinskerOrder s) (4*(1+s/2)) where
  H := H
  X := X
  μ := μ
  kernel_measurable := hkernel
  kappa_nonneg := hκ
  diagonal_bound := hdiag
  n := 1
  sample_pos := by norm_num
  f := 0
  lam := 1
  lambda_pos := by norm_num
  φ := ResidualFilter.pinsker 1 s
  spectral_filter := ResidualFilter.pinsker_spectralFilter (by norm_num) (zero_le_one.trans hs)
  filter_contract := ResidualFilter.pinsker_contract (by norm_num) hs

/-- The upper-bound corollary with exactly the original primitive model,
source parameters and counting law as public inputs. All finite Gaussian
sampling laws and actual spectrum relabeling are constructed internally. -/
theorem rkhs_gaussian_pinsker_upper_bound
    {I : Type*} {l : Filter I} [NeBot l] {β R σ D : ℝ}
    (hβ : 1 < β) (hR : 0 < R) (hσ : 0 < σ) (hD : 0 < D)
    (hcount : Tendsto
      (fun t => (featureSpectralCount (rkhsFeature (H := H))
        (rkhsFeature_memLp μ hkernel κ hκ hdiag) t : ℝ)/(D*t^(-(1/β))))
      (𝓝[>] 0) (𝓝 1))
    (n : I → ℕ) (hnpos : ∀ i, 0 < n i) (hn : Tendsto (fun i => (n i : ℝ)) l atTop) :
    let b := pinskerPrimitiveModel μ hkernel hκ hdiag hs
    let rows := fun i => canonicalPinskerOracleRiskRow b hs hβ hR hσ hD (n i) (hnpos i)
    (∀ᶠ i in l, BddAbove (Set.range (fun θ => (rows i θ).expectationRisk))) ∧
      Tendsto (fun i => sSup (Set.range (fun θ => (rows i θ).expectationRisk)) /
        pinskerOracleWorstBenchmark b β R σ D (n i)) l (𝓝 1) ∧
      Tendsto (fun i => (n i : ℝ)^pinskerRiskExponent s β *
        sSup (Set.range (fun θ => (rows i θ).expectationRisk))) l
        (𝓝 (pinskerUpperConstant s β R σ D)) :=
  canonical_gaussian_pinsker_sourceBall_upper_bound (pinskerPrimitiveModel μ hkernel hκ hdiag hs)
    hs hβ hR hσ hD hcount n hnpos hn

end
end KernelSeq
