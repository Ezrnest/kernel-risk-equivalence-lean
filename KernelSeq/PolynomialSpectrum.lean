import KernelSeq.SpectralMoments

/-!
# Polynomial envelopes of the actual covariance spectrum

The hypotheses concern the original eigenvalues themselves, via a bijective
enumeration of their positive singular indices. Effective-dimension and
filter-dimension estimates are conclusions, never fields of a model.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelSeq
noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

theorem prefix_card_le_featureSpectralCount (k : X → H) (hk : MemLp k 2 μ)
    (e : FeatureSpectrumEnumeration k hk) {t : ℝ} (ht : 0 < t) (n : ℕ)
    (hprefix : ∀ j < n, t ≤ enumeratedEigenvalue k hk e j) :
    n ≤ featureSpectralCount k hk t := by
  classical
  let s := (finite_featureSpectrum_above k hk ht).toFinset
  have hsub : (Finset.range n).image e ⊆ s := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have he := hprefix j (Finset.mem_range.mp hj)
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq, enumeratedEigenvalue] using he
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ e.injective, Finset.card_range] at hc
  simpa only [featureSpectralCount,
    Set.ncard_eq_toFinset_card _ (finite_featureSpectrum_above k hk ht), s] using hc

theorem polynomial_lower_covers_prefix {w : ℕ → ℝ} {c β t : ℝ}
    (hc : 0 < c) (hβ : 0 < β) (ht : 0 < t)
    (hlower : ∀ j : ℕ, c * ((j : ℝ) + 1) ^ (-β) ≤ w j)
    (j : ℕ) (hj : (j : ℝ) + 1 ≤ (c / t) ^ (1 / β)) : t ≤ w j := by
  have hj0 : 0 < (j : ℝ) + 1 := by positivity
  have hpow := Real.rpow_le_rpow hj0.le hj hβ.le
  rw [one_div, Real.rpow_inv_rpow (div_pos hc ht).le hβ.ne'] at hpow
  have hmul : t * ((j : ℝ) + 1) ^ β ≤ c := by
    have hh := (le_div_iff₀ ht).mp hpow
    simpa only [mul_comm] using hh
  calc
    t ≤ c / ((j : ℝ) + 1) ^ β :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hj0 _)).mpr hmul
    _ = c * ((j : ℝ) + 1) ^ (-β) := by rw [Real.rpow_neg hj0.le]; ring
    _ ≤ _ := hlower j

/-- The quarter-count inequality gives the genuine variance-dimension lower
bound under a polynomial spectral envelope. -/
theorem featureFilterDimension_ge_polynomial
    (k : X → H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk)
    (φ : ℝ → ℝ) {lam M ρ A c β : ℝ}
    (hlam : 0 < lam) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hc : 0 < c) (hβ : 0 < β)
    (hlower : ∀ j : ℕ, c * ((j : ℝ) + 1) ^ (-β) ≤ enumeratedEigenvalue k hk e j)
    (hlarge : 2 ≤ (c / (lam * ResidualFilter.resolvedScaleFactor ρ A)) ^ (1 / β)) :
    (1 / 8 : ℝ) * (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β) *
      lam ^ (-(1 / β)) ≤ featureFilterDimension k hk φ := by
  have hA := h.constant_nonneg hlam ((norm_nonneg _).trans hM)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  let t := lam * ResidualFilter.resolvedScaleFactor ρ A
  have ht : 0 < t := mul_pos hlam hD
  let U := (c / t) ^ (1 / β)
  have hU0 : 0 ≤ U := Real.rpow_nonneg (div_pos hc ht).le _
  have hcount := prefix_card_le_featureSpectralCount k hk e ht ⌊U⌋₊ (fun j hj => by
    apply polynomial_lower_covers_prefix hc hβ ht hlower
    have hj' : (j : ℝ) + 1 ≤ (⌊U⌋₊ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
    exact hj'.trans (Nat.floor_le hU0))
  have hfloor : U < (⌊U⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one U
  have hcount' : (⌊U⌋₊ : ℝ) ≤ featureSpectralCount k hk t := by exact_mod_cast hcount
  have hQ := quarter_mul_featureSpectralCount_le_filterDimension k hk φ hlam hM hf h
  have hUQ : (1 / 8 : ℝ) * U ≤ featureFilterDimension k hk φ := by
    change (1 / 4 : ℝ) * (featureSpectralCount k hk t : ℝ) ≤ _ at hQ
    change 2 ≤ U at hlarge
    linarith
  have heq : U = (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β) *
      lam ^ (-(1 / β)) := by
    have hdiv : c / t = (c / ResidualFilter.resolvedScaleFactor ρ A) / lam := by
      dsimp only [t]
      field_simp
    dsimp only [U]
    rw [hdiv, Real.div_rpow (div_pos hc hD).le hlam.le, Real.rpow_neg hlam.le]
    ring
  simpa only [heq, mul_assoc] using hUQ

/-- A polynomial spectral upper bound supplies the actual fractional moment
and then the true effective-dimension bound, with a common scalar constant. -/
theorem featureEffectiveDimension_le_polynomial
    (k : X → H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk)
    {lam C β p : ℝ} (hlam : 0 < lam) (hC : 0 ≤ C) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hpβ : 1 < β * p)
    (hupper : ∀ j, enumeratedEigenvalue k hk e j ≤ C * ((j : ℝ) + 1) ^ (-β)) :
    featureEffectiveDimension k hk lam ≤
      (C ^ p * polynomialMomentConstant β p) * lam ^ (-p) := by
  have hw : ∀ j, 0 ≤ enumeratedEigenvalue k hk e j := fun j => (e j).2.le
  have hs := summable_moment_of_polynomial_upper hw hC hp hpβ hupper
  have hsi : Summable (fun i : PredictionSingularIndex (featureEmbedding μ k hk) => i.1.1 ^ p) :=
    e.summable_iff.mp hs
  have hmoment := moment_le_polynomial_constant hw hC hp hpβ hupper
  rw [← featureSpectralMoment_eq_enumerated k hk e p] at hmoment
  exact (featureEffectiveDimension_le_fractional_moment k hk hlam hp hp1 hsi).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg hlam.le (-p)))

end
end KernelSeq
