import KernelSeq.PolynomialSpectrum

/-!
# Eventual polynomial spectral envelopes

The original asymptotic hypothesis concerns sufficiently large spectral
indices. A common threshold and the original kernel norm bound control the
initial prefix. Neither a uniform lower bound on the first eigenvalue nor
a global comparison is imposed as an additional assumption.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace KernelSeq
noncomputable section

def polynomialEnvelopeGlobalConstant (C M β : ℝ) (J : ℕ) : ℝ :=
  C + M * ((J : ℝ) + 1) ^ β

theorem polynomial_upper_global_of_threshold {w : ℕ → ℝ} {C M β : ℝ} (J : ℕ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hβ : 0 ≤ β) (hwM : ∀ j, w j ≤ M)
    (hupper : ∀ j : ℕ, J ≤ j → w j ≤ C * ((j : ℝ) + 1) ^ (-β)) :
    ∀ j : ℕ, w j ≤ polynomialEnvelopeGlobalConstant C M β J * ((j : ℝ) + 1) ^ (-β) := by
  intro j
  have hCM : C ≤ polynomialEnvelopeGlobalConstant C M β J :=
    le_add_of_nonneg_right (mul_nonneg hM (Real.rpow_nonneg (by positivity) _))
  by_cases hj : J ≤ j
  · exact (hupper j hj).trans (mul_le_mul_of_nonneg_right hCM (Real.rpow_nonneg (by positivity) _))
  have hj' : (j : ℝ) + 1 ≤ (J : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (le_of_lt (lt_of_not_ge hj)) 1
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (j : ℝ) + 1) hj' hβ
  have hpj : 0 < ((j : ℝ) + 1) ^ β := Real.rpow_pos_of_pos (by positivity) _
  have hratio : 1 ≤ ((J : ℝ) + 1) ^ β * ((j : ℝ) + 1) ^ (-β) := by
    rw [Real.rpow_neg (by positivity : 0 ≤ (j : ℝ) + 1), ← div_eq_mul_inv]
    exact (one_le_div hpj).mpr hp
  calc
    w j ≤ M := hwM j
    _ ≤ M * (((J : ℝ) + 1) ^ β * ((j : ℝ) + 1) ^ (-β)) :=
      le_mul_of_one_le_right hM hratio
    _ = (M * ((J : ℝ) + 1) ^ β) * ((j : ℝ) + 1) ^ (-β) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (Real.rpow_nonneg (by positivity) _)

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {μ : Measure X} [IsProbabilityMeasure μ]

theorem index_finset_card_le_featureSpectralCount (k : X → H) (hk : MemLp k 2 μ)
    (e : FeatureSpectrumEnumeration k hk) {t : ℝ} (ht : 0 < t) (s : Finset ℕ)
    (hindices : ∀ j ∈ s, t ≤ enumeratedEigenvalue k hk e j) :
    s.card ≤ featureSpectralCount k hk t := by
  classical
  let r := (finite_featureSpectrum_above k hk ht).toFinset
  have hsub : s.image e ⊆ r := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have he := hindices j hj
    simpa only [r, Set.Finite.mem_toFinset, Set.mem_setOf_eq, enumeratedEigenvalue] using he
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ e.injective] at hc
  simpa only [featureSpectralCount,
    Set.ncard_eq_toFinset_card _ (finite_featureSpectrum_above k hk ht), r] using hc

theorem featureFilterDimension_ge_polynomial_threshold
    (k : X → H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk) (J : ℕ)
    (φ : ℝ → ℝ) {lam M ρ A c β : ℝ}
    (hlam : 0 < lam) (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (hc : 0 < c) (hβ : 0 < β)
    (hlower : ∀ j : ℕ, J ≤ j → c * ((j : ℝ) + 1) ^ (-β) ≤ enumeratedEigenvalue k hk e j)
    (hlarge : 2 * ((J : ℝ) + 1) ≤ (c / (lam * ResidualFilter.resolvedScaleFactor ρ A)) ^ (1 / β)) :
    (1 / 8 : ℝ) * (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β) *
      lam ^ (-(1 / β)) ≤ featureFilterDimension k hk φ := by
  classical
  have hA := h.constant_nonneg hlam ((norm_nonneg _).trans hM)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  let t := lam * ResidualFilter.resolvedScaleFactor ρ A
  have ht : 0 < t := mul_pos hlam hD
  let U := (c / t) ^ (1 / β)
  have hU0 : 0 ≤ U := Real.rpow_nonneg (div_pos hc ht).le _
  have hlarge' : 2 * ((J : ℝ) + 1) ≤ U := hlarge
  have hJU : J ≤ ⌊U⌋₊ := Nat.le_floor (by linarith)
  have hfloor : U < (⌊U⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one U
  have hcount := index_finset_card_le_featureSpectralCount k hk e ht (Finset.Ico J ⌊U⌋₊) (by
    intro j hj
    obtain ⟨hjJ, hjU⟩ := Finset.mem_Ico.mp hj
    have hj' : (j : ℝ) + 1 ≤ (⌊U⌋₊ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hjU
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (j : ℝ) + 1)
      (hj'.trans (Nat.floor_le hU0)) hβ.le
    dsimp only [U] at hpow
    rw [one_div, Real.rpow_inv_rpow (div_pos hc ht).le hβ.ne'] at hpow
    have hmul : t * ((j : ℝ) + 1) ^ β ≤ c := by
      simpa only [mul_comm] using (le_div_iff₀ ht).mp hpow
    calc
      t ≤ c / ((j : ℝ) + 1) ^ β :=
        (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr hmul
      _ = c * ((j : ℝ) + 1) ^ (-β) := by rw [Real.rpow_neg (by positivity : 0 ≤ (j : ℝ) + 1)]; ring
      _ ≤ _ := hlower j hjJ)
  rw [Nat.card_Ico] at hcount
  have hcount' : (⌊U⌋₊ : ℝ) - (J : ℝ) ≤ featureSpectralCount k hk t := by
    rw [← Nat.cast_sub hJU]
    exact_mod_cast hcount
  have hQ := quarter_mul_featureSpectralCount_le_filterDimension k hk φ hlam hM hf h
  change (1 / 4 : ℝ) * (featureSpectralCount k hk t : ℝ) ≤ _ at hQ
  have hUQ : (1 / 8 : ℝ) * U ≤ featureFilterDimension k hk φ := by linarith
  have heq : U = (c / ResidualFilter.resolvedScaleFactor ρ A) ^ (1 / β) * lam ^ (-(1 / β)) := by
    have hdiv : c / t = (c / ResidualFilter.resolvedScaleFactor ρ A) / lam := by
      dsimp only [t]
      field_simp
    dsimp only [U]
    rw [hdiv, Real.div_rpow (div_pos hc hD).le hlam.le, Real.rpow_neg hlam.le]
    ring
  simpa only [heq, mul_assoc] using hUQ

theorem featureEffectiveDimension_le_polynomial_threshold
    (k : X → H) (hk : MemLp k 2 μ) (e : FeatureSpectrumEnumeration k hk) (J : ℕ)
    {lam C M β p : ℝ} (hlam : 0 < lam) (hC : 0 ≤ C)
    (hM : ‖populationCovariance (featureEmbedding μ k hk)‖ ≤ M)
    (hβ : 0 ≤ β) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hpβ : 1 < β * p)
    (hupper : ∀ j : ℕ, J ≤ j → enumeratedEigenvalue k hk e j ≤ C * ((j : ℝ) + 1) ^ (-β)) :
    featureEffectiveDimension k hk lam ≤
      (polynomialEnvelopeGlobalConstant C M β J ^ p * polynomialMomentConstant β p) * lam ^ (-p) := by
  have hMn : 0 ≤ M := (norm_nonneg _).trans hM
  have hglobal := polynomial_upper_global_of_threshold J hC hMn hβ
    (fun j => (featureCovarianceEigenvalue_mem k hk hM (e j).1).2) hupper
  have hCg : 0 ≤ polynomialEnvelopeGlobalConstant C M β J := by
    unfold polynomialEnvelopeGlobalConstant
    positivity
  exact featureEffectiveDimension_le_polynomial k hk e hlam hCg hp hp1 hpβ hglobal

end
end KernelSeq
