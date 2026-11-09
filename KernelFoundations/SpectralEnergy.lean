import KernelFoundations.CompactCalculus

/-!
# Parseval and spectral multiplier energy
-/

namespace KernelFoundations

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Square summability is derived from the actual Hilbert-basis coefficients. -/
theorem hilbertBasis_coefficients_sq_summable (b : HilbertBasis ι ℝ H) (f : H) :
    Summable (fun i => b.repr f i ^ 2) := by
  apply (b.summable_inner_mul_inner f f).congr
  intro i
  rw [b.repr_apply_apply, real_inner_comm f (b i), pow_two]

/-- Parseval, including arbitrary infinite or empty basis index sets. -/
theorem hilbertBasis_norm_sq_eq_tsum (b : HilbertBasis ι ℝ H) (f : H) :
    ‖f‖ ^ 2 = ∑' i, b.repr f i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.tsum_inner_mul_inner f f]
  apply tsum_congr
  intro i
  rw [b.repr_apply_apply, real_inner_comm f (b i), pow_two]

variable [CompleteSpace H]

/-- The spectral multiplier's norm is its true weighted coefficient energy. -/
theorem compactSpectralMultiplier_norm_sq_eq_tsum (T : H →L[ℝ] H)
    (hc : IsCompactOperator T) (hp : T.IsPositive) (φ : ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ t ∈ Set.Icc (0 : ℝ) ‖T‖, |φ t| ≤ K) (f : H) :
    ‖compactSpectralMultiplier T hc hp φ K hK hφ f‖ ^ 2 =
      ∑' i : CompactSpectralIndex T,
        φ i.1 ^ 2 * (compactEigenbasis T hc hp.isSymmetric).repr f i ^ 2 := by
  rw [hilbertBasis_norm_sq_eq_tsum (compactEigenbasis T hc hp.isSymmetric)]
  simp_rw [compactSpectralMultiplier_repr, mul_pow]


end KernelFoundations
