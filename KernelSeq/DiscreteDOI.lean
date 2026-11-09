import KernelSeq.HilbertSchmidtIdeal

/-!
# Actual discrete double operator integrals on the HS space

A bounded matrix kernel acts as an actual bounded linear map on genuine HS
columns in two Hilbert bases. This is the pure-point spectral DOI needed for
the compact covariance operators. No Schatten multiplier estimate for p≠2 is
asserted by this construction.
-/

namespace KernelSeq

variable {ι κ H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Entrywise kernel multiplication in the genuine HS column Hilbert space. -/
noncomputable def hsSchurMultiplier (a : HilbertBasis κ ℝ E) (M : κ → ι → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K) :
    HilbertSchmidtColumns ι E →L[ℝ] HilbertSchmidtColumns ι E :=
  lp.mapCLM 2 (fun j => hilbertDiagonal a (fun i => M i j) K hK (fun i => hM i j)) hK
    (fun j => hilbertDiagonal_norm_le a (fun i => M i j) K hK (fun i => hM i j))

omit [CompleteSpace E] in
theorem hsSchurMultiplier_apply (a : HilbertBasis κ ℝ E) (M : κ → ι → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K)
    (c : HilbertSchmidtColumns ι E) (j : ι) :
    hsSchurMultiplier a M K hK hM c j =
      hilbertDiagonal a (fun i => M i j) K hK (fun i => hM i j) (c j) := rfl

omit [CompleteSpace E] in
/-- The exact HS operator norm estimate for bounded kernels. -/
theorem hsSchurMultiplier_norm_le (a : HilbertBasis κ ℝ E) (M : κ → ι → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K) :
    ‖hsSchurMultiplier a M K hK hM‖ ≤ K :=
  lp.norm_mapCLM_le 2 _ hK _

omit [CompleteSpace H] in
/-- The constructed map really multiplies every cross-basis matrix entry. -/
theorem hsSchurMultiplier_coefficient (a : HilbertBasis κ ℝ E) (b : HilbertBasis ι ℝ H)
    (M : κ → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K)
    (c : HilbertSchmidtColumns ι E) (i : κ) (j : ι) :
    inner ℝ (a i) (hilbertSchmidtOperator b (hsSchurMultiplier a M K hK hM c) (b j)) =
      M i j * inner ℝ (a i) (hilbertSchmidtOperator b c (b j)) := by
  rw [hilbertSchmidtOperator_basis, hilbertSchmidtOperator_basis, hsSchurMultiplier_apply]
  simpa only [HilbertBasis.repr_apply_apply] using
    hilbertDiagonal_repr a (fun i => M i j) K hK (fun i => hM i j) (c j) i

omit [CompleteSpace H] in
/-- Actual bounded-operator reconstruction of a discrete DOI from its matrix
coefficients. This is an equality theorem, not an assumed DOI formula. -/
theorem hsSchurMultiplier_represents (a : HilbertBasis κ ℝ E) (b : HilbertBasis ι ℝ H)
    (M : κ → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K)
    (c : HilbertSchmidtColumns ι E) (D : H →L[ℝ] E)
    (hD : ∀ i j, inner ℝ (a i) (D (b j)) =
      M i j * inner ℝ (a i) (hilbertSchmidtOperator b c (b j))) :
    hilbertSchmidtOperator b (hsSchurMultiplier a M K hK hM c) = D := by
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro j
  apply a.repr.injective
  ext i
  simpa only [HilbertBasis.repr_apply_apply] using
    (hsSchurMultiplier_coefficient a b M K hK hM c i j).trans (hD i j).symm

omit [CompleteSpace E] in
/-- Composition is exactly multiplication of the two kernels. -/
theorem hsSchurMultiplier_comp (a : HilbertBasis κ ℝ E) (M N : κ → ι → ℝ)
    (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hM : ∀ i j, ‖M i j‖ ≤ K) (hN : ∀ i j, ‖N i j‖ ≤ L) :
    (hsSchurMultiplier a M K hK hM).comp (hsSchurMultiplier a N L hL hN) =
      hsSchurMultiplier a (fun i j => M i j * N i j) (K * L) (mul_nonneg hK hL)
        (fun i j => (norm_mul_le _ _).trans
          (mul_le_mul (hM i j) (hN i j) (norm_nonneg _) hK)) := by
  ext c j
  apply a.repr.injective
  ext i
  simp only [ContinuousLinearMap.comp_apply, hsSchurMultiplier_apply, hilbertDiagonal_repr]
  ring

end KernelSeq
