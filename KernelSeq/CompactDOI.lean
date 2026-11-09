import KernelSeq.DiscreteDOI
import KernelSeq.LipschitzHS

/-!
# The actual compact pure-point Birman--Solomyak identity

A bounded Lipschitz real profile acts by the actual compact spectral calculus.
Its divided-difference kernel defines an actual bounded map on the genuine
Hilbert--Schmidt column space. Applying that map to actual columns of `T-U`
reconstructs `f(T)-f(U)`, with its HS norm bounded by the scalar Lipschitz
constant. No DOI identity or HS existence for the output is a premise.

This is the positive compact real pure-point case; it asserts neither a general
spectral-measure DOI theorem nor Schatten bounds for `p ≠ 2`. Basis indices
may be arbitrary, and neither the ambient Hilbert space nor any `L²` space is
assumed separable.
-/

namespace KernelSeq

/-- The zero diagonal is harmless in the Birman--Solomyak application: the
corresponding matrix coefficients of the perturbation vanish. -/
noncomputable def dividedDifference (f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  if s = t then 0 else (f s - f t) / (s - t)

/-- The exact scalar identity includes the equal-spectral-value branch. -/
theorem dividedDifference_mul_sub (f : ℝ → ℝ) (s t : ℝ) :
    dividedDifference f s t * (s - t) = f s - f t := by
  classical
  by_cases h : s = t
  · simp [dividedDifference, h]
  · rw [dividedDifference, if_neg h, div_mul_cancel₀ _ (sub_ne_zero.mpr h)]

/-- A scalar Lipschitz bound gives exactly the divided-difference bound. -/
theorem dividedDifference_norm_le {f : ℝ → ℝ} {s t L : ℝ} (hL : 0 ≤ L)
    (hf : |f s - f t| ≤ L * |s - t|) :
    ‖dividedDifference f s t‖ ≤ L := by
  classical
  by_cases h : s = t
  · simp only [dividedDifference, if_pos h, norm_zero]
    exact hL
  · rw [dividedDifference, if_neg h, Real.norm_eq_abs, abs_div]
    exact (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr h))).mpr hf

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section Spectral

variable (T U : H →L[ℝ] H) (hcT : IsCompactOperator T) (hcU : IsCompactOperator U)
  (hpT : T.IsPositive) (hpU : U.IsPositive)

include hcT hpT in
/-- Every selected spectral value lies in a common nonnegative interval. -/
theorem compactEigenvalue_mem_common_interval {M : ℝ} (hMT : ‖T‖ ≤ M)
    (i : CompactSpectralIndex T) : i.1 ∈ Set.Icc (0 : ℝ) M :=
  ⟨compactEigenvalue_nonneg T hcT hpT i,
    ((le_abs_self i.1).trans (compactEigenvalue_norm_le T hcT hpT.isSymmetric i)).trans hMT⟩

/-- The actual difference of two bounded compact spectral profiles, with one
common scalar bound on their common spectral interval. -/
noncomputable def compactProfileDifference (f : ℝ → ℝ) {M : ℝ}
    (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) M, |f t| ≤ K) : H →L[ℝ] H :=
  compactSpectralMultiplier T hcT hpT f K hK (fun t ht => hf t ⟨ht.1, ht.2.trans hMT⟩) -
    compactSpectralMultiplier U hcU hpU f K hK (fun t ht => hf t ⟨ht.1, ht.2.trans hMU⟩)

/-- Exact cross-basis coefficients of the actual spectral-profile difference. -/
theorem compactProfileDifference_cross_entry (f : ℝ → ℝ) {M : ℝ}
    (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) M, |f t| ≤ K)
    (i : CompactSpectralIndex T) (j : CompactSpectralIndex U) :
    inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
      (compactProfileDifference T U hcT hcU hpT hpU f hMT hMU K hK hf
        (compactEigenbasis U hcU hpU.isSymmetric j)) =
      (f i.1 - f j.1) *
        inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i) (compactEigenbasis U hcU hpU.isSymmetric j) := by
  have hT := compactSpectralMultiplier_repr T hcT hpT f K hK
    (fun t ht => hf t ⟨ht.1, ht.2.trans hMT⟩) (compactEigenbasis U hcU hpU.isSymmetric j) i
  simp only [HilbertBasis.repr_apply_apply] at hT
  rw [compactProfileDifference, sub_apply, inner_sub_right, hT,
    compactSpectralMultiplier_eigen U hcU hpU f K hK
      (fun t ht => hf t ⟨ht.1, ht.2.trans hMU⟩) (compactEigenbasis_eigen U hcU hpU.isSymmetric j),
    inner_smul_right]
  ring

/-- The actual perturbation coefficients vanish whenever the two selected
spectral values agree, independently of the overlap of their eigenspaces. -/
theorem compactDifference_cross_entry (i : CompactSpectralIndex T) (j : CompactSpectralIndex U) :
    inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
      ((T - U) (compactEigenbasis U hcU hpU.isSymmetric j)) =
      (i.1 - j.1) *
        inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i) (compactEigenbasis U hcU hpU.isSymmetric j) := by
  have hT := compactEigenbasis_repr_apply T hcT hpT.isSymmetric
    (compactEigenbasis U hcU hpU.isSymmetric j) i
  simp only [HilbertBasis.repr_apply_apply] at hT
  rw [sub_apply, inner_sub_right, hT, compactEigenbasis_eigen U hcU hpU.isSymmetric j, inner_smul_right]
  ring

/-- The actual pure-point divided-difference kernel. -/
noncomputable def compactDividedDifferenceKernel (f : ℝ → ℝ)
    (i : CompactSpectralIndex T) (j : CompactSpectralIndex U) : ℝ :=
  dividedDifference f i.1 j.1

include hcT hcU hpT hpU in
/-- The spectral DOI kernel has multiplier norm bounded by the common scalar
Lipschitz constant. -/
theorem compactDividedDifferenceKernel_norm_le (f : ℝ → ℝ) {M L : ℝ}
    (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Set.Icc (0 : ℝ) M, ∀ t ∈ Set.Icc (0 : ℝ) M,
      |f s - f t| ≤ L * |s - t|)
    (i : CompactSpectralIndex T) (j : CompactSpectralIndex U) :
    ‖compactDividedDifferenceKernel T U f i j‖ ≤ L :=
  dividedDifference_norm_le hL (hLip _
    (compactEigenvalue_mem_common_interval T hcT hpT hMT i) _
    (compactEigenvalue_mem_common_interval U hcU hpU hMU j))

/-- The actual Birman--Solomyak DOI on the HS space in two compact eigenbases. -/
noncomputable def compactBirmanSolomyakDOI (f : ℝ → ℝ) {M L : ℝ}
    (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Set.Icc (0 : ℝ) M, ∀ t ∈ Set.Icc (0 : ℝ) M,
      |f s - f t| ≤ L * |s - t|) :
    HilbertSchmidtColumns (CompactSpectralIndex U) H →L[ℝ]
      HilbertSchmidtColumns (CompactSpectralIndex U) H :=
  hsSchurMultiplier (compactEigenbasis T hcT hpT.isSymmetric)
    (compactDividedDifferenceKernel T U f) L hL
    (compactDividedDifferenceKernel_norm_le T U hcT hcU hpT hpU f hMT hMU hL hLip)

/-- The constructed DOI obeys its actual HS operator-norm estimate. -/
theorem compactBirmanSolomyakDOI_norm_le (f : ℝ → ℝ) {M L : ℝ}
    (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Set.Icc (0 : ℝ) M, ∀ t ∈ Set.Icc (0 : ℝ) M,
      |f s - f t| ≤ L * |s - t|) :
    ‖compactBirmanSolomyakDOI T U hcT hcU hpT hpU f hMT hMU hL hLip‖ ≤ L :=
  hsSchurMultiplier_norm_le _ _ _ _ _

/-- The actual compact pure-point Birman--Solomyak identity. The only HS
premise is that the input columns reconstruct the actual perturbation `T-U`;
the output is constructed, not supplied by a DOI or existence certificate. -/
theorem compactBirmanSolomyakDOI_represents (f : ℝ → ℝ) {M L : ℝ}
    (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Set.Icc (0 : ℝ) M, ∀ t ∈ Set.Icc (0 : ℝ) M,
      |f s - f t| ≤ L * |s - t|)
    (K : ℝ) (hK : 0 ≤ K) (hf : ∀ t ∈ Set.Icc (0 : ℝ) M, |f t| ≤ K)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H)
    (hc : hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) c = T - U) :
    hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric)
      (compactBirmanSolomyakDOI T U hcT hcU hpT hpU f hMT hMU hL hLip c) =
      compactProfileDifference T U hcT hcU hpT hpU f hMT hMU K hK hf := by
  apply hsSchurMultiplier_represents
  intro i j
  rw [hc, compactProfileDifference_cross_entry T U hcT hcU hpT hpU f hMT hMU K hK hf,
    compactDifference_cross_entry T U hcT hcU hpT hpU]
  change (f i.1 - f j.1) * _ = dividedDifference f i.1 j.1 * ((i.1 - j.1) * _)
  rw [← mul_assoc, dividedDifference_mul_sub]

/-- Applying the actual DOI gives actual HS columns of `f(T)-f(U)` with the
expected Lipschitz estimate, without assuming those output columns exist. -/
theorem compactBirmanSolomyakDOI_apply_norm_le (f : ℝ → ℝ) {M L : ℝ}
    (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Set.Icc (0 : ℝ) M, ∀ t ∈ Set.Icc (0 : ℝ) M,
      |f s - f t| ≤ L * |s - t|)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H) :
    ‖compactBirmanSolomyakDOI T U hcT hcU hpT hpU f hMT hMU hL hLip c‖ ≤ L * ‖c‖ :=
  (compactBirmanSolomyakDOI T U hcT hcU hpT hpU f hMT hMU hL hLip).le_of_opNorm_le
    (compactBirmanSolomyakDOI_norm_le T U hcT hcU hpT hpU f hMT hMU hL hLip) c

/-- The scalar kernel for a perturbation normalized by the two regularized
inverse square roots. -/
noncomputable def normalizedDividedDifference (f : ℝ → ℝ) (lam s t : ℝ) : ℝ :=
  dividedDifference f s t * (Real.sqrt (s + lam) * Real.sqrt (t + lam))

/-- Exact normalized scalar identity, including equal spectral values. -/
theorem normalizedDividedDifference_mul_quotient (f : ℝ → ℝ) {lam s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hlam : 0 < lam) :
    normalizedDividedDifference f lam s t *
      ((s - t) / (Real.sqrt (s + lam) * Real.sqrt (t + lam))) = f s - f t := by
  have hd : 0 < Real.sqrt (s + lam) * Real.sqrt (t + lam) :=
    mul_pos (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hs hlam))
      (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos ht hlam))
  unfold normalizedDividedDifference
  calc
    _ = (dividedDifference f s t * (s - t)) *
        ((Real.sqrt (s + lam) * Real.sqrt (t + lam)) /
          (Real.sqrt (s + lam) * Real.sqrt (t + lam))) := by ring
    _ = _ := by rw [div_self hd.ne', mul_one, dividedDifference_mul_sub]

/-- The normalized scalar Lipschitz estimate proves the actual normalized
multiplier bound, without a reciprocal gap assumption. -/
theorem normalizedDividedDifference_norm_le {f : ℝ → ℝ} {lam s t L : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hlam : 0 < lam) (hL : 0 ≤ L)
    (hf : |f s - f t| ≤ L *
      (|s - t| / (Real.sqrt (s + lam) * Real.sqrt (t + lam)))) :
    ‖normalizedDividedDifference f lam s t‖ ≤ L := by
  classical
  have hd : 0 < Real.sqrt (s + lam) * Real.sqrt (t + lam) :=
    mul_pos (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hs hlam))
      (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos ht hlam))
  by_cases he : s = t
  · simpa only [normalizedDividedDifference, dividedDifference, if_pos he, zero_mul, norm_zero] using hL
  · have hdelta : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr he)
    have hmul : |f s - f t| * (Real.sqrt (s + lam) * Real.sqrt (t + lam)) ≤ L * |s - t| :=
      (le_div_iff₀ hd).mp (by simpa only [mul_div_assoc] using hf)
    rw [normalizedDividedDifference, dividedDifference, if_neg he, Real.norm_eq_abs,
      abs_mul, abs_div, abs_of_pos hd]
    calc
      _ = (|f s - f t| * (Real.sqrt (s + lam) * Real.sqrt (t + lam))) / |s - t| := by ring
      _ ≤ L := (div_le_iff₀ hdelta).mpr hmul

/-- The normalized divided-difference kernel on the actual two spectral bases. -/
noncomputable def compactNormalizedDividedDifferenceKernel (f : ℝ → ℝ) (lam : ℝ)
    (i : CompactSpectralIndex T) (j : CompactSpectralIndex U) : ℝ :=
  normalizedDividedDifference f lam i.1 j.1

include hcT hcU hpT hpU in
/-- Uniform bound for the actual normalized spectral kernel. -/
theorem compactNormalizedDividedDifferenceKernel_norm_le (f : ℝ → ℝ) {lam M L : ℝ}
    (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Set.Icc (0 : ℝ) M, ∀ t ∈ Set.Icc (0 : ℝ) M,
      |f s - f t| ≤ L * (|s - t| / (Real.sqrt (s + lam) * Real.sqrt (t + lam))))
    (i : CompactSpectralIndex T) (j : CompactSpectralIndex U) :
    ‖compactNormalizedDividedDifferenceKernel T U f lam i j‖ ≤ L :=
  normalizedDividedDifference_norm_le (compactEigenvalue_nonneg T hcT hpT i)
    (compactEigenvalue_nonneg U hcU hpU j) hlam hL (hLip _
      (compactEigenvalue_mem_common_interval T hcT hpT hMT i) _
      (compactEigenvalue_mem_common_interval U hcU hpU hMU j))

/-- An actual normalized DOI acting on genuine HS columns. -/
noncomputable def compactNormalizedDOI (f : ℝ → ℝ) {lam M L : ℝ}
    (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Set.Icc (0 : ℝ) M, ∀ t ∈ Set.Icc (0 : ℝ) M,
      |f s - f t| ≤ L * (|s - t| / (Real.sqrt (s + lam) * Real.sqrt (t + lam)))) :
    HilbertSchmidtColumns (CompactSpectralIndex U) H →L[ℝ]
      HilbertSchmidtColumns (CompactSpectralIndex U) H :=
  hsSchurMultiplier (compactEigenbasis T hcT hpT.isSymmetric)
    (compactNormalizedDividedDifferenceKernel T U f lam) L hL
    (compactNormalizedDividedDifferenceKernel_norm_le T U hcT hcU hpT hpU f hlam hMT hMU hL hLip)

/-- The normalized DOI really reconstructs the actual spectral-profile
 difference from the actual mixed perturbation. The perturbation orientation
is `R_T (T-U) R_U`, matching its cross-basis entries. -/
theorem compactNormalizedDOI_represents (f : ℝ → ℝ) {lam M L : ℝ}
    (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Set.Icc (0 : ℝ) M, ∀ t ∈ Set.Icc (0 : ℝ) M,
      |f s - f t| ≤ L * (|s - t| / (Real.sqrt (s + lam) * Real.sqrt (t + lam))))
    (K : ℝ) (hK : 0 ≤ K) (hf : ∀ t ∈ Set.Icc (0 : ℝ) M, |f t| ≤ K)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H)
    (hc : hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) c =
      compactMixedDifference T U hcT hcU hpT hpU lam) :
    hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric)
      (compactNormalizedDOI T U hcT hcU hpT hpU f hlam hMT hMU hL hLip c) =
      compactProfileDifference T U hcT hcU hpT hpU f hMT hMU K hK hf := by
  apply hsSchurMultiplier_represents
  intro i j
  rw [hc, compactProfileDifference_cross_entry T U hcT hcU hpT hpU f hMT hMU K hK hf,
    compactMixedDifference_cross_entry T U hcT hcU hpT hpU lam hlam]
  change (f i.1 - f j.1) * _ = normalizedDividedDifference f lam i.1 j.1 *
    (((i.1 - j.1) / (Real.sqrt (i.1 + lam) * Real.sqrt (j.1 + lam))) * _)
  rw [← mul_assoc, normalizedDividedDifference_mul_quotient f
    (compactEigenvalue_nonneg T hcT hpT i) (compactEigenvalue_nonneg U hcU hpU j) hlam]

/-- Exact HS bound for the normalized DOI output. -/
theorem compactNormalizedDOI_apply_norm_le (f : ℝ → ℝ) {lam M L : ℝ}
    (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hL : 0 ≤ L)
    (hLip : ∀ s ∈ Set.Icc (0 : ℝ) M, ∀ t ∈ Set.Icc (0 : ℝ) M,
      |f s - f t| ≤ L * (|s - t| / (Real.sqrt (s + lam) * Real.sqrt (t + lam))))
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H) :
    ‖compactNormalizedDOI T U hcT hcU hpT hpU f hlam hMT hMU hL hLip c‖ ≤ L * ‖c‖ :=
  (compactNormalizedDOI T U hcT hcU hpT hpU f hlam hMT hMU hL hLip).le_of_opNorm_le
    (hsSchurMultiplier_norm_le _ _ _ _ _) c

/-- The manuscript's normalized shrinkage DOI is an actual bounded linear
operator on the HS space, with the original residual-only filter contract. -/
noncomputable def compactShrinkageDOI (φ : ℝ → ℝ) {lam M ρ A : ℝ}
    (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ) :
    HilbertSchmidtColumns (CompactSpectralIndex U) H →L[ℝ]
      HilbertSchmidtColumns (CompactSpectralIndex U) H :=
  compactNormalizedDOI T U hcT hcU hpT hpU (ResidualFilter.shrinkage φ) hlam hMT hMU
    (mul_nonneg (h.constant_nonneg hlam ((norm_nonneg T).trans hMT)) (by linarith [h.rho_pos]))
    (fun _ hs _ ht => h.shrinkage_normalized_difference_le hlam hs ht)

/-- The actual normalized shrinkage DOI reconstructs `q(T)-q(U)`. The
input represents the actual mixed perturbation; output existence and the DOI
identity are conclusions of the construction. -/
theorem compactShrinkageDOI_represents (φ : ℝ → ℝ) {lam M ρ A : ℝ}
    (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H)
    (hc : hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) c =
      compactMixedDifference T U hcT hcU hpT hpU lam) :
    hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric)
      (compactShrinkageDOI T U hcT hcU hpT hpU φ hlam hMT hMU h c) =
      compactShrinkageOperator T hcT hpT φ hMT hf - compactShrinkageOperator U hcU hpU φ hMU hf := by
  apply hsSchurMultiplier_represents
  intro i j
  rw [hc, compactShrinkageDifference_cross_entry T U hcT hcU hpT hpU φ hMT hMU hf,
    compactMixedDifference_cross_entry T U hcT hcU hpT hpU lam hlam]
  change (ResidualFilter.shrinkage φ i.1 - ResidualFilter.shrinkage φ j.1) * _ =
    normalizedDividedDifference (ResidualFilter.shrinkage φ) lam i.1 j.1 *
      (((i.1 - j.1) / (Real.sqrt (i.1 + lam) * Real.sqrt (j.1 + lam))) * _)
  rw [← mul_assoc, normalizedDividedDifference_mul_quotient (ResidualFilter.shrinkage φ)
    (compactEigenvalue_nonneg T hcT hpT i) (compactEigenvalue_nonneg U hcU hpU j) hlam]

/-- The source's uniform `A(1+ρ)` norm estimate for the actual normalized DOI. -/
theorem compactShrinkageDOI_apply_norm_le (φ : ℝ → ℝ) {lam M ρ A : ℝ}
    (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (h : ResidualFilter.Contract lam M ρ A φ)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H) :
    ‖compactShrinkageDOI T U hcT hcU hpT hpU φ hlam hMT hMU h c‖ ≤ (A * (1 + ρ)) * ‖c‖ :=
  compactNormalizedDOI_apply_norm_le _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The DOI construction agrees with the previously constructed actual
shrinkage-difference columns. This is proved by actual operator reconstruction
and its injectivity, not by identifying their norms alone. -/
theorem compactShrinkageDOI_eq_differenceColumns (φ : ℝ → ℝ) {lam M ρ A : ℝ}
    (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H)
    (hc : hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) c =
      compactMixedDifference T U hcT hcU hpT hpU lam) :
    compactShrinkageDOI T U hcT hcU hpT hpU φ hlam hMT hMU h c =
      compactShrinkageDifferenceColumns T U hcT hcU hpT hpU φ hlam hMT hMU hf h c hc := by
  apply hilbertSchmidtOperator_injective (compactEigenbasis U hcU hpU.isSymmetric)
  rw [compactShrinkageDOI_represents T U hcT hcU hpT hpU φ hlam hMT hMU hf h c hc,
    hilbertSchmidtOperator_compactShrinkageDifferenceColumns T U hcT hcU hpT hpU φ hlam hMT hMU hf h c hc]

end Spectral

end KernelSeq
