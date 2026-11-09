import KernelSeq.HilbertSchmidtInvariant
import KernelSeq.FilterDimension
import KernelSeq.ContinuousCompactCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Actual Hilbert--Schmidt shrinkage differences

The p=2 shrinkage comparison is proved through cross-basis matrix coefficients
and Parseval, without a DOI or an HMS multiplier assumption. Entry domination
first proves that the actual bounded difference has square-summable columns;
Hilbert--Schmidt existence of the difference is not an input. Hilbert-basis
indices may be uncountable, and no ambient separability is imposed.
-/

open scoped BigOperators ENNReal

namespace KernelSeq

variable {H E ι κ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace H] [CompleteSpace E] in
/-- Cross-basis entry domination proves actual column summability and a total
energy bound. Only the dominating column family is assumed Hilbert--Schmidt. -/
theorem hs_column_energy_of_entry_bound (b : HilbertBasis ι ℝ H) (e : HilbertBasis κ ℝ E)
    (D : H →L[ℝ] E) (c : HilbertSchmidtColumns ι E) (C : ℝ)
    (hentry : ∀ i j, |inner ℝ (e j) (D (b i))| ≤ C * |inner ℝ (e j) (c i)|) :
    Summable (fun i => ‖D (b i)‖ ^ 2) ∧
      (∑' i, ‖D (b i)‖ ^ 2) ≤ C ^ 2 * ‖c‖ ^ 2 := by
  have hcol (i : ι) : ‖D (b i)‖ ^ 2 ≤ C ^ 2 * ‖c i‖ ^ 2 := by
    rw [hilbertBasis_norm_sq_eq_tsum e (D (b i)), hilbertBasis_norm_sq_eq_tsum e (c i),
      ← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (hilbertBasis_coefficients_sq_summable e (D (b i)))
      ((hilbertBasis_coefficients_sq_summable e (c i)).mul_left _)
    intro j
    simpa only [HilbertBasis.repr_apply_apply, sq_abs, mul_pow] using
      pow_le_pow_left₀ (abs_nonneg (inner ℝ (e j) (D (b i)))) (hentry i j) 2
  have hs : Summable (fun i => ‖D (b i)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hcol ((hsColumns_sq_summable c).mul_left _)
  refine ⟨hs, ?_⟩
  rw [hsColumns_norm_sq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hcol hs ((hsColumns_sq_summable c).mul_left _)

/-- Actual columns of the bounded operator whose entries satisfy domination.
The `ℓ²` membership proof is derived from the preceding theorem. -/
noncomputable def hsColumnsOfEntryBound (b : HilbertBasis ι ℝ H) (e : HilbertBasis κ ℝ E)
    (D : H →L[ℝ] E) (c : HilbertSchmidtColumns ι E) (C : ℝ)
    (hentry : ∀ i j, |inner ℝ (e j) (D (b i))| ≤ C * |inner ℝ (e j) (c i)|) :
    HilbertSchmidtColumns ι E :=
  ⟨fun i => D (b i),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2 (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hs_column_energy_of_entry_bound b e D c C hentry).1)⟩

omit [CompleteSpace H] [CompleteSpace E] in
@[simp]
theorem hsColumnsOfEntryBound_apply (b : HilbertBasis ι ℝ H) (e : HilbertBasis κ ℝ E)
    (D : H →L[ℝ] E) (c : HilbertSchmidtColumns ι E) (C : ℝ)
    (hentry : ∀ i j, |inner ℝ (e j) (D (b i))| ≤ C * |inner ℝ (e j) (c i)|) (i : ι) :
    hsColumnsOfEntryBound b e D c C hentry i = D (b i) := rfl

omit [CompleteSpace H] in
/-- The newly constructed columns reconstruct the actual operator. -/
theorem hilbertSchmidtOperator_columnsOfEntryBound (b : HilbertBasis ι ℝ H)
    (e : HilbertBasis κ ℝ E) (D : H →L[ℝ] E) (c : HilbertSchmidtColumns ι E) (C : ℝ)
    (hentry : ∀ i j, |inner ℝ (e j) (D (b i))| ≤ C * |inner ℝ (e j) (c i)|) :
    hilbertSchmidtOperator b (hsColumnsOfEntryBound b e D c C hentry) = D := by
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro i
  rw [hilbertSchmidtOperator_basis, hsColumnsOfEntryBound_apply]

omit [CompleteSpace H] [CompleteSpace E] in
/-- The actual Hilbert--Schmidt norm satisfies the entrywise multiplier bound. -/
theorem hsColumnsOfEntryBound_norm_le (b : HilbertBasis ι ℝ H) (e : HilbertBasis κ ℝ E)
    (D : H →L[ℝ] E) (c : HilbertSchmidtColumns ι E) (C : ℝ) (hC : 0 ≤ C)
    (hentry : ∀ i j, |inner ℝ (e j) (D (b i))| ≤ C * |inner ℝ (e j) (c i)|) :
    ‖hsColumnsOfEntryBound b e D c C hentry‖ ≤ C * ‖c‖ := by
  have hb : ‖hsColumnsOfEntryBound b e D c C hentry‖ ^ 2 ≤ (C * ‖c‖) ^ 2 := by
    rw [hsColumns_norm_sq, mul_pow]
    exact (hs_column_energy_of_entry_bound b e D c C hentry).2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hb

/-- The logarithmic divided-difference factor is bounded by the inverse
geometric mean. This is the elementary `|v| ≤ |sinh v|` step of the source. -/
theorem abs_log_sub_le_div_sqrt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log x - Real.log y| ≤ |x - y| / (Real.sqrt x * Real.sqrt y) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hlog : Real.log (Real.sqrt x / Real.sqrt y) = (Real.log x - Real.log y) / 2 := by
    rw [Real.log_div hsx.ne' hsy.ne', Real.log_sqrt hx.le, Real.log_sqrt hy.le]
    ring
  have h := Real.self_le_sinh_iff.mpr (abs_nonneg (Real.log (Real.sqrt x / Real.sqrt y)))
  rw [← Real.abs_sinh, Real.sinh_log (div_pos hsx hsy), hlog] at h
  have hrat : (Real.sqrt x / Real.sqrt y - (Real.sqrt x / Real.sqrt y)⁻¹) / 2 =
      (x - y) / (2 * (Real.sqrt x * Real.sqrt y)) := by
    rw [inv_div]
    field_simp [hsx.ne', hsy.ne']
    nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]
  rw [hrat, abs_div, abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ)),
    abs_of_pos (by positivity : 0 < 2 * (Real.sqrt x * Real.sqrt y))] at h
  apply (le_div_iff₀ (mul_pos hsx hsy)).mpr
  have hm := (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 < 2 * (Real.sqrt x * Real.sqrt y))).mp h
  nlinarith

namespace ResidualFilter

/-- The source's uniformly bounded normalized scalar shrinkage difference.
The case `s=t` is included, so no arbitrary diagonal kernel is introduced. -/
theorem Contract.shrinkage_normalized_difference_le {lam M ρ A s t : ℝ} {φ : ℝ → ℝ}
    (h : Contract lam M ρ A φ) (hlam : 0 < lam)
    (hs : s ∈ Set.Icc (0 : ℝ) M) (ht : t ∈ Set.Icc (0 : ℝ) M) :
    |shrinkage φ s - shrinkage φ t| ≤
      (A * (1 + ρ)) * (|s - t| / (Real.sqrt (s + lam) * Real.sqrt (t + lam))) := by
  have hq := h.shrinkage_lipschitz hlam (log_coordinate_mem hlam hs) (log_coordinate_mem hlam ht)
  simp only [spectralCoordinate_log hlam hs.1, spectralCoordinate_log hlam ht.1] at hq
  have hlog (v : ℝ) (hv : 0 ≤ v) :
      Real.log (1 + v / lam) = Real.log (v + lam) - Real.log lam := by
    rw [show 1 + v / lam = (v + lam) / lam by field_simp; ring]
    exact Real.log_div (ne_of_gt (add_pos_of_nonneg_of_pos hv hlam)) hlam.ne'
  rw [hlog s hs.1, hlog t ht.1] at hq
  have hid : (Real.log (s + lam) - Real.log lam) -
      (Real.log (t + lam) - Real.log lam) = Real.log (s + lam) - Real.log (t + lam) := by ring
  rw [hid] at hq
  have hg := abs_log_sub_le_div_sqrt (add_pos_of_nonneg_of_pos hs.1 hlam)
    (add_pos_of_nonneg_of_pos ht.1 hlam)
  have hC : 0 ≤ A * (1 + ρ) :=
    mul_nonneg (h.constant_nonneg hlam (hs.1.trans hs.2)) (by linarith [h.rho_pos])
  exact hq.trans (mul_le_mul_of_nonneg_left (by simpa only [add_sub_add_right_eq_sub] using hg) hC)

end ResidualFilter

section Spectral

variable (T U : H →L[ℝ] H) (hcT : IsCompactOperator T) (hcU : IsCompactOperator U)
  (hpT : T.IsPositive) (hpU : U.IsPositive)

/-- The actual mixed perturbation, with the source orientation when
`T=T_X` and `U=T_population`. -/
noncomputable def compactMixedDifference (lam : ℝ) : H →L[ℝ] H :=
  compactRegularizedInvSqrt T hcT hpT lam * (T - U) * compactRegularizedInvSqrt U hcU hpU lam

/-- Exact cross-basis coefficient of the actual mixed perturbation. This also
shows directly that common-eigenvalue entries vanish. -/
theorem compactMixedDifference_cross_entry (lam : ℝ) (hlam : 0 < lam)
    (i : CompactSpectralIndex T) (j : CompactSpectralIndex U) :
    inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
      (compactMixedDifference T U hcT hcU hpT hpU lam (compactEigenbasis U hcU hpU.isSymmetric j)) =
      ((i.1 - j.1) / (Real.sqrt (i.1 + lam) * Real.sqrt (j.1 + lam))) *
        inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i) (compactEigenbasis U hcU hpU.isSymmetric j) := by
  have hR (v : H) : inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
      (compactRegularizedInvSqrt T hcT hpT lam v) =
      (Real.sqrt (i.1 + lam))⁻¹ * inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i) v := by
    simpa only [HilbertBasis.repr_apply_apply] using
      compactRegularizedInvSqrt_repr T hcT hpT lam hlam v i
  have hT (v : H) : inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i) (T v) =
      i.1 * inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i) v := by
    simpa only [HilbertBasis.repr_apply_apply] using compactEigenbasis_repr_apply T hcT hpT.isSymmetric v i
  change inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
    (compactRegularizedInvSqrt T hcT hpT lam
      ((T - U) (compactRegularizedInvSqrt U hcU hpU lam (compactEigenbasis U hcU hpU.isSymmetric j)))) = _
  rw [hR, compactRegularizedInvSqrt_eigenbasis U hcU hpU lam hlam j, map_smul,
    inner_smul_right, sub_apply, inner_sub_right, hT,
    compactEigenbasis_eigen U hcU hpU.isSymmetric j, inner_smul_right]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact cross-basis coefficient of the actual shrinkage difference. -/
theorem compactShrinkageDifference_cross_entry (φ : ℝ → ℝ) {M : ℝ}
    (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M) (hf : ResidualFilter.SpectralFilter M φ)
    (i : CompactSpectralIndex T) (j : CompactSpectralIndex U) :
    inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
      ((compactShrinkageOperator T hcT hpT φ hMT hf - compactShrinkageOperator U hcU hpU φ hMU hf)
        (compactEigenbasis U hcU hpU.isSymmetric j)) =
      (ResidualFilter.shrinkage φ i.1 - ResidualFilter.shrinkage φ j.1) *
        inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i) (compactEigenbasis U hcU hpU.isSymmetric j) := by
  have hT := compactShrinkageOperator_repr T hcT hpT φ hMT hf
    (compactEigenbasis U hcU hpU.isSymmetric j) i
  simp only [HilbertBasis.repr_apply_apply] at hT
  rw [sub_apply, inner_sub_right, hT,
    compactShrinkageOperator_eigenbasis U hcU hpU φ hMU hf, inner_smul_right]
  ring

/-- Uniform entry domination by the actual mixed perturbation. -/
theorem compactShrinkageDifference_entry_le (φ : ℝ → ℝ) {lam M ρ A : ℝ}
    (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (i : CompactSpectralIndex T) (j : CompactSpectralIndex U) :
    |inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
      ((compactShrinkageOperator T hcT hpT φ hMT hf - compactShrinkageOperator U hcU hpU φ hMU hf)
        (compactEigenbasis U hcU hpU.isSymmetric j))| ≤
      (A * (1 + ρ)) * |inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
        (compactMixedDifference T U hcT hcU hpT hpU lam (compactEigenbasis U hcU hpU.isSymmetric j))| := by
  have hi : i.1 ∈ Set.Icc (0 : ℝ) M := ⟨compactEigenvalue_nonneg T hcT hpT i,
    ((le_abs_self i.1).trans (compactEigenvalue_norm_le T hcT hpT.isSymmetric i)).trans hMT⟩
  have hj : j.1 ∈ Set.Icc (0 : ℝ) M := ⟨compactEigenvalue_nonneg U hcU hpU j,
    ((le_abs_self j.1).trans (compactEigenvalue_norm_le U hcU hpU.isSymmetric j)).trans hMU⟩
  have hden : 0 < Real.sqrt (i.1 + lam) * Real.sqrt (j.1 + lam) :=
    mul_pos (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hi.1 hlam))
      (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hj.1 hlam))
  rw [compactShrinkageDifference_cross_entry T U hcT hcU hpT hpU φ hMT hMU hf,
    compactMixedDifference_cross_entry T U hcT hcU hpT hpU lam hlam, abs_mul, abs_mul,
    abs_div, abs_of_pos hden]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (h.shrinkage_normalized_difference_le hlam hi hj)
    (abs_nonneg (inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
      (compactEigenbasis U hcU hpU.isSymmetric j)))

/-- Actual mixed columns supply the entry domination hypothesis. Their operator
identity is the only HS input; the shrinkage difference's HS property is derived. -/
theorem compactShrinkageDifference_entry_bound_of_mixedColumns
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H)
    (hK : hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) c =
      compactMixedDifference T U hcT hcU hpT hpU lam)
    (j : CompactSpectralIndex U) (i : CompactSpectralIndex T) :
    |inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i)
      ((compactShrinkageOperator T hcT hpT φ hMT hf - compactShrinkageOperator U hcU hpU φ hMU hf)
        (compactEigenbasis U hcU hpU.isSymmetric j))| ≤
      (A * (1 + ρ)) * |inner ℝ (compactEigenbasis T hcT hpT.isSymmetric i) (c j)| := by
  have hcj : c j = compactMixedDifference T U hcT hcU hpT hpU lam
      (compactEigenbasis U hcU hpU.isSymmetric j) := by
    rw [← hilbertSchmidtOperator_basis (compactEigenbasis U hcU hpU.isSymmetric) c j, hK]
  rw [hcj]
  exact compactShrinkageDifference_entry_le T U hcT hcU hpT hpU φ hlam hMT hMU hf h i j

/-- The actual shrinkage difference is now constructed in the Hilbert--Schmidt
column space, from the proved entry domination rather than an HS premise. -/
noncomputable def compactShrinkageDifferenceColumns
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H)
    (hK : hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) c =
      compactMixedDifference T U hcT hcU hpT hpU lam) :
    HilbertSchmidtColumns (CompactSpectralIndex U) H :=
  hsColumnsOfEntryBound (compactEigenbasis U hcU hpU.isSymmetric)
    (compactEigenbasis T hcT hpT.isSymmetric)
    (compactShrinkageOperator T hcT hpT φ hMT hf - compactShrinkageOperator U hcU hpU φ hMU hf)
    c (A * (1 + ρ))
    (compactShrinkageDifference_entry_bound_of_mixedColumns T U hcT hcU hpT hpU φ
      hlam hMT hMU hf h c hK)

/-- The constructed columns represent exactly `q(T)−q(U)`. -/
theorem hilbertSchmidtOperator_compactShrinkageDifferenceColumns
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H)
    (hK : hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) c =
      compactMixedDifference T U hcT hcU hpT hpU lam) :
    hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric)
      (compactShrinkageDifferenceColumns T U hcT hcU hpT hpU φ hlam hMT hMU hf h c hK) =
      compactShrinkageOperator T hcT hpT φ hMT hf - compactShrinkageOperator U hcU hpU φ hMU hf :=
  hilbertSchmidtOperator_columnsOfEntryBound _ _ _ _ _ _

/-- The source's p=2 shrinkage bound, with explicit uniform constant `A(1+ρ)`.
No good-event restriction is needed here: the mixed HS bound is supplied by
the separate covariance normalization argument. -/
theorem compactShrinkageDifferenceColumns_norm_le
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H)
    (hK : hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) c =
      compactMixedDifference T U hcT hcU hpT hpU lam) :
    ‖compactShrinkageDifferenceColumns T U hcT hcU hpT hpU φ hlam hMT hMU hf h c hK‖ ≤
      (A * (1 + ρ)) * ‖c‖ := by
  apply hsColumnsOfEntryBound_norm_le
  exact mul_nonneg (h.constant_nonneg hlam ((norm_nonneg T).trans hMT)) (by linarith [h.rho_pos])

/-- Actual HS existence and norm comparison, packaged without any reference to
the internal construction of the difference columns. -/
theorem exists_hs_compactShrinkageDifference
    (φ : ℝ → ℝ) {lam M ρ A : ℝ} (hlam : 0 < lam) (hMT : ‖T‖ ≤ M) (hMU : ‖U‖ ≤ M)
    (hf : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ)
    (c : HilbertSchmidtColumns (CompactSpectralIndex U) H)
    (hK : hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) c =
      compactMixedDifference T U hcT hcU hpT hpU lam) :
    ∃ d : HilbertSchmidtColumns (CompactSpectralIndex U) H,
      hilbertSchmidtOperator (compactEigenbasis U hcU hpU.isSymmetric) d =
        compactShrinkageOperator T hcT hpT φ hMT hf - compactShrinkageOperator U hcU hpU φ hMU hf ∧
      ‖d‖ ≤ (A * (1 + ρ)) * ‖c‖ :=
  ⟨compactShrinkageDifferenceColumns T U hcT hcU hpT hpU φ hlam hMT hMU hf h c hK,
    hilbertSchmidtOperator_compactShrinkageDifferenceColumns T U hcT hcU hpT hpU φ
      hlam hMT hMU hf h c hK,
    compactShrinkageDifferenceColumns_norm_le T U hcT hcU hpT hpU φ hlam hMT hMU hf h c hK⟩

end Spectral

end KernelSeq
