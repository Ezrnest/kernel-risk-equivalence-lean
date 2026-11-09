import KernelSeq.WalshWeakType
import KernelSeq.FiniteSingularOrder
import KernelSeq.RectangularTriangularSchur

/-!
# Actual finite selfadjoint extension of the Walsh weak-type bound

Positive and negative parts are constructed on the actual finite real
selfadjoint spectral basis. Their decomposition and trace/S1 identity are
proved, so extending the positive-input Walsh estimate does not assume a
positive-part or trace-norm certificate. No p<2 adjoint or ideal estimate is
used. A genuine real selfadjoint block dilation then extends the actual
weak bound to arbitrary finite real operator fields with constant 64.
-/

open MeasureTheory
open scoped BigOperators
namespace KernelSeq
noncomputable section
attribute [local instance] Classical.propDecidable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H]

/-- The actual positive square root of the actual singular covariance. -/
def finiteOperatorModulus (A : H →L[ℝ] H) : H →L[ℝ] H :=
  finitePositivePower (A.adjoint * A) (ContinuousLinearMap.isPositive_adjoint_comp_self A)
    (1 / 2) (by norm_num)

/-- Actual Schatten-one equals the actual trace of the constructed modulus. -/
theorem finiteSchatten_one_eq_trace_modulus {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b A) 1 = basisTrace b (finiteOperatorModulus A) := by
  rw [finiteOperatorModulus, finitePositivePower_trace]
  have h := hsSchattenNorm_rpow b (finiteOperatorColumns b A) (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one] at h
  change hsSchattenNorm b (finiteOperatorColumns b A) 1 =
    compactPositivePowerSum (hsSingularCovariance b (finiteOperatorColumns b A)) (1 / 2) at h
  have hcov : hsSingularCovariance b (finiteOperatorColumns b A) = A.adjoint * A := by
    simp only [hsSingularCovariance, hilbertSchmidtOperator_finiteOperatorColumns, ← ContinuousLinearMap.mul_def]
  rw [hcov] at h
  exact h

/-- The actual real spectral basis for a finite selfadjoint operator. -/
def finiteSelfAdjointBasis (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) :
    HilbertBasis (CompactSpectralIndex A) ℝ H :=
  compactEigenbasis A (isCompactOperator_of_locallyCompactSpace_dom A)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA)

theorem finiteSelfAdjoint_posWeight_bound (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (i : CompactSpectralIndex A) : ‖max i.1 0‖ ≤ ‖A‖ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le ((le_abs_self _).trans (compactEigenvalue_norm_le A (isCompactOperator_of_locallyCompactSpace_dom A)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) i)) (norm_nonneg _)

theorem finiteSelfAdjoint_negWeight_bound (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (i : CompactSpectralIndex A) : ‖max (-i.1) 0‖ ≤ ‖A‖ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le ((neg_le_abs _).trans (compactEigenvalue_norm_le A (isCompactOperator_of_locallyCompactSpace_dom A)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) i)) (norm_nonneg _)

/-- Actual positive spectral part, retaining every zero eigenspace. -/
def finitePositivePart (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) : H →L[ℝ] H :=
  hilbertDiagonal (finiteSelfAdjointBasis A hA) (fun i => max i.1 0) ‖A‖ (norm_nonneg A)
    (finiteSelfAdjoint_posWeight_bound A hA)

/-- Actual negative spectral part, with positive values on negative eigenvalues. -/
def finiteNegativePart (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) : H →L[ℝ] H :=
  hilbertDiagonal (finiteSelfAdjointBasis A hA) (fun i => max (-i.1) 0) ‖A‖ (norm_nonneg A)
    (finiteSelfAdjoint_negWeight_bound A hA)

theorem finitePositivePart_positive (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) :
    (finitePositivePart A hA).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mp (hilbertDiagonal_nonneg _ _ _ _ _ (fun _ => le_max_right _ _))

theorem finiteNegativePart_positive (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) :
    (finiteNegativePart A hA).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mp (hilbertDiagonal_nonneg _ _ _ _ _ (fun _ => le_max_right _ _))

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem hilbertDiagonal_basis_apply {ι : Type*} (b : HilbertBasis ι ℝ H)
    (w : ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hw : ∀ i, ‖w i‖ ≤ K) (i : ι) :
    hilbertDiagonal b w K hK hw (b i) = w i • b i := by
  apply b.repr.injective
  ext j
  by_cases hji : j = i
  · subst j
    simp [hilbertDiagonal_repr, HilbertBasis.repr_self]
  · simp [hilbertDiagonal_repr, HilbertBasis.repr_self, lp.single_apply, hji]

theorem finitePositivePart_eigen (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) (i : CompactSpectralIndex A) :
    finitePositivePart A hA (finiteSelfAdjointBasis A hA i) = max i.1 0 • finiteSelfAdjointBasis A hA i :=
  hilbertDiagonal_basis_apply _ _ _ _ _ _

theorem finiteNegativePart_eigen (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) (i : CompactSpectralIndex A) :
    finiteNegativePart A hA (finiteSelfAdjointBasis A hA i) = max (-i.1) 0 • finiteSelfAdjointBasis A hA i :=
  hilbertDiagonal_basis_apply _ _ _ _ _ _

/-- Exact actual positive/negative decomposition. -/
theorem finitePositivePart_sub_negativePart (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) :
    finitePositivePart A hA - finiteNegativePart A hA = A := by
  apply continuousLinearMap_eq_of_hilbertBasis (finiteSelfAdjointBasis A hA)
  intro i
  rw [_root_.sub_apply, finitePositivePart_eigen, finiteNegativePart_eigen]
  have he : A (finiteSelfAdjointBasis A hA i) = i.1 • finiteSelfAdjointBasis A hA i :=
    compactEigenbasis_eigen A (isCompactOperator_of_locallyCompactSpace_dom A)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) i
  rw [he, ← sub_smul]
  congr 1
  by_cases hi : 0 ≤ i.1
  · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]; ring
  · have hn : i.1 ≤ 0 := le_of_not_ge hi
    rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn)]; ring

theorem finiteOperatorModulus_selfAdjoint_eigen (A : H →L[ℝ] H) (hA : IsSelfAdjoint A)
    (i : CompactSpectralIndex A) :
    finiteOperatorModulus A (finiteSelfAdjointBasis A hA i) = |i.1| • finiteSelfAdjointBasis A hA i := by
  have he : A (finiteSelfAdjointBasis A hA i) = i.1 • finiteSelfAdjointBasis A hA i :=
    compactEigenbasis_eigen A _ (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) i
  have hcov : (A.adjoint * A) (finiteSelfAdjointBasis A hA i) =
      i.1 ^ 2 • finiteSelfAdjointBasis A hA i := by
    rw [hA.adjoint_eq, mul_apply_eq_comp, he, map_smul, he, smul_smul, pow_two]
  unfold finiteOperatorModulus
  rw [finitePositivePower_eigen _ _ _ _ hcov, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]

/-- The actual modulus is exactly the sum of the actual two spectral parts. -/
theorem finiteOperatorModulus_eq_parts (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) :
    finiteOperatorModulus A = finitePositivePart A hA + finiteNegativePart A hA := by
  apply continuousLinearMap_eq_of_hilbertBasis (finiteSelfAdjointBasis A hA)
  intro i
  rw [finiteOperatorModulus_selfAdjoint_eigen A hA i, _root_.add_apply,
    finitePositivePart_eigen, finiteNegativePart_eigen, ← add_smul]
  congr 1
  by_cases hi : 0 ≤ i.1
  · simp only [abs_of_nonneg hi, max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), add_zero]
  · have hn : i.1 ≤ 0 := (le_of_not_ge hi)
    simp only [abs_of_nonpos hn, max_eq_right hn, max_eq_left (neg_nonneg.mpr hn), zero_add]

/-- Exact S1 trace decomposition, derived from the actual singular covariance. -/
theorem finiteSchatten_one_eq_trace_parts {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) :
    hsSchattenNorm b (finiteOperatorColumns b A) 1 =
      basisTrace b (finitePositivePart A hA) + basisTrace b (finiteNegativePart A hA) := by
  rw [finiteSchatten_one_eq_trace_modulus b A, finiteOperatorModulus_eq_parts A hA]
  simp only [← finiteBasisTraceCLM_apply, map_add]

/-- Actual finite singular values are invariant under negation, proved
from optimal rank approximations rather than a p<2 ideal bound. -/
theorem finiteSingularValues_neg (A : H →L[ℝ] H) (k : ℕ) :
    (-A).toLinearMap.singularValues k = A.toLinearMap.singularValues k := by
  have hle (B : H →L[ℝ] H) : (-B).toLinearMap.singularValues k ≤ B.toLinearMap.singularValues k := by
    let F := finiteSingularTruncation B k
    have hr : (-F).range = F.range := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨-y, by simp⟩
      · rintro ⟨y, rfl⟩
        exact ⟨-y, by simp⟩
    have hrank : Module.finrank ℝ (-F).range ≤ k := by
      rw [hr]
      exact finiteSingularTruncation_rank_le B k
    calc
      _ ≤ ‖-B - (-F)‖ := finiteSingularValue_le_rank_approximation (-B) (-F) k hrank
      _ = ‖B - F‖ := by rw [show -B - (-F) = -(B - F) by abel, norm_neg]
      _ ≤ _ := finiteSingularTruncation_error_le B k
  have hh := hle (-A)
  simp only [neg_neg] at hh
  exact le_antisymm (hle A) hh

theorem finiteSingularCount_neg (A : H →L[ℝ] H) (t : ℝ) :
    finiteSingularCount (-A) t = finiteSingularCount A t := by
  simp only [finiteSingularCount, finiteSingularValues_neg]

/-- True subtraction distribution bound, including the actual invariance
under negation. -/
theorem finiteSingularCount_sub_le (A B : H →L[ℝ] H) {t : ℝ} (ht : 0 ≤ t) :
    finiteSingularCount (A - B) t ≤ finiteSingularCount A (t / 2) + finiteSingularCount B (t / 2) := by
  have h := finiteSingularCount_add_le A (-B) (by positivity : 0 ≤ t / 2) (by positivity : 0 ≤ t / 2)
  simpa only [← sub_eq_add_neg, finiteSingularCount_neg, show t / 2 + t / 2 = t by ring] using h

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem finiteWalshTransform_sub (X Y : ℕ → WalshCube n → H →L[ℝ] H)
    (σ : ℕ → ℝ) (N : ℕ) (ω : WalshCube n) :
    finiteWalshTransform (fun k η => X k η - Y k η) σ N ω =
      finiteWalshTransform X σ N ω - finiteWalshTransform Y σ N ω := by
  have hd (k : ℕ) : (X (k + 1) ω - Y (k + 1) ω) - (X k ω - Y k ω) =
      (X (k + 1) ω - X k ω) - (Y (k + 1) ω - Y k ω) := by abel
  simp only [finiteWalshTransform, hd, smul_sub, Finset.sum_sub_distrib]
  abel

omit [CompleteSpace H] [FiniteDimensional ℝ H] in
theorem walshPrefixTransform_sub (F G : WalshCube n → H →L[ℝ] H)
    (σ : ℕ → ℝ) (N : ℕ) (ω : WalshCube n) :
    walshPrefixTransform (fun η => F η - G η) σ N ω =
      walshPrefixTransform F σ N ω - walshPrefixTransform G σ N ω := by
  unfold walshPrefixTransform
  have hh : (fun k => walshPrefixAverage (k + 1) (fun η => F η - G η)) =
      (fun k η => walshPrefixAverage (k + 1) F η - walshPrefixAverage (k + 1) G η) := by
    funext k η
    exact walshPrefixAverage_sub _ _ _ _
  rw [hh]
  exact finiteWalshTransform_sub _ _ _ _ _

variable {n : ℕ}
local instance walshGeneralMeasurableSpace (n : ℕ) : MeasurableSpace (WalshCube n) := ⊤

/-- Genuine selfadjoint-input weak-(1,1) bound, using the actual spectral
positive/negative parts and the exact actual S1 trace decomposition. -/
theorem sum_walshPrefixTransform_weak_one_selfAdjoint {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, IsSelfAdjoint (F ω))
    (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    t * (∑ ω : WalshCube n, (finiteSingularCount (walshPrefixTransform F σ N ω) t : ℝ)) ≤
      32 * ∑ ω : WalshCube n, hsSchattenNorm b (finiteOperatorColumns b (F ω)) 1 := by
  let P := fun ω => finitePositivePart (F ω) (hF ω)
  let M := fun ω => finiteNegativePart (F ω) (hF ω)
  have hP (ω : WalshCube n) : (P ω).IsPositive := finitePositivePart_positive (F ω) (hF ω)
  have hM (ω : WalshCube n) : (M ω).IsPositive := finiteNegativePart_positive (F ω) (hF ω)
  have hparts : F = fun ω => P ω - M ω := by
    funext ω
    exact (finitePositivePart_sub_negativePart (F ω) (hF ω)).symm
  have hcount (ω : WalshCube n) : (finiteSingularCount (walshPrefixTransform F σ N ω) t : ℝ) ≤
      (finiteSingularCount (walshPrefixTransform P σ N ω) (t / 2) : ℝ) +
        (finiteSingularCount (walshPrefixTransform M σ N ω) (t / 2) : ℝ) := by
    rw [hparts, walshPrefixTransform_sub]
    exact_mod_cast finiteSingularCount_sub_le (walshPrefixTransform P σ N ω)
      (walshPrefixTransform M σ N ω) ht.le
  have hc := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hcount ω)) ht.le
  simp only [Finset.sum_add_distrib] at hc
  have hp := sum_walshPrefixTransform_weak_one_positive b P hP σ hσ N (by positivity : 0 < t / 2)
  have hm := sum_walshPrefixTransform_weak_one_positive b M hM σ hσ N (by positivity : 0 < t / 2)
  have hnorm : (∑ ω : WalshCube n, hsSchattenNorm b (finiteOperatorColumns b (F ω)) 1) =
      (∑ ω : WalshCube n, basisTrace b (P ω)) + ∑ ω : WalshCube n, basisTrace b (M ω) := by
    simp only [finiteSchatten_one_eq_trace_parts b _ (hF _), Finset.sum_add_distrib, P, M]
  rw [hnorm]
  linarith only [hc, hp, hm]

/-- Actual uniform-probability selfadjoint weak-(1,1), with no weak bound
or positive-part identity supplied as a premise. -/
theorem integral_walshPrefixTransform_weak_one_selfAdjoint {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H) (hF : ∀ ω, IsSelfAdjoint (F ω))
    (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    t * (∫ ω, (finiteSingularCount (walshPrefixTransform F σ N ω) t : ℝ) ∂walshUniformMeasure n) ≤
      32 * ∫ ω, hsSchattenNorm b (finiteOperatorColumns b (F ω)) 1 ∂walshUniformMeasure n := by
  simp only [integral_walshUniform_eq, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (sum_walshPrefixTransform_weak_one_selfAdjoint b F hF σ hσ N ht)
    (show 0 ≤ (Fintype.card (WalshCube n) : ℝ)⁻¹ by positivity)
  nlinarith only [h]

/-- Adjoint invariance of every actual finite singular value, derived from
optimal rank approximation and genuine adjoint rank/norm invariance. -/
theorem finiteSingularValues_adjoint (A : H →L[ℝ] H) (k : ℕ) :
    A.adjoint.toLinearMap.singularValues k = A.toLinearMap.singularValues k := by
  have hle (B : H →L[ℝ] H) : B.adjoint.toLinearMap.singularValues k ≤ B.toLinearMap.singularValues k := by
    let F := finiteSingularTruncation B k
    have hrank : Module.finrank ℝ F.adjoint.range ≤ k := by
      have hh := LinearMap.finrank_range_adjoint F.toLinearMap
      rw [ContinuousLinearMap.adjoint_toLinearMap] at hh
      exact hh.trans_le (finiteSingularTruncation_rank_le B k)
    calc
      _ ≤ ‖B.adjoint - F.adjoint‖ := finiteSingularValue_le_rank_approximation B.adjoint F.adjoint k hrank
      _ = ‖(B - F).adjoint‖ := by rw [map_sub]
      _ = ‖B - F‖ := ContinuousLinearMap.adjoint.norm_map _
      _ ≤ _ := finiteSingularTruncation_error_le B k
  have hh := hle A.adjoint
  simp only [ContinuousLinearMap.adjoint_adjoint] at hh
  exact le_antisymm (hle A) hh

/-- Actual finite Schatten-one adjoint invariance, with no p<2 premise. -/
theorem finiteSchatten_one_adjoint {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    hsSchattenNorm b (finiteOperatorColumns b A.adjoint) 1 = hsSchattenNorm b (finiteOperatorColumns b A) 1 := by
  have hA := finiteSchatten_rpow_eq_sum_singularValues b A (by norm_num : (0 : ℝ) < 1)
  have hAdj := finiteSchatten_rpow_eq_sum_singularValues b A.adjoint (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one, finiteSingularValues_adjoint] at hA hAdj
  exact hAdj.trans hA.symm

/-- Actual real selfadjoint dilation, acting by (x,y)↦(A*y,Ax). -/
def realSelfAdjointDilation (A : H →L[ℝ] H) : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
  (realProdInl (H := H) (E := H)).toContinuousLinearMap.comp
    (A.adjoint.comp (WithLp.sndL 2 ℝ H H)) + realOffDiagonalLift A

omit [FiniteDimensional ℝ H] in
theorem realSelfAdjointDilation_apply (A : H →L[ℝ] H) (z : WithLp 2 (H × H)) :
    realSelfAdjointDilation A z = WithLp.toLp 2 (A.adjoint z.snd, A z.fst) := by
  simp only [realSelfAdjointDilation, add_apply, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, realProdInl_apply, WithLp.sndL_apply, realOffDiagonalLift_apply]
  rw [← WithLp.toLp_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

omit [FiniteDimensional ℝ H] in
theorem realSelfAdjointDilation_selfAdjoint (A : H →L[ℝ] H) :
    IsSelfAdjoint (realSelfAdjointDilation A) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℝ (realSelfAdjointDilation A x) y = inner ℝ x (realSelfAdjointDilation A y)
  rw [realSelfAdjointDilation_apply, realSelfAdjointDilation_apply]
  change inner ℝ (A.adjoint x.snd) y.fst + inner ℝ (A x.fst) y.snd =
    inner ℝ x.fst (A.adjoint y.snd) + inner ℝ x.snd (A y.fst)
  rw [A.adjoint_inner_left, A.adjoint_inner_right]
  ring

omit [FiniteDimensional ℝ H] in
theorem realSelfAdjointDilation_covariance_inl (A : H →L[ℝ] H) (x : H) :
    ((realSelfAdjointDilation A).adjoint * realSelfAdjointDilation A) (realProdInl (E := H) x) =
      realProdInl (E := H) ((A.adjoint * A) x) := by
  rw [(realSelfAdjointDilation_selfAdjoint A).adjoint_eq, mul_apply_eq_comp]
  simp only [realProdInl_apply, realSelfAdjointDilation_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    map_zero, mul_apply_eq_comp]

omit [FiniteDimensional ℝ H] in
theorem realSelfAdjointDilation_covariance_inr (A : H →L[ℝ] H) (x : H) :
    ((realSelfAdjointDilation A).adjoint * realSelfAdjointDilation A) (realProdInr (H := H) x) =
      realProdInr (H := H) ((A.adjoint.adjoint * A.adjoint) x) := by
  rw [(realSelfAdjointDilation_selfAdjoint A).adjoint_eq, mul_apply_eq_comp]
  simp only [realProdInr_apply, realSelfAdjointDilation_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    map_zero, mul_apply_eq_comp, ContinuousLinearMap.adjoint_adjoint]

/-- The actual block modulus intertwines the first covariance spectral basis. -/
theorem realSelfAdjointDilation_modulus_inl (A : H →L[ℝ] H) (x : H) :
    finiteOperatorModulus (realSelfAdjointDilation A) (realProdInl (E := H) x) =
      realProdInl (E := H) (finiteOperatorModulus A x) := by
  let C := A.adjoint * A
  have hp : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self A
  let e := compactEigenbasis C (isCompactOperator_of_locallyCompactSpace_dom C) hp.isSymmetric
  have heq : (finiteOperatorModulus (realSelfAdjointDilation A)).comp
      (realProdInl (H := H) (E := H)).toContinuousLinearMap =
      (realProdInl (H := H) (E := H)).toContinuousLinearMap.comp (finiteOperatorModulus A) := by
    apply continuousLinearMap_eq_of_hilbertBasis e
    intro i
    have hv : C (e i) = i.1 • e i := compactEigenbasis_eigen C _ hp.isSymmetric i
    have hblock : ((realSelfAdjointDilation A).adjoint * realSelfAdjointDilation A)
        (realProdInl (E := H) (e i)) = i.1 • realProdInl (E := H) (e i) := by
      rw [realSelfAdjointDilation_covariance_inl, hv, map_smul]
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    unfold finiteOperatorModulus
    rw [finitePositivePower_eigen _ _ _ _ hblock, finitePositivePower_eigen _ _ _ _ hv, map_smul]
  exact congrArg (fun T => T x) heq

theorem realSelfAdjointDilation_modulus_inr (A : H →L[ℝ] H) (x : H) :
    finiteOperatorModulus (realSelfAdjointDilation A) (realProdInr (H := H) x) =
      realProdInr (H := H) (finiteOperatorModulus A.adjoint x) := by
  let C := A.adjoint.adjoint * A.adjoint
  have hp : C.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self A.adjoint
  let e := compactEigenbasis C (isCompactOperator_of_locallyCompactSpace_dom C) hp.isSymmetric
  have heq : (finiteOperatorModulus (realSelfAdjointDilation A)).comp
      (realProdInr (H := H) (E := H)).toContinuousLinearMap =
      (realProdInr (H := H) (E := H)).toContinuousLinearMap.comp (finiteOperatorModulus A.adjoint) := by
    apply continuousLinearMap_eq_of_hilbertBasis e
    intro i
    have hv : C (e i) = i.1 • e i := compactEigenbasis_eigen C _ hp.isSymmetric i
    have hblock : ((realSelfAdjointDilation A).adjoint * realSelfAdjointDilation A)
        (realProdInr (H := H) (e i)) = i.1 • realProdInr (H := H) (e i) := by
      rw [realSelfAdjointDilation_covariance_inr, hv, map_smul]
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    unfold finiteOperatorModulus
    rw [finitePositivePower_eigen _ _ _ _ hblock, finitePositivePower_eigen _ _ _ _ hv, map_smul]
  exact congrArg (fun T => T x) heq

/-- Genuine S1 norm of the actual selfadjoint real dilation. The proof
splits the actual modulus trace, so no p<2 ideal/adjoint bound is imported. -/
theorem realSelfAdjointDilation_schatten_one {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (A : H →L[ℝ] H) :
    hsSchattenNorm (realProdBasis b b) (finiteOperatorColumns (realProdBasis b b) (realSelfAdjointDilation A)) 1 =
      2 * hsSchattenNorm b (finiteOperatorColumns b A) 1 := by
  rw [finiteSchatten_one_eq_trace_modulus]
  have htrace : basisTrace (realProdBasis b b) (finiteOperatorModulus (realSelfAdjointDilation A)) =
      basisTrace b (finiteOperatorModulus A) + basisTrace b (finiteOperatorModulus A.adjoint) := by
    simp only [basisTrace, tsum_fintype, Fintype.sum_sum_type, realProdBasis_inl, realProdBasis_inr]
    simp_rw [realSelfAdjointDilation_modulus_inl, realSelfAdjointDilation_modulus_inr]
    simp only [realProdInl_apply, realProdInr_apply, WithLp.prod_inner_apply,
      inner_zero_left, add_zero, zero_add]
  rw [htrace, ← finiteSchatten_one_eq_trace_modulus, ← finiteSchatten_one_eq_trace_modulus,
    finiteSchatten_one_adjoint]
  ring

/-- Actual singular-value contraction between different finite Hilbert
spaces, proved by pulling back genuine optimal rank approximations. -/
theorem finiteSingularValues_compression_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (A : H →L[ℝ] H) (B : E →L[ℝ] E)
    (P : E →L[ℝ] H) (I : H →L[ℝ] E) (hP : ‖P‖ ≤ 1) (hI : ‖I‖ ≤ 1)
    (hA : A = P.comp (B.comp I)) (k : ℕ) :
    A.toLinearMap.singularValues k ≤ B.toLinearMap.singularValues k := by
  let Bk := finiteSingularTruncation B k
  let F := P.comp (Bk.comp I)
  have hsub : (Bk.comp I).range ≤ Bk.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨I x, rfl⟩
  have hr : F.range = (Bk.comp I).range.map P.toLinearMap :=
    LinearMap.range_comp (Bk.comp I).toLinearMap P.toLinearMap
  have hF : Module.finrank ℝ F.range ≤ k := by
    rw [hr]
    exact (Submodule.finrank_map_le P.toLinearMap (Bk.comp I).range).trans
      ((Submodule.finrank_mono hsub).trans (finiteSingularTruncation_rank_le B k))
  have heq : A - F = P.comp ((B - Bk).comp I) := by
    rw [hA]
    ext x
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply, map_sub, F]
  calc
    _ ≤ ‖A - F‖ := finiteSingularValue_le_rank_approximation A F k hF
    _ = ‖P.comp ((B - Bk).comp I)‖ := congrArg norm heq
    _ ≤ ‖P‖ * ‖(B - Bk).comp I‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖P‖ * (‖B - Bk‖ * ‖I‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖B - Bk‖ * 1) := mul_le_mul hP (mul_le_mul_of_nonneg_left hI (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    _ = ‖B - Bk‖ := by ring
    _ ≤ _ := finiteSingularTruncation_error_le B k

/-- The actual off-diagonal coordinate compression does not increase the
singular exceedance count of the selfadjoint dilation. -/
theorem realSelfAdjointDilation_count_le (A : H →L[ℝ] H) {t : ℝ} (ht : 0 ≤ t) :
    finiteSingularCount A t ≤ finiteSingularCount (realSelfAdjointDilation A) t := by
  have hcomp : A = (WithLp.sndL 2 ℝ H H).comp
      ((realSelfAdjointDilation A).comp (realProdInl (H := H) (E := H)).toContinuousLinearMap) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      realProdInl_apply, realSelfAdjointDilation_apply, WithLp.sndL_apply,
      WithLp.toLp_fst, WithLp.toLp_snd]
  apply (finiteSingularCount_le_iff A ht _).mpr
  exact (finiteSingularValues_compression_le A (realSelfAdjointDilation A)
    (WithLp.sndL 2 ℝ H H) (realProdInl (H := H) (E := H)).toContinuousLinearMap
    realProd_snd_norm_le (realProdInl (H := H) (E := H)).norm_toContinuousLinearMap_le hcomp _).trans
      ((finiteSingularCount_le_iff (realSelfAdjointDilation A) ht _).mp le_rfl)

/-- The real block dilation is an actual real linear map on operators. -/
def realSelfAdjointDilationLinear : (H →L[ℝ] H) →ₗ[ℝ] (WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H)) where
  toFun := realSelfAdjointDilation
  map_add' A B := by
    ext z
    simp only [realSelfAdjointDilation_apply, add_apply, map_add]
    rw [← WithLp.toLp_add]
    rfl
  map_smul' s A := by
    ext z
    simp only [realSelfAdjointDilation_apply, smul_apply, map_smul, RingHom.id_apply]
    rw [← WithLp.toLp_smul]
    rfl

omit [FiniteDimensional ℝ H] in
/-- The actual Walsh prefix transform commutes with real selfadjoint
dilation because both conditional averaging and the transform are linear. -/
theorem walshPrefixTransform_realSelfAdjointDilation
    (F : WalshCube n → H →L[ℝ] H) (σ : ℕ → ℝ) (N : ℕ) (ω : WalshCube n) :
    walshPrefixTransform (fun η => realSelfAdjointDilation (F η)) σ N ω =
      realSelfAdjointDilation (walshPrefixTransform F σ N ω) := by
  change walshPrefixTransform (fun η => realSelfAdjointDilationLinear (F η)) σ N ω =
    realSelfAdjointDilationLinear (walshPrefixTransform F σ N ω)
  simp only [walshPrefixTransform, finiteWalshTransform, walshPrefixAverage_map,
    map_add, map_sum, map_smul, map_sub]

/-- Genuine arbitrary real operator-input finite Walsh weak-(1,1) bound.
The selfadjoint block, its S1 equality, and count compression are actual
constructions proved above; no p<2 ideal or weak estimate is assumed. -/
theorem sum_walshPrefixTransform_weak_one {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H)
    (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    t * (∑ ω : WalshCube n, (finiteSingularCount (walshPrefixTransform F σ N ω) t : ℝ)) ≤
      64 * ∑ ω : WalshCube n, hsSchattenNorm b (finiteOperatorColumns b (F ω)) 1 := by
  let B := fun ω => realSelfAdjointDilation (F ω)
  have hweak := sum_walshPrefixTransform_weak_one_selfAdjoint (realProdBasis b b) B
    (fun ω => realSelfAdjointDilation_selfAdjoint (F ω)) σ hσ N ht
  have hc (ω : WalshCube n) : (finiteSingularCount (walshPrefixTransform F σ N ω) t : ℝ) ≤
      (finiteSingularCount (walshPrefixTransform B σ N ω) t : ℝ) := by
    change _ ≤ (finiteSingularCount (walshPrefixTransform (fun η => realSelfAdjointDilation (F η)) σ N ω) t : ℝ)
    rw [walshPrefixTransform_realSelfAdjointDilation]
    exact_mod_cast realSelfAdjointDilation_count_le (walshPrefixTransform F σ N ω) ht.le
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hc ω)) ht.le
  simp only [B, realSelfAdjointDilation_schatten_one, ← Finset.mul_sum] at hweak
  linarith only [hs, hweak]

/-- Actual uniform-probability weak-(1,1) for arbitrary finite real operator
fields, suitable for the finite-field Marcinkiewicz theorem. -/
theorem integral_walshPrefixTransform_weak_one {ι : Type*} [Fintype ι]
    (b : HilbertBasis ι ℝ H) (F : WalshCube n → H →L[ℝ] H)
    (σ : ℕ → ℝ) (hσ : ∀ k, |σ k| = 1) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    t * (∫ ω, (finiteSingularCount (walshPrefixTransform F σ N ω) t : ℝ) ∂walshUniformMeasure n) ≤
      64 * ∫ ω, hsSchattenNorm b (finiteOperatorColumns b (F ω)) 1 ∂walshUniformMeasure n := by
  simp only [integral_walshUniform_eq, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (sum_walshPrefixTransform_weak_one b F σ hσ N ht)
    (show 0 ≤ (Fintype.card (WalshCube n) : ℝ)⁻¹ by positivity)
  nlinarith only [h]

end
end KernelSeq
