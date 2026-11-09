import KernelSeq.DyadicTriangularSchur
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Actual rectangular sign and strict-step Schur multipliers

The two real Hilbert spaces are embedded in their actual L2 direct sum.
Off-diagonal block lifting preserves the actual Schatten quantity by the
proved ideal bound and reverse isometric compression. The square sign bound
then gives the rectangular bound. No complexification or basis-norm identity
is supplied as a certificate. Strict comparison is implemented by an internally
derived positive finite-grid perturbation, preserving zero values at equality
and giving the uniform dyadic strict-step bound `p/2`, also for shifted thresholds.
-/

open scoped BigOperators
open Filter Topology

namespace KernelSeq
noncomputable section

variable {ι κ H E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual first-coordinate inclusion into the real Hilbert direct sum. -/
def realProdInl : H →ₗᵢ[ℝ] WithLp 2 (H × E) where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (H × E)).symm.toLinearMap.comp (LinearMap.inl ℝ H E)
  norm_map' x := WithLp.norm_toLp_fst 2 H E x

/-- The actual second-coordinate inclusion into the real Hilbert direct sum. -/
def realProdInr : E →ₗᵢ[ℝ] WithLp 2 (H × E) where
  toLinearMap := (WithLp.linearEquiv 2 ℝ (H × E)).symm.toLinearMap.comp (LinearMap.inr ℝ H E)
  norm_map' x := WithLp.norm_toLp_snd 2 H E x

omit [CompleteSpace H] [CompleteSpace E] in
@[simp] theorem realProdInl_apply (x : H) : realProdInl (E := E) x = WithLp.toLp 2 (x, 0) := rfl
omit [CompleteSpace H] [CompleteSpace E] in
@[simp] theorem realProdInr_apply (x : E) : realProdInr (H := H) x = WithLp.toLp 2 (0, x) := rfl

/-- The labelled product basis retains the two original basis index types. -/
def realProdBasis (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) :
    HilbertBasis (ι ⊕ κ) ℝ (WithLp 2 (H × E)) :=
  (b.toOrthonormalBasis.prod a.toOrthonormalBasis).toHilbertBasis

@[simp] theorem realProdBasis_inl (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (j : ι) :
    realProdBasis b a (Sum.inl j) = realProdInl (E := E) (b j) := by
  simp only [realProdBasis, OrthonormalBasis.coe_toHilbertBasis, OrthonormalBasis.prod_apply,
    Sum.elim_inl, Function.comp_apply, HilbertBasis.coe_toOrthonormalBasis]
  rfl

@[simp] theorem realProdBasis_inr (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E) (i : κ) :
    realProdBasis b a (Sum.inr i) = realProdInr (H := H) (a i) := by
  simp only [realProdBasis, OrthonormalBasis.coe_toHilbertBasis, OrthonormalBasis.prod_apply,
    Sum.elim_inr, Function.comp_apply, HilbertBasis.coe_toOrthonormalBasis]
  rfl

omit [CompleteSpace H] [CompleteSpace E] in
/-- Both actual coordinate projections are contractions, including zero spaces. -/
theorem realProd_fst_norm_le : ‖WithLp.fstL 2 ℝ H E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [WithLp.fstL_apply, one_mul] using WithLp.norm_fst_le H z

omit [CompleteSpace H] [CompleteSpace E] in
theorem realProd_snd_norm_le : ‖WithLp.sndL 2 ℝ H E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [WithLp.sndL_apply, one_mul] using WithLp.norm_snd_le H z

/-- The actual off-diagonal lift of a rectangular operator. -/
def realOffDiagonalLift (A : H →L[ℝ] E) : WithLp 2 (H × E) →L[ℝ] WithLp 2 (H × E) :=
  (realProdInr (H := H)).toContinuousLinearMap.comp (A.comp (WithLp.fstL 2 ℝ H E))

omit [CompleteSpace H] [CompleteSpace E] in
@[simp] theorem realOffDiagonalLift_apply (A : H →L[ℝ] E) (z : WithLp 2 (H × E)) :
    realOffDiagonalLift A z = WithLp.toLp 2 (0, A z.fst) := rfl

/-- Actual square HS columns of the off-diagonal lift. -/
def realOffDiagonalColumns (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (c : HilbertSchmidtColumns ι E) : HilbertSchmidtColumns (ι ⊕ κ) (WithLp 2 (H × E)) :=
  hsLeftComposition (realProdInr (H := H)).toContinuousLinearMap
    (hsRightComposition b (realProdBasis b a) a (WithLp.fstL 2 ℝ H E) c)

/-- The columns reconstruct the actual off-diagonal operator. -/
theorem hilbertSchmidtOperator_realOffDiagonalColumns (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (c : HilbertSchmidtColumns ι E) :
    hilbertSchmidtOperator (realProdBasis b a) (realOffDiagonalColumns b a c) =
      realOffDiagonalLift (hilbertSchmidtOperator b c) := by
  rw [realOffDiagonalColumns, hilbertSchmidtOperator_leftComposition, hilbertSchmidtOperator_rightComposition]
  rfl

/-- The actual rectangular block lift preserves every existing Schatten norm
`p ≥ 2`; equality follows from two actual contraction inequalities. -/
theorem realOffDiagonalColumns_schatten_eq (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm (realProdBasis b a) (realOffDiagonalColumns b a c) p = hsSchattenNorm b c p := by
  let d := realProdBasis b a
  have hn : 0 ≤ hsSchattenNorm b c p := hsSchattenNorm_nonneg b c p
  have hlift : hsSchattenNorm d (realOffDiagonalColumns b a c) p ≤ hsSchattenNorm b c p := by
    have h := hsSchattenNorm_twoSidedComposition_le b d a (WithLp.fstL 2 ℝ H E)
      (realProdInr (H := H)).toContinuousLinearMap c hp
    have hI := (realProdInr (H := H) (E := E)).norm_toContinuousLinearMap_le
    have hP := realProd_fst_norm_le (H := H) (E := E)
    exact h.trans (by
      have hmul := mul_le_mul (mul_le_mul_of_nonneg_right hI hn) hP
        (norm_nonneg (WithLp.fstL 2 ℝ H E)) (by simpa only [one_mul] using hn)
      simpa only [one_mul, mul_one] using hmul)
  have hrep : hilbertSchmidtOperator b (hsCompressionColumns d b d (realProdInl (E := E))
      (WithLp.sndL 2 ℝ H E) (realOffDiagonalColumns b a c)) = hilbertSchmidtOperator b c := by
    rw [hilbertSchmidtOperator_compression, hilbertSchmidtOperator_realOffDiagonalColumns]
    ext x
    rfl
  have hcomp := hsSchattenNorm_compression_le d b d (realProdInl (E := E)) (WithLp.sndL 2 ℝ H E)
    (realProd_snd_norm_le (H := H) (E := E)) (realOffDiagonalColumns b a c) hp
  rw [hsSchattenNorm_reconstruction_eq b b _ c hrep p] at hcomp
  exact le_antisymm hlift hcomp

/-- Exact coefficients of an arbitrary square operator under rectangular
coordinate compression in the actual labelled product basis. -/
theorem realProd_compression_coefficient (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (D : WithLp 2 (H × E) →L[ℝ] WithLp 2 (H × E)) (i : κ) (j : ι) :
    inner ℝ (a i) ((WithLp.sndL 2 ℝ H E) (D (realProdInl (E := E) (b j)))) =
      finiteBasisEntry (realProdBasis b a) D (Sum.inr i) (Sum.inl j) := by
  rw [finiteBasisEntry, realProdBasis_inl, realProdBasis_inr]
  simp only [realProdInr_apply, WithLp.prod_inner_apply, inner_zero_left, zero_add, WithLp.sndL_apply]
  rfl

/-- Exact nonzero cross-block coefficients of the actual lifted operator. -/
theorem realOffDiagonalLift_coefficient (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (A : H →L[ℝ] E) (i : κ) (j : ι) :
    finiteBasisEntry (realProdBasis b a) (realOffDiagonalLift A) (Sum.inr i) (Sum.inl j) =
      inner ℝ (a i) (A (b j)) := by
  rw [← realProd_compression_coefficient]
  rfl

/-- The actual rectangular sign multiplier on the two independent grids. -/
def rectangularSignColumns (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ) :
    HilbertSchmidtColumns ι E →L[ℝ] HilbertSchmidtColumns ι E :=
  hsSchurMultiplier a (fun i j => Real.sign (x i - y j)) 1 zero_le_one
    (fun i j => triangularSign_norm_le (x i - y j))

omit [CompleteSpace H] in
/-- This is exactly the explicit actual finite matrix-column construction. -/
theorem rectangularSignColumns_eq_finite (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E) :
    rectangularSignColumns a x y c = finiteMatrixSchurColumns a (fun i j => Real.sign (x i - y j)) c :=
  (finiteMatrixSchurColumns_eq b a _ 1 zero_le_one _ c).symm

/-- Exact actual reconstruction of the rectangular sign map by square sign
multiplication on the real off-diagonal lift and actual coordinate compression. -/
theorem rectangularSignColumns_eq_compression (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E) :
    rectangularSignColumns a x y c =
      hsCompressionColumns (realProdBasis b a) b (realProdBasis b a) (realProdInl (E := E))
        (WithLp.sndL 2 ℝ H E)
        (triangularSchurHS (realProdBasis b a) (Sum.elim y x) (realOffDiagonalColumns b a c)) := by
  let d := realProdBasis b a
  let z := Sum.elim y x
  let lc := realOffDiagonalColumns b a c
  apply hilbertSchmidtOperator_injective b
  rw [hilbertSchmidtOperator_compression]
  apply hsSchurMultiplier_represents
  intro i j
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [realProd_compression_coefficient b a,
    hilbertSchmidtOperator_triangularSchurHS, triangularSchur_entry,
    hilbertSchmidtOperator_realOffDiagonalColumns, realOffDiagonalLift_coefficient]
  simp only [Sum.elim_inr, Sum.elim_inl]

/-- The genuine rectangular sign multiplier has the same dimension-free
`p-1` bound at every dyadic exponent. Empty spaces and repeated labels remain
included; the real block lift has its exact Schatten norm proved above. -/
theorem rectangularSignColumns_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (x : κ → ℝ) (y : ι → ℝ) (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (rectangularSignColumns a x y c) ((2 : ℝ) ^ (m + 1)) ≤
      ((2 : ℝ) ^ (m + 1) - 1) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  have hp : 2 ≤ (2 : ℝ) ^ (m + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 1)
  rw [rectangularSignColumns_eq_compression b a x y c]
  calc
    _ ≤ hsSchattenNorm (realProdBasis b a)
        (triangularSchurHS (realProdBasis b a) (Sum.elim y x) (realOffDiagonalColumns b a c)) ((2 : ℝ) ^ (m + 1)) :=
      hsSchattenNorm_compression_le (realProdBasis b a) b (realProdBasis b a) (realProdInl (E := E))
        (WithLp.sndL 2 ℝ H E) (realProd_snd_norm_le (H := H) (E := E)) _ hp
    _ ≤ ((2 : ℝ) ^ (m + 1) - 1) *
        hsSchattenNorm (realProdBasis b a) (realOffDiagonalColumns b a c) ((2 : ℝ) ^ (m + 1)) :=
      triangularSchurHS_dyadic_le (realProdBasis b a) (Sum.elim y x) m _
    _ = _ := by rw [realOffDiagonalColumns_schatten_eq b a c hp]

/-- The same actual dyadic bound for the explicit finite sign matrix. -/
theorem finiteRectangularSign_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (x : κ → ℝ) (y : ι → ℝ) (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => Real.sign (x i - y j)) c) ((2 : ℝ) ^ (m + 1)) ≤
      ((2 : ℝ) ^ (m + 1) - 1) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  rw [← rectangularSignColumns_eq_finite b a]
  exact rectangularSignColumns_dyadic_le b a x y m c

/-- A finite positive perturbation implements strict comparison exactly.
The perturbation is derived internally from the finitely many positive gaps;
coincident labels give sign `-1` and hence strict-step value zero. -/
theorem exists_pos_shift_strictStep_sign (x : κ → ℝ) (y : ι → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, (if y j < x i then (1 : ℝ) else 0) =
      (1 + Real.sign (x i - (y j + δ))) / 2 := by
  have hgap : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), ∀ i j, y j < x i → δ < x i - y j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases h : y j < x i
    · exact (eventually_lt_nhds (sub_pos.mpr h)).mono (fun δ hδ _ => hδ)
    · exact Eventually.of_forall (fun _ h' => (h h').elim)
  have hchoice : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ ∧ ∀ i j, y j < x i → δ < x i - y j := by
    have hg := hgap.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    have hp : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
    filter_upwards [hg, hp] with δ hgδ hpδ
    exact ⟨hpδ, hgδ⟩
  obtain ⟨δ, hδpos, hδ⟩ := hchoice.exists
  refine ⟨δ, hδpos, ?_⟩
  intro i j
  by_cases h : y j < x i
  · rw [if_pos h, Real.sign_of_pos (by linarith [hδ i j h])]
    norm_num
  · rw [if_neg h, Real.sign_of_neg (by linarith [le_of_not_gt h])]
    norm_num

omit [CompleteSpace E] in
/-- The all-one actual finite Schur matrix is the identity on HS columns. -/
theorem finiteMatrixSchurColumns_one (a : HilbertBasis κ ℝ E) (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a (fun _ _ => 1) c = c := by
  ext j
  rw [finiteMatrixSchurColumns_apply]
  simp only [one_mul]
  simpa only [HilbertBasis.coe_toOrthonormalBasis] using a.toOrthonormalBasis.sum_repr' (c j)

/-- The actual strict rectangular step multiplier, with value zero at equality. -/
def rectangularStrictStepColumns (a : HilbertBasis κ ℝ E) (x : κ → ℝ) (y : ι → ℝ) :
    HilbertSchmidtColumns ι E →L[ℝ] HilbertSchmidtColumns ι E :=
  hsSchurMultiplier a (fun i j => if y j < x i then 1 else 0) 1 zero_le_one
    (fun i j => by split_ifs <;> norm_num)

omit [CompleteSpace H] in
/-- This is the actual finite strict-step matrix, including equality entries. -/
theorem rectangularStrictStepColumns_eq_finite (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E) :
    rectangularStrictStepColumns a x y c = finiteMatrixSchurColumns a (fun i j => if y j < x i then 1 else 0) c :=
  (finiteMatrixSchurColumns_eq b a _ 1 zero_le_one _ c).symm

/-- Genuine rectangular strict-step bound at every dyadic exponent. A small
finite-grid perturbation converts strict comparison into a sign multiplier;
no diagonal-block Schatten estimate or spectral-gap premise is assumed. -/
theorem rectangularStrictStepColumns_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (x : κ → ℝ) (y : ι → ℝ) (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (rectangularStrictStepColumns a x y c) ((2 : ℝ) ^ (m + 1)) ≤
      ((2 : ℝ) ^ (m + 1) / 2) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  have hp : 2 ≤ (2 : ℝ) ^ (m + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ m + 1)
  obtain ⟨δ, _, hδ⟩ := exists_pos_shift_strictStep_sign x y
  have hker : (fun i j => if y j < x i then (1 : ℝ) else 0) =
      (fun i j => (1 / 2 : ℝ) * (1 + Real.sign (x i - (y j + δ)))) := by
    funext i j
    rw [hδ i j]
    ring
  have hcols : rectangularStrictStepColumns a x y c =
      (1 / 2 : ℝ) • (c + rectangularSignColumns a x (fun j => y j + δ) c) := by
    rw [rectangularStrictStepColumns_eq_finite b a, hker, finiteMatrixSchurColumns_smul,
      finiteMatrixSchurColumns_add, finiteMatrixSchurColumns_one,
      ← rectangularSignColumns_eq_finite b a x (fun j => y j + δ) c]
  rw [hcols, hsSchattenNorm_smul b _ _ hp, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) +
        hsSchattenNorm b (rectangularSignColumns a x (fun j => y j + δ) c) ((2 : ℝ) ^ (m + 1))) :=
      mul_le_mul_of_nonneg_left (hsSchattenNorm_add_le b _ _ hp) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) +
        ((2 : ℝ) ^ (m + 1) - 1) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1))) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl (rectangularSignColumns_dyadic_le b a x (fun j => y j + δ) m c)) (by norm_num)
    _ = _ := by ring

/-- The same strict-step bound for the actual finite matrix columns. -/
theorem finiteRectangularStrictStep_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (x : κ → ℝ) (y : ι → ℝ) (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => if y j < x i then 1 else 0) c) ((2 : ℝ) ^ (m + 1)) ≤
      ((2 : ℝ) ^ (m + 1) / 2) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) := by
  rw [← rectangularStrictStepColumns_eq_finite b a]
  exact rectangularStrictStepColumns_dyadic_le b a x y m c

/-- Arbitrary translated thresholds have the identical uniform bound; strict
equality entries are still zero, and neither grid needs distinct labels. -/
theorem finiteRectangularThresholdStep_dyadic_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (x : κ → ℝ) (y : ι → ℝ) (r : ℝ) (m : ℕ) (c : HilbertSchmidtColumns ι E) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => if y j + r < x i then 1 else 0) c) ((2 : ℝ) ^ (m + 1)) ≤
      ((2 : ℝ) ^ (m + 1) / 2) * hsSchattenNorm b c ((2 : ℝ) ^ (m + 1)) :=
  finiteRectangularStrictStep_dyadic_le b a x (fun j => y j + r) m c

end
end KernelSeq
