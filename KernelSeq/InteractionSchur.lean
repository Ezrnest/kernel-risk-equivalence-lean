import KernelSeq.FourierSchur
import KernelSeq.AnalyticSchurBounds
import KernelSeq.LogProfileBounds

/-!
# The actual three-term interaction Schur estimate

The Fourier factor has a constant independent of p. Only the two general
finite analytic theorems remain external: Lipschitz divided differences and
the off-diagonal HMS symbol. All actual finite column products, diagonal
factors, sums and finite-to-infinite extension are proved here.
-/

open MeasureTheory

namespace KernelSeq
noncomputable section

universe uι uκ uH uE
variable {ι : Type uι} {κ : Type uκ} {H : Type uH} {E : Type uE}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Finite
variable [Fintype ι] [Fintype κ]

omit [CompleteSpace H] in
theorem finiteMatrixSchurColumns_comp (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (M N : κ → ι → ℝ) (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a M (finiteMatrixSchurColumns a N c) =
      finiteMatrixSchurColumns a (fun i j => M i j * N i j) c := by
  apply hilbertSchmidtOperator_injective b
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro j
  apply a.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply, finiteMatrixSchurColumns_coefficient,
    ← hilbertSchmidtOperator_basis b (finiteMatrixSchurColumns a N c) j]
  ring

theorem finiteMatrixSchurColumns_sides_eq (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (M : κ → ι → ℝ) (u : κ → ℝ) (v : ι → ℝ) {L R : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hu : ∀ i, ‖u i‖ ≤ L) (hv : ∀ j, ‖v j‖ ≤ R)
    (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a (fun i j => u i * M i j * v j) c =
      hsLeftComposition (hilbertDiagonal a u L hL hu)
        (hsRightComposition b b a (hilbertDiagonal b v R hR hv)
          (finiteMatrixSchurColumns a M c)) := by
  apply hilbertSchmidtOperator_injective b
  rw [hilbertSchmidtOperator_leftComposition, hilbertSchmidtOperator_rightComposition]
  apply continuousLinearMap_eq_of_hilbertBasis b
  intro j
  apply a.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply, finiteMatrixSchurColumns_coefficient]
  simp only [ContinuousLinearMap.comp_apply, hilbertDiagonal_eigen, map_smul,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hilbertSchmidtOperator_basis,
    HilbertBasis.repr_apply_apply]
  have hd : inner ℝ (a i) (hilbertDiagonal a u L hL hu
      (finiteMatrixSchurColumns a M c j)) =
      u i * inner ℝ (a i) (finiteMatrixSchurColumns a M c j) := by
    simpa only [HilbertBasis.repr_apply_apply] using hilbertDiagonal_repr a u L hL hu
      (finiteMatrixSchurColumns a M c j) i
  rw [hd, ← hilbertSchmidtOperator_basis b (finiteMatrixSchurColumns a M c) j,
    finiteMatrixSchurColumns_coefficient]
  ring

theorem finiteMatrixSchurColumns_sides_schatten_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (M : κ → ι → ℝ) (u : κ → ℝ) (v : ι → ℝ) {L R : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hu : ∀ i, ‖u i‖ ≤ L) (hv : ∀ j, ‖v j‖ ≤ R)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => u i * M i j * v j) c) p ≤
      L * hsSchattenNorm b (finiteMatrixSchurColumns a M c) p * R := by
  rw [finiteMatrixSchurColumns_sides_eq b a M u v hL hR hu hv c]
  refine (hsSchattenNorm_twoSidedComposition_le b b a _ _ _ hp).trans ?_
  have h1 := hilbertDiagonal_norm_le a u L hL hu
  have h2 := hilbertDiagonal_norm_le b v R hR hv
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h1 (hsSchattenNorm_nonneg b _ p)) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left h2 (mul_nonneg hL (hsSchattenNorm_nonneg b _ p)))

end Finite

/-- The actual scalar kernel of the three-term logarithmic decomposition. -/
def factorizedInteractionGrid (F P θ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ)
    (x : κ → ℝ) (y : ι → ℝ) (i : κ) (j : ι) : ℝ :=
  (1 / (1 + P (y j))) *
    (-F (x i) * θ (x i - y j) * dividedDifference P (x i) (y j) +
      P (x i) * θ (x i - y j) * dividedDifference F (x i) (y j) +
      F (x i) * P (y j) * offDiagonalGridKernel χ x y i j)

def interactionSchurConstant (CL CH p A LP LF W B : ℝ) : ℝ :=
  A * (4 * W) * schurSchattenConstant CL p LP +
    A * (4 * W) * schurSchattenConstant CL p LF +
      A ^ 2 * schurSchattenConstant CH p B

theorem interactionSchurConstant_nonneg {CL CH p A LP LF W B : ℝ}
    (hCL : 0 ≤ CL) (hCH : 0 ≤ CH) (hp : 1 < p) (hA : 0 ≤ A)
    (hLP : 0 ≤ LP) (hLF : 0 ≤ LF) (hW : 0 ≤ W) (hB : 0 ≤ B) :
    0 ≤ interactionSchurConstant CL CH p A LP LF W B := by
  unfold interactionSchurConstant
  exact add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg hA (by positivity)) (schurSchattenConstant_nonneg hCL hp hLP))
    (mul_nonneg (mul_nonneg hA (by positivity)) (schurSchattenConstant_nonneg hCL hp hLF)))
    (mul_nonneg (sq_nonneg _) (schurSchattenConstant_nonneg hCH hp hB))

section Finite
variable [Fintype ι] [Fintype κ]

/-- The actual finite three-term estimate needs only three displayed bounds
on the same actual input columns and exponent. The Fourier and side-factor
arguments do not require a universal Lipschitz or HMS proposition. -/
theorem finite_factorizedInteraction_schatten_le_of_gridBounds {CL CH p A LP LF B : ℝ}
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (F P θ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) (w : ℝ → ℂ) (hw : Integrable w)
    (hθ : ∀ z, θ z = (∫ ξ, w ξ * Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)).re)
    (hA : 0 ≤ A) (hF : ∀ t, |F t| ≤ A) (hP : ∀ t, |P t| ≤ A) (hP0 : ∀ t, 0 ≤ P t)
    (x : κ → ℝ) (y : ι → ℝ)
    (c : HilbertSchmidtColumns ι E) (hp : 2 ≤ p)
    (hcP : hsSchattenNorm b (finiteMatrixSchurColumns a (lipschitzGridKernel P x y) c) p ≤
      schurSchattenConstant CL p LP * hsSchattenNorm b c p)
    (hcF : hsSchattenNorm b (finiteMatrixSchurColumns a (lipschitzGridKernel F x y) c) p ≤
      schurSchattenConstant CL p LF * hsSchattenNorm b c p)
    (hcχ : hsSchattenNorm b (finiteMatrixSchurColumns a (offDiagonalGridKernel χ x y) c) p ≤
      schurSchattenConstant CH p B * hsSchattenNorm b c p) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (factorizedInteractionGrid F P θ χ x y) c) p ≤
      interactionSchurConstant CL CH p A LP LF (∫ ξ, ‖w ξ‖) B * hsSchattenNorm b c p := by
  let D := fun j => 1 / (1 + P (y j))
  have hD : ∀ j, ‖D j‖ ≤ 1 := by
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (by linarith [hP0 (y j)]))]
    exact (div_le_one (by linarith [hP0 (y j)] : 0 < 1 + P (y j))).mpr (by linarith [hP0 (y j)])
  let N1 := fun i j => θ (x i - y j) * dividedDifference P (x i) (y j)
  let N2 := fun i j => θ (x i - y j) * dividedDifference F (x i) (y j)
  let N3 := offDiagonalGridKernel χ x y
  let d1 := finiteMatrixSchurColumns a (fun i j => (-F (x i)) * N1 i j * D j) c
  let d2 := finiteMatrixSchurColumns a (fun i j => P (x i) * N2 i j * D j) c
  let d3 := finiteMatrixSchurColumns a (fun i j => F (x i) * N3 i j * (P (y j) * D j)) c
  have hc1 : hsSchattenNorm b (finiteMatrixSchurColumns a N1 c) p ≤
      (4 * ∫ ξ, ‖w ξ‖) * schurSchattenConstant CL p LP * hsSchattenNorm b c p := by
    change hsSchattenNorm b (finiteMatrixSchurColumns a
      (fun i j => θ (x i - y j) * lipschitzGridKernel P x y i j) c) p ≤ _
    rw [← finiteMatrixSchurColumns_comp b a (fun i j => θ (x i - y j))
      (lipschitzGridKernel P x y) c]
    have ht := finite_fourierSchur_schatten_le b a w hw x y
      (finiteMatrixSchurColumns a (lipschitzGridKernel P x y) c) hp
    have hfun : (fun i j => realFourierProfile w (x i - y j)) = (fun i j => θ (x i - y j)) := by
      funext i j
      exact (hθ _).symm
    rw [hfun] at ht
    exact ht.trans ((mul_le_mul_of_nonneg_left hcP (by positivity)).trans_eq (by ring))
  have hc2 : hsSchattenNorm b (finiteMatrixSchurColumns a N2 c) p ≤
      (4 * ∫ ξ, ‖w ξ‖) * schurSchattenConstant CL p LF * hsSchattenNorm b c p := by
    change hsSchattenNorm b (finiteMatrixSchurColumns a
      (fun i j => θ (x i - y j) * lipschitzGridKernel F x y i j) c) p ≤ _
    rw [← finiteMatrixSchurColumns_comp b a (fun i j => θ (x i - y j))
      (lipschitzGridKernel F x y) c]
    have ht := finite_fourierSchur_schatten_le b a w hw x y
      (finiteMatrixSchurColumns a (lipschitzGridKernel F x y) c) hp
    have hfun : (fun i j => realFourierProfile w (x i - y j)) = (fun i j => θ (x i - y j)) := by
      funext i j
      exact (hθ _).symm
    rw [hfun] at ht
    exact ht.trans ((mul_le_mul_of_nonneg_left hcF (by positivity)).trans_eq (by ring))
  have hc3 : hsSchattenNorm b (finiteMatrixSchurColumns a N3 c) p ≤
      schurSchattenConstant CH p B * hsSchattenNorm b c p := hcχ
  have hd1 : hsSchattenNorm b d1 p ≤
      (A * (4 * ∫ ξ, ‖w ξ‖) * schurSchattenConstant CL p LP) * hsSchattenNorm b c p := by
    have ht := finiteMatrixSchurColumns_sides_schatten_le b a N1
      (fun i => -F (x i)) D hA zero_le_one (fun i => by simpa only [norm_neg, Real.norm_eq_abs] using hF (x i)) hD c hp
    calc
      _ ≤ A * hsSchattenNorm b (finiteMatrixSchurColumns a N1 c) p * 1 := ht
      _ = A * hsSchattenNorm b (finiteMatrixSchurColumns a N1 c) p := mul_one _
      _ ≤ A * ((4 * ∫ ξ, ‖w ξ‖) * schurSchattenConstant CL p LP * hsSchattenNorm b c p) :=
        mul_le_mul_of_nonneg_left hc1 hA
      _ = _ := by ring
  have hd2 : hsSchattenNorm b d2 p ≤
      (A * (4 * ∫ ξ, ‖w ξ‖) * schurSchattenConstant CL p LF) * hsSchattenNorm b c p := by
    have ht := finiteMatrixSchurColumns_sides_schatten_le b a N2
      (fun i => P (x i)) D hA zero_le_one (fun i => by simpa only [Real.norm_eq_abs] using hP (x i)) hD c hp
    calc
      _ ≤ A * hsSchattenNorm b (finiteMatrixSchurColumns a N2 c) p * 1 := ht
      _ = A * hsSchattenNorm b (finiteMatrixSchurColumns a N2 c) p := mul_one _
      _ ≤ A * ((4 * ∫ ξ, ‖w ξ‖) * schurSchattenConstant CL p LF * hsSchattenNorm b c p) :=
        mul_le_mul_of_nonneg_left hc2 hA
      _ = _ := by ring
  have hd3 : hsSchattenNorm b d3 p ≤
      (A ^ 2 * schurSchattenConstant CH p B) * hsSchattenNorm b c p := by
    have hr : ∀ j, ‖P (y j) * D j‖ ≤ A := by
      intro j
      exact (norm_mul_le _ _).trans ((mul_le_mul (by simpa only [Real.norm_eq_abs] using hP (y j))
        (hD j) (norm_nonneg _) hA).trans_eq (mul_one A))
    have ht := finiteMatrixSchurColumns_sides_schatten_le b a N3
      (fun i => F (x i)) (fun j => P (y j) * D j) hA hA
      (fun i => by simpa only [Real.norm_eq_abs] using hF (x i)) hr c hp
    exact ht.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc3 hA) hA).trans_eq (by ring))
  have heq : finiteMatrixSchurColumns a (factorizedInteractionGrid F P θ χ x y) c = d1 + d2 + d3 := by
    rw [← finiteMatrixSchurColumns_add, ← finiteMatrixSchurColumns_add]
    congr 1
    funext i j
    simp only [factorizedInteractionGrid, N1, N2, N3, D]
    ring
  rw [heq]
  have ht1 := hsSchattenNorm_add_le b d1 d2 hp
  have ht2 := hsSchattenNorm_add_le b (d1 + d2) d3 hp
  unfold interactionSchurConstant
  nlinarith

/-- The existing Lipschitz interface supplies the two divided-difference
grid bounds. The chi bound remains explicit, preserving the original API. -/
theorem finite_factorizedInteraction_schatten_le_of_chiBound {CL CH p A LP LF B : ℝ}
    (hLip : FiniteLipschitzSchur.{uι, uκ, uH, uE} CL)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (F P θ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) (w : ℝ → ℂ) (hw : Integrable w)
    (hθ : ∀ z, θ z = (∫ ξ, w ξ * Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)).re)
    (hA : 0 ≤ A) (hF : ∀ t, |F t| ≤ A) (hP : ∀ t, |P t| ≤ A) (hP0 : ∀ t, 0 ≤ P t)
    (hLP : 0 ≤ LP) (hLF : 0 ≤ LF)
    (hPlip : ∀ s t, |P s - P t| ≤ LP * |s - t|)
    (hFlip : ∀ s t, |F s - F t| ≤ LF * |s - t|)
    (x : κ → ℝ) (y : ι → ℝ)
    (c : HilbertSchmidtColumns ι E) (hp : 2 ≤ p)
    (hcχ : hsSchattenNorm b (finiteMatrixSchurColumns a (offDiagonalGridKernel χ x y) c) p ≤
      schurSchattenConstant CH p B * hsSchattenNorm b c p) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (factorizedInteractionGrid F P θ χ x y) c) p ≤
      interactionSchurConstant CL CH p A LP LF (∫ ξ, ‖w ξ‖) B * hsSchattenNorm b c p := by
  have hcP := hLip.bound b a x y P LP hLP hPlip p hp c
  rw [← finiteMatrixSchurColumns_eq b a _ LP hLP (lipschitzGridKernel_norm_le hLP hPlip x y) c] at hcP
  have hcF := hLip.bound b a x y F LF hLF hFlip p hp c
  rw [← finiteMatrixSchurColumns_eq b a _ LF hLF (lipschitzGridKernel_norm_le hLF hFlip x y) c] at hcF
  exact finite_factorizedInteraction_schatten_le_of_gridBounds b a
    F P θ χ w hw hθ hA hF hP hP0 x y c hp hcP hcF hcχ

theorem finite_factorizedInteraction_schatten_le {CL CH p A LP LF B : ℝ}
    (hLip : FiniteLipschitzSchur.{uι, uκ, uH, uE} CL)
    (hHMS : FiniteHMS.{uι, uκ, uH, uE} CH)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (F P θ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) (w : ℝ → ℂ) (hw : Integrable w)
    (hθ : ∀ z, θ z = (∫ ξ, w ξ * Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)).re)
    (hA : 0 ≤ A) (hF : ∀ t, |F t| ≤ A) (hP : ∀ t, |P t| ≤ A) (hP0 : ∀ t, 0 ≤ P t)
    (hLP : 0 ≤ LP) (hLF : 0 ≤ LF)
    (hPlip : ∀ s t, |P s - P t| ≤ LP * |s - t|)
    (hFlip : ∀ s t, |F s - F t| ≤ LF * |s - t|)
    (hχ : HMSBoundedSymbol χ B) (x : κ → ℝ) (y : ι → ℝ)
    (c : HilbertSchmidtColumns ι E) (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (factorizedInteractionGrid F P θ χ x y) c) p ≤
      interactionSchurConstant CL CH p A LP LF (∫ ξ, ‖w ξ‖) B * hsSchattenNorm b c p := by
  have hcχ := hHMS.bound b a x y χ B hχ p (by linarith) c
  rw [← finiteMatrixSchurColumns_eq b a _ B hχ.bound_nonneg (hχ.grid_norm_le x y) c] at hcχ
  exact finite_factorizedInteraction_schatten_le_of_chiBound hLip b a
    F P θ χ w hw hθ hA hF hP hP0 hLP hLF hPlip hFlip x y c hp hcχ

end Finite

/-- The actual infinite-dimensional three-term bound. The bounded scalar
kernel determines the existing HS map; its Schatten estimate is derived from
the finite analytic leaves and the scalar Fourier representation. -/
theorem factorizedInteraction_schatten_le {CL CH p A LP LF B K : ℝ}
    (hLip : FiniteLipschitzSchur.{uι, uκ, uH, uE} CL)
    (hHMS : FiniteHMS.{uι, uκ, uH, uE} CH)
    (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (F P θ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) (w : ℝ → ℂ) (hw : Integrable w)
    (hθ : ∀ z, θ z = (∫ ξ, w ξ * Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)).re)
    (hA : 0 ≤ A) (hF : ∀ t, |F t| ≤ A) (hP : ∀ t, |P t| ≤ A) (hP0 : ∀ t, 0 ≤ P t)
    (hLP : 0 ≤ LP) (hLF : 0 ≤ LF)
    (hPlip : ∀ s t, |P s - P t| ≤ LP * |s - t|)
    (hFlip : ∀ s t, |F s - F t| ≤ LF * |s - t|)
    (hχ : HMSBoundedSymbol χ B) (x : κ → ℝ) (y : ι → ℝ)
    (hK : 0 ≤ K) (hgrid : ∀ i j, ‖factorizedInteractionGrid F P θ χ x y i j‖ ≤ K)
    (c : HilbertSchmidtColumns ι E) (hp : 2 ≤ p) :
    hsSchattenNorm b (hsSchurMultiplier a (factorizedInteractionGrid F P θ χ x y) K hK hgrid c) p ≤
      interactionSchurConstant CL CH p A LP LF (∫ ξ, ‖w ξ‖) B * hsSchattenNorm b c p := by
  apply hsSchur_schatten_bound_of_finite b a _ K hK hgrid hp
    (interactionSchurConstant_nonneg hLip.constant_nonneg hHMS.constant_nonneg
      (by linarith) hA hLP hLF (integral_nonneg fun _ => norm_nonneg _) hχ.bound_nonneg) ?_ c
  intro s t d
  rw [← finiteMatrixSchurColumns_eq (finiteSpectralLabelBasis b s)
    (finiteSpectralLabelBasis a t) _ K hK (fun i j => hgrid i j) d]
  exact finite_factorizedInteraction_schatten_le hLip hHMS
    (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
    F P θ χ w hw hθ hA hF hP hP0 hLP hLF hPlip hFlip hχ
    (fun i : t => x i) (fun j : s => y j) d hp

theorem factorizedInteractionGrid_norm_le {A LP LF W B : ℝ}
    (F P θ : ℝ → ℝ) (χ : ℝ → ℝ → ℝ)
    (hA : 0 ≤ A) (hLP : 0 ≤ LP) (hLF : 0 ≤ LF) (hW : 0 ≤ W) (hB : 0 ≤ B)
    (hF : ∀ t, |F t| ≤ A) (hP : ∀ t, |P t| ≤ A) (hP0 : ∀ t, 0 ≤ P t)
    (hθ : ∀ t, |θ t| ≤ W) (hχ : ∀ s t, |χ s t| ≤ B)
    (hPlip : ∀ s t, |P s - P t| ≤ LP * |s - t|)
    (hFlip : ∀ s t, |F s - F t| ≤ LF * |s - t|)
    (x : κ → ℝ) (y : ι → ℝ) (i : κ) (j : ι) :
    ‖factorizedInteractionGrid F P θ χ x y i j‖ ≤
      A * W * LP + A * W * LF + A ^ 2 * B := by
  have hD0 : 0 ≤ 1 / (1 + P (y j)) := one_div_nonneg.mpr (by linarith [hP0 (y j)])
  have hD1 : |1 / (1 + P (y j))| ≤ 1 := by
    rw [abs_of_nonneg hD0]
    exact (div_le_one (by linarith [hP0 (y j)] : 0 < 1 + P (y j))).mpr (by linarith [hP0 (y j)])
  have hdP := dividedDifference_norm_le hLP (hPlip (x i) (y j))
  have hdF := dividedDifference_norm_le hLF (hFlip (x i) (y j))
  have hχgrid : |offDiagonalGridKernel χ x y i j| ≤ B := by
    unfold offDiagonalGridKernel
    split_ifs
    · simpa only [abs_zero] using hB
    · exact hχ _ _
  rw [factorizedInteractionGrid, Real.norm_eq_abs, abs_mul]
  refine (mul_le_mul_of_nonneg_right hD1 (abs_nonneg _)).trans ?_
  rw [one_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_neg]
      exact mul_le_mul (mul_le_mul (hF _) (hθ _) (abs_nonneg _) hA)
        (by simpa only [Real.norm_eq_abs] using hdP) (abs_nonneg _) (mul_nonneg hA hW)
    · rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hP _) (hθ _) (abs_nonneg _) hA)
        (by simpa only [Real.norm_eq_abs] using hdF) (abs_nonneg _) (mul_nonneg hA hW)
  · rw [abs_mul, abs_mul]
    have hh := mul_le_mul (mul_le_mul (hF (x i)) (hP (y j)) (abs_nonneg _) hA)
      hχgrid (abs_nonneg _) (mul_nonneg hA hA)
    simpa only [pow_two] using hh

/-- A constant independent of the inverse-profile Lipschitz constant. -/
def interactionProfileConstant (CL CH A LP W B : ℝ) : ℝ :=
  8 * A * W * CL * (LP + 1) + 2 * A ^ 2 * CH * B

theorem interactionProfileConstant_nonneg {CL CH A LP W B : ℝ}
    (hCL : 0 ≤ CL) (hCH : 0 ≤ CH) (hA : 0 ≤ A) (hLP : 0 ≤ LP) (hW : 0 ≤ W) (hB : 0 ≤ B) :
    0 ≤ interactionProfileConstant CL CH A LP W B := by
  unfold interactionProfileConstant
  positivity

theorem interactionSchurConstant_le_profile {CL CH p A LP LF W B : ℝ}
    (hCL : 0 ≤ CL) (hCH : 0 ≤ CH) (hp : 2 ≤ p) (hA : 0 ≤ A)
    (hLP : 0 ≤ LP) (hLF : 0 ≤ LF) (hW : 0 ≤ W) (hB : 0 ≤ B) :
    interactionSchurConstant CL CH p A LP LF W B ≤
      interactionProfileConstant CL CH A LP W B * (1 + LF) * p := by
  have h1 := schurSchattenConstant_le_two_mul hCL hp hLP
  have h2 := schurSchattenConstant_le_two_mul hCL hp hLF
  have h3 := schurSchattenConstant_le_two_mul hCH hp hB
  have hterm : interactionSchurConstant CL CH p A LP LF W B ≤
      (8 * A * W * CL * (LP + LF) + 2 * A ^ 2 * CH * B) * p := by
    unfold interactionSchurConstant
    calc
      _ ≤ A * (4 * W) * (2 * CL * p * LP) +
          A * (4 * W) * (2 * CL * p * LF) + A ^ 2 * (2 * CH * p * B) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (by positivity)))
          (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
      _ = _ := by ring
  refine hterm.trans (mul_le_mul_of_nonneg_right ?_ (by linarith : 0 ≤ p))
  unfold interactionProfileConstant
  have hdiff : 0 ≤ 8 * A * W * CL * (1 + LP * LF) + 2 * A ^ 2 * CH * B * LF := by positivity
  nlinarith

end
end KernelSeq
