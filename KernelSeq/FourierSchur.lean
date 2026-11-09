import KernelSeq.FiniteSchurExtension
import KernelSeq.SchattenIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FunProp

/-!
# Fourier-L1 Schur bounds on actual real Hilbert--Schmidt operators

Real separated kernels are implemented by actual left/right diagonal factors.
Their integrals are actual HS-valued Bochner integrals, with the grid Fourier
identity proved coefficient by coefficient. Fourier kernels are split into
four real cosine/sine separated factors, giving a constant independent of p.
The final finite-to-infinite extension does not use complex Schatten spaces,
an HMS bound, or an assumed Fourier multiplier operator identity.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace KernelSeq

noncomputable section

variable {ι κ H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Finite

variable [Fintype ι] [Fintype κ]

/-- The actual HS columns of an arbitrary finite Schur matrix. A finite sum
of actual single columns avoids a measurability or HS-membership certificate. -/
def finiteMatrixSchurColumns (a : HilbertBasis κ ℝ E) (M : κ → ι → ℝ)
    (c : HilbertSchmidtColumns ι E) : HilbertSchmidtColumns ι E := by
  classical
  exact ∑ j, ∑ i, M i j • ((inner ℝ (a i) (c j)) • lp.single 2 j (a i))

omit [CompleteSpace E] in
@[simp]
theorem finiteMatrixSchurColumns_apply (a : HilbertBasis κ ℝ E) (M : κ → ι → ℝ)
    (c : HilbertSchmidtColumns ι E) (j : ι) :
    finiteMatrixSchurColumns a M c j = ∑ i, (M i j * inner ℝ (a i) (c j)) • a i := by
  classical
  simp only [finiteMatrixSchurColumns, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_smul]
  simp only [smul_ite, smul_zero, Finset.sum_ite_irrel]
  simp

omit [CompleteSpace H] in
/-- Exact finite cross-basis coefficients of the actual column construction. -/
theorem finiteMatrixSchurColumns_coefficient (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (M : κ → ι → ℝ) (c : HilbertSchmidtColumns ι E) (i : κ) (j : ι) :
    inner ℝ (a i) (hilbertSchmidtOperator b (finiteMatrixSchurColumns a M c) (b j)) =
      M i j * inner ℝ (a i) (c j) := by
  classical
  rw [hilbertSchmidtOperator_basis, finiteMatrixSchurColumns_apply]
  simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.mp a.orthonormal]
  simp

omit [CompleteSpace H] in
/-- The explicit finite columns equal the actual bounded-kernel HS Schur map. -/
theorem finiteMatrixSchurColumns_eq (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (M : κ → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hM : ∀ i j, ‖M i j‖ ≤ K)
    (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a M c = hsSchurMultiplier a M K hK hM c := by
  apply hilbertSchmidtOperator_injective b
  symm
  apply hsSchurMultiplier_represents
  intro i j
  rw [finiteMatrixSchurColumns_coefficient, hilbertSchmidtOperator_basis]

/-- Real separation is an exact actual left/right factorization. -/
theorem finiteSeparatedSchurColumns_eq (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (u : κ → ℝ) (v : ι → ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1)
    (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a (fun i j => u i * v j) c =
      hsLeftComposition (hilbertDiagonal a u 1 zero_le_one hu)
        (hsRightComposition b b a (hilbertDiagonal b v 1 zero_le_one hv) c) := by
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
  have hd : inner ℝ (a i) (hilbertDiagonal a u 1 zero_le_one hu (c j)) =
      u i * inner ℝ (a i) (c j) := by
    simpa only [HilbertBasis.repr_apply_apply] using hilbertDiagonal_repr a u 1 zero_le_one hu (c j) i
  rw [hd]
  ring

/-- A real separated kernel whose two scalar factors are contractions has a
uniform Schatten bound, with no factor growing in p. -/
theorem finiteSeparatedSchur_schatten_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (u : κ → ℝ) (v : ι → ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ 1)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteMatrixSchurColumns a (fun i j => u i * v j) c) p ≤
      hsSchattenNorm b c p := by
  rw [finiteSeparatedSchurColumns_eq b a u v hu hv c]
  refine (hsSchattenNorm_twoSidedComposition_le b b a _ _ c hp).trans ?_
  have h1 := hilbertDiagonal_norm_le a u 1 zero_le_one hu
  have h2 := hilbertDiagonal_norm_le b v 1 zero_le_one hv
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h1 (hsSchattenNorm_nonneg b c p)) (norm_nonneg _)).trans
    (by simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_left h2 (hsSchattenNorm_nonneg b c p))

omit [CompleteSpace E] in
/-- Linearity in a common real scalar, at the level of the actual HS columns. -/
theorem finiteMatrixSchurColumns_smul (a : HilbertBasis κ ℝ E) (M : κ → ι → ℝ)
    (r : ℝ) (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a (fun i j => r * M i j) c = r • finiteMatrixSchurColumns a M c := by
  classical
  simp only [finiteMatrixSchurColumns, Finset.smul_sum, mul_smul]

omit [CompleteSpace E] in
/-- Additivity of the actual finite Schur columns in the scalar matrix. -/
theorem finiteMatrixSchurColumns_add (a : HilbertBasis κ ℝ E) (M N : κ → ι → ℝ)
    (c : HilbertSchmidtColumns ι E) :
    finiteMatrixSchurColumns a (fun i j => M i j + N i j) c =
      finiteMatrixSchurColumns a M c + finiteMatrixSchurColumns a N c := by
  classical
  simp only [finiteMatrixSchurColumns, add_smul, Finset.sum_add_distrib]

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

omit [CompleteSpace E] in
/-- Integrability of every scalar coordinate gives actual HS integrability
for a finite grid, without an operator-valued measurability premise. -/
theorem integrable_finiteMatrixSchurColumns (a : HilbertBasis κ ℝ E)
    (M : Ω → κ → ι → ℝ) (hM : ∀ i j, Integrable (fun ω => M ω i j) ν)
    (c : HilbertSchmidtColumns ι E) :
    Integrable (fun ω => finiteMatrixSchurColumns a (M ω) c) ν := by
  classical
  unfold finiteMatrixSchurColumns
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro i _
  exact (hM i j).smul_const _

/-- The actual HS Bochner integral has exactly the integrated scalar matrix;
this proves the Fourier/Schur reconstruction step, rather than assuming it. -/
theorem integral_finiteMatrixSchurColumns (a : HilbertBasis κ ℝ E)
    (M : Ω → κ → ι → ℝ) (hM : ∀ i j, Integrable (fun ω => M ω i j) ν)
    (c : HilbertSchmidtColumns ι E) :
    (∫ ω, finiteMatrixSchurColumns a (M ω) c ∂ν) =
      finiteMatrixSchurColumns a (fun i j => ∫ ω, M ω i j ∂ν) c := by
  classical
  unfold finiteMatrixSchurColumns
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => (hM i j).smul_const _))]
  congr 1
  funext j
  rw [integral_finsetSum _ (fun i _ => (hM i j).smul_const _)]
  simp only [integral_smul_const]

/-- A general absolutely integrable real separated-kernel representation gives
an actual finite-grid Schatten bound with constant one, independently of p. -/
theorem finite_realSeparatedIntegral_schatten_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (w : Ω → ℝ) (hw : Integrable w ν) (u : Ω → κ → ℝ) (v : Ω → ι → ℝ)
    (hu : ∀ i, AEStronglyMeasurable (fun ω => u ω i) ν)
    (hv : ∀ j, AEStronglyMeasurable (fun ω => v ω j) ν)
    (hub : ∀ ω i, ‖u ω i‖ ≤ 1) (hvb : ∀ ω j, ‖v ω j‖ ≤ 1)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteMatrixSchurColumns a
      (fun i j => ∫ ω, w ω * (u ω i * v ω j) ∂ν) c) p ≤
      (∫ ω, |w ω| ∂ν) * hsSchattenNorm b c p := by
  have hcoords : ∀ i j, Integrable (fun ω => w ω * (u ω i * v ω j)) ν := by
    intro i j
    apply hw.mul_bdd ((hu i).mul (hv j))
    exact Eventually.of_forall fun ω => (norm_mul_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul (hub ω i) (hvb ω j) (norm_nonneg _) zero_le_one)
  rw [← integral_finiteMatrixSchurColumns a _ hcoords c]
  have hF := integrable_finiteMatrixSchurColumns a _ hcoords c
  calc
    _ ≤ ∫ ω, |w ω| * hsSchattenNorm b c p ∂ν :=
      hsSchattenNorm_integral_le_of_ae_bound b hp _ hF _
        (hw.norm.mul_const _) (Eventually.of_forall fun ω => by
          rw [finiteMatrixSchurColumns_smul, hsSchattenNorm_smul b _ _ hp]
          exact mul_le_mul_of_nonneg_left
            (finiteSeparatedSchur_schatten_le b a (u ω) (v ω) (hub ω) (hvb ω) c hp) (abs_nonneg _))
    _ = _ := integral_mul_const _ _

end Integral
end Finite

/-- The real Fourier representation with unnormalized exponential. Any Fourier
normalization constant belongs in the integrable density `w`. -/
def realFourierProfile (w : ℝ → ℂ) (z : ℝ) : ℝ :=
  (∫ ξ, w ξ * Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)).re

/-- The actual complex Fourier integrand is integrable, derived from `w ∈ L¹`
and unit modulus of its exponential factor. -/
theorem integrable_fourierProduct (w : ℝ → ℂ) (hw : Integrable w) (z : ℝ) :
    Integrable (fun ξ => w ξ * Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)) := by
  apply hw.mul_bdd
  · have hc : Continuous (fun ξ : ℝ => Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)) := by fun_prop
    exact hc.aestronglyMeasurable
  · exact Eventually.of_forall fun ξ => by rw [Complex.norm_exp_ofReal_mul_I]

/-- Passing to the real part commutes with the genuine scalar Bochner integral. -/
theorem realFourierProfile_eq_integral (w : ℝ → ℂ) (hw : Integrable w) (z : ℝ) :
    realFourierProfile w z =
      ∫ ξ, (w ξ * Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)).re :=
  (Complex.reCLM.integral_comp_comm (integrable_fourierProduct w hw z)).symm

/-- The pointwise Fourier integrand has its actual scalar L¹ majorant. -/
theorem fourierEntry_norm_le (w : ℂ) (s : ℝ) :
    ‖(w * Complex.exp ((s : ℂ) * Complex.I)).re‖ ≤ ‖w‖ := by
  refine (Complex.abs_re_le_norm _).trans_eq ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The Fourier profile is bounded by the true density L¹ norm. -/
theorem realFourierProfile_norm_le (w : ℝ → ℂ) (hw : Integrable w) (z : ℝ) :
    ‖realFourierProfile w z‖ ≤ ∫ ξ, ‖w ξ‖ := by
  rw [realFourierProfile_eq_integral w hw z]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono ((integrable_fourierProduct w hw z).re.norm) hw.norm (fun ξ => fourierEntry_norm_le _ _))

/-- Four real separated factors exactly equal the real complex exponential
kernel. This identity introduces no complex operator or complex Schatten norm. -/
theorem fourierEntry_four_real_factors (w : ℂ) (s t : ℝ) :
    (w * Complex.exp (((s - t : ℝ) : ℂ) * Complex.I)).re =
      ((w.re * (Real.cos s * Real.cos t) + w.re * (Real.sin s * Real.sin t)) +
        (-w.im) * (Real.sin s * Real.cos t)) + w.im * (Real.cos s * Real.sin t) := by
  rw [Complex.mul_re, Complex.exp_re, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
    Real.exp_zero, one_mul]
  rw [Real.cos_sub, Real.sin_sub]
  ring

section FourierFinite

variable [Fintype ι] [Fintype κ]

/-- A fixed Fourier integrand is bounded in every p≥2 by four real diagonal
contractions. The constant four is independent of p and of the scalar grids. -/
theorem finite_fourierEntry_schatten_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (w : ℂ) (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E)
    {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteMatrixSchurColumns a
      (fun i j => (w * Complex.exp (((x i - y j : ℝ) : ℂ) * Complex.I)).re) c) p ≤
      4 * ‖w‖ * hsSchattenNorm b c p := by
  let d1 := finiteMatrixSchurColumns a (fun i j => Real.cos (x i) * Real.cos (y j)) c
  let d2 := finiteMatrixSchurColumns a (fun i j => Real.sin (x i) * Real.sin (y j)) c
  let d3 := finiteMatrixSchurColumns a (fun i j => Real.sin (x i) * Real.cos (y j)) c
  let d4 := finiteMatrixSchurColumns a (fun i j => Real.cos (x i) * Real.sin (y j)) c
  have hcos (s : ℝ) : ‖Real.cos s‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one s
  have hsin (s : ℝ) : ‖Real.sin s‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one s
  have h1 : hsSchattenNorm b (w.re • d1) p ≤ ‖w‖ * hsSchattenNorm b c p := by
    rw [hsSchattenNorm_smul b _ _ hp]
    exact (mul_le_mul_of_nonneg_left (finiteSeparatedSchur_schatten_le b a _ _
      (fun i => hcos (x i)) (fun j => hcos (y j)) c hp) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm w) (hsSchattenNorm_nonneg b c p))
  have h2 : hsSchattenNorm b (w.re • d2) p ≤ ‖w‖ * hsSchattenNorm b c p := by
    rw [hsSchattenNorm_smul b _ _ hp]
    exact (mul_le_mul_of_nonneg_left (finiteSeparatedSchur_schatten_le b a _ _
      (fun i => hsin (x i)) (fun j => hsin (y j)) c hp) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm w) (hsSchattenNorm_nonneg b c p))
  have h3 : hsSchattenNorm b ((-w.im) • d3) p ≤ ‖w‖ * hsSchattenNorm b c p := by
    rw [hsSchattenNorm_smul b _ _ hp, abs_neg]
    exact (mul_le_mul_of_nonneg_left (finiteSeparatedSchur_schatten_le b a _ _
      (fun i => hsin (x i)) (fun j => hcos (y j)) c hp) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm w) (hsSchattenNorm_nonneg b c p))
  have h4 : hsSchattenNorm b (w.im • d4) p ≤ ‖w‖ * hsSchattenNorm b c p := by
    rw [hsSchattenNorm_smul b _ _ hp]
    exact (mul_le_mul_of_nonneg_left (finiteSeparatedSchur_schatten_le b a _ _
      (fun i => hcos (x i)) (fun j => hsin (y j)) c hp) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm w) (hsSchattenNorm_nonneg b c p))
  have hmatrix : (fun i j => (w * Complex.exp (((x i - y j : ℝ) : ℂ) * Complex.I)).re) =
      (fun i j => ((w.re * (Real.cos (x i) * Real.cos (y j)) +
        w.re * (Real.sin (x i) * Real.sin (y j))) +
          (-w.im) * (Real.sin (x i) * Real.cos (y j))) +
            w.im * (Real.cos (x i) * Real.sin (y j))) := by
    funext i j
    exact fourierEntry_four_real_factors w (x i) (y j)
  rw [hmatrix]
  simp only [finiteMatrixSchurColumns_add, finiteMatrixSchurColumns_smul]
  change hsSchattenNorm b (((w.re • d1 + w.re • d2) + (-w.im) • d3) + w.im • d4) p ≤ _
  have ht1 := hsSchattenNorm_add_le b (w.re • d1) (w.re • d2) hp
  have ht2 := hsSchattenNorm_add_le b (w.re • d1 + w.re • d2) ((-w.im) • d3) hp
  have ht3 := hsSchattenNorm_add_le b ((w.re • d1 + w.re • d2) + (-w.im) • d3) (w.im • d4) hp
  linarith

/-- The actual finite-grid Fourier-L1 Schur estimate. The integrated HS columns
are reconstructed from the scalar Fourier representation, not assumed to be a
DOI output. All HS integrability follows from scalar density integrability. -/
theorem finite_fourierSchur_schatten_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (w : ℝ → ℂ) (hw : Integrable w) (x : κ → ℝ) (y : ι → ℝ)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (finiteMatrixSchurColumns a
      (fun i j => realFourierProfile w (x i - y j)) c) p ≤
      (4 * ∫ ξ, ‖w ξ‖) * hsSchattenNorm b c p := by
  let M := fun ξ i j => (w ξ * Complex.exp (((ξ * (x i - y j) : ℝ) : ℂ) * Complex.I)).re
  have hcoords : ∀ i j, Integrable (fun ξ => M ξ i j) :=
    fun i j => (integrable_fourierProduct w hw (x i - y j)).re
  have hprofile : (fun i j => realFourierProfile w (x i - y j)) =
      (fun i j => ∫ ξ, M ξ i j) := by
    funext i j
    exact realFourierProfile_eq_integral w hw (x i - y j)
  rw [hprofile, ← integral_finiteMatrixSchurColumns a M hcoords c]
  have hF := integrable_finiteMatrixSchurColumns a M hcoords c
  calc
    _ ≤ ∫ ξ, 4 * ‖w ξ‖ * hsSchattenNorm b c p :=
      hsSchattenNorm_integral_le_of_ae_bound b hp _ hF _ ((hw.norm.const_mul 4).mul_const _)
        (Eventually.of_forall fun ξ => by
          have ht := finite_fourierEntry_schatten_le b a (w ξ) (fun i => ξ * x i) (fun j => ξ * y j) c hp
          simpa only [M, mul_sub] using ht)
    _ = _ := by rw [integral_mul_const, integral_const_mul]

end FourierFinite

/-- The actual Fourier grid kernel, with no diagonal removal. Its diagonal
value is the genuine scalar value θ(0). -/
def fourierGridKernel (w : ℝ → ℂ) (x : κ → ℝ) (y : ι → ℝ) (i : κ) (j : ι) : ℝ :=
  realFourierProfile w (x i - y j)

/-- Fourier-L1 representation proves a uniform p≥2 bound for the actual
infinite HS Schur DOI. The constant four has no p-dependence. This applies to
any integrable density; no bound for a particular localization kernel is a
premise, and no external Schur multiplier theorem is used. -/
theorem infinite_fourierSchur_schatten_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (w : ℝ → ℂ) (hw : Integrable w) (x : κ → ℝ) (y : ι → ℝ)
    (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (hsSchurMultiplier a (fourierGridKernel w x y) (∫ ξ, ‖w ξ‖)
      (integral_nonneg fun _ => norm_nonneg _) (fun i j => realFourierProfile_norm_le w hw _) c) p ≤
      (4 * ∫ ξ, ‖w ξ‖) * hsSchattenNorm b c p := by
  apply hsSchur_schatten_bound_of_finite b a _ _ _ _ hp (by positivity) ?_ c
  intro s t d
  have ht := finite_fourierSchur_schatten_le (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
    w hw (fun i : t => x i) (fun j : s => y j) d hp
  rw [finiteMatrixSchurColumns_eq (finiteSpectralLabelBasis b s) (finiteSpectralLabelBasis a t)
    _ (∫ ξ, ‖w ξ‖) (integral_nonneg fun _ => norm_nonneg _)
    (fun i j => realFourierProfile_norm_le w hw _) d] at ht
  exact ht

/-- A supplied scalar Fourier-L1 representation gives the actual infinite
Schur bound for that scalar profile. This hypothesis is scalar analysis only;
it is not an operator multiplier or localization-interaction certificate. -/
theorem fourierRepresentedGrid_schatten_le (b : HilbertBasis ι ℝ H) (a : HilbertBasis κ ℝ E)
    (θ : ℝ → ℝ) (w : ℝ → ℂ) (hw : Integrable w)
    (hθ : ∀ z, θ z = (∫ ξ, w ξ * Complex.exp (((ξ * z : ℝ) : ℂ) * Complex.I)).re)
    (x : κ → ℝ) (y : ι → ℝ) (c : HilbertSchmidtColumns ι E) {p : ℝ} (hp : 2 ≤ p) :
    hsSchattenNorm b (hsSchurMultiplier a (fun i j => θ (x i - y j)) (∫ ξ, ‖w ξ‖)
      (integral_nonneg fun _ => norm_nonneg _) (fun i j => by
        rw [hθ]
        exact realFourierProfile_norm_le w hw _) c) p ≤
      (4 * ∫ ξ, ‖w ξ‖) * hsSchattenNorm b c p := by
  have hfun : θ = realFourierProfile w := funext hθ
  subst θ
  exact infinite_fourierSchur_schatten_le b a w hw x y c hp

end
end KernelSeq
