import KernelSeq.SphericalLeverage
import KernelSeq.SphereMonomialBlock
import KernelSeq.PolynomialScaleBounds
import KernelSeq.SubspaceSpectralCount
import KernelSeq.PolynomialKernelEnergy

/-!
# Actual spherical scale rows and their quantitative bounds

The row constructor fixes the design law to the actual normalized surface
measure and the input domain to the actual sphere. Its inputs are only the
original associated real RKHS, literal zonal kernel, bounded diagonal,
filter, target, sample size and regularization. No leverage, moment,
counting or eigenvalue estimate is a field or an input.
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology BigOperators
noncomputable section

/-- A fixed positive regularization threshold for degree m. The loss of a
factor m! from choosing one tensor word is harmless for the scale result. -/
def sphericalSmallScaleConstant (m : ℕ) (am ρ A : ℝ) : ℝ :=
  (am * ((1 + 2 * (m : ℝ))^m)⁻¹) / (2 * ResidualFilter.resolvedScaleFactor ρ A)

theorem sphericalSmallScaleConstant_pos {m : ℕ} {am ρ A : ℝ}
    (ham : 0 < am) (hA : 0 ≤ A) : 0 < sphericalSmallScaleConstant m am ρ A := by
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  unfold sphericalSmallScaleConstant
  positivity

section SingleRow
variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [RKHS ℝ H (KernelSphere (EuclideanSpace ℝ ι)) ℝ]
  {κ ρ A : ℝ}

/-- A genuine primitive sphere model, with no estimated quantity among the
inputs. The original fixed Φ can be shared across arbitrary changing rows. -/
def sphericalScaleModel (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (n : ℕ) (hn : 0 < n)
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))
    (lam : ℝ) (hlam : 0 < lam) (φ : ℝ → ℝ)
    (hf : ResidualFilter.SpectralFilter (κ^2) φ)
    (h : ResidualFilter.Contract lam (κ^2) ρ A φ) : SpectralScaleModel κ ρ A where
  H := H
  X := KernelSphere (EuclideanSpace ℝ ι)
  μ := uniformSphere
  kernel_measurable := by
    have heq : (fun p : KernelSphere (EuclideanSpace ℝ ι) × KernelSphere (EuclideanSpace ℝ ι) =>
        rkhsKernel (H := H) p.1 p.2) = fun p => zonalSphereKernel Φ p.1 p.2 :=
      funext fun p => hkernel p.1 p.2
    rw [heq]
    exact (zonalSphereKernel_continuous Φ hΦ).measurable
  kappa_nonneg := hκ
  diagonal_bound := by intro x; rw [hkernel, zonalSphereKernel_diag]; exact hdiag
  n := n
  sample_pos := hn
  f := f
  lam := lam
  lambda_pos := hlam
  φ := φ
  spectral_filter := hf
  filter_contract := h

variable (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ x y : KernelSphere (EuclideanSpace ℝ ι),
      rkhsKernel (H := H) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (n : ℕ) (hn : 0 < n)
    (f : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))
    (lam : ℝ) (hlam : 0 < lam) (φ : ℝ → ℝ)
    (hf : ResidualFilter.SpectralFilter (κ^2) φ)
    (h : ResidualFilter.Contract lam (κ^2) ρ A φ)

omit [DecidableEq ι] in
/-- The spherical addition-formula consequence is supplied by actual
orthogonal symmetry, with no harmonic basis assumption. -/
theorem sphericalScaleModel_leverage_eq_dimension :
    (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).L =
      (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).N := by
  exact zonalSphere_leverageEssentialSup_eq_effectiveDimension Φ hΦ hkernel hlam

omit [DecidableEq ι] in
theorem sphericalScaleModel_dimension_le_trace :
    (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).N ≤ κ^2 / lam := by
  rw [← sphericalScaleModel_leverage_eq_dimension Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h]
  exact (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).L_le_universal

/-- The actual finite tensor block forces genuinely many population
coordinates to be resolved by the original filter. -/
theorem sphericalScaleModel_filter_dimension_lower
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j * t^j) (Φ t))
    (m : ℕ)
    (hsmall : 2 * lam * ResidualFilter.resolvedScaleFactor ρ A ≤ a m * degreeSphereMoment ι m) :
    (1 / 4 : ℝ) * ((Fintype.card ι).choose m : ℝ) ≤
      (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).Q := by
  let k := rkhsFeature (H := H)
  let hk := zonalSphereFeature_memLp Φ hΦ hkernel
  have hA := h.constant_nonneg hlam (sq_nonneg κ)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  have hc : 0 < 2 * lam * ResidualFilter.resolvedScaleFactor ρ A := by positivity
  have hcoercive (x : squarefreeSphereBlock ι m) :
      (2 * lam * ResidualFilter.resolvedScaleFactor ρ A) * ‖(x : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))‖^2 ≤
        ‖(featureEmbedding uniformSphere k hk).adjoint (x : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))‖^2 := by
    have hframe := squarefreeSphereBlock_tensor_energy_lower (x : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) x.property
    have he := featureAdjoint_powerSeries_energy_lower k hk
      (fun x : KernelSphere (EuclideanSpace ℝ ι) => (x : EuclideanSpace ℝ ι))
      measurable_subtype_coe (fun x => (mem_sphere_zero_iff_norm.mp x.property).le)
      a ha Φ hseries (by
        intro x y
        change inner ℝ (rkhsFeature (H := H) x) (rkhsFeature (H := H) y) = _
        rw [rkhsFeature_inner, rkhsFeature_apply, hkernel]
        rfl) (x : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) m
    calc
      _ ≤ a m * degreeSphereMoment ι m * ‖(x : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι)))‖^2 :=
        mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
      _ ≤ a m * tensorMomentEnergy uniformSphere
          (fun x : KernelSphere (EuclideanSpace ℝ ι) => (x : EuclideanSpace ℝ ι)) m
          (x : Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ ι))) := by
        simpa only [tensorMomentEnergy, tensorMonomial, mul_assoc] using
          mul_le_mul_of_nonneg_left hframe (ha m)
      _ ≤ _ := he
  have hcount := finrank_le_featureSpectralCount_of_prediction_subspace k hk
    (squarefreeSphereBlock ι m) hc hcoercive
  rw [squarefreeSphereBlock_finrank] at hcount
  have hthresh : 2 * lam * ResidualFilter.resolvedScaleFactor ρ A / 2 =
      lam * ResidualFilter.resolvedScaleFactor ρ A := by ring
  rw [hthresh] at hcount
  have hh : ((Fintype.card ι).choose m : ℝ) ≤
      (featureSpectralCount k hk (lam * ResidualFilter.resolvedScaleFactor ρ A) : ℝ) :=
    by exact_mod_cast hcount
  have hM : ‖populationCovariance (featureEmbedding uniformSphere k hk)‖ ≤ κ^2 :=
    (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).population_bound
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1/4)).trans
    (quarter_mul_featureSpectralCount_le_filterDimension k hk φ hlam hM hf h)


/-- The original small-c schedule supplies the actual regularized block
condition, using the exact sphere moments proved from rotations. -/
theorem sphericalScaleModel_filter_dimension_lower_of_small_constant
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j * t^j) (Φ t))
    (m : ℕ) {c : ℝ} (hc : c ≤ sphericalSmallScaleConstant m (a m) ρ A)
    (hreg : lam = c * (Fintype.card ι : ℝ)^(-(m : ℝ))) :
    (1 / 4 : ℝ) * ((Fintype.card ι).choose m : ℝ) ≤
      (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).Q := by
  have hA := h.constant_nonneg hlam (sq_nonneg κ)
  have hD := ResidualFilter.resolvedScaleFactor_pos (ρ := ρ) hA
  have hcs : 2 * c * ResidualFilter.resolvedScaleFactor ρ A ≤
      a m * ((1 + 2 * (m : ℝ))^m)⁻¹ := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hD)).mp hc
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_left (degreeSphereMoment_ge_dimension_power (ι := ι) m) (ha m)
  have hdp := Real.rpow_nonneg (Nat.cast_nonneg (Fintype.card ι)) (-(m : ℝ))
  have hh := mul_le_mul_of_nonneg_right hcs hdp
  apply sphericalScaleModel_filter_dimension_lower Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h a ha hseries m
  rw [hreg]
  nlinarith only [hh, hm]

/-- Actual Q positivity and its inverse bound. Every quantity in this
conclusion comes from the actual covariance, original filter and uniform
sphere law. No block, moment, spectral or leverage bound is an input. -/
theorem sphericalScaleModel_inverse_filter_dimension_bound
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j * t^j) (Φ t))
    (m : ℕ) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ sphericalSmallScaleConstant m (a m) ρ A)
    (hreg : lam = c * (Fintype.card ι : ℝ)^(-(m : ℝ)))
    (hd : 2*m ≤ Fintype.card ι) :
    let model := sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h
    0 < model.Q ∧ model.Q⁻¹ ≤ (4 * 2^m * (m.factorial : ℝ) / c) * lam := by
  dsimp only
  let Q := (sphericalScaleModel Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h).Q
  have hraw := sphericalScaleModel_filter_dimension_lower_of_small_constant
    Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h a ha hseries m hc hreg
  have hdim := squarefreeSphereBlock_dimension_lower (ι := ι) m hd
  rw [squarefreeSphereBlock_finrank] at hdim
  have hcoarse : (Fintype.card ι : ℝ)^m / (4 * 2^m * (m.factorial : ℝ)) ≤ Q := by
    have hh := mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 1/4)
    dsimp only [Q]
    calc
      _ = (1/4 : ℝ) * ((Fintype.card ι : ℝ)^m / (2^m * (m.factorial : ℝ))) := by ring
      _ ≤ _ := hh.trans hraw
  have hd0 : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hbase : 0 < (Fintype.card ι : ℝ)^m / (4 * 2^m * (m.factorial : ℝ)) := by
    have hf : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr m.factorial_pos
    positivity
  have hQ := hbase.trans_le hcoarse
  refine ⟨hQ, ?_⟩
  have hh := one_div_le_one_div_of_le hbase hcoarse
  have heq : (1 : ℝ) / ((Fintype.card ι : ℝ)^m / (4 * 2^m * (m.factorial : ℝ))) =
      (4 * 2^m * (m.factorial : ℝ) / c) * lam := by
    rw [hreg, Real.rpow_neg hd0.le, Real.rpow_natCast]
    field_simp
  simpa only [one_div, heq] using hh


end SingleRow
end
end KernelSeq
