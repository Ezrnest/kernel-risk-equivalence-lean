import KernelSeq.SphericalSpectralDecomposition
import KernelSeq.EigenbasisWeightedSum
import KernelSeq.SpectralMoments

/-!
# Exact population spectral sums by actual spherical degree

The basis change retains all multiplicities and counts each actual
orthogonal polynomial layer once. Nonnegative weighted sums may be regrouped
even when distinct degrees have the same eigenvalue. The finite trace and
effective dimensions have real `HasSum` results, not only identities of
totalized infinite sums.
-/

namespace KernelSeq
open MeasureTheory Set
open scoped ContDiff ENNReal BigOperators
noncomputable section

section SupportedOperator
variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Restrict the genuine prediction operator to its closed prediction range. -/
def supportedPredictionCovariance (S : H →L[ℝ] E) :
    PredictionRange S →L[ℝ] PredictionRange S :=
  ((S.comp S.adjoint).comp (PredictionRange S).subtypeL).codRestrict (PredictionRange S)
    (fun f => S.range.le_topologicalClosure ⟨S.adjoint (f : E), rfl⟩)

theorem supportedPredictionCovariance_isSymmetric (S : H →L[ℝ] E) :
    (supportedPredictionCovariance S).IsSymmetric :=
  fun x y => (ContinuousLinearMap.isPositive_self_comp_adjoint S).isSymmetric (x : E) (y : E)

end SupportedOperator

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (k : KernelSphere (EuclideanSpace ℝ ι) → H) (hk : MemLp k 2 uniformSphere)
  (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (Φ : ℝ → ℝ)
  (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
  (hkernel : ∀ x y, inner ℝ (k x) (k y) = zonalSphereKernel Φ x y)
  (hΦ : ContDiffOn ℝ (((⊤ : ℕ∞) : ℕ∞ω)) Φ (Icc (-1 : ℝ) 1))

local notation "S" => featureEmbedding uniformSphere k hk
local notation "μd" => zonalSphereDegreeValue (ι := ι) a
local notation "Dm" => fun m : ℕ => Module.finrank ℝ (spherePolynomialLayer ι m)

include ha hseries hkernel hΦ in
set_option maxHeartbeats 1800000 in
theorem zonalSphere_positiveSpectrum_tsum_ennreal (w : ℝ → ℝ≥0∞) :
    (∑' i : PredictionSingularIndex S, w i.1.1) =
      ∑' m : ℕ, (Dm m : ℝ≥0∞) * w (μd m) := by
  let hc : IsCompactOperator ((S).adjoint.comp S) :=
    populationCovariance_feature_isCompact uniformSphere k hk
  let L := supportedPredictionCovariance S
  let b := predictionSingularBasis S hc
  let e := zonalSpherePredictionBasis k hk a ha Φ hseries hkernel
  have hb (i : PredictionSingularIndex S) : L (b i) = i.1.1 • b i :=
    Subtype.ext (predictionSingularBasis_eigen S hc i)
  have he (p : SpherePolynomialSpectralIndex ι) : L (e p) = μd p.1 • e p :=
    Subtype.ext (zonalSpherePredictionBasis_eigen k hk a ha Φ hseries hkernel hΦ p)
  rw [eigenbases_tsum_eq_ennreal L (supportedPredictionCovariance_isSymmetric S)
    b e (fun i => i.1.1) (fun p => μd p.1) hb he w, ENNReal.tsum_sigma']
  apply tsum_congr
  intro m
  rw [tsum_fintype]
  change (∑ _ : Fin (Dm m), w (μd m)) = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

include ha hseries hkernel hΦ in
/-- Any actual finite nonnegative population spectral sum can be computed on
the spherical degree layers with their true dimensions. -/
theorem hasSum_zonalSphere_positiveSpectrum (w : ℝ → ℝ)
    (hw : ∀ t ≥ 0, 0 ≤ w t)
    (hs : Summable (fun i : PredictionSingularIndex S => w i.1.1)) :
    HasSum (fun m : ℕ => (Dm m : ℝ) * w (μd m)) (∑' i : PredictionSingularIndex S, w i.1.1) := by
  let F : ℕ → ℝ := fun m => (Dm m : ℝ)*w (μd m)
  have hF (m : ℕ) : 0 ≤ F m :=
    mul_nonneg (Nat.cast_nonneg _) (hw _ (zonalSphereDegreeValue_nonneg a (fun j => (ha j).le) m))
  have hn (i : PredictionSingularIndex S) : 0 ≤ w i.1.1 := hw _ i.2.le
  have hh := zonalSphere_positiveSpectrum_tsum_ennreal k hk a ha Φ hseries hkernel hΦ
    (fun t => ENNReal.ofReal (w t))
  change (∑' i : PredictionSingularIndex S, ENNReal.ofReal (w i.1.1)) =
    ∑' m : ℕ, (Dm m : ℝ≥0∞) * ENNReal.ofReal (w (μd m)) at hh
  have he (m : ℕ) : (Dm m : ℝ≥0∞) * ENNReal.ofReal (w (μd m)) = ENNReal.ofReal (F m) := by
    dsimp only [F]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn hs] at hh
  simp only [he] at hh
  have ht : (∑' m, ENNReal.ofReal (F m)) ≠ (⊤ : ℝ≥0∞) := hh ▸ ENNReal.ofReal_ne_top
  have hh' := ENNReal.hasSum_toReal ht
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), ← hh,
    ENNReal.toReal_ofReal (tsum_nonneg hn)] at hh'
  simpa only [ENNReal.toReal_ofReal (hF _)] using hh'

variable [TopologicalSpace.SeparableSpace H]

include ha hseries hkernel hΦ in
theorem hasSum_zonalSphere_filterDimension (φ : ℝ → ℝ) {lam M ρ A : ℝ}
    (hlam : 0 < lam) (hM : ‖populationCovariance S‖ ≤ M)
    (hfilter : ResidualFilter.SpectralFilter M φ) (h : ResidualFilter.Contract lam M ρ A φ) :
    HasSum (fun m : ℕ => (Dm m : ℝ) * ResidualFilter.shrinkage φ (μd m)^2)
      (featureFilterDimension k hk φ) := by
  rw [featureFilterDimension_eq_positive_sequence]
  exact hasSum_zonalSphere_positiveSpectrum k hk a ha Φ hseries hkernel hΦ
    (fun t => ResidualFilter.shrinkage φ t ^ 2) (fun _ _ => sq_nonneg _)
    (summable_positive_sequence_filterDimension k hk φ hlam hM hfilter h)

include ha hseries hkernel hΦ in
theorem hasSum_zonalSphere_effectiveDimension (lam : ℝ) (hlam : 0 < lam) :
    HasSum (fun m : ℕ => (Dm m : ℝ) * (μd m/(μd m+lam))) (featureEffectiveDimension k hk lam) := by
  rw [featureEffectiveDimension_eq_positive_sequence]
  exact hasSum_zonalSphere_positiveSpectrum k hk a ha Φ hseries hkernel hΦ
    (fun t => t/(t+lam)) (fun t ht => div_nonneg ht (by linarith))
    ((summable_featureEffectiveDimension k hk lam hlam).subtype _)

include ha hseries hkernel hΦ in
theorem hasSum_zonalSphere_covarianceTrace :
    HasSum (fun m : ℕ => (Dm m : ℝ) * μd m) (featureCovarianceTrace k hk) := by
  have he : featureCovarianceTrace k hk = ∑' i : PredictionSingularIndex S, i.1.1 := by
    unfold featureCovarianceTrace
    symm
    apply tsum_subtype_eq_of_support_subset
      (s := {i : FeatureCovarianceIndex k hk | 0 < i.1}) (f := fun i => i.1)
    intro i hi
    have ht := compactEigenvalue_nonneg _ (populationCovariance_feature_isCompact uniformSphere k hk)
      (populationCovariance_isPositive S) i
    exact lt_of_le_of_ne ht (Ne.symm hi)
  rw [he]
  exact hasSum_zonalSphere_positiveSpectrum k hk a ha Φ hseries hkernel hΦ id (fun _ ht => ht)
    (summable_positive_covariance_eigenvalues k hk)



omit [DecidableEq ι] in
include hkernel in
/-- On the uniform sphere the actual trace equals the diagonal value Φ(1). -/
theorem zonalSphere_covarianceTrace_eq_profile_one :
    featureCovarianceTrace k hk = Φ 1 := by
  rw [featureCovarianceTrace_eq_integral]
  have hdiag (x : KernelSphere (EuclideanSpace ℝ ι)) : ‖k x‖ ^ 2 = Φ 1 := by
    rw [← real_inner_self_eq_norm_sq, hkernel x x, zonalSphereKernel_diag]
  simp only [hdiag, integral_const, probReal_univ, one_smul]

include hk ha hseries hkernel hΦ in
theorem hasSum_zonalSphere_degreeTrace :
    HasSum (fun m : ℕ => (Dm m : ℝ) * μd m) (Φ 1) := by
  rw [← zonalSphere_covarianceTrace_eq_profile_one k hk Φ hkernel]
  exact hasSum_zonalSphere_covarianceTrace k hk a ha Φ hseries hkernel hΦ

include ha hseries hkernel hΦ in
/-- The actual population counting function, with every multiplicity,
is the finite mass of the corresponding positive spherical degree levels. -/
theorem hasSum_zonalSphere_spectralCount (t : ℝ) (ht : 0 < t) :
    HasSum (fun m : ℕ => (Dm m : ℝ) * (if t ≤ μd m then 1 else 0))
      (featureSpectralCount k hk t : ℝ) := by
  classical
  let J := PredictionSingularIndex S
  let V : Set J := {i | t ≤ i.1.1}
  let w : ℝ → ℝ := fun r => if t ≤ r then 1 else 0
  have hV : V.Finite := finite_featureSpectrum_above k hk ht
  have hW (i : J) (hi : i ∉ V) : w i.1.1 = 0 := if_neg hi
  have hs : Summable (fun i : J => w i.1.1) :=
    summable_of_hasFiniteSupport (hV.subset (fun i hi => by
      by_contra hin
      exact hi (hW i hin)))
  have htotal : (∑' i : J, w i.1.1) = (featureSpectralCount k hk t : ℝ) := by
    rw [tsum_eq_sum (s := hV.toFinset) (fun i hi => hW i (fun hm => hi (hV.mem_toFinset.mpr hm)))]
    unfold featureSpectralCount
    change _ = (V.ncard : ℝ)
    rw [Set.ncard_eq_toFinset_card V hV]
    have hconst : ∀ i ∈ hV.toFinset, w i.1.1 = 1 :=
      fun i hi => if_pos (hV.mem_toFinset.mp hi)
    rw [Finset.sum_congr rfl hconst]
    simp
  rw [← htotal]
  exact hasSum_zonalSphere_positiveSpectrum k hk a ha Φ hseries hkernel hΦ w
    (fun r _ => by dsimp only [w]; split_ifs <;> norm_num) hs

end
end KernelSeq
