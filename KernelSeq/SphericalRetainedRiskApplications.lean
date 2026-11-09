import KernelSeq.SphericalRetainedScaleVerification
import KernelSeq.ConcreteUniformRiskApplications

/-!
# Actual regression risk for the general spherical schedules with actual degree-m retention

The presented row is a genuine original regression model, including its
independent observation pairs and conditional noise moments. The literal
scale-model equality identifies only its primitive kernel/design/target/
filter data with the genuine sphere constructor; no scale or risk estimate
is a premise. All three original scales are supplied internally.
-/

namespace KernelSeq
open MeasureTheory Filter Set Asymptotics
open scoped Topology
noncomputable section

universe uJ uI uH uΩ
section ActualRows
variable {J : Type uJ} {l : Filter J} [NeBot l]
    (ι : J → Type uI) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (H : J → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]
    {κ ρ A : ℝ}
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (n : J → ℕ) (hn : ∀ i, 0 < n i)
    (f : ∀ i, Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ (ι i))))
    (lam : J → ℝ) (hlam : ∀ i, 0 < lam i) (φ : J → ℝ → ℝ)
    (hf : ∀ i, ResidualFilter.SpectralFilter (κ^2) (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) (κ^2) ρ A (φ i))

/-- Original conditional risk, expectation risk, and normalized conditional
L1 equivalence for actual spherical rows with only the original noise moments. -/
theorem spherical_retained_sourceBall_risk_equivalence
    (rows : J → TriangularRiskModel.{uH, uI, uΩ} κ ρ A)
    (hrows : ∀ i, (rows i).scaleModel =
      sphericalScaleModel Φ hΦ (hkernel i) hκ hdiag
        (n i) (hn i) (f i) (lam i) (hlam i) (φ i) (hf i) (h i))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    {γ s R s0 : ℝ} (m : ℕ) (hm : 0 < m) (hmγ : (m : ℝ) < γ)
    (ham : 0 < a m) (hs : 0 < s) (hR : 0 < R)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in l, s0 ≤ (rows i).σ)
    (hd : Tendsto (fun i => (Fintype.card (ι i) : ℝ)) l atTop)
    (hnschedule : (fun i => (n i : ℝ)) =Θ[l]
      (fun i => (Fintype.card (ι i) : ℝ)^γ))
    (hreg : lam =Θ[l] (fun i => (Fintype.card (ι i) : ℝ)^(-(m : ℝ))))
    (hretain : ∃ q0 > 0, ∀ᶠ i in l, q0 ≤
      ResidualFilter.shrinkage (φ i) (zonalSphereDegreeValue (ι := ι i) a m))
    (hsource : ∀ᶠ i in l, f i ∈ featureSourceBall (rkhsFeature (H := H i))
      (zonalSphereFeature_memLp Φ hΦ (hkernel i)) s hs.le R) :
    ConcreteRowRiskEquivalence rows l := by
  have hscales := spherical_retained_sourceBall_original_scales ι H Φ hΦ hkernel hκ hdiag
    n hn f lam hlam φ hf h a ha hseries m hm hmγ ham hs hR hd hnschedule hreg hretain hsource
  apply concreteRowRiskEquivalence_of_verified_scales rows hs0 hnoise
  simpa only [hrows] using hscales

end ActualRows

section UniformRows
variable {I Θ : Type*} {l : Filter I} [NeBot l] [Nonempty Θ]
    (ι : I × Θ → Type uI) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] [∀ i, Nonempty (ι i)]
    (H : I × Θ → Type uH)
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, RKHS ℝ (H i) (KernelSphere (EuclideanSpace ℝ (ι i))) ℝ]
    {κ ρ A : ℝ}
    (Φ : ℝ → ℝ) (hΦ : ContinuousOn Φ (Icc (-1 : ℝ) 1))
    (hkernel : ∀ i (x y : KernelSphere (EuclideanSpace ℝ (ι i))),
      rkhsKernel (H := H i) x y = zonalSphereKernel Φ x y)
    (hκ : 0 ≤ κ) (hdiag : Φ 1 ≤ κ^2)
    (n : I × Θ → ℕ) (hn : ∀ i, 0 < n i)
    (f : ∀ i, Lp ℝ 2 (uniformSphere (E := EuclideanSpace ℝ (ι i))))
    (lam : I × Θ → ℝ) (hlam : ∀ i, 0 < lam i) (φ : I × Θ → ℝ → ℝ)
    (hf : ∀ i, ResidualFilter.SpectralFilter (κ^2) (φ i))
    (h : ∀ i, ResidualFilter.Contract (lam i) (κ^2) ρ A (φ i))

/-- Uniformity uses one common index threshold for every parameter, and
returns the actual supremum of individual failure probabilities. Spaces and
laws can vary with both the sample index and the family parameter. -/
theorem uniform_spherical_retained_sourceBall_risk_equivalence
    (rows : I × Θ → TriangularRiskModel.{uH, uI, uΩ} κ ρ A)
    (hrows : ∀ i, (rows i).scaleModel =
      sphericalScaleModel Φ hΦ (hkernel i) hκ hdiag
        (n i) (hn i) (f i) (lam i) (hlam i) (φ i) (hf i) (h i))
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun j => a j*t^j) (Φ t))
    {γ s R s0 : ℝ} (m : ℕ) (hm : 0 < m) (hmγ : (m : ℝ) < γ)
    (ham : 0 < a m) (hs : 0 < s) (hR : 0 < R)
    (hs0 : 0 < s0) (hnoise : ∀ᶠ i in uniformFamilyFilter l Θ, s0 ≤ (rows i).σ)
    (hd : Tendsto (fun i => (Fintype.card (ι i) : ℝ)) (uniformFamilyFilter l Θ) atTop)
    (hnschedule : (fun i => (n i : ℝ)) =Θ[uniformFamilyFilter l Θ]
      (fun i => (Fintype.card (ι i) : ℝ)^γ))
    (hreg : lam =Θ[uniformFamilyFilter l Θ]
      (fun i => (Fintype.card (ι i) : ℝ)^(-(m : ℝ))))
    (hretain : ∃ q0 > 0, ∀ᶠ i in uniformFamilyFilter l Θ, q0 ≤
      ResidualFilter.shrinkage (φ i) (zonalSphereDegreeValue (ι := ι i) a m))
    (hsource : ∀ᶠ i in uniformFamilyFilter l Θ, f i ∈ featureSourceBall (rkhsFeature (H := H i))
      (zonalSphereFeature_memLp Φ hΦ (hkernel i)) s hs.le R) :
    ConcreteUniformRiskEquivalence rows l := by
  apply concreteUniformRiskEquivalence_of_product_rows rows
  exact spherical_retained_sourceBall_risk_equivalence (l := uniformFamilyFilter l Θ)
    ι H Φ hΦ hkernel hκ hdiag n hn f lam hlam φ hf h rows hrows
    a ha hseries m hm hmγ ham hs hR hs0 hnoise hd hnschedule hreg hretain hsource

end UniformRows
end
end KernelSeq
