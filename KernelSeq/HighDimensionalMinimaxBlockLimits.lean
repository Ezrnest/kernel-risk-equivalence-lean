import KernelSeq.HighDimensionalMinimaxBlocks
import KernelSeq.HighDimensionalPhaseLimits
import KernelSeq.SphereZonalAsymptotics

/-!
# The exact high-dimensional limits of the finite Gaussian block priors

At the first transition the two contributions to the degree-p posterior
variance balance. In every positive-remainder phase the prior puts a
vanishing source-energy share on degree p. This share still makes the
degree-p posterior loss asymptotic to its noise variance. The degree-(p+1)
posterior loss is asymptotic to the remaining source capacity.
-/

namespace KernelSeq
open Filter Set
open scoped Topology ContDiff
noncomputable section

def highDimensionalBlockNoise (d n m : ℕ) (σ : ℝ) : ℝ :=
  (d.choose m : ℝ)*σ^2/n

def highDimensionalMinimaxShare (d δ : ℝ) : ℝ := d^(-(δ/2))/2

theorem highDimensionalMinimaxShare_mem {d δ : ℝ} (hd : 1 ≤ d) (hδ : 0 ≤ δ) :
    highDimensionalMinimaxShare d δ ∈ Ioo (0 : ℝ) 1 := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hu := Real.rpow_le_one_of_one_le_of_nonpos hd (show -(δ/2) ≤ 0 by linarith)
  unfold highDimensionalMinimaxShare
  exact ⟨by positivity, by linarith⟩

def highDimensionalPriorSequenceRisk (d n : ℕ) (t : ℕ → ℝ) (s γ R σ : ℝ) : ℝ :=
  let p := highDimensionalDegree s γ
  let δ := highDimensionalRemainder s γ
  if δ = 0 then highDimensionalBlockBayesRisk (R^2*(t p)^s) (highDimensionalBlockNoise d n p σ)
  else
    let r := highDimensionalMinimaxShare d δ
    highDimensionalBlockBayesRisk (r*(R^2*(t p)^s)) (highDimensionalBlockNoise d n p σ) +
      highDimensionalBlockBayesRisk ((1-r)*(R^2*(t (p+1))^s)) (highDimensionalBlockNoise d n (p+1) σ)

private theorem blockBayesRisk_comm (A B : ℝ) :
    highDimensionalBlockBayesRisk A B = highDimensionalBlockBayesRisk B A := by
  simp only [highDimensionalBlockBayesRisk, mul_comm, add_comm]

private theorem blockBayesRisk_mul {x : ℝ} (hx : x ≠ 0) (A B : ℝ) :
    highDimensionalBlockBayesRisk (x*A) (x*B) = x*highDimensionalBlockBayesRisk A B := by
  unfold highDimensionalBlockBayesRisk
  rw [show x*A+x*B = x*(A+B) by ring,
    show (x*A)*(x*B) = x*(x*(A*B)) by ring,
    mul_div_mul_left _ _ hx, mul_div_assoc]

section ScalarLimits
variable {I : Type*} {l : Filter I} {d A B : I → ℝ}

private theorem blockBayesRisk_balanced_limit {α a b : ℝ} (hd0 : ∀ i, 0 < d i)
    (ha : 0 < a) (hb : 0 < b)
    (hA : Tendsto (fun i => d i^α*A i) l (𝓝 a))
    (hB : Tendsto (fun i => d i^α*B i) l (𝓝 b)) :
    Tendsto (fun i => d i^α*highDimensionalBlockBayesRisk (A i) (B i)) l
      (𝓝 (highDimensionalBlockBayesRisk a b)) := by
  have hlim := (hA.mul hB).div (hA.add hB) (add_pos ha hb).ne'
  exact hlim.congr (fun i => blockBayesRisk_mul (Real.rpow_pos_of_pos (hd0 i) _).ne' (A i) (B i))

private theorem blockBayesRisk_variance_limit {α β a b : ℝ}
    (hd : Tendsto d l atTop) (hd0 : ∀ i, 0 < d i) (hgap : α < β) (ha : 0 < a)
    (hA : Tendsto (fun i => d i^α*A i) l (𝓝 a))
    (hB : Tendsto (fun i => d i^β*B i) l (𝓝 b)) :
    Tendsto (fun i => d i^β*highDimensionalBlockBayesRisk (A i) (B i)) l (𝓝 b) := by
  have hs := (dimensionPower_rescale_tendsto_zero hd hd0 hgap hB).div hA ha.ne'
  rw [zero_div] at hs
  have hr : Tendsto (fun i => B i/A i) l (𝓝 0) := by
    apply hs.congr
    intro i
    exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos (hd0 i) _).ne'
  have hden := (tendsto_const_nhds (x := (1 : ℝ))).add hr
  simp only [add_zero] at hden
  have hh := hB.div hden (by norm_num)
  rw [div_one] at hh
  apply hh.congr'
  filter_upwards [hA.eventually (lt_mem_nhds ha)] with i hi
  have hAi : 0 < A i := pos_of_mul_pos_right hi (Real.rpow_nonneg (hd0 i).le _)
  have he : highDimensionalBlockBayesRisk (A i) (B i) = B i/(1+B i/A i) := by
    unfold highDimensionalBlockBayesRisk
    rw [show 1+B i/A i = (A i+B i)/A i by rw [add_div, div_self hAi.ne'],
      div_div_eq_mul_div, mul_comm (B i) (A i)]
  rw [he]
  change d i^β*B i/(1+B i/A i) = d i^β*(B i/(1+B i/A i))
  rw [mul_div_assoc]

private theorem blockBayesRisk_capacity_limit {α β a b : ℝ}
    (hd : Tendsto d l atTop) (hd0 : ∀ i, 0 < d i) (hgap : β < α) (hb : 0 < b)
    (hA : Tendsto (fun i => d i^α*A i) l (𝓝 a))
    (hB : Tendsto (fun i => d i^β*B i) l (𝓝 b)) :
    Tendsto (fun i => d i^α*highDimensionalBlockBayesRisk (A i) (B i)) l (𝓝 a) := by
  simpa only [blockBayesRisk_comm (B _) (A _)] using
    blockBayesRisk_variance_limit hd hd0 hgap hb hB hA

end ScalarLimits

section ActualLimits
variable {I : Type*} {l : Filter I}
  (ι : I → Type*) [∀ i, Fintype (ι i)] [∀ i, Nonempty (ι i)]

theorem spherical_minimax_block_noise_tendsto
    (n : I → ℕ) {γ σ η : ℝ} (hη : 0 < η) (m : ℕ)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hn : Tendsto (fun i => (n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) l (𝓝 η)) :
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^(γ-(m : ℝ))*
      highDimensionalBlockNoise (Fintype.card (ι i)) (n i) m σ) l
      (𝓝 (highDimensionalNoiseConstant σ η m)) := by
  have hd0 (i : I) : 0 < (Fintype.card (ι i) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hfac : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr m.factorial_pos
  have hh := (choose_shift_dimension_ratio_tendsto 0 m).comp hd
  simp only [Function.comp_def, Nat.add_zero] at hh
  have hchoose : Tendsto (fun i => ((Fintype.card (ι i)).choose m : ℝ)/
      (Fintype.card (ι i) : ℝ)^m) l (𝓝 ((m.factorial : ℝ)⁻¹)) := by
    have h := hh.const_mul ((m.factorial : ℝ)⁻¹)
    rw [mul_one] at h
    apply h.congr
    intro i
    field_simp [(pow_pos (hd0 i) m).ne', hfac.ne']
  have h := (hchoose.const_mul (σ^2)).div hn hη.ne'
  have hconst : σ^2*(m.factorial : ℝ)⁻¹/η = highDimensionalNoiseConstant σ η m := by
    unfold highDimensionalNoiseConstant
    field_simp
  rw [hconst] at h
  apply h.congr
  intro i
  change (σ^2*(((Fintype.card (ι i)).choose m : ℝ)/(Fintype.card (ι i) : ℝ)^m))/
    ((n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) = _
  unfold highDimensionalBlockNoise
  rw [Real.rpow_sub (hd0 i), Real.rpow_natCast]
  rw [div_div_eq_mul_div]
  ring

theorem spherical_minimax_source_capacity_tendsto
    (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun m => a m*t^m) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1)) (m : ℕ)
    {s R : ℝ} (hs : 0 ≤ s)
    (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop) :
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^((m : ℝ)*s)*
      (R^2*zonalSphereDegreeValue (ι := ι i) a m^s)) l
      (𝓝 (highDimensionalSourceConstant a s R m)) := by
  have h := ((zonalSphereDegreeValue_scaled_tendsto ι a ha Φ hseries hΦ m hd).rpow_const
    (p := s) (Or.inr hs)).const_mul (R^2)
  apply h.congr
  intro i
  have hd0 : 0 < (Fintype.card (ι i) : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [Real.mul_rpow (zonalSphereDegreeValue_nonneg a ha m) (pow_nonneg hd0.le _),
    ← Real.rpow_natCast (Fintype.card (ι i) : ℝ) m, ← Real.rpow_mul hd0.le]
  ring

theorem spherical_minimax_prior_sequence_limit
    (a : ℕ → ℝ) (ha : ∀ m, 0 < a m) (Φ : ℝ → ℝ)
    (hseries : ∀ t ∈ Icc (-1 : ℝ) 1, HasSum (fun m => a m*t^m) (Φ t))
    (hΦ : ContDiffOn ℝ ∞ Φ (Icc (-1 : ℝ) 1))
    {s γ R σ η : ℝ} (hs : 0 < s) (hγ : s+1 ≤ γ) (hR : 0 < R) (hσ : 0 < σ) (hη : 0 < η)
    (n : I → ℕ) (hd : Tendsto (fun i => Fintype.card (ι i)) l atTop)
    (hn : Tendsto (fun i => (n i : ℝ)/(Fintype.card (ι i) : ℝ)^γ) l (𝓝 η)) :
    Tendsto (fun i => (Fintype.card (ι i) : ℝ)^(highDimensionalRiskExponent s γ)*
      highDimensionalPriorSequenceRisk (Fintype.card (ι i)) (n i)
        (zonalSphereDegreeValue (ι := ι i) a) s γ R σ) l
      (𝓝 (highDimensionalPinskerConstant a s γ R σ η)) := by
  let p := highDimensionalDegree s γ
  let δ := highDimensionalRemainder s γ
  let d := fun i => (Fintype.card (ι i) : ℝ)
  let A := fun m i => R^2*zonalSphereDegreeValue (ι := ι i) a m^s
  let B := fun m i => highDimensionalBlockNoise (Fintype.card (ι i)) (n i) m σ
  let r := fun i => highDimensionalMinimaxShare (d i) δ
  have hδ := highDimensionalRemainder_mem hs hγ
  have hdp : Tendsto d l atTop := tendsto_natCast_atTop_atTop.comp hd
  have hd0 (i : I) : 0 < d i := Nat.cast_pos.mpr Fintype.card_pos
  have hA (m : ℕ) : Tendsto (fun i => d i^((m : ℝ)*s)*A m i) l
      (𝓝 (highDimensionalSourceConstant a s R m)) :=
    spherical_minimax_source_capacity_tendsto ι a (fun m => (ha m).le) Φ hseries hΦ m hs.le hd
  have hB (m : ℕ) : Tendsto (fun i => d i^(γ-(m : ℝ))*B m i) l
      (𝓝 (highDimensionalNoiseConstant σ η m)) :=
    spherical_minimax_block_noise_tendsto ι n hη m hd hn
  have hVexp : γ-(p : ℝ) = (p : ℝ)*s+δ := by dsimp [δ, p, highDimensionalRemainder]; ring
  by_cases hz : δ = 0
  · have hz' : highDimensionalRemainder s γ = 0 := hz
    have he : highDimensionalRiskExponent s γ = (p : ℝ)*s := by
      rw [highDimensionalRiskExponent_eq, show highDimensionalRemainder s γ = 0 from hz,
        min_eq_left hs.le, add_zero]
    have hv : γ-(p : ℝ) = (p : ℝ)*s := by linarith
    have hBp := hB p
    rw [hv] at hBp
    have hlim := blockBayesRisk_balanced_limit hd0 (highDimensionalSourceConstant_pos ha hR p)
      (highDimensionalNoiseConstant_pos hσ hη p) (hA p) hBp
    simpa only [highDimensionalPriorSequenceRisk, highDimensionalPinskerConstant,
      if_pos hz', he, highDimensionalBlockBayesRisk, d, p, A, B] using hlim
  · have hz' : highDimensionalRemainder s γ ≠ 0 := hz
    have hdpos : 0 < δ := lt_of_le_of_ne hδ.1 (Ne.symm hz)
    have hr : Tendsto r l (𝓝 0) := by
      have h := ((tendsto_rpow_neg_atTop (show 0 < δ/2 by positivity)).comp hdp).div_const 2
      simpa only [Function.comp_def, zero_div, r, highDimensionalMinimaxShare] using h
    have hAp : Tendsto (fun i => d i^((p : ℝ)*s+δ/2)*(r i*A p i)) l
        (𝓝 (highDimensionalSourceConstant a s R p/2)) := by
      apply ((hA p).div_const 2).congr
      intro i
      have he : d i^((p : ℝ)*s+δ/2)*r i = d i^((p : ℝ)*s)/2 := by
        dsimp [r, highDimensionalMinimaxShare]
        rw [← mul_div_assoc, ← Real.rpow_add (hd0 i)]
        congr 2
        ring
      calc
        _ = (d i^((p : ℝ)*s)/2)*A p i := by ring
        _ = _ := by rw [← he, mul_assoc]
    have hAq : Tendsto (fun i => d i^(((p+1 : ℕ) : ℝ)*s)*((1-r i)*A (p+1) i)) l
        (𝓝 (highDimensionalSourceConstant a s R (p+1))) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hr).mul (hA (p+1))
      simp only [sub_zero, one_mul] at h
      exact h.congr (fun i => by ring)
    let bp := fun i => highDimensionalBlockBayesRisk (r i*A p i) (B p i)
    let bq := fun i => highDimensionalBlockBayesRisk ((1-r i)*A (p+1) i) (B (p+1) i)
    have hp : Tendsto (fun i => d i^(γ-(p : ℝ))*bp i) l
        (𝓝 (highDimensionalNoiseConstant σ η p)) :=
      blockBayesRisk_variance_limit hdp hd0 (by linarith) (by
        exact div_pos (highDimensionalSourceConstant_pos ha hR p) (by norm_num)) hAp (hB p)
    have hq : Tendsto (fun i => d i^(((p+1 : ℕ) : ℝ)*s)*bq i) l
        (𝓝 (highDimensionalSourceConstant a s R (p+1))) :=
      blockBayesRisk_capacity_limit hdp hd0 (by push_cast; linarith [hδ.2])
        (highDimensionalNoiseConstant_pos hσ hη (p+1)) hAq (hB (p+1))
    have h := highDimensionalPinsker_phase_limit d bq bp hdp hd0 a ha hs hγ hR hσ hη
    have hw : highDimensionalPinskerWeight a s γ R σ η = 1 := if_neg hz
    have hlim := h (fun he => (hz he).elim) (fun _ => by simpa only [Nat.cast_add, Nat.cast_one] using hq)
      (by simpa only [hw, one_pow, mul_one] using hp)
    simpa only [highDimensionalPriorSequenceRisk, if_neg hz', d, p, δ, A, B, r, bp, bq, add_comm] using hlim

end ActualLimits
end
end KernelSeq
