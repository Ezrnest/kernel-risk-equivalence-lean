import KernelSeq.HighDimensionalConstants
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Original spherical Pinsker constants and phase normalization
-/

namespace KernelSeq
open Filter
open scoped Topology
noncomputable section

def highDimensionalSourceConstant (a : ℕ → ℝ) (s R : ℝ) (j : ℕ) : ℝ :=
  R^2 * (a j * (j.factorial : ℝ))^s

def highDimensionalNoiseConstant (σ η : ℝ) (p : ℕ) : ℝ :=
  σ^2 / (η * (p.factorial : ℝ))

def highDimensionalPinskerWeight (a : ℕ → ℝ) (s γ R σ η : ℝ) : ℝ :=
  let p := highDimensionalDegree s γ
  if highDimensionalRemainder s γ = 0 then
    highDimensionalPartialWeight (highDimensionalSourceConstant a s R p)
      (highDimensionalNoiseConstant σ η p)
  else 1

def highDimensionalPinskerConstant (a : ℕ → ℝ) (s γ R σ η : ℝ) : ℝ :=
  let p := highDimensionalDegree s γ
  let δ := highDimensionalRemainder s γ
  let A := highDimensionalSourceConstant a s R p
  let B := highDimensionalNoiseConstant σ η p
  let A' := highDimensionalSourceConstant a s R (p+1)
  if δ = 0 then A*B/(A+B)
  else if δ < s then B
  else if δ = s then B+A'
  else A'

theorem highDimensionalSourceConstant_pos {a : ℕ → ℝ} (ha : ∀ j, 0 < a j)
    {s R : ℝ} (hR : 0 < R) (j : ℕ) : 0 < highDimensionalSourceConstant a s R j := by
  unfold highDimensionalSourceConstant
  have hj := ha j
  positivity

theorem highDimensionalNoiseConstant_pos {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η)
    (p : ℕ) : 0 < highDimensionalNoiseConstant σ η p := by
  unfold highDimensionalNoiseConstant
  positivity

theorem highDimensionalPinskerConstant_pos {a : ℕ → ℝ} (ha : ∀ j, 0 < a j)
    {s γ R σ η : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hη : 0 < η) :
    0 < highDimensionalPinskerConstant a s γ R σ η := by
  have hA := highDimensionalSourceConstant_pos (s := s) ha hR (highDimensionalDegree s γ)
  have hA' := highDimensionalSourceConstant_pos (s := s) ha hR (highDimensionalDegree s γ + 1)
  have hB := highDimensionalNoiseConstant_pos hσ hη (highDimensionalDegree s γ)
  unfold highDimensionalPinskerConstant
  dsimp only
  split_ifs <;> positivity

theorem highDimensionalPinskerWeight_mem {a : ℕ → ℝ} (ha : ∀ j, 0 < a j)
    {s γ R σ η : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hη : 0 < η) :
    highDimensionalPinskerWeight a s γ R σ η ∈ Set.Ioc (0 : ℝ) 1 := by
  unfold highDimensionalPinskerWeight
  dsimp only
  split_ifs
  · have h := highDimensionalPartialWeight_mem
      (highDimensionalSourceConstant_pos (s := s) ha hR (highDimensionalDegree s γ))
      (highDimensionalNoiseConstant_pos hσ hη (highDimensionalDegree s γ))
    exact ⟨h.1,h.2.le⟩
  · exact ⟨zero_lt_one,le_rfl⟩

theorem highDimensionalRiskExponent_eq {s γ : ℝ} :
    highDimensionalRiskExponent s γ =
      (highDimensionalDegree s γ : ℝ)*s + min (highDimensionalRemainder s γ) s := by
  unfold highDimensionalRiskExponent highDimensionalRemainder
  rw [add_min]
  congr 1 <;> ring

theorem dimensionPower_rescale_tendsto_zero {I : Type*} {l : Filter I}
    {d u : I → ℝ} {a b c : ℝ} (hd : Tendsto d l atTop)
    (hd0 : ∀ i, 0 < d i) (hab : a < b)
    (hu : Tendsto (fun i => d i^b*u i) l (𝓝 c)) :
    Tendsto (fun i => d i^a*u i) l (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop (show 0 < b-a by linarith)).comp hd
  have h := hpow.mul hu
  rw [zero_mul] at h
  apply h.congr
  intro i
  change d i^(-(b-a)) * (d i^b*u i) = _
  rw [← mul_assoc, ← Real.rpow_add (hd0 i)]
  congr 2
  ring

theorem highDimensionalPinsker_phase_limit {I : Type*} {l : Filter I}
    (d bias variance : I → ℝ) (hd : Tendsto d l atTop) (hd0 : ∀ i, 0 < d i)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j)
    {s γ R σ η : ℝ} (hs : 0 < s) (hγ : s+1 ≤ γ)
    (hR : 0 < R) (hσ : 0 < σ) (hη : 0 < η) :
    let p := highDimensionalDegree s γ
    let δ := highDimensionalRemainder s γ
    let w := highDimensionalPinskerWeight a s γ R σ η
    (δ = 0 → Tendsto (fun i => d i^((p : ℝ)*s)*bias i) l
      (𝓝 (highDimensionalSourceConstant a s R p * (1-w)^2))) →
    (0 < δ → Tendsto (fun i => d i^(((p : ℝ)+1)*s)*bias i) l
      (𝓝 (highDimensionalSourceConstant a s R (p+1)))) →
    Tendsto (fun i => d i^(γ-(p : ℝ))*variance i) l
      (𝓝 (highDimensionalNoiseConstant σ η p*w^2)) →
    Tendsto (fun i => d i^(highDimensionalRiskExponent s γ)*(bias i+variance i)) l
      (𝓝 (highDimensionalPinskerConstant a s γ R σ η)) := by
  intro p δ w hb0 hb hv
  let A := highDimensionalSourceConstant a s R p
  let A' := highDimensionalSourceConstant a s R (p+1)
  let B := highDimensionalNoiseConstant σ η p
  have hδ := highDimensionalRemainder_mem hs hγ
  have heq : γ-(p : ℝ) = (p : ℝ)*s+δ := by dsimp [δ, p, highDimensionalRemainder]; ring
  have hex : highDimensionalRiskExponent s γ = min (γ-(p : ℝ)) (((p : ℝ)+1)*s) := rfl
  simp_rw [mul_add]
  by_cases hzero : δ = 0
  · have hV : γ-(p : ℝ) = (p : ℝ)*s := by linarith
    have hX : highDimensionalRiskExponent s γ = (p : ℝ)*s := by
      rw [hex,hV,min_eq_left (by nlinarith)]
    have hw : w = highDimensionalPartialWeight A B := if_pos hzero
    have hc : highDimensionalPinskerConstant a s γ R σ η = A*B/(A+B) := if_pos hzero
    have hb0' := hb0 hzero
    change Tendsto (fun i => d i^((p : ℝ)*s)*bias i) l (𝓝 (A*(1-w)^2)) at hb0'
    rw [hV] at hv
    change Tendsto (fun i => d i^((p : ℝ)*s)*variance i) l (𝓝 (B*w^2)) at hv
    rw [hX,hc]
    have hh := hb0'.add hv
    rwa [hw, highDimensionalPartialWeight_value
      (highDimensionalSourceConstant_pos ha hR p)
      (highDimensionalNoiseConstant_pos hσ hη p)] at hh
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ.1 (Ne.symm hzero)
    have hw : w = 1 := if_neg hzero
    have hb' := hb hδpos
    change Tendsto (fun i => d i^(γ-(p : ℝ))*variance i) l (𝓝 (B*w^2)) at hv
    rw [hw,one_pow,mul_one] at hv
    by_cases hlow : δ < s
    · have hlt : γ-(p : ℝ) < ((p : ℝ)+1)*s := by nlinarith
      have hc : highDimensionalPinskerConstant a s γ R σ η = B := by
        unfold highDimensionalPinskerConstant
        rw [if_neg hzero,if_pos hlow]
      rw [hex,min_eq_left hlt.le,hc]
      simpa only [zero_add] using (dimensionPower_rescale_tendsto_zero hd hd0 hlt hb').add hv
    · by_cases he : δ = s
      · have hV : γ-(p : ℝ) = ((p : ℝ)+1)*s := by nlinarith
        have hc : highDimensionalPinskerConstant a s γ R σ η = B+A' := by
          unfold highDimensionalPinskerConstant
          rw [if_neg hzero,if_neg hlow,if_pos he]
        rw [hex,hV,min_self,hc,add_comm B A']
        rw [hV] at hv
        exact hb'.add hv
      · have hlt : ((p : ℝ)+1)*s < γ-(p : ℝ) := by
          have : s < δ := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm he)
          nlinarith
        have hc : highDimensionalPinskerConstant a s γ R σ η = A' := by
          unfold highDimensionalPinskerConstant
          rw [if_neg hzero,if_neg hlow,if_neg he]
        rw [hex,min_eq_right hlt.le,hc]
        simpa only [add_zero] using hb'.add (dimensionPower_rescale_tendsto_zero hd hd0 hlt hv)

end
end KernelSeq
