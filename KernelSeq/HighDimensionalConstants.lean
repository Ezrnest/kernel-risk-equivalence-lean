import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Original high-dimensional phase constants and scale inequalities

The exact transition weight and the sample/source exponents are derived
algebraically from the manuscript's `p=floor(gamma/(s+1))`. This module does
not replace the required actual spherical spectral estimates.
-/

namespace KernelSeq
noncomputable section

def highDimensionalDegree (s γ : ℝ) : ℕ := ⌊γ/(s+1)⌋₊
def highDimensionalRemainder (s γ : ℝ) : ℝ := γ-(highDimensionalDegree s γ : ℝ)*(s+1)
def highDimensionalRiskExponent (s γ : ℝ) : ℝ :=
  min (γ-(highDimensionalDegree s γ : ℝ)) (((highDimensionalDegree s γ : ℝ)+1)*s)

theorem highDimensionalDegree_bounds {s γ : ℝ} (hs : 0 < s) (hγ : s+1 ≤ γ) :
    1 ≤ highDimensionalDegree s γ ∧
      (highDimensionalDegree s γ : ℝ)*(s+1) ≤ γ ∧
      γ < ((highDimensionalDegree s γ : ℝ)+1)*(s+1) ∧
      (highDimensionalDegree s γ : ℝ) < γ := by
  have hsp : 0 < s+1 := by linarith
  have hdiv : 1 ≤ γ/(s+1) := (le_div_iff₀ hsp).mpr (by simpa using hγ)
  have hγ0 : 0 ≤ γ/(s+1) := zero_le_one.trans hdiv
  have hp : 1 ≤ highDimensionalDegree s γ := Nat.le_floor (by simpa only [Nat.cast_one] using hdiv)
  have hlo : (highDimensionalDegree s γ : ℝ)*(s+1) ≤ γ :=
    (le_div_iff₀ hsp).mp (Nat.floor_le hγ0)
  have hhi : γ < ((highDimensionalDegree s γ : ℝ)+1)*(s+1) :=
    (div_lt_iff₀ hsp).mp (Nat.lt_floor_add_one (γ/(s+1)))
  have hpR : (1 : ℝ) ≤ highDimensionalDegree s γ := by exact_mod_cast hp
  refine ⟨hp,hlo,hhi,?_⟩
  nlinarith

theorem highDimensionalRemainder_mem {s γ : ℝ} (hs : 0 < s) (hγ : s+1 ≤ γ) :
    highDimensionalRemainder s γ ∈ Set.Ico (0 : ℝ) (s+1) := by
  obtain ⟨_,hlo,hhi,_⟩ := highDimensionalDegree_bounds hs hγ
  constructor <;> dsimp [highDimensionalRemainder] <;> linarith

def highDimensionalPartialWeight (A B : ℝ) : ℝ := A/(A+B)

theorem highDimensionalPartialWeight_mem {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    highDimensionalPartialWeight A B ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold highDimensionalPartialWeight
  constructor
  · exact div_pos hA (by linarith)
  · exact (div_lt_one (by linarith : 0 < A+B)).mpr (by linarith)

theorem highDimensionalPartialWeight_completion {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (w : ℝ) :
    A*(1-w)^2+B*w^2 = A*B/(A+B)+(A+B)*(w-highDimensionalPartialWeight A B)^2 := by
  unfold highDimensionalPartialWeight
  field_simp
  ring

theorem highDimensionalPartialWeight_minimizes {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (w : ℝ) :
    A*B/(A+B) ≤ A*(1-w)^2+B*w^2 := by
  rw [highDimensionalPartialWeight_completion hA hB]
  exact le_add_of_nonneg_right (mul_nonneg (by linarith) (sq_nonneg _))

theorem highDimensionalPartialWeight_value {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A*(1-highDimensionalPartialWeight A B)^2+B*(highDimensionalPartialWeight A B)^2 = A*B/(A+B) := by
  rw [highDimensionalPartialWeight_completion hA hB]
  simp

/-- The original KRR schedule satisfies both strict exponent inequalities
required by the actual scale engine, over the full original `0<s<=1` range. -/
theorem highDimensionalKRR_exponent_inequalities {s γ : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hγ : s+1 ≤ γ) :
    let p := (highDimensionalDegree s γ : ℝ)
    let δ := highDimensionalRemainder s γ
    let a := p+min δ s/2
    p ≤ a ∧ a < γ ∧ 3*a-2*p < γ ∧ a*(1-s)-p < 0 := by
  obtain ⟨hp,_,_,_⟩ := highDimensionalDegree_bounds hs hγ
  have hp1 : (1 : ℝ) ≤ highDimensionalDegree s γ := by exact_mod_cast hp
  have hδ := highDimensionalRemainder_mem hs hγ
  have hmin0 : 0 ≤ min (highDimensionalRemainder s γ) s := le_min hδ.1 hs.le
  have hmins := min_le_right (highDimensionalRemainder s γ) s
  have hmind := min_le_left (highDimensionalRemainder s γ) s
  have hid : γ = (highDimensionalDegree s γ : ℝ)*(s+1)+highDimensionalRemainder s γ := by
    unfold highDimensionalRemainder
    ring
  dsimp only
  have hps : s ≤ (highDimensionalDegree s γ : ℝ)*s := by nlinarith
  refine ⟨by linarith,?_,?_,?_⟩
  · nlinarith
  · nlinarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs1)
      (sub_nonneg.mpr hmins)]

end
end KernelSeq
