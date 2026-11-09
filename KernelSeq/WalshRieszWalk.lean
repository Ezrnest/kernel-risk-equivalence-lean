import KernelSeq.HeatRieszPolynomial
import KernelSeq.CuculescuWalsh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# A finite two-coordinate Walsh walk for the base second-order Riesz symbol

Each cycle reveals an x-sign and then a y-sign. The two genuine backward
Markov differences have zero conditional Boolean mean. Their signed sum is
averaged after the actual endpoint pullback. Its coefficient is calculated
from the finite random walk, rather than assumed as a Fourier bound.

This alternating-walk construction is a local derivation suggested by the
heat/Riesz calculation; it is not claimed as a theorem already stated in
GMSS. No UMD, Fourier multiplier, or Schatten estimate is asserted here.
-/

open Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace KernelSeq
noncomputable section

def walkComplexPhase (a : ℝ) : ℂ := (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I

@[simp] theorem walkComplexPhase_zero : walkComplexPhase 0 = 1 := by
  simp [walkComplexPhase]

theorem walkComplexPhase_add (a b : ℝ) :
    walkComplexPhase (a + b) = walkComplexPhase a * walkComplexPhase b := by
  apply Complex.ext <;> simp [walkComplexPhase, Real.cos_add, Real.sin_add]
  ring

theorem walkComplexPhase_neg (a : ℝ) : walkComplexPhase (-a) = conj (walkComplexPhase a) := by
  apply Complex.ext <;> simp [walkComplexPhase]

@[simp] theorem walkComplexPhase_conj_mul (a : ℝ) :
    conj (walkComplexPhase a) * walkComplexPhase a = 1 := by
  rw [← walkComplexPhase_neg, ← walkComplexPhase_add, neg_add_cancel, walkComplexPhase_zero]

@[simp] theorem walkComplexPhase_mul_conj (a : ℝ) :
    walkComplexPhase a * conj (walkComplexPhase a) = 1 := by
  rw [mul_comm, walkComplexPhase_conj_mul]

/-- Exact uniform average of one Boolean sign. -/
def walkBoolAverage (f : Bool → ℂ) : ℂ := (f true + f false) / 2

@[simp] theorem walkBoolAverage_const (z : ℂ) : walkBoolAverage (fun _ => z) = z := by
  unfold walkBoolAverage
  ring

theorem walkBoolAverage_add (f g : Bool → ℂ) :
    walkBoolAverage (fun e => f e + g e) = walkBoolAverage f + walkBoolAverage g := by
  unfold walkBoolAverage
  ring

theorem walkBoolAverage_sub (f g : Bool → ℂ) :
    walkBoolAverage (fun e => f e - g e) = walkBoolAverage f - walkBoolAverage g := by
  unfold walkBoolAverage
  ring

theorem walkBoolAverage_const_mul (z : ℂ) (f : Bool → ℂ) :
    walkBoolAverage (fun e => z * f e) = z * walkBoolAverage f := by
  unfold walkBoolAverage
  ring

theorem walkBoolAverage_mul_const (f : Bool → ℂ) (z : ℂ) :
    walkBoolAverage (fun e => f e * z) = walkBoolAverage f * z := by
  unfold walkBoolAverage
  ring

def walkSignedPhase (a : ℝ) (e : Bool) : ℂ := walkComplexPhase (walshSign e * a)

@[simp] theorem walkBoolAverage_phase (a : ℝ) :
    walkBoolAverage (walkSignedPhase a) = (Real.cos a : ℂ) := by
  apply Complex.ext <;>
    simp [walkBoolAverage, walkSignedPhase, walkComplexPhase, walshSign]

@[simp] theorem walkBoolAverage_conj_phase (a : ℝ) :
    walkBoolAverage (fun e => conj (walkSignedPhase a e)) = (Real.cos a : ℂ) := by
  apply Complex.ext <;>
    simp [walkBoolAverage, walkSignedPhase, walkComplexPhase, walshSign]

@[simp] theorem walkSignedPhase_conj_mul (a : ℝ) (e : Bool) :
    conj (walkSignedPhase a e) * walkSignedPhase a e = 1 :=
  walkComplexPhase_conj_mul _

/-- One-cycle Markov eigenvalue. -/
def walkCycleMultiplier (a b : ℝ) : ℝ := Real.cos a * Real.cos b

def walkCyclePhase (a b : ℝ) (e d : Bool) : ℂ := walkSignedPhase a e * walkSignedPhase b d

def walkCycleAverage (f : Bool → Bool → ℂ) : ℂ :=
  walkBoolAverage (fun e => walkBoolAverage (f e))

theorem walkCycleAverage_add (f g : Bool → Bool → ℂ) :
    walkCycleAverage (fun e d => f e d + g e d) = walkCycleAverage f + walkCycleAverage g := by
  simp only [walkCycleAverage, walkBoolAverage_add]

theorem walkCycleAverage_const_mul (z : ℂ) (f : Bool → Bool → ℂ) :
    walkCycleAverage (fun e d => z * f e d) = z * walkCycleAverage f := by
  simp only [walkCycleAverage, walkBoolAverage_const_mul]

theorem walkCycleAverage_mul_const (f : Bool → Bool → ℂ) (z : ℂ) :
    walkCycleAverage (fun e d => f e d * z) = walkCycleAverage f * z := by
  simp only [walkCycleAverage, walkBoolAverage_mul_const]

@[simp] theorem walkCycleAverage_const (z : ℂ) : walkCycleAverage (fun _ _ => z) = z := by
  simp only [walkCycleAverage, walkBoolAverage_const]

@[simp] theorem walkCyclePhase_conj_mul (a b : ℝ) (e d : Bool) :
    conj (walkCyclePhase a b e d) * walkCyclePhase a b e d = 1 := by
  simp only [walkCyclePhase, map_mul]
  calc
    _ = (conj (walkSignedPhase a e) * walkSignedPhase a e) *
        (conj (walkSignedPhase b d) * walkSignedPhase b d) := by ring
    _ = _ := by rw [walkSignedPhase_conj_mul, walkSignedPhase_conj_mul]; ring

theorem walkCycleAverage_separated (f g : Bool → ℂ) :
    walkCycleAverage (fun e d => f e * g d) = walkBoolAverage f * walkBoolAverage g := by
  simp only [walkCycleAverage, walkBoolAverage_const_mul, walkBoolAverage_mul_const]

@[simp] theorem walkCycleAverage_phase (a b : ℝ) :
    walkCycleAverage (walkCyclePhase a b) = (walkCycleMultiplier a b : ℂ) := by
  change walkCycleAverage (fun e d => walkSignedPhase a e * walkSignedPhase b d) = _
  rw [walkCycleAverage_separated, walkBoolAverage_phase, walkBoolAverage_phase]
  simp only [walkCycleMultiplier, Complex.ofReal_mul]

/-- Actual x-difference: y remains unobserved and is averaged by `cos b`. -/
def walkDifferenceX (a b : ℝ) (e : Bool) : ℂ :=
  (Real.cos b : ℂ) * (walkSignedPhase a e - (Real.cos a : ℂ))

/-- Actual y-difference, conditional on the revealed x-sign. -/
def walkDifferenceY (a b : ℝ) (e d : Bool) : ℂ :=
  walkSignedPhase a e * (walkSignedPhase b d - (Real.cos b : ℂ))

theorem walkDifferenceX_mean_zero (a b : ℝ) : walkBoolAverage (walkDifferenceX a b) = 0 := by
  change walkBoolAverage (fun e => (Real.cos b : ℂ) * (walkSignedPhase a e - (Real.cos a : ℂ))) = 0
  simp only [walkBoolAverage_const_mul, walkBoolAverage_sub,
    walkBoolAverage_phase, walkBoolAverage_const, sub_self, mul_zero]

theorem walkDifferenceY_mean_zero (a b : ℝ) (e : Bool) :
    walkBoolAverage (walkDifferenceY a b e) = 0 := by
  change walkBoolAverage (fun d => walkSignedPhase a e * (walkSignedPhase b d - (Real.cos b : ℂ))) = 0
  simp only [walkBoolAverage_const_mul, walkBoolAverage_sub,
    walkBoolAverage_phase, walkBoolAverage_const, sub_self, mul_zero]

/-- The two genuine Markov differences telescope to the one-cycle terminal
value minus its actual conditional mean. -/
theorem walkDifferences_add (a b : ℝ) (e d : Bool) :
    walkDifferenceX a b e + walkDifferenceY a b e d =
      walkCyclePhase a b e d - (walkCycleMultiplier a b : ℂ) := by
  simp only [walkDifferenceX, walkDifferenceY, walkCyclePhase, walkCycleMultiplier, Complex.ofReal_mul]
  ring

/-- The deterministic `+1,-1` transform at a single cycle. -/
def walkSignedDifference (a b : ℝ) (e d : Bool) : ℂ :=
  walkDifferenceX a b e - walkDifferenceY a b e d

def walkRieszNumerator (a b : ℝ) : ℝ :=
  Real.sin a ^ 2 * Real.cos b ^ 2 - Real.sin b ^ 2

private theorem walkBoolAverage_conj_difference (a : ℝ) :
    walkBoolAverage (fun e => conj (walkSignedPhase a e) *
      (walkSignedPhase a e - (Real.cos a : ℂ))) = 1 - (Real.cos a : ℂ) ^ 2 := by
  have heq : (fun e => conj (walkSignedPhase a e) *
      (walkSignedPhase a e - (Real.cos a : ℂ))) =
      (fun e => 1 - (Real.cos a : ℂ) * conj (walkSignedPhase a e)) := by
    funext e
    rw [mul_sub, walkSignedPhase_conj_mul]
    ring
  rw [heq, walkBoolAverage_sub, walkBoolAverage_const, walkBoolAverage_const_mul,
    walkBoolAverage_conj_phase]
  ring

/-- The actual four-point endpoint pullback gives the Riesz numerator. -/
theorem walkSignedDifference_endpoint_average (a b : ℝ) :
    walkCycleAverage (fun e d => conj (walkCyclePhase a b e d) *
      walkSignedDifference a b e d) = (walkRieszNumerator a b : ℂ) := by
  have hx : walkCycleAverage (fun e d => conj (walkCyclePhase a b e d) * walkDifferenceX a b e) =
      (Real.cos b : ℂ) ^ 2 * (1 - (Real.cos a : ℂ) ^ 2) := by
    calc
      _ = (Real.cos b : ℂ) *
          walkBoolAverage (fun e => conj (walkSignedPhase a e) *
            (walkSignedPhase a e - (Real.cos a : ℂ))) *
          walkBoolAverage (fun d => conj (walkSignedPhase b d)) := by
        simp only [walkCycleAverage, walkBoolAverage, walkCyclePhase, walkDifferenceX, map_mul]
        ring
      _ = _ := by rw [walkBoolAverage_conj_difference, walkBoolAverage_conj_phase]; ring
  have hy : walkCycleAverage (fun e d => conj (walkCyclePhase a b e d) * walkDifferenceY a b e d) =
      1 - (Real.cos b : ℂ) ^ 2 := by
    have heq : (fun e d => conj (walkCyclePhase a b e d) * walkDifferenceY a b e d) =
        (fun _ d => conj (walkSignedPhase b d) *
          (walkSignedPhase b d - (Real.cos b : ℂ))) := by
      funext e d
      simp only [walkCyclePhase, walkDifferenceY, map_mul]
      calc
        _ = (conj (walkSignedPhase a e) * walkSignedPhase a e) *
            (conj (walkSignedPhase b d) * (walkSignedPhase b d - (Real.cos b : ℂ))) := by ring
        _ = _ := by rw [walkSignedPhase_conj_mul, one_mul]
    rw [heq]
    simp only [walkCycleAverage, walkBoolAverage_conj_difference, walkBoolAverage_const]
  have heq : walkCycleAverage (fun e d => conj (walkCyclePhase a b e d) *
      walkSignedDifference a b e d) =
      walkCycleAverage (fun e d => conj (walkCyclePhase a b e d) * walkDifferenceX a b e) -
        walkCycleAverage (fun e d => conj (walkCyclePhase a b e d) * walkDifferenceY a b e d) := by
    simp only [walkCycleAverage, walkSignedDifference, mul_sub, walkBoolAverage_sub]
  rw [heq, hx, hy]
  have ha : Real.sin a ^ 2 = 1 - Real.cos a ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq a]
  have hb : Real.sin b ^ 2 = 1 - Real.cos b ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq b]
  have hr : Real.cos b ^ 2 * (1 - Real.cos a ^ 2) - (1 - Real.cos b ^ 2) =
      walkRieszNumerator a b := by
    rw [walkRieszNumerator, ha, hb]
    ring
  exact_mod_cast hr

/-- A genuine finite Boolean path, with the two signs revealed in order. -/
def RieszWalkPath : ℕ → Type
  | 0 => PUnit
  | n + 1 => (Bool × Bool) × RieszWalkPath n

instance rieszWalkPathFintype : (n : ℕ) → Fintype (RieszWalkPath n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI := rieszWalkPathFintype n
    exact inferInstanceAs (Fintype ((Bool × Bool) × RieszWalkPath n))

/-- The actual path character, equal to the product of all step phases. -/
def rieszWalkCharacter (a b : ℝ) : (n : ℕ) → RieszWalkPath n → ℂ
  | 0, _ => 1
  | n + 1, ω => walkCyclePhase a b ω.1.1 ω.1.2 * rieszWalkCharacter a b n ω.2

/-- The actual backward-Markov signed difference sum on the finite path. -/
def rieszWalkTransform (a b : ℝ) : (n : ℕ) → RieszWalkPath n → ℂ
  | 0, _ => 0
  | n + 1, ω => (walkCycleMultiplier a b : ℂ) ^ n * walkSignedDifference a b ω.1.1 ω.1.2 +
      walkCyclePhase a b ω.1.1 ω.1.2 * rieszWalkTransform a b n ω.2

/-- The same genuine path difference sum without signs. -/
def rieszWalkUnsigned (a b : ℝ) : (n : ℕ) → RieszWalkPath n → ℂ
  | 0, _ => 0
  | n + 1, ω => (walkCycleMultiplier a b : ℂ) ^ n *
      (walkDifferenceX a b ω.1.1 + walkDifferenceY a b ω.1.1 ω.1.2) +
        walkCyclePhase a b ω.1.1 ω.1.2 * rieszWalkUnsigned a b n ω.2

theorem rieszWalkUnsigned_telescope (a b : ℝ) (n : ℕ) (ω : RieszWalkPath n) :
    rieszWalkUnsigned a b n ω = rieszWalkCharacter a b n ω - (walkCycleMultiplier a b : ℂ) ^ n := by
  induction n with
  | zero => simp only [rieszWalkUnsigned, rieszWalkCharacter, pow_zero, sub_self]
  | succ n ih =>
    simp only [rieszWalkUnsigned, rieszWalkCharacter, walkDifferences_add, ih, pow_succ]
    ring

/-- Actual recursive uniform average on the finite Boolean path. -/
def rieszWalkAverage : (n : ℕ) → (RieszWalkPath n → ℂ) → ℂ
  | 0, f => f PUnit.unit
  | n + 1, f => walkCycleAverage (fun e d => rieszWalkAverage n (fun ω => f ((e, d), ω)))

theorem rieszWalkAverage_add (n : ℕ) (f g : RieszWalkPath n → ℂ) :
    rieszWalkAverage n (fun ω => f ω + g ω) = rieszWalkAverage n f + rieszWalkAverage n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rieszWalkAverage, ih, walkCycleAverage, walkBoolAverage_add]

theorem rieszWalkAverage_const_mul (n : ℕ) (z : ℂ) (f : RieszWalkPath n → ℂ) :
    rieszWalkAverage n (fun ω => z * f ω) = z * rieszWalkAverage n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rieszWalkAverage, ih, walkCycleAverage, walkBoolAverage_const_mul]

theorem rieszWalkAverage_const (n : ℕ) (z : ℂ) : rieszWalkAverage n (fun _ => z) = z := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rieszWalkAverage, ih, walkCycleAverage, walkBoolAverage_const]

theorem rieszWalkAverage_character (a b : ℝ) (n : ℕ) :
    rieszWalkAverage n (rieszWalkCharacter a b n) = (walkCycleMultiplier a b : ℂ) ^ n := by
  induction n with
  | zero => simp only [rieszWalkCharacter, rieszWalkAverage_const, pow_zero]
  | succ n ih =>
    simp only [rieszWalkAverage, rieszWalkCharacter, rieszWalkAverage_const_mul, ih,
      walkCycleAverage, walkBoolAverage_mul_const]
    change walkCycleAverage (walkCyclePhase a b) * (walkCycleMultiplier a b : ℂ) ^ n = _
    rw [walkCycleAverage_phase, pow_succ']

theorem rieszWalkCharacter_conj_mul (a b : ℝ) (n : ℕ) (ω : RieszWalkPath n) :
    conj (rieszWalkCharacter a b n ω) * rieszWalkCharacter a b n ω = 1 := by
  induction n with
  | zero => simp only [rieszWalkCharacter, map_one, one_mul]
  | succ n ih =>
    simp only [rieszWalkCharacter, walkCyclePhase, map_mul]
    calc
      _ = (conj (walkSignedPhase a ω.1.1) * walkSignedPhase a ω.1.1) *
          (conj (walkSignedPhase b ω.1.2) * walkSignedPhase b ω.1.2) *
          (conj (rieszWalkCharacter a b n ω.2) * rieszWalkCharacter a b n ω.2) := by ring
      _ = _ := by rw [walkSignedPhase_conj_mul, walkSignedPhase_conj_mul, ih]; ring

theorem rieszWalkAverage_conj (n : ℕ) (f : RieszWalkPath n → ℂ) :
    rieszWalkAverage n (fun ω => conj (f ω)) = conj (rieszWalkAverage n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rieszWalkAverage, ih, walkCycleAverage, walkBoolAverage, map_add, map_div₀, map_ofNat]

theorem rieszWalkAverage_conj_character (a b : ℝ) (n : ℕ) :
    rieszWalkAverage n (fun ω => conj (rieszWalkCharacter a b n ω)) =
      (walkCycleMultiplier a b : ℂ) ^ n := by
  rw [rieszWalkAverage_conj, rieszWalkAverage_character]
  simp only [map_pow, Complex.conj_ofReal]

/-- The recursive average is exactly the normalized sum over all 4^n paths. -/
theorem rieszWalkAverage_eq_sum (n : ℕ) (f : RieszWalkPath n → ℂ) :
    rieszWalkAverage n f = (1 / 4 : ℂ) ^ n * ∑ ω : RieszWalkPath n, f ω := by
  induction n with
  | zero => simp [rieszWalkAverage, RieszWalkPath]
  | succ n ih =>
    change walkCycleAverage (fun e d => rieszWalkAverage n (fun ω => f ((e, d), ω))) =
      (1 / 4 : ℂ) ^ (n + 1) * ∑ ω : (Bool × Bool) × RieszWalkPath n, f ω
    simp only [ih, walkCycleAverage, walkBoolAverage, Fintype.sum_prod_type, Fintype.sum_bool,
      pow_succ]
    ring

/-- Finite backward Markov conditional average after revealing the x-sign.
The unobserved y-sign and all future path signs are genuinely averaged. -/
theorem rieszWalkBackward_mid (a b : ℝ) (n : ℕ) (z : ℂ) (e : Bool) :
    walkBoolAverage (fun d => rieszWalkAverage n (fun ω =>
      z * walkCyclePhase a b e d * rieszWalkCharacter a b n ω)) =
        z * walkSignedPhase a e * (Real.cos b : ℂ) * (walkCycleMultiplier a b : ℂ) ^ n := by
  simp only [rieszWalkAverage_const_mul, rieszWalkAverage_character, walkCyclePhase,
    walkBoolAverage_mul_const, walkBoolAverage_const_mul, walkBoolAverage_phase]
  ring

/-- Before either current sign is revealed, the actual terminal conditional
average is the full Markov eigenvalue times the future average. -/
theorem rieszWalkBackward_before (a b : ℝ) (n : ℕ) (z : ℂ) :
    walkCycleAverage (fun e d => rieszWalkAverage n (fun ω =>
      z * walkCyclePhase a b e d * rieszWalkCharacter a b n ω)) =
        z * (walkCycleMultiplier a b : ℂ) ^ (n + 1) := by
  simp only [rieszWalkAverage_const_mul, rieszWalkAverage_character,
    walkCycleAverage_mul_const, walkCycleAverage_const_mul, walkCycleAverage_phase, pow_succ]
  ring

/-- The exact finite projected multiplier produced by the signed path sum. -/
def walkRieszFiniteCoefficient (a b : ℝ) (n : ℕ) : ℝ :=
  walkRieszNumerator a b * ∑ q ∈ Finset.range n, (walkCycleMultiplier a b ^ 2) ^ q

/-- Actual endpoint pullback and finite uniform averaging recover the exact
discrete Riesz coefficient. No Fourier multiplier or probabilistic certificate
is a premise. -/
theorem rieszWalkTransform_endpoint_average (a b : ℝ) (n : ℕ) :
    rieszWalkAverage n (fun ω => conj (rieszWalkCharacter a b n ω) * rieszWalkTransform a b n ω) =
      (walkRieszFiniteCoefficient a b n : ℂ) := by
  induction n with
  | zero =>
    simp only [rieszWalkAverage, rieszWalkTransform, mul_zero, walkRieszFiniteCoefficient,
      Finset.range_zero, Finset.sum_empty, mul_zero, Complex.ofReal_zero]
  | succ n ih =>
    have heq : (fun ω : RieszWalkPath (n + 1) =>
        conj (rieszWalkCharacter a b (n + 1) ω) * rieszWalkTransform a b (n + 1) ω) =
        (fun ω => ((walkCycleMultiplier a b : ℂ) ^ n *
            (conj (walkCyclePhase a b ω.1.1 ω.1.2) * walkSignedDifference a b ω.1.1 ω.1.2)) *
              conj (rieszWalkCharacter a b n ω.2) +
          conj (rieszWalkCharacter a b n ω.2) * rieszWalkTransform a b n ω.2) := by
      funext ω
      simp only [rieszWalkCharacter, rieszWalkTransform, map_mul]
      calc
        _ = ((walkCycleMultiplier a b : ℂ) ^ n *
              (conj (walkCyclePhase a b ω.1.1 ω.1.2) * walkSignedDifference a b ω.1.1 ω.1.2)) *
                conj (rieszWalkCharacter a b n ω.2) +
            (conj (walkCyclePhase a b ω.1.1 ω.1.2) * walkCyclePhase a b ω.1.1 ω.1.2) *
              (conj (rieszWalkCharacter a b n ω.2) * rieszWalkTransform a b n ω.2) := by ring
        _ = _ := by rw [walkCyclePhase_conj_mul, one_mul]
    rw [heq]
    change walkCycleAverage (fun e d => rieszWalkAverage n (fun ω =>
      ((walkCycleMultiplier a b : ℂ) ^ n *
        (conj (walkCyclePhase a b e d) * walkSignedDifference a b e d)) *
          conj (rieszWalkCharacter a b n ω) +
        conj (rieszWalkCharacter a b n ω) * rieszWalkTransform a b n ω)) = _
    simp only [rieszWalkAverage_add, rieszWalkAverage_const_mul,
      rieszWalkAverage_conj_character, ih, walkCycleAverage_add,
      walkCycleAverage_mul_const, walkCycleAverage_const_mul, walkCycleAverage_const,
      walkSignedDifference_endpoint_average]
    have hp : (walkCycleMultiplier a b : ℂ) ^ n * (walkCycleMultiplier a b : ℂ) ^ n =
        ((walkCycleMultiplier a b : ℂ) ^ 2) ^ n := by
      rw [← mul_pow, pow_two]
    simp only [walkRieszFiniteCoefficient, Finset.sum_range_succ, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_pow]
    calc
      _ = (walkRieszNumerator a b : ℂ) *
          ((∑ q ∈ Finset.range n, ((walkCycleMultiplier a b : ℂ) ^ 2) ^ q) +
            ((walkCycleMultiplier a b : ℂ) ^ 2) ^ n) := by rw [← hp]; ring
      _ = _ := rfl

/-- Number of genuine Boolean paths, derived from their actual product type. -/
theorem rieszWalkPath_card (n : ℕ) : Fintype.card (RieszWalkPath n) = 4 ^ n := by
  induction n with
  | zero => simp [RieszWalkPath]
  | succ n ih =>
    change Fintype.card ((Bool × Bool) × RieszWalkPath n) = _
    simp only [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    ring

/-- Actual normalized finite-path mean, now for arbitrary real vector values. -/
def rieszWalkMean {E : Type*} [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (f : RieszWalkPath n → E) : E :=
  (1 / 4 : ℝ) ^ n • ∑ ω : RieszWalkPath n, f ω

theorem rieszWalkMean_complex (n : ℕ) (f : RieszWalkPath n → ℂ) :
    rieszWalkMean n f = rieszWalkAverage n f := by
  rw [rieszWalkAverage_eq_sum]
  simp only [rieszWalkMean, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]

section VectorMean

variable {E F J : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [Fintype J]

theorem rieszWalkMean_add (n : ℕ) (f g : RieszWalkPath n → E) :
    rieszWalkMean n (fun ω => f ω + g ω) = rieszWalkMean n f + rieszWalkMean n g := by
  simp only [rieszWalkMean, Finset.sum_add_distrib, smul_add]

theorem rieszWalkMean_fun_sum (n : ℕ) (f : J → RieszWalkPath n → E) :
    rieszWalkMean n (fun ω => ∑ j, f j ω) = ∑ j, rieszWalkMean n (f j) := by
  unfold rieszWalkMean
  rw [Finset.sum_comm, Finset.smul_sum]

theorem rieszWalkMean_smul_const (n : ℕ) (f : RieszWalkPath n → ℝ) (x : E) :
    rieszWalkMean n (fun ω => f ω • x) = rieszWalkMean n f • x := by
  simp only [rieszWalkMean, ← Finset.sum_smul, smul_smul, smul_eq_mul]

theorem map_rieszWalkMean (L : E →ₗ[ℝ] F) (n : ℕ) (f : RieszWalkPath n → E) :
    L (rieszWalkMean n f) = rieszWalkMean n (fun ω => L (f ω)) := by
  simp only [rieszWalkMean, map_smul, map_sum]

end VectorMean

@[simp] theorem walkComplexPhase_re (a : ℝ) : (walkComplexPhase a).re = Real.cos a := by
  simp only [walkComplexPhase, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

@[simp] theorem walkComplexPhase_im (a : ℝ) : (walkComplexPhase a).im = Real.sin a := by
  simp only [walkComplexPhase, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

/-- The actual signed path field pulled back by its endpoint, with an
arbitrary initial Fourier phase. -/
def rieszWalkProjectedMode (a b z : ℝ) (n : ℕ) (ω : RieszWalkPath n) : ℂ :=
  walkComplexPhase z *
    (conj (rieszWalkCharacter a b n ω) * rieszWalkTransform a b n ω)

theorem rieszWalkProjectedMode_mean (a b z : ℝ) (n : ℕ) :
    rieszWalkMean n (rieszWalkProjectedMode a b z n) =
      walkComplexPhase z * (walkRieszFiniteCoefficient a b n : ℂ) := by
  rw [rieszWalkMean_complex]
  change rieszWalkAverage n (fun ω => walkComplexPhase z *
    (conj (rieszWalkCharacter a b n ω) * rieszWalkTransform a b n ω)) = _
  rw [rieszWalkAverage_const_mul, rieszWalkTransform_endpoint_average]

section ProjectedPolynomial

variable {J E : Type*} [Fintype J] [AddCommGroup E] [Module ℝ E]

/-- Actual finite vector-valued path field, using the same two Boolean steps
for every frequency and genuine endpoint pullback. -/
def rieszWalkProjectedPolynomial (k : J → ℤ × ℤ) (a b : J → ℝ) (X Y : J → E)
    (n : ℕ) (θ : ℝ × ℝ) (ω : RieszWalkPath n) : E :=
  ∑ j, ((rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n ω).re • X j +
    (rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n ω).im • Y j)

/-- The actual finite-path projection of the signed polynomial is precisely
the finite discrete Riesz multiplier polynomial. This is an equality of real
vector values, without an operator or norm certificate. -/
theorem rieszWalkProjectedPolynomial_mean (k : J → ℤ × ℤ) (a b : J → ℝ) (X Y : J → E)
    (n : ℕ) (θ : ℝ × ℝ) :
    rieszWalkMean n (rieszWalkProjectedPolynomial k a b X Y n θ) =
      ∑ j, ((walkRieszFiniteCoefficient (a j) (b j) n * Real.cos (integerPlanePhase (k j) θ)) • X j +
        (walkRieszFiniteCoefficient (a j) (b j) n * Real.sin (integerPlanePhase (k j) θ)) • Y j) := by
  change rieszWalkMean n (fun ω => ∑ j,
    ((rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n ω).re • X j +
      (rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n ω).im • Y j)) = _
  rw [rieszWalkMean_fun_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [rieszWalkMean_add, rieszWalkMean_smul_const, rieszWalkMean_smul_const]
  have hre := map_rieszWalkMean Complex.reLm n
    (rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n)
  have him := map_rieszWalkMean Complex.imLm n
    (rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n)
  change (rieszWalkMean n (rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n)).re =
    rieszWalkMean n (fun ω => (rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n ω).re) at hre
  change (rieszWalkMean n (rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n)).im =
    rieszWalkMean n (fun ω => (rieszWalkProjectedMode (a j) (b j) (integerPlanePhase (k j) θ) n ω).im) at him
  rw [← hre, ← him, rieszWalkProjectedMode_mean]
  simp only [Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, walkComplexPhase_re, walkComplexPhase_im,
    zero_mul, sub_zero, zero_add, mul_comm]

end ProjectedPolynomial

/-- The actual projected path polynomial has exactly the coefficient action
used by the existing finite real matrix Fourier interface. -/
theorem rieszWalkProjectedPolynomial_matrix_mean {J H : Type*} [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (k : J → ℤ × ℤ) (a b : J → ℝ) (X Y : J → H →L[ℝ] H) (n : ℕ) (θ : ℝ × ℝ) :
    rieszWalkMean n (rieszWalkProjectedPolynomial k a b X Y n θ) =
      realMatrixTrigPolynomial k
        (fun j => walkRieszFiniteCoefficient (a j) (b j) n • X j)
        (fun j => walkRieszFiniteCoefficient (a j) (b j) n • Y j) θ := by
  rw [rieszWalkProjectedPolynomial_mean]
  simp only [realMatrixTrigPolynomial, smul_smul, mul_comm]

/-- The infinite-horizon coefficient for a fixed nondegenerate step size. -/
def walkRieszInfiniteCoefficient (a b : ℝ) : ℝ :=
  walkRieszNumerator a b / (1 - walkCycleMultiplier a b ^ 2)

theorem walkRieszFiniteCoefficient_tendsto (a b : ℝ) (hc : |walkCycleMultiplier a b| < 1) :
    Tendsto (walkRieszFiniteCoefficient a b) atTop (𝓝 (walkRieszInfiniteCoefficient a b)) := by
  have hc2 : |walkCycleMultiplier a b ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    obtain ⟨hl, hr⟩ := abs_lt.mp hc
    nlinarith
  unfold walkRieszFiniteCoefficient walkRieszInfiniteCoefficient
  simpa only [div_eq_mul_inv] using
    (hasSum_geometric_of_abs_lt_one hc2).tendsto_sum_nat.const_mul (walkRieszNumerator a b)

/-- The denominator is exactly the total two-step martingale energy. -/
theorem walkRieszDenominator (a b : ℝ) :
    1 - walkCycleMultiplier a b ^ 2 = Real.sin a ^ 2 * Real.cos b ^ 2 + Real.sin b ^ 2 := by
  have ha := congrArg (fun x : ℝ => x * Real.cos b ^ 2) (Real.sin_sq_add_cos_sq a)
  have hb := Real.sin_sq_add_cos_sq b
  unfold walkCycleMultiplier
  nlinarith

def walkSincSlope (a h : ℝ) : ℝ := a * Real.sinc (h * a)

theorem sin_step_eq_sinc (a h : ℝ) : Real.sin (h * a) = h * walkSincSlope a h := by
  by_cases ha : h * a = 0
  · simp only [walkSincSlope, ha, Real.sin_zero, Real.sinc_zero, mul_one]
  · rw [walkSincSlope, Real.sinc_of_ne_zero ha]
    symm
    calc
      _ = ((h * a) * Real.sin (h * a)) / (h * a) := by ring
      _ = _ := mul_div_cancel_left₀ _ ha

def walkScaledRieszCoefficient (a b h : ℝ) : ℝ :=
  (walkSincSlope a h ^ 2 * Real.cos (h * b) ^ 2 - walkSincSlope b h ^ 2) /
    (walkSincSlope a h ^ 2 * Real.cos (h * b) ^ 2 + walkSincSlope b h ^ 2)

theorem walkRieszInfiniteCoefficient_scaled (a b : ℝ) {h : ℝ} (hh : h ≠ 0) :
    walkRieszInfiniteCoefficient (h * a) (h * b) = walkScaledRieszCoefficient a b h := by
  have hn : walkRieszNumerator (h * a) (h * b) = h ^ 2 *
      (walkSincSlope a h ^ 2 * Real.cos (h * b) ^ 2 - walkSincSlope b h ^ 2) := by
    rw [walkRieszNumerator, sin_step_eq_sinc, sin_step_eq_sinc]
    ring
  have hd : 1 - walkCycleMultiplier (h * a) (h * b) ^ 2 = h ^ 2 *
      (walkSincSlope a h ^ 2 * Real.cos (h * b) ^ 2 + walkSincSlope b h ^ 2) := by
    rw [walkRieszDenominator, sin_step_eq_sinc, sin_step_eq_sinc]
    ring
  rw [walkRieszInfiniteCoefficient, hn, hd, mul_div_mul_left _ _ (pow_ne_zero 2 hh)]
  rfl

/-- After the genuine horizon limit, the small-step limit is the exact base
second-order Riesz symbol, for every nonzero planar frequency. -/
theorem walkRieszInfiniteCoefficient_small_step_tendsto (a b : ℝ) (hab : (a, b) ≠ 0) :
    Tendsto (fun h => walkRieszInfiniteCoefficient (h * a) (h * b)) (𝓝[≠] (0 : ℝ))
      (𝓝 (planarRieszSymbol planarReflectionMatrix (a, b))) := by
  have hp : a ^ 2 + b ^ 2 ≠ 0 := (planarFrequencySq_pos hab).ne'
  have hs : ContinuousAt (walkScaledRieszCoefficient a b) 0 := by
    apply ContinuousAt.div
    · unfold walkSincSlope
      fun_prop
    · unfold walkSincSlope
      fun_prop
    · simpa only [walkSincSlope, zero_mul, Real.sinc_zero, mul_one, Real.cos_zero, one_pow,
        mul_one] using hp
  have ht := hs.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have heq : (fun h => walkRieszInfiniteCoefficient (h * a) (h * b)) =ᶠ[𝓝[≠] (0 : ℝ)]
      walkScaledRieszCoefficient a b := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact walkRieszInfiniteCoefficient_scaled a b hh
  simpa [walkScaledRieszCoefficient, walkSincSlope, planarRieszSymbol, planarReflectionMatrix,
    planarQuadraticForm, planarFrequencySq, sub_eq_add_neg] using ht.congr' heq.symm

/-- For every nonzero frequency, all sufficiently small nonzero steps are
genuinely nondegenerate, so the horizon limit applies on a punctured neighborhood. -/
theorem walkCycleMultiplier_small_step_abs_lt_one (a b : ℝ) (hab : (a, b) ≠ 0) :
    ∀ᶠ h in 𝓝[≠] (0 : ℝ), |walkCycleMultiplier (h * a) (h * b)| < 1 := by
  let D : ℝ → ℝ := fun h => walkSincSlope a h ^ 2 * Real.cos (h * b) ^ 2 + walkSincSlope b h ^ 2
  have hD : Continuous D := by unfold D walkSincSlope; fun_prop
  have hpos : 0 < D 0 := by
    simpa only [D, walkSincSlope, zero_mul, Real.sinc_zero, Real.cos_zero, one_pow, planarFrequencySq,
      mul_one] using planarFrequencySq_pos hab
  have hevent : ∀ᶠ h in 𝓝 (0 : ℝ), 0 < D h :=
    (isOpen_lt continuous_const hD).mem_nhds hpos
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hd hh
  have heq : 1 - walkCycleMultiplier (h * a) (h * b) ^ 2 = h ^ 2 * D h := by
    rw [walkRieszDenominator, sin_step_eq_sinc, sin_step_eq_sinc]
    dsimp only [D]
    ring
  have henergy : 0 < 1 - walkCycleMultiplier (h * a) (h * b) ^ 2 := by
    rw [heq]
    exact mul_pos (sq_pos_of_ne_zero hh) hd
  rw [abs_lt]
  constructor <;> nlinarith

/-- The actual finite-walk coefficients have the two successive limits used
by the discrete Riesz construction. No joint scaling regime is assumed. -/
theorem walkRiesz_iterated_limits (a b : ℝ) (hab : (a, b) ≠ 0) :
    (∀ᶠ h in 𝓝[≠] (0 : ℝ), Tendsto (walkRieszFiniteCoefficient (h * a) (h * b)) atTop
      (𝓝 (walkRieszInfiniteCoefficient (h * a) (h * b)))) ∧
    Tendsto (fun h => walkRieszInfiniteCoefficient (h * a) (h * b)) (𝓝[≠] (0 : ℝ))
      (𝓝 (planarRieszSymbol planarReflectionMatrix (a, b))) := by
  constructor
  · exact (walkCycleMultiplier_small_step_abs_lt_one a b hab).mono
      (fun h hh => walkRieszFiniteCoefficient_tendsto _ _ hh)
  · exact walkRieszInfiniteCoefficient_small_step_tendsto a b hab

/-- The finite two-sign tree is actually the existing 2n-coordinate Walsh
cube, with x then y at the head of each cycle. -/
def rieszWalkCubeEquiv : (n : ℕ) → RieszWalkPath n ≃ WalshCube (2 * n)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun ω => by cases ω; rfl
      right_inv := fun _ => by funext i; exact Fin.elim0 i }
  | n + 1 => by
    change ((Bool × Bool) × RieszWalkPath n) ≃ (Fin (2 * (n + 1)) → Bool)
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    exact (Equiv.prodCongr (Equiv.refl (Bool × Bool)) (rieszWalkCubeEquiv n)).trans
      ((Equiv.prodAssoc Bool Bool (WalshCube (2 * n))).trans
        ((Equiv.prodCongr (Equiv.refl Bool) (Fin.consEquiv (fun _ : Fin (2 * n + 1) => Bool))).trans
          (Fin.consEquiv (fun _ : Fin ((2 * n + 1) + 1) => Bool))))

/-- The actual path mean is precisely the existing Walsh prefix conditional
average at level zero, after the constructed cube equivalence. -/
theorem rieszWalkMean_eq_walshPrefixAverage_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (f : RieszWalkPath n → E) (ω : WalshCube (2 * n)) :
    rieszWalkMean n f =
      walshPrefixAverage 0 (fun η => f ((rieszWalkCubeEquiv n).symm η)) ω := by
  classical
  have hcard : (Fintype.card (WalshCube (2 * n)) : ℝ) = (4 : ℝ) ^ n := by
    have hn := (Fintype.card_congr (rieszWalkCubeEquiv n)).symm.trans (rieszWalkPath_card n)
    exact_mod_cast hn
  have hsum : (∑ η : WalshCube (2 * n), f ((rieszWalkCubeEquiv n).symm η)) =
      ∑ η : RieszWalkPath n, f η := Equiv.sum_comp (rieszWalkCubeEquiv n).symm f
  have hmerge (η : WalshCube (2 * n)) : walshMerge 0 ω η = η := by
    funext j
    simp only [walshMerge, Nat.not_lt_zero, if_false]
  simp only [rieszWalkMean, walshPrefixAverage, hmerge, hsum, hcard]
  congr 1
  simp only [one_div, inv_pow]

/-- A common planar step for the two independent signs. Directions need not
be coordinate axes or rational vectors. -/
def rieszWalkSpatialStep (h : ℝ) (u v : ℝ × ℝ) (e d : Bool) : ℝ × ℝ :=
  (walshSign e * h) • u + (walshSign d * h) • v

def rieszWalkDisplacement (h : ℝ) (u v : ℝ × ℝ) : (n : ℕ) → RieszWalkPath n → ℝ × ℝ
  | 0, _ => 0
  | n + 1, ω => rieszWalkSpatialStep h u v ω.1.1 ω.1.2 + rieszWalkDisplacement h u v n ω.2

/-- The path character is the actual Fourier phase of the common planar
random-walk displacement, for every real pair of directions. -/
theorem rieszWalkCharacter_displacement (k : ℤ × ℤ) (h : ℝ) (u v : ℝ × ℝ)
    (n : ℕ) (ω : RieszWalkPath n) :
    rieszWalkCharacter (integerPlanePhase k (h • u)) (integerPlanePhase k (h • v)) n ω =
      walkComplexPhase (integerPlanePhase k (rieszWalkDisplacement h u v n ω)) := by
  induction n with
  | zero => simp [rieszWalkCharacter, rieszWalkDisplacement, integerPlanePhase]
  | succ n ih =>
    simp only [rieszWalkCharacter, walkCyclePhase, walkSignedPhase, ih,
      rieszWalkDisplacement, ← walkComplexPhase_add]
    congr 1
    simp only [rieszWalkSpatialStep, integerPlanePhase, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- The full terminal mode is the actual translated initial Fourier mode. -/
theorem rieszWalkTerminalMode_eq_translate (k : ℤ × ℤ) (h : ℝ) (u v θ : ℝ × ℝ)
    (n : ℕ) (ω : RieszWalkPath n) :
    walkComplexPhase (integerPlanePhase k θ) *
      rieszWalkCharacter (integerPlanePhase k (h • u)) (integerPlanePhase k (h • v)) n ω =
        walkComplexPhase (integerPlanePhase k (θ + rieszWalkDisplacement h u v n ω)) := by
  rw [rieszWalkCharacter_displacement, ← walkComplexPhase_add]
  congr 1
  simp only [integerPlanePhase, Prod.fst_add, Prod.snd_add]
  ring

/-- The projected mode uses the actual inverse endpoint translation. -/
theorem rieszWalkProjectedMode_eq_endpoint_pullback (k : ℤ × ℤ) (h : ℝ) (u v θ : ℝ × ℝ)
    (n : ℕ) (ω : RieszWalkPath n) :
    rieszWalkProjectedMode (integerPlanePhase k (h • u)) (integerPlanePhase k (h • v))
      (integerPlanePhase k θ) n ω =
        walkComplexPhase (integerPlanePhase k (θ - rieszWalkDisplacement h u v n ω)) *
          rieszWalkTransform (integerPlanePhase k (h • u)) (integerPlanePhase k (h • v)) n ω := by
  rw [rieszWalkProjectedMode, rieszWalkCharacter_displacement, ← walkComplexPhase_neg]
  rw [← mul_assoc, ← walkComplexPhase_add]
  congr 2
  simp only [integerPlanePhase, Prod.fst_sub, Prod.snd_sub]
  ring

end
end KernelSeq
