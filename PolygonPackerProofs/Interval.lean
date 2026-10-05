module

public import Mathlib
public import PolygonPacker.Certificate.Check

/-!
# Soundness of the rational interval arithmetic
-/

@[expose] public section

namespace PolygonPacker

/-- The real number `x` lies in the interval `I`. -/
def Ival.Mem (x : ℝ) (I : Ival) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- The complex number `z` lies in the box `B`. -/
def Box.Mem (z : ℂ) (B : Box) : Prop := Ival.Mem z.re B.re ∧ Ival.Mem z.im B.im

namespace Ival

lemma mem_ofRat (q : ℚ) : Mem (q : ℝ) (ofRat q) := ⟨le_rfl, le_rfl⟩

lemma mem_add {x y : ℝ} {a b : Ival} (hx : Mem x a) (hy : Mem y b) : Mem (x + y) (a.add b) := by
  unfold Mem add at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma mem_sub {x y : ℝ} {a b : Ival} (hx : Mem x a) (hy : Mem y b) : Mem (x - y) (a.sub b) := by
  unfold Mem sub at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

private lemma mul_bounds {x y a b : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
  · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩

private lemma mul_bounds' {k y c d : ℝ} (hy : c ≤ y ∧ y ≤ d) :
    min (k * c) (k * d) ≤ k * y ∧ k * y ≤ max (k * c) (k * d) := by
  have := mul_bounds (y := k) hy
  simp only [mul_comm _ k] at this
  exact this

lemma mem_mul {x y : ℝ} {a b : Ival} (hx : Mem x a) (hy : Mem y b) : Mem (x * y) (a.mul b) := by
  unfold Mem mul at *
  obtain ⟨h1, h2⟩ := mul_bounds (y := y) hx
  obtain ⟨l1, u1⟩ := mul_bounds' (k := (a.lo : ℝ)) hy
  obtain ⟨l2, u2⟩ := mul_bounds' (k := (a.hi : ℝ)) hy
  push_cast
  exact ⟨le_trans (min_le_min l1 l2) h1, le_trans h2 (max_le_max u1 u2)⟩

lemma mem_inv {x : ℝ} {a : Ival} (hx : Mem x a) (ha : 0 < a.lo) : Mem x⁻¹ a.inv := by
  unfold Mem inv at *
  have h0 : (0 : ℝ) < a.lo := by exact_mod_cast ha
  push_cast
  constructor
  · rw [one_div]; exact inv_anti₀ (by linarith [hx.1]) hx.2
  · rw [one_div]; exact inv_anti₀ h0 hx.1

lemma mem_round {x : ℝ} {a : Ival} (hx : Mem x a) : Mem x a.round := by
  unfold Mem round at *
  have hs : (0 : ℝ) < (2 : ℝ) ^ prec := by positivity
  push_cast
  constructor
  · rw [div_le_iff₀ hs]
    have h' : ((((a.lo * 2 ^ prec).floor : ℚ)) : ℝ) ≤ ((a.lo * 2 ^ prec : ℚ) : ℝ) := by
      exact_mod_cast Rat.floor_le _
    push_cast at h'
    nlinarith [hx.1]
  · rw [le_div_iff₀ hs]
    have h' : ((((-(a.hi * 2 ^ prec)).floor : ℚ)) : ℝ) ≤ ((-(a.hi * 2 ^ prec) : ℚ) : ℝ) := by
      exact_mod_cast Rat.floor_le _
    push_cast at h'
    nlinarith [hx.2]

end Ival

end PolygonPacker
