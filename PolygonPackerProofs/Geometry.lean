module

public import Mathlib

/-!
# Two elementary facts of plane geometry used by the checker

* a point whose barycentric coordinates (computed with cross products) are nonnegative
  lies in the triangle;
* two point sets separated (weakly) by a line have convex hulls with disjoint interiors.
-/

@[expose] public section

namespace PolygonPacker

/-- Cross product of two plane vectors. -/
def crossC (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- Inner product with a fixed vector `w`. -/
def dotC (w z : ℂ) : ℝ := w.re * z.re + w.im * z.im

theorem mem_convexHull_triangle {A B C p : ℂ}
    (hA : 0 ≤ crossC (B - p) (C - p)) (hB : 0 ≤ crossC (C - p) (A - p))
    (hC : 0 ≤ crossC (A - p) (B - p))
    (hD : 0 < crossC (B - p) (C - p) + crossC (C - p) (A - p) + crossC (A - p) (B - p)) :
    p ∈ convexHull ℝ ({A, B, C} : Set ℂ) := by
  set a := crossC (B - p) (C - p)
  set b := crossC (C - p) (A - p)
  set c := crossC (A - p) (B - p)
  set D := a + b + c
  have hconv := (convex_convexHull ℝ ({A, B, C} : Set ℂ)).sum_mem (t := Finset.univ)
    (w := ![a / D, b / D, c / D]) (z := ![A, B, C])
    (by intro i _; fin_cases i <;> simp <;> positivity)
    (by simp [Fin.sum_univ_three]; field_simp; rfl)
    (by intro i _; fin_cases i <;> simp <;> apply subset_convexHull <;> simp)
  convert hconv using 1
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  apply Complex.ext <;> simp <;> field_simp <;>
    simp only [a, b, c, D, crossC, Complex.sub_re, Complex.sub_im] <;> ring

private lemma dotC_linear (w : ℂ) : IsLinearMap ℝ (dotC w) where
  map_add x y := by simp [dotC]; ring
  map_smul r x := by simp [dotC]; ring

theorem disjoint_interior_convexHull_of_sep {s t : Set ℂ} (w : ℂ) (hw : w ≠ 0)
    (h : ∀ x ∈ s, ∀ y ∈ t, dotC w x ≤ dotC w y) :
    Disjoint (interior (convexHull ℝ s)) (interior (convexHull ℝ t)) := by
  -- every point of `hull s` is below every point of `hull t`
  have h1 : ∀ x ∈ convexHull ℝ s, ∀ y ∈ t, dotC w x ≤ dotC w y := by
    intro x hx y hy
    exact convexHull_min (t := {z | dotC w z ≤ dotC w y}) (fun z hz => h z hz y hy)
      (convex_halfSpace_le (dotC_linear w) _) hx
  have h2 : ∀ x ∈ convexHull ℝ s, ∀ y ∈ convexHull ℝ t, dotC w x ≤ dotC w y := by
    intro x hx y hy
    exact convexHull_min (t := {z | dotC w x ≤ dotC w z}) (fun z hz => h1 x hx z hz)
      (convex_halfSpace_ge (dotC_linear w) _) hy
  rw [Set.disjoint_left]
  intro z hzs hzt
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hzs hzt
  obtain ⟨ε₁, hε₁, hb₁⟩ := hzs
  obtain ⟨ε₂, hε₂, hb₂⟩ := hzt
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set δ := min ε₁ ε₂ / (2 * ‖w‖)
  have hδ : 0 < δ := by positivity
  have hdist : δ * ‖w‖ < min ε₁ ε₂ := by
    simp only [δ]; rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [lt_min hε₁ hε₂]
  have hp : z + (δ : ℂ) * w ∈ convexHull ℝ s := hb₁ (by
    rw [Metric.mem_ball, dist_eq_norm]; simp [abs_of_pos hδ]
    exact hdist.trans_le (min_le_left _ _))
  have hq : z - (δ : ℂ) * w ∈ convexHull ℝ t := hb₂ (by
    rw [Metric.mem_ball, dist_eq_norm]; simp [abs_of_pos hδ]
    exact hdist.trans_le (min_le_right _ _))
  have := h2 _ hp _ hq
  have hw2 : 0 < w.re * w.re + w.im * w.im := by
    have : w.re ≠ 0 ∨ w.im ≠ 0 := by
      by_contra hc; push Not at hc; exact hw (Complex.ext hc.1 hc.2)
    rcases this with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg w.im]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg w.re]
  simp [dotC] at this
  nlinarith

end PolygonPacker
