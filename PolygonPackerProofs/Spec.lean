module

public import Mathlib
public import PolygonPacker.Certificate.Check

/-!
# What a certificate means

The plane is identified with `ℂ`.  `regPolygon m c R a` is the (closed, filled) regular
`m`-gon with centre `c` and circumradius `R`, whose vertices are
`c + R * exp ((a + 2πk/m) i)` for `k < m`.

A certificate describes:
* the inner polygons: for every `Piece` `p`, the regular `nsi`-gon of circumradius `1`
  centred at `(p.x, p.y)` and rotated by `p.angle` (all exact decimals);
* the container: the regular `nsc`-gon centred at the origin with a vertex on the positive
  `x`-axis and circumradius `side * sin (π / nsi) / sin (π / nsc)`, i.e. whose side
  length is exactly `side` times the side length of the inner polygons
  (`Cert.container_side_length`).

`Cert.Valid` says that these exact real polygons form a packing.
-/

@[expose] public section

namespace PolygonPacker

open Complex

/-- Vertex `k` of the regular `m`-gon with centre `c`, circumradius `R` and rotation `a`. -/
noncomputable def regVertex (m : ℕ) (c : ℂ) (R a : ℝ) (k : ℕ) : ℂ :=
  c + R * exp (((a + 2 * Real.pi * k / m : ℝ) : ℂ) * I)

/-- The filled regular `m`-gon with centre `c`, circumradius `R` and rotation `a`. -/
def regPolygon (m : ℕ) (c : ℂ) (R a : ℝ) : Set ℂ :=
  convexHull ℝ (Set.range fun k : Fin m => regVertex m c R a k)

/-- The inner polygon described by a piece: a regular `m`-gon of circumradius `1`. -/
def Piece.toSet (m : ℕ) (p : Piece) : Set ℂ :=
  regPolygon m ⟨(p.x.toRat : ℝ), (p.y.toRat : ℝ)⟩ 1 (p.angle.toRat : ℝ)

/-- The circumradius of the container. -/
noncomputable def Cert.radius (c : Cert) : ℝ :=
  (c.side.toRat : ℝ) * Real.sin (Real.pi / c.nsi) / Real.sin (Real.pi / c.nsc)

/-- The container described by a certificate. -/
def Cert.container (c : Cert) : Set ℂ := regPolygon c.nsc 0 c.radius 0

/-- The certificate describes a genuine packing: the right number of inner polygons, all
inside the container, no two of them overlapping (their interiors are disjoint). -/
structure Cert.Valid (c : Cert) : Prop where
  three_le_nsi : 3 ≤ c.nsi
  three_le_nsc : 3 ≤ c.nsc
  length_eq : c.pieces.length = c.n
  side_pos : 0 < (c.side.toRat : ℝ)
  subset_container : ∀ p ∈ c.pieces, p.toSet c.nsi ⊆ c.container
  disjoint_interiors : ∀ i j : Fin c.pieces.length, i ≠ j →
    Disjoint (interior ((c.pieces.get i).toSet c.nsi)) (interior ((c.pieces.get j).toSet c.nsi))

/-- Consecutive vertices of a regular `m`-gon of circumradius `R ≥ 0` are at distance
`2 R sin (π / m)` (the side length). -/
theorem regVertex_dist (m : ℕ) (hm : 0 < m) (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (a : ℝ) (k : ℕ) :
    dist (regVertex m c R a k) (regVertex m c R a (k + 1)) = 2 * R * Real.sin (Real.pi / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h : regVertex m c R a (k + 1) - regVertex m c R a k =
      R * exp (((a + 2 * Real.pi * k / m : ℝ) : ℂ) * I) *
        (exp (I * ((2 * Real.pi / m : ℝ) : ℂ)) - 1) := by
    unfold regVertex
    have e : (((a + 2 * Real.pi * ((k + 1 : ℕ) : ℝ) / m : ℝ) : ℂ) * I) =
        ((a + 2 * Real.pi * k / m : ℝ) : ℂ) * I + I * ((2 * Real.pi / m : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.exp_add]; ring
  rw [dist_comm, dist_eq_norm, h, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hR, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hs : 0 ≤ Real.sin (2 * Real.pi / m / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · rw [div_div, mul_comm (m : ℝ) 2, ← div_div, mul_div_cancel_left₀ _ (two_ne_zero)]
      exact div_le_self Real.pi_pos.le (by exact_mod_cast hm)
  rw [abs_of_nonneg hs]
  rw [div_div, mul_comm (m : ℝ) 2, ← div_div, mul_div_cancel_left₀ _ (two_ne_zero)]
  ring

/-- The side length of the container is exactly `side` times the side length of an inner
polygon. -/
theorem Cert.container_side_length (c : Cert) (h : c.Valid) (p : Piece) (k l : ℕ) :
    dist (regVertex c.nsc 0 c.radius 0 k) (regVertex c.nsc 0 c.radius 0 (k + 1)) =
      (c.side.toRat : ℝ) *
        dist (regVertex c.nsi ⟨(p.x.toRat : ℝ), (p.y.toRat : ℝ)⟩ 1 (p.angle.toRat : ℝ) l)
          (regVertex c.nsi ⟨(p.x.toRat : ℝ), (p.y.toRat : ℝ)⟩ 1 (p.angle.toRat : ℝ) (l + 1)) := by
  have hi : (0 : ℝ) < Real.sin (Real.pi / c.nsi) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < c.nsi := by exact_mod_cast (by linarith [h.three_le_nsi] : 0 < c.nsi)
      positivity
    · exact div_lt_self Real.pi_pos (by exact_mod_cast (by linarith [h.three_le_nsi] : 1 < c.nsi))
  have hc : (0 : ℝ) < Real.sin (Real.pi / c.nsc) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < c.nsc := by exact_mod_cast (by linarith [h.three_le_nsc] : 0 < c.nsc)
      positivity
    · exact div_lt_self Real.pi_pos (by exact_mod_cast (by linarith [h.three_le_nsc] : 1 < c.nsc))
  have hR : 0 ≤ c.radius := by
    unfold Cert.radius; exact (div_pos (mul_pos h.side_pos hi) hc).le
  rw [regVertex_dist _ (by linarith [h.three_le_nsc]) _ hR,
    regVertex_dist _ (by linarith [h.three_le_nsi]) _ zero_le_one]
  unfold Cert.radius
  field_simp

end PolygonPacker
