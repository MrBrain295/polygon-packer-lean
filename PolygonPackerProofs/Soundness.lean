module

public import PolygonPackerProofs.Trig
public import PolygonPackerProofs.Spec
public import PolygonPackerProofs.Geometry
public import PolygonPacker.Certificate.Certify

/-!
# Soundness of the certificate checker and correctness of the program's output

* `Cert.check_sound`: if the exact checker accepts a certificate, the certificate describes
  a genuine packing (`Cert.Valid`): every inner polygon lies in the container and no two
  inner polygons overlap.
* `certifyBest_valid`: every certificate the program can output is valid, and its side
  length is exactly the side length of its container (`certifyBest_side_length`).
-/

@[expose] public section

namespace PolygonPacker

open Complex

/-! ## Vertices -/

lemma vertexAngle_mem (m : ℕ) (a : ℚ) (k : ℕ) :
    Ival.Mem ((a : ℝ) + 2 * Real.pi * k / m) (vertexAngle m a k) := by
  have h := Ival.mem_add (Ival.mem_ofRat a) (Ival.mem_mul pi_mem (Ival.mem_ofRat (2 * k / m)))
  have e : ((a : ℝ) + Real.pi * (((2 * k / m : ℚ)) : ℝ)) = (a : ℝ) + 2 * Real.pi * k / m := by
    push_cast; ring
  rw [e] at h
  exact h

lemma pieceVertex_sound (m : ℕ) (x y a : ℚ) (k : ℕ) :
    Box.Mem (regVertex m ⟨(x : ℝ), (y : ℝ)⟩ 1 (a : ℝ) k) (pieceVertex m x y a k) := by
  have he := expBox_sound (vertexAngle_mem m a k)
  unfold regVertex pieceVertex
  refine ⟨?_, ?_⟩
  · simpa using Ival.mem_add (Ival.mem_ofRat x) he.1
  · simpa using Ival.mem_add (Ival.mem_ofRat y) he.2

lemma sinPiDiv_sound (m : ℕ) : Ival.Mem (Real.sin (Real.pi / m)) (sinPiDiv m) := by
  have h := (expBox_sound (Ival.mem_mul pi_mem (Ival.mem_ofRat (1 / m)))).2
  have e : Real.pi * (((1 / m : ℚ)) : ℝ) = Real.pi / m := by push_cast; ring
  rw [e, Complex.exp_ofReal_mul_I_im] at h
  exact h

lemma radius_sound (c : Cert) (h : 0 < (sinPiDiv c.nsc).lo) : Ival.Mem c.radius c.radiusIval := by
  unfold Cert.radius Cert.radiusIval
  apply Ival.mem_round
  rw [div_eq_mul_inv]
  exact Ival.mem_mul (Ival.mem_mul (Ival.mem_ofRat _) (sinPiDiv_sound _))
    (Ival.mem_inv (sinPiDiv_sound _) h)

lemma containerVertex_sound (m : ℕ) {R : ℝ} {RI : Ival} (hR : Ival.Mem R RI) (k : ℕ) :
    Box.Mem (regVertex m 0 R 0 k) (containerVertex m RI k) := by
  have he := expBox_sound (vertexAngle_mem m 0 k)
  simp only [Rat.cast_zero] at he
  unfold regVertex containerVertex
  refine ⟨?_, ?_⟩
  · simpa using Ival.mem_round (Ival.mem_mul hR he.1)
  · simpa using Ival.mem_round (Ival.mem_mul hR he.2)

/-! ## Geometric tests -/

lemma Box.mem_sub {u v : ℂ} {U V : Box} (hu : Box.Mem u U) (hv : Box.Mem v V) :
    Box.Mem (u - v) (U.sub V) :=
  ⟨by
    change Ival.Mem (u.re - v.re) (U.re.sub V.re)
    exact Ival.mem_sub hu.1 hv.1,
   by
    change Ival.Mem (u.im - v.im) (U.im.sub V.im)
    exact Ival.mem_sub hu.2 hv.2⟩

lemma cross_sound {u v : ℂ} {U V : Box} (hu : Box.Mem u U) (hv : Box.Mem v V) :
    Ival.Mem (crossC u v) (cross U V) :=
  Ival.mem_sub (Ival.mem_mul hu.1 hv.2) (Ival.mem_mul hu.2 hv.1)

lemma inTriangle_sound {p A B C : ℂ} {P BA BB BC : Box} (h : inTriangle P BA BB BC = true)
    (hp : Box.Mem p P) (hA : Box.Mem A BA) (hB : Box.Mem B BB) (hC : Box.Mem C BC) :
    p ∈ convexHull ℝ ({A, B, C} : Set ℂ) := by
  unfold inTriangle at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have dA := cross_sound (Box.mem_sub hB hp) (Box.mem_sub hC hp)
  have dB := cross_sound (Box.mem_sub hC hp) (Box.mem_sub hA hp)
  have dC := cross_sound (Box.mem_sub hA hp) (Box.mem_sub hB hp)
  have dS := Ival.mem_add (Ival.mem_add dA dB) dC
  apply mem_convexHull_triangle
  · exact le_trans (by exact_mod_cast h1) dA.1
  · exact le_trans (by exact_mod_cast h2) dB.1
  · exact le_trans (by exact_mod_cast h3) dC.1
  · exact lt_of_lt_of_le (by exact_mod_cast h4) dS.1

lemma inHull_sound {cv : List Box} {V : Set ℂ} (hcv : ∀ B ∈ cv, ∃ z ∈ V, Box.Mem z B)
    {P : Box} {p : ℂ} (h : inHull cv P = true) (hp : Box.Mem p P) : p ∈ convexHull ℝ V := by
  unfold inHull at h
  simp only [List.any_eq_true] at h
  obtain ⟨BA, hBA, BB, hBB, BC, hBC, ht⟩ := h
  obtain ⟨A, hA, hAm⟩ := hcv BA hBA
  obtain ⟨B, hB, hBm⟩ := hcv BB hBB
  obtain ⟨C, hC, hCm⟩ := hcv BC hBC
  have := inTriangle_sound ht hp hAm hBm hCm
  refine convexHull_mono ?_ this
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> assumption

lemma dotI_sound (w : ℚ × ℚ) {z : ℂ} {B : Box} (hz : Box.Mem z B) :
    Ival.Mem (dotC ⟨(w.1 : ℝ), (w.2 : ℝ)⟩ z) (dotI w B) :=
  Ival.mem_add (Ival.mem_mul (Ival.mem_ofRat _) hz.1) (Ival.mem_mul (Ival.mem_ofRat _) hz.2)

lemma separatedBy_sound {U V : List Box} {s t : Set ℂ} {w : ℚ × ℚ}
    (h : separatedBy U V w = true)
    (hs : ∀ x ∈ s, ∃ B ∈ U, Box.Mem x B) (ht : ∀ y ∈ t, ∃ B ∈ V, Box.Mem y B) :
    Disjoint (interior (convexHull ℝ s)) (interior (convexHull ℝ t)) := by
  unfold separatedBy at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hw, hall⟩ := h
  apply disjoint_interior_convexHull_of_sep ⟨(w.1 : ℝ), (w.2 : ℝ)⟩
  · intro h0
    have h1 : (w.1 : ℝ) = 0 := congrArg Complex.re h0
    have h2 : (w.2 : ℝ) = 0 := congrArg Complex.im h0
    rcases hw with hw | hw
    · exact hw (by exact_mod_cast h1)
    · exact hw (by exact_mod_cast h2)
  · intro x hx y hy
    obtain ⟨BX, hBX, hxm⟩ := hs x hx
    obtain ⟨BY, hBY, hym⟩ := ht y hy
    have := hall BX hBX BY hBY
    exact le_trans (dotI_sound w hxm).2 (le_trans (by exact_mod_cast this) (dotI_sound w hym).1)

lemma separated_sound {U V : List Box} {s t : Set ℂ} {cu cv : ℚ × ℚ}
    (h : separated U V cu cv = true)
    (hs : ∀ x ∈ s, ∃ B ∈ U, Box.Mem x B) (ht : ∀ y ∈ t, ∃ B ∈ V, Box.Mem y B) :
    Disjoint (interior (convexHull ℝ s)) (interior (convexHull ℝ t)) := by
  unfold separated at h
  simp only [List.any_eq_true, Bool.or_eq_true] at h
  obtain ⟨w, -, hw | hw⟩ := h
  · exact separatedBy_sound hw hs ht
  · exact (separatedBy_sound hw ht hs).symm

lemma allPairs_sound {α : Type} {f : α → α → Bool} {l : List α} (h : allPairs f l = true) :
    l.Pairwise fun a b => f a b = true := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    simp only [allPairs, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (ih h.2)

/-! ## The checker is sound -/

lemma pieceBoxes_cover (c : Cert) (p : Piece) :
    ∀ z ∈ Set.range (fun k : Fin c.nsi =>
        regVertex c.nsi ⟨(p.x.toRat : ℝ), (p.y.toRat : ℝ)⟩ 1 (p.angle.toRat : ℝ) k),
      ∃ B ∈ c.pieceBoxes p, Box.Mem z B := by
  rintro z ⟨k, rfl⟩
  exact ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr k.2, rfl⟩, pieceVertex_sound _ _ _ _ _⟩

lemma containerBoxes_cover (c : Cert) (h : 0 < (sinPiDiv c.nsc).lo) :
    ∀ B ∈ c.containerBoxes, ∃ z ∈ Set.range (fun k : Fin c.nsc => regVertex c.nsc 0 c.radius 0 k),
      Box.Mem z B := by
  intro B hB
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hB
  exact ⟨_, ⟨⟨k, List.mem_range.mp hk⟩, rfl⟩, containerVertex_sound _ (radius_sound c h) _⟩

/-- **Soundness of the exact checker.** If `Cert.check` accepts a certificate, then the
exact regular polygons it describes form a packing: there are `n` inner polygons, each lies
inside the container, and no two of them overlap (their interiors are disjoint). -/
theorem Cert.check_sound (c : Cert) (h : c.check = true) : c.Valid := by
  unfold Cert.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hnsi, hnsc⟩, hlen⟩, hside⟩, hsin⟩, hin⟩, hpairs⟩ := h
  refine ⟨hnsi, hnsc, hlen, by exact_mod_cast hside, ?_, ?_⟩
  · intro p hp
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro z hz
    obtain ⟨B, hB, hzB⟩ := pieceBoxes_cover c p z hz
    exact inHull_sound (containerBoxes_cover c hsin) (hin p hp B hB) hzB
  · have hpw := allPairs_sound hpairs
    have key : ∀ i j : Fin c.pieces.length, i < j →
        Disjoint (interior ((c.pieces.get i).toSet c.nsi))
          (interior ((c.pieces.get j).toSet c.nsi)) := by
      intro i j hij
      have := List.pairwise_iff_get.mp hpw i j hij
      exact separated_sound this (pieceBoxes_cover c _) (pieceBoxes_cover c _)
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact key i j hlt
    · exact (key j i hlt).symm

/-! ## Everything the program outputs is valid -/

/-- Every certificate produced by `certify` passes the exact checker. -/
theorem certify_check {P : Problem} {S : Float} {x : FloatArray} {c : Cert}
    (h : certify P S x = some c) : c.check = true := by
  unfold certify at h
  obtain ⟨f, -, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · split at hf
    · cases hf; assumption
    · cases hf
  · cases hf

/-- Every certificate produced by `certify` describes a genuine packing. -/
theorem certify_valid {P : Problem} {S : Float} {x : FloatArray} {c : Cert}
    (h : certify P S x = some c) : c.Valid :=
  Cert.check_sound c (certify_check h)

/-- **The program's output is correct.** The certificate written by `polygon_packer` is the
one returned by `certifyBest`; whatever floating point results the search produced, any
certificate returned by `certifyBest` describes a genuine packing of `P.n` regular
`P.nsi`-gons in the regular `P.nsc`-gon, with no overlaps. -/
theorem certifyBest_valid {P : Problem} {results : List (Nat × Float × FloatArray)}
    {seed : Nat} {c : Cert} (h : certifyBest P results = some (seed, c)) :
    c.Valid ∧ c.n = P.n ∧ c.nsi = P.nsi ∧ c.nsc = P.nsc := by
  unfold certifyBest at h
  obtain ⟨⟨s, S, x⟩, -, hf⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hf
  obtain ⟨c', hc', -, rfl⟩ := hf
  refine ⟨certify_valid hc', ?_⟩
  unfold certify at hc'
  obtain ⟨f, -, hf⟩ := List.exists_of_findSome?_eq_some hc'
  split at hf
  · rename_i c'' hcand
    split at hf
    · cases hf
      unfold candidate at hcand
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at hcand
      obtain ⟨side, -, pieces, -, rfl⟩ := hcand
      exact ⟨rfl, rfl, rfl⟩
    · cases hf
  · cases hf

/-- **The side length is correct.** For any certificate the program outputs, the side length
of the container is exactly `side_length` times the side length of the inner polygons. -/
theorem certifyBest_side_length {P : Problem} {results : List (Nat × Float × FloatArray)}
    {seed : Nat} {c : Cert} (h : certifyBest P results = some (seed, c)) (p : Piece) (k l : ℕ) :
    dist (regVertex c.nsc 0 c.radius 0 k) (regVertex c.nsc 0 c.radius 0 (k + 1)) =
      (c.side.toRat : ℝ) *
        dist (regVertex c.nsi ⟨(p.x.toRat : ℝ), (p.y.toRat : ℝ)⟩ 1 (p.angle.toRat : ℝ) l)
          (regVertex c.nsi ⟨(p.x.toRat : ℝ), (p.y.toRat : ℝ)⟩ 1 (p.angle.toRat : ℝ) (l + 1)) :=
  c.container_side_length (certifyBest_valid h).1 p k l

end PolygonPacker
