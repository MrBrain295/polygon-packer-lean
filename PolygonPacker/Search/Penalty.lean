module

public import PolygonPacker.Basic

/-!
# The packing penalty and its gradient

This is the Lean version of `bh_function` from `polygon_packer.py`.

A state is a vector `values` of length `3 * N`: polygon `i` has centre
`(values[3i], values[3i+1])` and rotation `values[3i+2]`.  Inner polygons are regular
`nsi`-gons of circumradius `1`, the container is a regular `nsc`-gon of circumradius `S`
(both with a vertex on the positive `x`-axis before rotation).

The penalty is
* for every vertex of every inner polygon and every edge of the container, the squared
  distance by which the vertex pokes out through that edge, plus
* for every pair of inner polygons that the separating axis test says overlap, the
  square of the minimal overlap over all candidate axes (the edge normals of both
  polygons).

Unlike the Python program (which lets SciPy approximate the gradient by finite
differences) we also compute the exact gradient of this piecewise-smooth function.
-/

public section

namespace PolygonPacker

/-- The fixed data of a packing problem. -/
structure Problem where
  /-- number of inner polygons -/
  n : Nat
  /-- number of sides of each inner polygon -/
  nsi : Nat
  /-- number of sides of the container -/
  nsc : Nat
  /-- vertices of the unit inner polygon, interleaved `x, y` -/
  unitVerts : FloatArray
  /-- unit edge normals of the unit inner polygon, interleaved `x, y` -/
  unitVecs : FloatArray
  /-- vertices of the unit container -/
  contVerts : FloatArray
  /-- unit edge normals of the unit container -/
  contVecs : FloatArray
  /-- apothem of the unit container, `cos (π / nsc)` -/
  apothem : Float
deriving Inhabited

/-- Interleaved coordinates of `(cos (2πk/m + φ), sin (2πk/m + φ))` for `k < m`. -/
def circlePoints (m : Nat) (φ : Float) : FloatArray := Id.run do
  let mut r := FloatArray.emptyWithCapacity (2 * m)
  for k in [0:m] do
    let t := 2.0 * pi * k.toFloat / m.toFloat + φ
    r := (r.push t.cos).push t.sin
  return r

/-- Set up the problem data (corresponds to the module level arrays of the Python code). -/
def Problem.make (n nsi nsc : Nat) : Problem where
  n := n
  nsi := nsi
  nsc := nsc
  unitVerts := circlePoints nsi 0.0
  unitVecs := circlePoints nsi (pi / nsi.toFloat)
  contVerts := circlePoints nsc 0.0
  contVecs := circlePoints nsc (pi / nsc.toFloat)
  apothem := (pi / nsc.toFloat).cos

/-- Vertices (interleaved, polygon-major) of all inner polygons for state `x`. -/
def Problem.vertices (P : Problem) (x : FloatArray) : FloatArray := Id.run do
  let mut verts := FloatArray.emptyWithCapacity (2 * P.n * P.nsi)
  for i in [0:P.n] do
    let px := x[3 * i]!
    let py := x[3 * i + 1]!
    let a := x[3 * i + 2]!
    let c := a.cos
    let s := a.sin
    for k in [0:P.nsi] do
      let ux := P.unitVerts[2 * k]!
      let uy := P.unitVerts[2 * k + 1]!
      verts := (verts.push (px + (ux * c - uy * s))).push (py + (ux * s + uy * c))
  return verts

/-- Rotated edge normals (interleaved, polygon-major) of all inner polygons. -/
def Problem.axes (P : Problem) (x : FloatArray) : FloatArray := Id.run do
  let mut axes := FloatArray.emptyWithCapacity (2 * P.n * P.nsi)
  for i in [0:P.n] do
    let a := x[3 * i + 2]!
    let c := a.cos
    let s := a.sin
    for k in [0:P.nsi] do
      let wx := P.unitVecs[2 * k]!
      let wy := P.unitVecs[2 * k + 1]!
      axes := (axes.push (wx * c - wy * s)).push (wx * s + wy * c)
  return axes

private def addAt (g : FloatArray) (i : Nat) (v : Float) : FloatArray :=
  g.set! i (g[i]! + v)

/-- Add `coef * ∇ (P · A)` to `g`, where `P` is vertex `v` of polygon `q` and `A` is
axis `k` of polygon `r`.  With `c_q` the centre of `q`, `∂P/∂c_q = id`,
`∂P/∂a_q = perp (P - c_q)` and `∂A/∂a_r = perp A`, where `perp (u, w) = (-w, u)`. -/
private def addDotGrad (m : Nat) (x verts axes g : FloatArray)
    (q v r k : Nat) (coef : Float) : FloatArray :=
  let pxv := verts[2 * (q * m + v)]!
  let pyv := verts[2 * (q * m + v) + 1]!
  let ax := axes[2 * (r * m + k)]!
  let ay := axes[2 * (r * m + k) + 1]!
  let cx := x[3 * q]!
  let cy := x[3 * q + 1]!
  let g := addAt g (3 * q) (coef * ax)
  let g := addAt g (3 * q + 1) (coef * ay)
  let g := addAt g (3 * q + 2) (coef * (-(pyv - cy) * ax + (pxv - cx) * ay))
  addAt g (3 * r + 2) (coef * (-pxv * ay + pyv * ax))

/-- Projection of the vertices of polygon `i` onto the axis `(ax, ay)`:
`(min, argmin, max, argmax)` (first index wins ties, as in the Python loop). -/
private def project (m : Nat) (verts : FloatArray) (i : Nat) (ax ay : Float) :
    Float × Nat × Float × Nat := Id.run do
  let mut mn := 1.0e20
  let mut amn := 0
  let mut mx := -1.0e20
  let mut amx := 0
  for v in [0:m] do
    let d := verts[2 * (i * m + v)]! * ax + verts[2 * (i * m + v) + 1]! * ay
    if d < mn then
      mn := d
      amn := v
    if d > mx then
      mx := d
      amx := v
  return (mn, amn, mx, amx)

/-- Data of the active (minimal) overlap of a colliding pair:
the axis `(owner, index)` and the two vertices `(owner, index)` defining the overlap. -/
private structure Active where
  axOwner : Nat := 0
  axIdx : Nat := 0
  hiOwner : Nat := 0
  hiVert : Nat := 0
  loOwner : Nat := 0
  loVert : Nat := 0

/-- The penalty (`bh_function`) together with its gradient. -/
def penaltyGrad (P : Problem) (S : Float) (x : FloatArray) : Float × FloatArray := Id.run do
  let n := P.n
  let m := P.nsi
  let verts := P.vertices x
  let axes := P.axes x
  let mut pen := 0.0
  let mut g := Vec.zeros (3 * n)
  -- vertices poking out of the container
  let lim := P.apothem * S
  for i in [0:n] do
    let px := x[3 * i]!
    let py := x[3 * i + 1]!
    for v in [0:m] do
      let vx := verts[2 * (i * m + v)]!
      let vy := verts[2 * (i * m + v) + 1]!
      for e in [0:P.nsc] do
        let nx := P.contVecs[2 * e]!
        let ny := P.contVecs[2 * e + 1]!
        let dist := vx * nx + vy * ny
        if dist > lim then
          let diff := dist - lim
          pen := pen + diff * diff
          let t := 2.0 * diff
          g := addAt g (3 * i) (t * nx)
          g := addAt g (3 * i + 1) (t * ny)
          g := addAt g (3 * i + 2) (t * (-(vy - py) * nx + (vx - px) * ny))
  -- pairwise overlaps (separating axis test)
  for i in [0:n] do
    for j in [i+1:n] do
      let mut collision := true
      let mut minOv := 1.0e20
      let mut act : Active := {}
      for ax in [0:2 * m] do
        let (own, idx) := if ax < m then (i, ax) else (j, ax - m)
        let axx := axes[2 * (own * m + idx)]!
        let axy := axes[2 * (own * m + idx) + 1]!
        let (min1, amin1, max1, amax1) := project m verts i axx axy
        let (min2, amin2, max2, amax2) := project m verts j axx axy
        let (hiVal, hiOwn, hiV) := if max1 ≤ max2 then (max1, i, amax1) else (max2, j, amax2)
        let (loVal, loOwn, loV) := if min1 ≥ min2 then (min1, i, amin1) else (min2, j, amin2)
        let ov := hiVal - loVal
        if ov ≤ 0.0 then
          collision := false
          break
        if ov < minOv then
          minOv := ov
          act := { axOwner := own, axIdx := idx, hiOwner := hiOwn, hiVert := hiV,
                   loOwner := loOwn, loVert := loV }
      if collision then
        pen := pen + minOv * minOv
        let t := 2.0 * minOv
        g := addDotGrad m x verts axes g act.hiOwner act.hiVert act.axOwner act.axIdx t
        g := addDotGrad m x verts axes g act.loOwner act.loVert act.axOwner act.axIdx (-t)
  return (pen, g)

/-- The penalty alone. -/
def penalty (P : Problem) (S : Float) (x : FloatArray) : Float := (penaltyGrad P S x).1

/-- Side length of the container (floating point) when the inner polygons have side
length one.  The search measures the container by its circumradius `S` (the inner
polygons have circumradius `1`). -/
def sideLength (P : Problem) (S : Float) : Float :=
  S * (pi / P.nsc.toFloat).sin / (pi / P.nsi.toFloat).sin

end PolygonPacker
