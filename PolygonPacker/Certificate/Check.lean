module

/-!
# Exact checking of packing certificates

Everything in this file is computed with exact rational arithmetic (no floating point).

A certificate (`Cert`) lists the problem sizes, the container side length (measured in
units of the inner polygons' side length), and for every inner polygon the centre and
rotation angle (inner polygons have circumradius `1`).  All of these numbers are finite
decimals (`Decimal`), so the certificate printed to JSON contains exactly these values.

`Cert.check` decides, using rigorous rational interval arithmetic for `π`, `sin` and `cos`,
that the polygons described by the certificate lie inside the container and that no two of
them overlap.  The meaning of `Cert.check c = true` is proved in
`PolygonPackerProofs/Soundness.lean`: the real (exact, irrational) regular polygons described
by `c` form a packing with pairwise disjoint interiors inside the container.
-/

@[expose] public section

namespace PolygonPacker

/-! ## Decimals -/

/-- The number `mant * 10 ^ exp`. -/
structure Decimal where
  mant : Int
  exp : Int
deriving Inhabited, Repr, BEq

/-- The exact rational value of a decimal. -/
def Decimal.toRat (d : Decimal) : Rat :=
  if 0 ≤ d.exp then (d.mant : Rat) * ((10 : Rat) ^ d.exp.toNat)
  else (d.mant : Rat) / ((10 : Rat) ^ d.exp.natAbs)

/-- Exact decimal notation of `d`, e.g. `6.1052372273055502e0` (valid JSON, and parsed
exactly by Python's `fractions.Fraction`). -/
def Decimal.toString (d : Decimal) : String :=
  if d.mant == 0 then "0.0"
  else
    let ds := Nat.toDigits 10 d.mant.natAbs
    let sign := if d.mant < 0 then "-" else ""
    let tail := String.ofList ds.tail
    let e : Int := d.exp + (ds.length - 1 : Nat)
    s!"{sign}{ds.head!}.{if tail.isEmpty then "0" else tail}e{e}"

/-! ## Rational intervals -/

/-- Absolute value of a rational number. -/
def qabs (q : Rat) : Rat := if q < 0 then -q else q

/-- A closed interval `[lo, hi]` with rational end points. -/
structure Ival where
  lo : Rat
  hi : Rat
deriving Inhabited, Repr

namespace Ival

/-- The point interval `[q, q]`. -/
def ofRat (q : Rat) : Ival := ⟨q, q⟩

/-- Interval sum. -/
def add (a b : Ival) : Ival := ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Interval difference. -/
def sub (a b : Ival) : Ival := ⟨a.lo - b.hi, a.hi - b.lo⟩

/-- Interval product. -/
def mul (a b : Ival) : Ival :=
  let p₁ := a.lo * b.lo
  let p₂ := a.lo * b.hi
  let p₃ := a.hi * b.lo
  let p₄ := a.hi * b.hi
  ⟨min (min p₁ p₂) (min p₃ p₄), max (max p₁ p₂) (max p₃ p₄)⟩

/-- Interval reciprocal (meaningful when `0 < a.lo`). -/
def inv (a : Ival) : Ival := ⟨1 / a.hi, 1 / a.lo⟩

/-- Number of fractional bits kept when rounding interval end points. -/
def prec : Nat := 120

/-- Round the end points outwards to multiples of `2 ^ (-prec)` (keeps numbers small). -/
def round (a : Ival) : Ival :=
  let s : Rat := (2 : Rat) ^ prec
  ⟨((a.lo * s).floor : Rat) / s, (-((-(a.hi * s)).floor) : Rat) / s⟩

end Ival

/-- An axis-parallel box in the plane: an enclosure of a point. -/
structure Box where
  re : Ival
  im : Ival
deriving Inhabited, Repr

/-! ## Enclosures of `π`, `cos` and `sin` -/

/-- An interval containing `π`. -/
def piIval : Ival :=
  ⟨314159265358979323846 / 100000000000000000000, 314159265358979323847 / 100000000000000000000⟩

/-- Factorial. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `j`-th term of the cosine Taylor series (`0` for odd `j`). -/
def cosTerm (r : Rat) (j : Nat) : Rat :=
  if j % 4 = 0 then r ^ j / (fact j : Rat)
  else if j % 4 = 2 then -(r ^ j / (fact j : Rat)) else 0

/-- `j`-th term of the sine Taylor series (`0` for even `j`). -/
def sinTerm (r : Rat) (j : Nat) : Rat :=
  if j % 4 = 1 then r ^ j / (fact j : Rat)
  else if j % 4 = 3 then -(r ^ j / (fact j : Rat)) else 0

/-- Taylor polynomial of `cos` with the terms of degree `< n`. -/
def cosTaylor (n : Nat) (r : Rat) : Rat := ((List.range n).map (cosTerm r)).sum

/-- Taylor polynomial of `sin` with the terms of degree `< n`. -/
def sinTaylor (n : Nat) (r : Rat) : Rat := ((List.range n).map (sinTerm r)).sum

/-- Number of Taylor terms used. -/
def taylorTerms : Nat := 60

/-- An enclosure of `exp (t * I) = cos t + i sin t` valid for every `t ∈ T`. -/
def expBox (T : Ival) : Box :=
  let r := (T.lo + T.hi) / 2
  let η := (T.hi - T.lo) / 2
  let n := taylorTerms
  if 2 * qabs r ≤ (n + 1 : Nat) then
    let e := qabs r ^ n / (fact n : Rat) * 2 + η
    let c := cosTaylor n r
    let s := sinTaylor n r
    ⟨Ival.round ⟨c - e, c + e⟩, Ival.round ⟨s - e, s + e⟩⟩
  else ⟨⟨-1, 1⟩, ⟨-1, 1⟩⟩

/-! ## Vertices -/

/-- Enclosure of the angle `a + 2πk/m`. -/
def vertexAngle (m : Nat) (a : Rat) (k : Nat) : Ival :=
  (Ival.ofRat a).add (piIval.mul (Ival.ofRat (2 * k / m)))

/-- Enclosure of vertex `k` of the regular `m`-gon with circumradius `1`, centre `(x, y)`
and rotation `a`. -/
def pieceVertex (m : Nat) (x y a : Rat) (k : Nat) : Box :=
  let e := expBox (vertexAngle m a k)
  ⟨(Ival.ofRat x).add e.re, (Ival.ofRat y).add e.im⟩

/-- Enclosure of `sin (π / m)`. -/
def sinPiDiv (m : Nat) : Ival := (expBox (piIval.mul (Ival.ofRat (1 / m)))).im

/-- Enclosure of vertex `k` of the regular `m`-gon with circumradius in `R`, centred at the
origin, with a vertex on the positive `x`-axis. -/
def containerVertex (m : Nat) (R : Ival) (k : Nat) : Box :=
  let e := expBox (vertexAngle m 0 k)
  ⟨(R.mul e.re).round, (R.mul e.im).round⟩

/-! ## Geometric tests -/

/-- Enclosure of `u - v`. -/
def Box.sub (u v : Box) : Box := ⟨u.re.sub v.re, u.im.sub v.im⟩

/-- Enclosure of the cross product `u × v`. -/
def cross (u v : Box) : Ival := (u.re.mul v.im).sub (u.im.mul v.re)

/-- Certifies that the point in `p` lies in the triangle `ABC`. -/
def inTriangle (p A B C : Box) : Bool :=
  let a := A.sub p
  let b := B.sub p
  let c := C.sub p
  let dA := cross b c
  let dB := cross c a
  let dC := cross a b
  decide (0 ≤ dA.lo) && decide (0 ≤ dB.lo) && decide (0 ≤ dC.lo) &&
    decide (0 < ((dA.add dB).add dC).lo)

/-- Certifies that the point in `p` lies in the convex hull of the points in `cv`. -/
def inHull (cv : List Box) (p : Box) : Bool :=
  cv.any fun A => cv.any fun B => cv.any fun C => inTriangle p A B C

/-- Enclosure of `⟨w, p⟩`. -/
def dotI (w : Rat × Rat) (p : Box) : Ival :=
  ((Ival.ofRat w.1).mul p.re).add ((Ival.ofRat w.2).mul p.im)

/-- Certifies `⟨w, p⟩ ≤ ⟨w, q⟩` for all points `p` in `U` and `q` in `V` (with `w ≠ 0`). -/
def separatedBy (U V : List Box) (w : Rat × Rat) : Bool :=
  (decide (w.1 ≠ 0) || decide (w.2 ≠ 0)) &&
    U.all fun p => V.all fun q => decide ((dotI w p).hi ≤ (dotI w q).lo)

/-- Midpoint of a box. -/
def Box.mid (p : Box) : Rat × Rat := ((p.re.lo + p.re.hi) / 2, (p.im.lo + p.im.hi) / 2)

/-- Approximate edge normals of the polygon with vertices in `V` (candidate axes). -/
def edgeNormals (V : List Box) : List (Rat × Rat) :=
  (V.zip (V.drop 1 ++ V.take 1)).map fun (p, q) =>
    let a := p.mid
    let b := q.mid
    (a.2 - b.2, b.1 - a.1)

/-- Certifies that the polygons with vertices in `U` and `V` (centres `cu`, `cv`) have
disjoint interiors, by finding a separating axis. -/
def separated (U V : List Box) (cu cv : Rat × Rat) : Bool :=
  let ws := (cv.1 - cu.1, cv.2 - cu.2) :: (edgeNormals U ++ edgeNormals V)
  ws.any fun w => separatedBy U V w || separatedBy V U w

/-- `f a b` for all pairs of list entries `a` before `b`. -/
def allPairs {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => l.all (f a) && allPairs f l

/-! ## Certificates -/

/-- An inner polygon: centre `(x, y)` and rotation `angle` (circumradius `1`). -/
structure Piece where
  x : Decimal
  y : Decimal
  angle : Decimal
deriving Inhabited, Repr

/-- A packing certificate. The inner polygons are regular `nsi`-gons of circumradius `1`;
the container is the regular `nsc`-gon centred at the origin, with a vertex on the positive
`x`-axis, whose side length is `side` times the side length of an inner polygon. -/
structure Cert where
  n : Nat
  nsi : Nat
  nsc : Nat
  side : Decimal
  pieces : List Piece
deriving Inhabited, Repr

/-- Centre of a piece. -/
def Piece.centre (p : Piece) : Rat × Rat := (p.x.toRat, p.y.toRat)

namespace Cert

/-- Enclosure of the container circumradius `side * sin (π / nsi) / sin (π / nsc)`. -/
def radiusIval (c : Cert) : Ival :=
  (((Ival.ofRat c.side.toRat).mul (sinPiDiv c.nsi)).mul (sinPiDiv c.nsc).inv).round

/-- Enclosures of the container vertices. -/
def containerBoxes (c : Cert) : List Box :=
  (List.range c.nsc).map (containerVertex c.nsc c.radiusIval)

/-- Enclosures of the vertices of a piece. -/
def pieceBoxes (c : Cert) (p : Piece) : List Box :=
  (List.range c.nsi).map (pieceVertex c.nsi p.x.toRat p.y.toRat p.angle.toRat)

/-- The exact certificate checker. -/
def check (c : Cert) : Bool :=
  decide (3 ≤ c.nsi) && decide (3 ≤ c.nsc) && decide (c.pieces.length = c.n) &&
  decide (0 < c.side.toRat) && decide (0 < (sinPiDiv c.nsc).lo) &&
  (c.pieces.all fun p => (c.pieceBoxes p).all (inHull c.containerBoxes)) &&
  allPairs (fun p q => separated (c.pieceBoxes p) (c.pieceBoxes q) p.centre q.centre) c.pieces

end Cert

end PolygonPacker
