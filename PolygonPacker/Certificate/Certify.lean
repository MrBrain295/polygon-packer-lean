module

public import PolygonPacker.Certificate.Check
public import PolygonPacker.Search.Penalty

/-!
# Turning a floating point packing into a checked certificate

The search works with floating point numbers and accepts configurations whose penalty is
merely *small*, so its raw output may contain tiny overlaps.  `certify` converts the result
into exact decimals, spreads the configuration out by a tiny factor if necessary (moving the
centres apart and enlarging the container by the same factor), and only returns a
certificate once the exact checker `Cert.check` accepts it.  Hence every certificate returned
by `certify` (and therefore every certificate written by the program) passes `Cert.check`,
and so describes a genuine packing (see `PolygonPackerProofs/Soundness.lean`).
-/

@[expose] public section

namespace PolygonPacker

/-- The double `x` rounded to a decimal with 17 significant digits (`none` for NaN and
infinities). The decimal is printed with the same digits as `floatToJson x`. -/
def floatToDecimal (x : Float) : Option Decimal := Id.run do
  if x.isNaN || x.isInf then return none
  let bits := x.toBits
  let neg := (bits >>> 63) == 1
  let ebits := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if ebits == 0 && frac == 0 then return some ⟨0, 0⟩
  let (m, e) : Nat × Int :=
    if ebits == 0 then (frac, -1074) else (frac + 2 ^ 52, (ebits : Int) - 1075)
  let (num, den) : Nat × Nat :=
    if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ e.natAbs)
  let numDigits (n : Nat) : Nat := (Nat.toDigits 10 n).length
  let roundDiv (a b : Nat) : Nat := (2 * a + b) / (2 * b)
  let scaled (d : Int) : Nat :=
    let k := 16 - d
    if k ≥ 0 then roundDiv (num * 10 ^ k.toNat) den
    else roundDiv num (den * 10 ^ k.natAbs)
  let mut d : Int := (numDigits num : Int) - (numDigits den : Int)
  let mut s := scaled d
  for _ in [0:4] do
    if s ≥ 10 ^ 17 then
      d := d + 1
      s := scaled d
    else if s < 10 ^ 16 then
      d := d - 1
      s := scaled d
  let mant : Int := if neg then -(s : Int) else s
  return some ⟨mant, d - 16⟩

/-- The angle `a` reduced to `[-π, π]` (approximately). -/
def normAngle (a : Float) : Float := a - 2.0 * pi * (a / (2.0 * pi)).round

/-- Candidate certificate: centres and container scaled by `f`. -/
def candidate (P : Problem) (S : Float) (x : FloatArray) (f : Float) : Option Cert := do
  let side ← floatToDecimal (f * sideLength P S)
  let pieces ← (List.range P.n).mapM fun i => do
    let px ← floatToDecimal (f * x[3 * i]!)
    let py ← floatToDecimal (f * x[3 * i + 1]!)
    let pa ← floatToDecimal (normAngle x[3 * i + 2]!)
    pure ({ x := px, y := py, angle := pa } : Piece)
  pure { n := P.n, nsi := P.nsi, nsc := P.nsc, side, pieces }

/-- Scale factors tried, in order. -/
def scaleFactors : List Float :=
  [1.0, 1.0 + 1e-12, 1.0 + 1e-10, 1.0 + 1e-8, 1.0 + 1e-7, 1.0 + 1e-6, 1.0 + 3e-6,
    1.0 + 1e-5, 1.0 + 2e-5, 1.0 + 5e-5, 1.0 + 1e-4, 1.0 + 2e-4, 1.0 + 5e-4, 1.0 + 1e-3,
    1.0 + 2e-3, 1.0 + 5e-3, 1.0 + 1e-2, 1.0 + 2e-2, 1.0 + 5e-2, 1.1, 1.2, 1.5, 2.0]

/-- The first candidate certificate accepted by the exact checker, if any. -/
def certify (P : Problem) (S : Float) (x : FloatArray) : Option Cert :=
  scaleFactors.findSome? fun f =>
    match candidate P S x f with
    | some c => if c.check then some c else none
    | none => none

/-- Pick the best (smallest container) result that can be certified, trying the results in
order of increasing container size. -/
def certifyBest (P : Problem) (results : List (Nat × Float × FloatArray)) :
    Option (Nat × Cert) :=
  let sorted := results.mergeSort fun a b => a.2.1 ≤ b.2.1
  sorted.findSome? fun (seed, S, x) => (certify P S x).map fun c => (seed, c)

/-- A point as a JSON pair. -/
def jsonPointF (x y : Float) : String := s!"[{floatToJson x}, {floatToJson y}]"

/-- The JSON certificate. The fields `side_length` and `polygons` are the exact (checked)
data; the remaining numeric fields are floating point approximations for drawing. -/
def Cert.toJson (c : Cert) (attempts seed : Nat) : String :=
  let toF (d : Decimal) : Float := (parseFloat? d.toString).getD 0.0
  let P := Problem.make c.n c.nsi c.nsc
  let side := toF c.side
  let S := side * (pi / c.nsi.toFloat).sin / (pi / c.nsc.toFloat).sin
  let polys := c.pieces.map fun p =>
    s!"    \{\"x\": {p.x.toString}, \"y\": {p.y.toString}, \"angle\": {p.angle.toString}}"
  let polyVerts := c.pieces.map fun p =>
    let (px, py, a) := (toF p.x, toF p.y, toF p.angle)
    let items := (List.range c.nsi).map fun k =>
      let ux := P.unitVerts[2 * k]!
      let uy := P.unitVerts[2 * k + 1]!
      jsonPointF (px + (ux * a.cos - uy * a.sin)) (py + (ux * a.sin + uy * a.cos))
    "    [" ++ ", ".intercalate items ++ "]"
  let cont := (List.range c.nsc).map fun k =>
    jsonPointF (S * P.contVerts[2 * k]!) (S * P.contVerts[2 * k + 1]!)
  "{\n" ++
  "  \"format\": \"polygon-packing-certificate\",\n" ++
  "  \"version\": 2,\n" ++
  s!"  \"inner_polygons\": {c.n},\n" ++
  s!"  \"inner_sides\": {c.nsi},\n" ++
  s!"  \"container_sides\": {c.nsc},\n" ++
  "  \"inner_circumradius\": 1.0,\n" ++
  s!"  \"side_length\": {c.side.toString},\n" ++
  s!"  \"container_circumradius\": {floatToJson S},\n" ++
  "  \"verified\": true,\n" ++
  s!"  \"attempts\": {attempts},\n" ++
  s!"  \"best_seed\": {seed},\n" ++
  "  \"polygons\": [\n" ++ ",\n".intercalate polys ++ "\n  ],\n" ++
  s!"  \"container_vertices\": [{", ".intercalate cont}],\n" ++
  "  \"polygon_vertices\": [\n" ++ ",\n".intercalate polyVerts ++ "\n  ]\n" ++
  "}\n"

end PolygonPacker
