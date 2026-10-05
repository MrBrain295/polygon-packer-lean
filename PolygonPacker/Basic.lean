module

/-!
# Basic utilities for the polygon packer

* a small deterministic pseudo-random number generator (SplitMix64),
* dense vector operations on `FloatArray`,
* parsing of decimal / scientific floating point literals (for the command line),
* exact round-trip printing of `Float`s (for the certificate).
-/

public section

namespace PolygonPacker

/-- `π` as a double. -/
def pi : Float := 3.141592653589793

/-! ## Random numbers -/

/-- SplitMix64 pseudo-random number generator. -/
structure Rng where
  state : UInt64
deriving Inhabited

namespace Rng

/-- Generator determined by an integer seed (the attempt number). -/
def ofSeed (seed : Nat) : Rng :=
  ⟨UInt64.ofNat seed * 0x9E3779B97F4A7C15 + 0x2545F4914F6CDD1D⟩

/-- Next 64 random bits. -/
def nextU64 (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := s
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Uniform sample in `[0, 1)` (53 random bits). -/
def uniform01 (r : Rng) : Float × Rng :=
  let (z, r) := r.nextU64
  ((z >>> 11).toFloat / 9007199254740992.0, r)

/-- Uniform sample in `[lo, hi)`. -/
def uniform (r : Rng) (lo hi : Float) : Float × Rng :=
  let (u, r) := r.uniform01
  (lo + (hi - lo) * u, r)

end Rng

/-! ## Vector operations -/

namespace Vec

/-- The zero vector of dimension `n`. -/
def zeros (n : Nat) : FloatArray := ⟨Array.replicate n 0.0⟩

/-- Dot product. -/
def dot (a b : FloatArray) : Float := Id.run do
  let mut s := 0.0
  for i in [0:a.size] do
    s := s + a[i]! * b[i]!
  return s

/-- `y + α • x`. -/
def axpy (α : Float) (x y : FloatArray) : FloatArray := Id.run do
  let mut r := y
  for i in [0:y.size] do
    r := r.set! i (y[i]! + α * x[i]!)
  return r

/-- `α • x`. -/
def scale (α : Float) (x : FloatArray) : FloatArray := Id.run do
  let mut r := x
  for i in [0:x.size] do
    r := r.set! i (α * x[i]!)
  return r

/-- `a - b`. -/
def sub (a b : FloatArray) : FloatArray := axpy (-1.0) b a

/-- Maximum absolute entry (sup norm). -/
def maxAbs (a : FloatArray) : Float := Id.run do
  let mut m := 0.0
  for i in [0:a.size] do
    let v := a[i]!.abs
    if v > m then m := v
  return m

/-- Euclidean norm. -/
def norm (a : FloatArray) : Float := (dot a a).sqrt

end Vec

/-! ## Parsing floats -/

private def digitsToNat (cs : List Char) : Nat :=
  cs.foldl (fun acc c => 10 * acc + (c.toNat - '0'.toNat)) 0

/-- Parse an optional exponent suffix such as `e-8` (the empty suffix means `0`). -/
private def parseExponent? : List Char → Option Int
  | [] => some 0
  | c :: t =>
    if c == 'e' || c == 'E' then
      let (eneg, t) : Bool × List Char := match t with
        | '-' :: t => (true, t)
        | '+' :: t => (false, t)
        | t => (false, t)
      if t.isEmpty || !t.all Char.isDigit then none
      else
        let e : Int := Int.ofNat (digitsToNat t)
        some (if eneg then -e else e)
    else none

/-- Parse a literal such as `0.0001`, `1e-8`, `-2.5E+3` or `7`. -/
def parseFloat? (str : String) : Option Float := do
  let cs := str.trimAscii.toString.toList
  let (neg, cs) := match cs with
    | '-' :: t => (true, t)
    | '+' :: t => (false, t)
    | t => (false, t)
  let intPart := cs.takeWhile Char.isDigit
  let cs := cs.dropWhile Char.isDigit
  let (fracPart, cs) := match cs with
    | '.' :: t => (t.takeWhile Char.isDigit, t.dropWhile Char.isDigit)
    | t => ([], t)
  if intPart.isEmpty && fracPart.isEmpty then none
  let expo ← parseExponent? cs
  let mant := digitsToNat (intPart ++ fracPart)
  let e : Int := expo - fracPart.length
  let v := if e < 0 then Float.ofScientific mant true e.natAbs
    else Float.ofScientific mant false e.natAbs
  return if neg then -v else v

/-! ## Printing floats exactly -/

private def numDigits (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- Correctly rounded (half-up) integer quotient. -/
private def roundDiv (a b : Nat) : Nat := (2 * a + b) / (2 * b)

/-- Render a finite double with 17 significant digits in scientific notation.
Seventeen significant digits are always enough for the decimal string to parse back
(e.g. with Python's `float`) to exactly the same double.  Non-finite values become
`null` (they never occur in a valid certificate). -/
def floatToJson (x : Float) : String := Id.run do
  if x.isNaN || x.isInf then return "null"
  let bits := x.toBits
  let neg := (bits >>> 63) == 1
  let ebits := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if ebits == 0 && frac == 0 then return (if neg then "-0.0" else "0.0")
  -- value = m * 2^e
  let (m, e) : Nat × Int :=
    if ebits == 0 then (frac, -1074) else (frac + 2 ^ 52, (ebits : Int) - 1075)
  let (num, den) : Nat × Nat :=
    if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ e.natAbs)
  -- scaled d := round(num/den * 10^(16 - d))
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
  let ds := Nat.toDigits 10 s
  let head := ds.head!
  let tail := String.ofList ds.tail!
  let sign := if neg then "-" else ""
  return s!"{sign}{head}.{tail}e{d}"

end PolygonPacker
