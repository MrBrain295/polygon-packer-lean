module

public import PolygonPacker.Search.Penalty
public import PolygonPacker.Search.Optimize

/-!
# One packing attempt

Lean version of `repetition(seed)` from `polygon_packer.py`: start from a random
(or grid) configuration in a large container, and repeatedly shrink the container,
re-minimising the penalty (first with L-BFGS, then, if that fails, with basin hopping),
until no overlap-free configuration is found any more.  The last feasible container
size and configuration are returned.
-/

public section

namespace PolygonPacker

/-- Search parameters. -/
structure Settings where
  /-- a configuration is accepted when its penalty is below this value -/
  tolerance : Float := 1e-8
  /-- the theoretical final shrink step -/
  finalStep : Float := 0.0001
  /-- maximum iterations for each local minimisation -/
  maxIterations : Nat := 15000
  /-- maximum basin-hopping rounds for each failed local minimisation -/
  basinHops : Nat := 50
deriving Inhabited

/-- `n` equally spaced points from `lo` to `hi` inclusive (`numpy.linspace`). -/
def linspace (lo hi : Float) (n : Nat) : Array Float :=
  if n ≤ 1 then Array.replicate n lo
  else (Array.range n).map fun k => lo + (hi - lo) * k.toFloat / (n - 1).toFloat

/-- Random starting configuration for container size `S`. -/
def initialState (P : Problem) (S : Float) (rng : Rng) : FloatArray × Rng := Id.run do
  let n := P.n
  let mut rng := rng
  let (u, r) := rng.uniform01
  rng := r
  let mut x := Vec.zeros (3 * n)
  if u < 0.5 then
    for k in [0:3 * n] do
      let (v, r) := rng.uniform (-S / 2.0) (S / 2.0)
      rng := r
      x := x.set! k v
  else
    let side := (Float.sqrt n.toFloat).ceil.toUInt64.toNat
    let grid := linspace (-S / 2.0 * 0.9) (S / 2.0 * 0.9) side
    for i in [0:n] do
      x := x.set! (3 * i) grid[i % side]!
      x := x.set! (3 * i + 1) grid[i / side]!
    for i in [0:n] do
      let (v, r) := rng.uniform 0.0 (2.0 * pi)
      rng := r
      x := x.set! (3 * i + 2) v
  return (x, rng)

/-- One attempt with the given seed: returns the smallest feasible container
circumradius found and the corresponding configuration. -/
def repetition (P : Problem) (cfg : Settings) (seed : Nat) : Float × FloatArray := Id.run do
  let mut rng := Rng.ofSeed seed
  let sqrtN := Float.sqrt P.n.toFloat
  let (u, r) := rng.uniform01
  rng := r
  let mut dynS := sqrtN * (2.0 + u * 2.0)
  let initialS := dynS
  let lowestS := sqrtN
  let range := initialS - lowestS
  let (x0, r) := initialState P dynS rng
  rng := r
  let mut x := x0
  let mut lastX := x0
  let mut lastS := dynS
  repeat
    let S := dynS
    let f := penaltyGrad P S
    let localMin := fun (y : FloatArray) => lbfgs f y cfg.maxIterations
    let res := localMin x
    let multiplier :=
      1.0 - cfg.finalStep - (dynS - lowestS) * (0.01 - cfg.finalStep) / range
    if res.fx < cfg.tolerance then
      lastX := res.x
      lastS := dynS
      x := Vec.scale multiplier res.x
      dynS := dynS * multiplier
    else
      let (bh, r) := basinhopping localMin x rng cfg.basinHops
      rng := r
      if bh.fx < cfg.tolerance then
        lastX := bh.x
        lastS := dynS
        x := Vec.scale multiplier bh.x
        dynS := dynS * multiplier
      else
        break
  return (lastS, lastX)

end PolygonPacker
