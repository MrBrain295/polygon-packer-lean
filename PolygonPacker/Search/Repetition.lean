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
  /-- relative container shrink applied after each feasible minimisation -/
  shrinkStep : Float := 0.01
  /-- fresh starts to try when local and basin-hopping minimisation fail -/
  restarts : Nat := 0
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

def scalePositions (factor : Float) (x : FloatArray) : FloatArray := Id.run do
  let mut y := x
  for i in [0:x.size / 3] do
    y := y.set! (3 * i) (factor * x[3 * i]!)
    y := y.set! (3 * i + 1) (factor * x[3 * i + 1]!)
  return y

/-- One attempt with the given seed: returns the smallest feasible container
circumradius found and the corresponding configuration. -/
def repetition (P : Problem) (cfg : Settings) (seed : Nat) : Float × FloatArray := Id.run do
  let mut rng := Rng.ofSeed seed
  let sqrtN := Float.sqrt P.n.toFloat
  let (u, r) := rng.uniform01
  rng := r
  let mut dynS := sqrtN * (2.0 + u * 2.0)
  let (x0, r) := initialState P dynS rng
  rng := r
  let mut x := x0
  let mut best : Option (Float × FloatArray) := none
  let localMin := fun (S : Float) (y : FloatArray) =>
    lbfgs (penaltyGrad P S) y (maxIter := cfg.maxIterations)
  let searchAt := fun (S : Float) (guess : FloatArray) (rng : Rng) =>
    let res := localMin S guess
    if res.fx < cfg.tolerance then
      (some res.x, rng)
    else
      let (bh, rng) := basinhopping (localMin S) guess rng cfg.basinHops
      if bh.fx < cfg.tolerance then
        (some bh.x, rng)
      else
        Id.run do
          let mut rng := rng
          let mut recovered : Option FloatArray := none
          for _ in [0:cfg.restarts] do
            let (restart, r) := initialState P S rng
            rng := r
            let trial := localMin S restart
            if trial.fx < cfg.tolerance then
              recovered := some trial.x
              break
          return (recovered, rng)
  repeat
    let S := dynS
    let multiplier := 1.0 - cfg.shrinkStep
    let (feasible, r) := searchAt S x rng
    rng := r
    match feasible with
    | some feasible =>
      best := some (S, feasible)
      x := scalePositions multiplier feasible
      dynS := S * multiplier
    | none =>
      if cfg.finalStep > 0.0 then
        match best with
        | some (bestS, bestX) =>
          let mut hiS := bestS
          let mut hiX := bestX
          let mut loS := S
          while (hiS - loS) / (max hiS 1.0) > cfg.finalStep do
            let midS := (hiS + loS) / 2.0
            let midGuess := scalePositions (midS / hiS) hiX
            let (midFeasible, r) := searchAt midS midGuess rng
            rng := r
            match midFeasible with
            | some midX =>
              hiS := midS
              hiX := midX
            | none =>
              loS := midS
          best := some (hiS, hiX)
        | none => pure ()
      break
  return best.getD (dynS, x0)

end PolygonPacker
