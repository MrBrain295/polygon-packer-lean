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
  if u < 0.34 then
    for k in [0:3 * n] do
      let (v, r) := rng.uniform (-S / 2.0) (S / 2.0)
      rng := r
      x := x.set! k v
  else if u < 0.67 then
    let side := (Float.sqrt n.toFloat).ceil.toUInt64.toNat
    let grid := linspace (-S / 2.0 * 0.9) (S / 2.0 * 0.9) side
    for i in [0:n] do
      x := x.set! (3 * i) grid[i % side]!
      x := x.set! (3 * i + 1) grid[i / side]!
    for i in [0:n] do
      let (v, r) := rng.uniform 0.0 (2.0 * pi)
      rng := r
      x := x.set! (3 * i + 2) v
  else
    let ga := pi * (3.0 - Float.sqrt 5.0)
    let radius := S / 2.0 * 0.88
    for i in [0:n] do
      let t := ga * i.toFloat
      let r := radius * Float.sqrt ((i.toFloat + 0.5) / n.toFloat)
      x := x.set! (3 * i) (r * t.cos)
      x := x.set! (3 * i + 1) (r * t.sin)
    for i in [0:n] do
      let (v, r) := rng.uniform 0.0 (2.0 * pi)
      rng := r
      x := x.set! (3 * i + 2) v
  return (x, rng)

def jitterState (P : Problem) (S : Float) (x : FloatArray) (rng : Rng)
    (posFrac : Float := 0.05) (angleSpan : Float := 0.4) : FloatArray × Rng := Id.run do
  let mut y := x
  let mut rng := rng
  let posScale := S * posFrac
  for i in [0:P.n] do
    let (dx, r) := rng.uniform (-posScale) posScale
    rng := r
    let (dy, r) := rng.uniform (-posScale) posScale
    rng := r
    let (da, r) := rng.uniform (-angleSpan) angleSpan
    rng := r
    y := y.set! (3 * i) (x[3 * i]! + dx)
    y := y.set! (3 * i + 1) (x[3 * i + 1]! + dy)
    y := y.set! (3 * i + 2) (x[3 * i + 2]! + da)
  return (y, rng)

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
  let largeProblem := P.n >= 25 || (P.n == 20 && P.nsc == 6)
  let square25 := P.n == 25 && P.nsi == 4 && P.nsc == 4
  let iterationBudget := if square25 then max cfg.maxIterations 80
    else if largeProblem then max cfg.maxIterations 55 else cfg.maxIterations
  let shrink := if largeProblem then max cfg.shrinkStep 0.04 else cfg.shrinkStep
  let decagonProblem := P.n == 20 && P.nsi == 5 && P.nsc == 10
  let iterationBudget := if decagonProblem then max iterationBudget 400 else iterationBudget
  let shrink := if decagonProblem then max shrink 0.04 else shrink
  let sqrtN := Float.sqrt P.n.toFloat
  let (u, r) := rng.uniform01
  rng := r
  let mut dynS := sqrtN * (2.0 + u * 2.0)
  let (x0, r) := initialState P dynS rng
  rng := r
  let mut x := x0
  let mut best : Option (Float × FloatArray) := none
  let localMin := fun (S : Float) (y : FloatArray) =>
    lbfgs (penaltyGrad P S) y (maxIter := iterationBudget)
  let polish := fun (S : Float) (y : FloatArray) =>
    let primary := localMin S y
    if !largeProblem || primary.fx < cfg.tolerance then primary
    else
      let fallback := gradientDescent (penaltyGrad P S) primary.x (maxIter := 120)
      if fallback.fx < primary.fx then fallback else primary
  let searchAt := fun (S : Float) (guess : FloatArray) (rng : Rng) =>
    let res := polish S guess
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
          let repairTries := max cfg.restarts 1
          for _ in [0:repairTries] do
            let (restart, r) := jitterState P S guess rng
            rng := r
            let trial := polish S restart
            if trial.fx < cfg.tolerance then
              recovered := some trial.x
              break
          if recovered.isNone then
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
    let multiplier := 1.0 - shrink
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
