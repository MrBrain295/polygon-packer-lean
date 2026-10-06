module

import PolygonPacker

open PolygonPacker

structure Args where
  name : String
  n : Nat
  nsi : Nat
  nsc : Nat
  milliseconds : Nat
  seed : Nat
  certificate : String
  result : String

def usage : String :=
  "usage: timed_packer NAME N INNER_SIDES CONTAINER_SIDES MILLISECONDS SEED CERTIFICATE RESULT"

def parseNat (label value : String) : Except String Nat :=
  value.toNat?.elim (.error s!"invalid {label} value {value}") .ok

def parseArgs : List String → Except String Args
  | [name, n, nsi, nsc, milliseconds, seed, certificate, result] => do
    let n ← parseNat "n" n
    let nsi ← parseNat "inner sides" nsi
    let nsc ← parseNat "container sides" nsc
    let milliseconds ← parseNat "milliseconds" milliseconds
    let seed ← parseNat "seed" seed
    if n == 0 || nsi < 3 || nsc < 3 || milliseconds == 0 then
      .error "need n > 0, at least 3 sides, and a positive time limit"
    else
      pure { name, n, nsi, nsc, milliseconds, seed, certificate, result }
  | _ => .error usage

def jsonFloat (x : Float) : String := floatToJson x

partial def searchUntil (P : Problem) (cfg : Settings) (seed limit start : Nat)
  (results : List (Nat × Float × FloatArray)) (curve : List (Nat × Nat × Float))
    (best : Option (Nat × Float × FloatArray)) : IO
    (List (Nat × Float × FloatArray) × List (Nat × Nat × Float) × Option (Nat × Float × FloatArray) × Nat) := do
  let now ← IO.monoMsNow
  let elapsed := now - start
  if elapsed >= limit then
    return (results, curve, best, elapsed)
  let currentSeed := seed + results.length
  let (side, x) := repetition P cfg currentSeed
  let attemptEnd ← IO.monoMsNow
  let elapsed := attemptEnd - start
  let results := (currentSeed, side, x) :: results
  let (best, curve) := match best with
    | some (_, bestSide, _) =>
      if side < bestSide then
        (some (currentSeed, side, x), (currentSeed, elapsed, side) :: curve)
      else
        (best, curve)
    | none =>
      (some (currentSeed, side, x), [(currentSeed, elapsed, side)])
  if elapsed >= limit then
    return (results, curve, best, elapsed)
  searchUntil P cfg seed limit start results curve best

def curveJson (curve : List (Nat × Nat × Float)) : String :=
  let entries := curve.reverse.map fun (seed, ms, side) =>
    "{\"seed\": " ++ toString seed ++ ", \"milliseconds\": " ++ toString ms ++
      ", \"objective\": " ++ jsonFloat side ++ "}"
  "[" ++ ", ".intercalate entries ++ "]"

public def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error e => IO.eprintln e; return 1
  | .ok args =>
    let P := Problem.make args.n args.nsi args.nsc
    let cfg : Settings := if args.n >= 25 || args.name == "tri_hexagon_20" then
      { maxIterations := 10, basinHops := 0, shrinkStep := 0.02, restarts := 1 }
    else if args.name == "hex_square_10" then
      { maxIterations := 400, basinHops := 10, shrinkStep := 0.02, restarts := 1 }
    else if args.name == "pent_decagon_20" then
      { maxIterations := 200, basinHops := 5, shrinkStep := 0.02, restarts := 1 }
    else
      { maxIterations := 100, basinHops := 2, shrinkStep := 0.02, restarts := 1 }
    let start ← IO.monoMsNow
    let (results, curve, _, elapsed) ← searchUntil P cfg args.seed args.milliseconds start [] [] none
    let resultList := results.reverse
    let certified := certifyBest P resultList
    IO.FS.createDirAll "certificates"
    IO.FS.createDirAll "benchmarks/certificates"
    IO.FS.createDirAll "benchmarks/results"
    let (valid, bestSeed, bestSide, certificateJson) := match certified with
      | some (bestSeed, cert) =>
        ("true", toString bestSeed, cert.side.toString, cert.toJson resultList.length bestSeed)
      | none =>
        ("false", "null", "null", "null")
    if let some (bestSeed, cert) := certified then
      IO.FS.writeFile args.certificate (cert.toJson resultList.length bestSeed)
    let timeToBest : Option Nat := match certified with
      | some (bestSeed, _) =>
        curve.findSome? fun (seed, ms, _) => if seed == bestSeed then some ms else none
      | none => none
    let json :=
      "{\n" ++
      s!"  \"problem\": \"{args.name}\",\n" ++
      s!"  \"seed\": {args.seed},\n" ++
      s!"  \"time_limit_ms\": {args.milliseconds},\n" ++
      s!"  \"elapsed_ms\": {elapsed},\n" ++
      s!"  \"attempts\": {resultList.length},\n" ++
      s!"  \"best_objective\": {bestSide},\n" ++
      s!"  \"best_seed\": {bestSeed},\n" ++
      s!"  \"time_to_best_ms\": {timeToBest.map toString |>.getD "null"},\n" ++
      s!"  \"valid\": {valid},\n" ++
      s!"  \"curve\": {curveJson curve},\n" ++
      s!"  \"certificate\": {certificateJson}\n" ++
      "}\n"
    IO.FS.writeFile args.result json
    IO.println s!"{args.name} seed {args.seed}: {resultList.length} attempts, valid={valid}"
    return 0
