module

import PolygonPacker

/-!
# `polygon_packer` executable

Usage (same arguments as `python/polygon_packer.py`, minus the image options):

```
lake exe polygon_packer [n] [nsi] [nsc] [--attempts A] [--tolerance T]
                        [--finalstep F] [--output FILE]
```

The best packing is written as a JSON certificate (by default to
`certificates/{n}_{nsi}_in_{nsc}.json`, or `certificates/{n}_{nsi}_in_{nsc}_(k).json` if that exists);
render it with `python3 python/render_certificate.py FILE`.
-/

open PolygonPacker

structure Args where
  n : Nat
  nsi : Nat
  nsc : Nat
  attempts : Nat := 1000
  tolerance : Float := 1e-8
  finalStep : Float := 0.0001
  output : Option String := none

def usage : String :=
  "usage: polygon_packer inner_polygons inner_sides container_sides " ++
  "[--attempts N] [--tolerance T] [--finalstep F] [--output FILE]"

partial def parseOptions (a : Args) : List String → Except String Args
  | [] => .ok a
  | "--attempts" :: v :: rest => do
    let k ← (v.toNat?).elim (.error s!"invalid --attempts value {v}") .ok
    parseOptions { a with attempts := k } rest
  | "--tolerance" :: v :: rest => do
    let t ← (parseFloat? v).elim (.error s!"invalid --tolerance value {v}") .ok
    parseOptions { a with tolerance := t } rest
  | "--finalstep" :: v :: rest => do
    let t ← (parseFloat? v).elim (.error s!"invalid --finalstep value {v}") .ok
    parseOptions { a with finalStep := t } rest
  | "--output" :: v :: rest => parseOptions { a with output := some v } rest
  | o :: _ => .error s!"unrecognised argument {o}\n{usage}"

def parseArgs : List String → Except String Args
  | n :: nsi :: nsc :: rest =>
    match n.toNat?, nsi.toNat?, nsc.toNat? with
    | some n, some nsi, some nsc =>
      if n == 0 || nsi < 3 || nsc < 3 then
        .error "need at least one inner polygon and at least 3 sides per polygon"
      else parseOptions { n, nsi, nsc } rest
    | _, _, _ => .error usage
  | _ => .error usage

/-- First file name of the form `base.json`, `base_(1).json`, ... that does not exist. -/
partial def freshName (base : String) (k : Nat := 0) : IO String := do
  let name := if k == 0 then s!"{base}.json" else s!"{base}_({k}).json"
  if ← System.FilePath.pathExists name then freshName base (k + 1) else return name

public def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error e => IO.eprintln e; return 1
  | .ok args =>
  if args.attempts == 0 then
    IO.eprintln "--attempts must be positive"; return 1
  let P := Problem.make args.n args.nsi args.nsc
  let cfg : Settings := { tolerance := args.tolerance, finalStep := args.finalStep }
  let stdout ← IO.getStdout
  let tasks ← (List.range args.attempts).mapM fun seed =>
    IO.asTask do
      stdout.putStrLn s!"Attempt {seed}"
      stdout.flush
      let r := repetition P cfg seed
      return (seed, r)
  let mut results : List (Nat × Float × FloatArray) := []
  for t in tasks do
    match ← IO.wait t with
    | .error e => throw e
    | .ok r => results := r :: results
  -- Only certificates accepted by the exact checker `Cert.check` are ever written.
  let some (seed, cert) := certifyBest P results.reverse
    | IO.eprintln "no packing found could be certified exactly; nothing written"; return 1
  if let some (_, bS, _) := results.foldl (fun acc r => match acc with
      | some a => if r.2.1 < a.2.1 then some r else some a
      | none => some r) none then
    IO.println s!"Best side length found in floating point: {floatToJson (sideLength P bS)}"
  IO.println s!"Final side length (checked exactly): {cert.side.toString}"
  let file ← match args.output with
    | some f => pure f
    | none => freshName s!"certificates/{args.n}_{args.nsi}_in_{args.nsc}"
  IO.FS.createDirAll "certificates"
  IO.FS.writeFile file (cert.toJson args.attempts seed)
  IO.println s!"Certificate written to {file}"
  return 0
