module

public import PolygonPacker.Basic

/-!
# Local and global minimisation

* `lbfgs`: limited-memory BFGS (memory 10), the unconstrained case of SciPy's
  `minimize(..., method="L-BFGS-B", tol=1e-8)`.  It uses the same stopping rules as
  SciPy: stop when the relative decrease
  `(f_k - f_{k+1}) / max(|f_k|, |f_{k+1}|, 1) ≤ ftol` or when `‖∇f‖_∞ ≤ gtol`
  (both `1e-8`), after at most `15000` iterations, or when the line search fails.
  The line search is a backtracking Armijo search (at most 20 trials).
* `basinhopping`: SciPy's `basinhopping` with the defaults used by the Python program
  (`niter = 50`, `T = 0.1`, `stepsize = 0.1`): random uniform displacement, local
  minimisation, Metropolis acceptance, keep the lowest accepted minimum.
-/

public section

namespace PolygonPacker

/-- Result of a minimisation. -/
structure MinResult where
  x : FloatArray
  fx : Float
deriving Inhabited

/-- L-BFGS two-loop recursion: returns `-H ∇f` for the current inverse Hessian model. -/
private def lbfgsDirection (ss ys : Array FloatArray) (rhos : Array Float)
    (g : FloatArray) : FloatArray := Id.run do
  let k := ss.size
  let mut q := g
  let mut alphas := Array.replicate k 0.0
  for t in [0:k] do
    let i := k - 1 - t
    let a := rhos[i]! * Vec.dot ss[i]! q
    alphas := alphas.set! i a
    q := Vec.axpy (-a) ys[i]! q
  let gamma := if k == 0 then 1.0
    else Vec.dot ss[k-1]! ys[k-1]! / Vec.dot ys[k-1]! ys[k-1]!
  let mut r := Vec.scale gamma q
  for i in [0:k] do
    let b := rhos[i]! * Vec.dot ys[i]! r
    r := Vec.axpy (alphas[i]! - b) ss[i]! r
  return Vec.scale (-1.0) r

/-- Minimise `f` (given as value-and-gradient) starting from `x0` with L-BFGS. -/
def lbfgs (f : FloatArray → Float × FloatArray) (x0 : FloatArray)
    (memory : Nat := 10) (ftol : Float := 1e-8) (gtol : Float := 1e-8)
    (maxIter : Nat := 15000) (maxLs : Nat := 20) : MinResult := Id.run do
  let (f0, g0) := f x0
  let mut x := x0
  let mut fx := f0
  let mut g := g0
  let mut ss : Array FloatArray := #[]
  let mut ys : Array FloatArray := #[]
  let mut rhos : Array Float := #[]
  if Vec.maxAbs g ≤ gtol then return { x, fx }
  for _ in [0:maxIter] do
    let mut d := lbfgsDirection ss ys rhos g
    let mut dg := Vec.dot d g
    if !(dg < 0.0) then
      -- not a descent direction: restart from steepest descent
      ss := #[]; ys := #[]; rhos := #[]
      d := Vec.scale (-1.0) g
      dg := -(Vec.dot g g)
    let mut step := if ss.isEmpty then min 1.0 (1.0 / Vec.norm g) else 1.0
    let mut accepted := false
    let mut xn := x
    let mut fn := fx
    let mut gn := g
    for _ in [0:maxLs] do
      let xt := Vec.axpy step d x
      let (ft, gt) := f xt
      if ft ≤ fx + 1e-4 * step * dg then
        xn := xt; fn := ft; gn := gt
        accepted := true
        break
      -- safeguarded quadratic interpolation
      let denom := 2.0 * (ft - fx - dg * step)
      let trial := if denom > 0.0 then -dg * step * step / denom else 0.5 * step
      step := max (0.1 * step) (min (0.5 * step) trial)
    if !accepted then break
    let s := Vec.sub xn x
    let y := Vec.sub gn g
    let sy := Vec.dot s y
    if sy > 2.2e-16 * Vec.dot y y then
      if ss.size == memory then
        ss := ss.eraseIdx! 0; ys := ys.eraseIdx! 0; rhos := rhos.eraseIdx! 0
      ss := ss.push s; ys := ys.push y; rhos := rhos.push (1.0 / sy)
    let fold := fx
    x := xn; fx := fn; g := gn
    if (fold - fx) / max (max fold.abs fx.abs) 1.0 ≤ ftol then break
    if Vec.maxAbs g ≤ gtol then break
  return { x, fx }

/-- Basin hopping around the local minimiser `localMin`. -/
def basinhopping (localMin : FloatArray → MinResult) (x0 : FloatArray) (rng : Rng)
    (niter : Nat := 50) (temperature : Float := 0.1) (stepsize : Float := 0.1) :
    MinResult × Rng := Id.run do
  let mut rng := rng
  let start := localMin x0
  let mut cur := start
  let mut best := start
  for _ in [0:niter] do
    let mut xt := cur.x
    for k in [0:xt.size] do
      let (u, r) := rng.uniform (-stepsize) stepsize
      rng := r
      xt := xt.set! k (xt[k]! + u)
    let res := localMin xt
    let (u, r) := rng.uniform01
    rng := r
    let w := Float.exp (min 0.0 (-(res.fx - cur.fx) / temperature))
    if w ≥ u then
      cur := res
      if res.fx < best.fx then best := res
  return (best, rng)

end PolygonPacker
