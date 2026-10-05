This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Flamethrower's polygon packer
This program can quickly solve the 2D bin packing problem for any number of any polygons inside any other polygon! It was the tool used to find all the optimal packings under the name "Ignacio Vallejo" on [Erich's Packing Center](https://erich-friedman.github.io/packing/).
<img width="640" height="480" alt="30 triangles in a hexagon" src="https://github.com/user-attachments/assets/48591a93-3ed9-4031-9c42-8b6eb579d91e" />

### How to use
Install the dependencies (`pip install -r python/requirements.txt`) and run it like this:

`python3 python/polygon_packer.py [n] [nsi] [nsc]`
- Replace `[n]` with the number of inner polygons you want to solve for
- Replace `[nsi]` with the number of sides of the inner polygons (e.g. 4 for a square)
- Replace `[nsc]` with the number of sides of the container polygon

Optional parameters:
- `--attempts`: the total number of attempts to run. Increase to explore more possible packings. Defaults to 1000.
- `--tolerance`: the tolerance for the penalty function. More penalty reduces the margin of overlap but limits exporation. Defaults to an empirical sweetspot of 0.00000001.
- `--finalstep`: the container size is decreased by a smaller factor each time, to save compute at the beginning and achieve greater precision near the end. This sets the step size of the shrinkage which would correspond to the theoretical minimum container size (which, for most packings, will not actually be reached, so keep that in mind when setting this parameter). Defaults to 0.0001.
- `--output_format`: the file type of the output image. Currently supported types are png (default) and svg.

## Project layout

```
.
├── lakefile.toml, lean-toolchain, lake-manifest.json   Lean project (Lean 4.28, Mathlib)
├── Main.lean                      `polygon_packer` executable (argument parsing, parallel attempts, output)
├── PolygonPacker.lean             root of the program library
├── PolygonPacker/
│   ├── Basic.lean                 random numbers, 2D vectors, number parsing/printing
│   ├── Search/                    floating point search (port of python/polygon_packer.py)
│   │   ├── Penalty.lean           penalty (`bh_function`) and its exact gradient, side length
│   │   ├── Optimize.lean          L-BFGS and basin hopping
│   │   └── Repetition.lean        one packing attempt (`repetition(seed)`)
│   └── Certificate/               exact certificates
│       ├── Check.lean             exact rational checker `Cert.check`
│       └── Certify.lean           rounding + spreading, `certify` / `certifyBest`
├── PolygonPackerProofs.lean       root of the proof library (uses Mathlib)
├── PolygonPackerProofs/
│   ├── Interval.lean              soundness of the interval arithmetic
│   ├── Trig.lean                  rigorous bounds for π, sin, cos
│   ├── Spec.lean                  what a valid packing is (`Cert.Valid`)
│   ├── Geometry.lean              convex-polygon / separating-axis facts
│   └── Soundness.lean             `Cert.check_sound`, `certifyBest_valid`, `certifyBest_side_length`
├── python/
│   ├── polygon_packer.py          the original Python packer
│   ├── render_certificate.py      draws a certificate written by the Lean program
│   └── requirements.txt
└── examples/
    ├── 10_6_in_4.json / .png      certificate from the Lean program and its picture
    └── 10_6_in_4_original_python.svg   picture from the original Python program
```

`lake build` builds everything (program library, executable and proofs).
`lake build polygon_packer` builds only the executable, without the proofs.

## Lean version of the packer

The packing search (everything up to choosing the best packing) is also implemented in
Lean 4 in `PolygonPacker/` (executable root `Main.lean`). It does not draw
anything. It writes a JSON **certificate** of the best packing instead, and
`python/render_certificate.py` turns that file into the picture.

```
lake build polygon_packer
lake exe polygon_packer 10 6 4 --attempts 1000      # writes 10_6_in_4.json
python3 python/render_certificate.py 10_6_in_4.json --output_format svg
```

Options: `--attempts`, `--tolerance`, `--finalstep` (same meaning and defaults as above) and
`--output FILE` (the default is `{n}_{nsi}_in_{nsc}.json`, with `_(k)` appended if that file
already exists). Attempts run in parallel on all cores.

### Every certificate is checked exactly, and this is proved in Lean

The search uses floating point numbers and only asks for a *small* penalty, so its raw
result can contain tiny overlaps (around `1e-4`). The Lean program therefore never writes
that raw result. Instead (`PolygonPacker/Certificate/Certify.lean`):

1. the positions, angles and side length are rounded to exact decimals (17 significant
   digits);
2. the exact checker `Cert.check` (`PolygonPacker/Certificate/Check.lean`) runs on these decimals. It
   uses exact rational arithmetic, with rigorous interval bounds for `π`, `sin` and `cos`;
3. if the check fails, the configuration is spread out by a tiny factor (the centres move
   apart and the container grows by the same factor: `1 + 1e-12`, ..., `1 + 1e-4`, ...)
   and checked again. The first configuration that passes is written. If none passes,
   nothing is written and the program exits with an error.

As a result, the side length printed by the program can be slightly larger (about `1e-4`
relative in tests with hexagons) than the floating point value from the search, which the
program also prints. It is never smaller than the true side length of the container that
holds the packing.

The proofs are in `PolygonPackerProofs/` (build with `lake build PolygonPackerProofs`):

* `Cert.check_sound` (`Soundness.lean`): if `Cert.check c = true`, then `c.Valid` holds.
  Here `c.Valid` (`Spec.lean`) means: there are exactly `n` inner polygons; each one is the
  exact regular `nsi`-gon of circumradius 1 with the certificate's centre and angle, and
  lies inside the container; and no two of them overlap (their interiors are disjoint).
  The container is the regular `nsc`-gon centred at the origin with circumradius
  `side_length * sin(π/nsi) / sin(π/nsc)`.
* `certifyBest_valid`: every certificate that `certifyBest` returns is valid and is for the
  requested `n`, `nsi`, `nsc`. The executable writes exactly the certificate returned by
  `certifyBest`, so this covers every packing the program outputs, whatever the floating
  point search did.
* `certifyBest_side_length` / `Cert.container_side_length`: the side of the container is
  exactly `side_length` times the side of an inner polygon.

The proofs use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
They cover the certificate data. The conversion of those exact decimals into JSON text
(`Decimal.toString`) is ordinary code and has not been proved correct.

Certificate fields (version 2): `inner_polygons`, `inner_sides`, `container_sides`,
`inner_circumradius` (always 1), `side_length` (exact, checked), `polygons` (a list of
`{x, y, angle}`, exact, checked), `verified` (always `true`), `attempts`, `best_seed`, and,
for drawing only, the floating point approximations `container_circumradius`,
`container_vertices` and `polygon_vertices`. The exact numbers are finite decimals such
as `6.1052372273055502e0`, which Python's `fractions.Fraction` reads exactly.

Differences from the Python version:
* SciPy's L-BFGS-B, which estimates the gradient by finite differences, is replaced by
  an L-BFGS (memory 10) that uses the exact gradient of the penalty. It has the same
  stopping rules (`ftol = gtol = 1e-8`, at most 15000 iterations) and a backtracking
  Armijo line search.
* `basinhopping` is reimplemented with the same settings (`niter=50`, `T=0.1`,
  `stepsize=0.1`, Metropolis acceptance). SciPy's adaptive step size never takes effect
  with `niter=50`, so it is left out.
* The random number generator is SplitMix64 seeded with the attempt number, so results
  are reproducible run to run but differ from NumPy's.
