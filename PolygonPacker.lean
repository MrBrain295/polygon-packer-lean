module

public import PolygonPacker.Basic
public import PolygonPacker.Search.Penalty
public import PolygonPacker.Search.Optimize
public import PolygonPacker.Search.Repetition
public import PolygonPacker.Certificate.Check
public import PolygonPacker.Certificate.Certify

/-!
# Polygon packer

* `PolygonPacker.Basic` — random numbers, 2D vectors, number parsing and printing.
* `PolygonPacker.Search.*` — the floating point search (port of `python/polygon_packer.py`):
  penalty and gradient, L-BFGS and basin hopping, and one packing attempt.
* `PolygonPacker.Certificate.*` — exact certificates: the rational checker `Cert.check`
  and `certifyBest`, which turns a search result into a checked certificate.

The executable is `Main.lean`; the correctness proofs are in the separate library
`PolygonPackerProofs`.
-/
