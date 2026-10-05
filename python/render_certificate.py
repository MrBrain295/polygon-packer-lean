"""Render a packing certificate produced by the Lean polygon packer.

Usage:
    python3 render_certificate.py CERTIFICATE.json [--output_format png|svg] [--output FILE]

The picture is drawn exactly like the one produced by polygon_packer.py.
Before drawing, the script recomputes the penalty of the configuration in floating point
(the same function as `bh_function` in polygon_packer.py; for a checked certificate any
tiny positive value is floating point noise) and checks that the vertex coordinates stored
in the certificate agree with the stored positions and rotations.
"""

import argparse
import json
import os

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as ppt


def regular_polygon(sides, phase=0.0):
    angles = np.linspace(0, 2 * np.pi, sides, endpoint=False) + phase
    return np.column_stack((np.cos(angles), np.sin(angles)))


def transform_polygon(x, y, a, vertices):
    c, s = np.cos(a), np.sin(a)
    rot = np.array([[c, -s], [s, c]])
    return vertices @ rot.T + np.array([x, y])


def penalty(values, S, nsi, nsc):
    """Same penalty as bh_function in polygon_packer.py."""
    N = len(values) // 3
    unit_vertices = regular_polygon(nsi)
    unit_vectors = regular_polygon(nsi, np.pi / nsi)
    container_vectors = regular_polygon(nsc, np.pi / nsc)
    limit = np.cos(np.pi / nsc) * S
    polys, axes = [], []
    total = 0.0
    for i in range(N):
        x, y, a = values[3 * i: 3 * i + 3]
        p = transform_polygon(x, y, a, unit_vertices)
        polys.append(p)
        axes.append(transform_polygon(0.0, 0.0, a, unit_vectors))
        d = p @ container_vectors.T - limit
        total += float(np.sum(np.where(d > 0, d, 0.0) ** 2))
    for i in range(N):
        for j in range(i + 1, N):
            min_overlap = None
            for axis in np.vstack((axes[i], axes[j])):
                p1, p2 = polys[i] @ axis, polys[j] @ axis
                overlap = min(p1.max(), p2.max()) - max(p1.min(), p2.min())
                if overlap <= 0:
                    min_overlap = None
                    break
                min_overlap = overlap if min_overlap is None else min(min_overlap, overlap)
            if min_overlap is not None:
                total += min_overlap ** 2
    return total


def output_name(base, ext):
    name = f"{base}.{ext}"
    i = 1
    while os.path.exists(name):
        name = f"{base}_({i}).{ext}"
        i += 1
    return name


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", help="JSON certificate written by the Lean packer")
    parser.add_argument("--output_format", default="png", help="png (default) or svg")
    parser.add_argument("--output", default=None, help="output file name")
    args = parser.parse_args()

    with open(args.certificate) as f:
        cert = json.load(f)
    if cert.get("format") != "polygon-packing-certificate":
        raise SystemExit("not a polygon packing certificate")

    N = cert["inner_polygons"]
    nsi = cert["inner_sides"]
    nsc = cert["container_sides"]
    S = cert["container_circumradius"]
    values = np.array([[p["x"], p["y"], p["angle"]] for p in cert["polygons"]]).flatten()
    assert len(cert["polygons"]) == N

    # consistency checks
    unit_vertices = regular_polygon(nsi)
    vertex_error = 0.0
    for i in range(N):
        recomputed = transform_polygon(*values[3 * i: 3 * i + 3], unit_vertices)
        vertex_error = max(vertex_error, float(np.max(np.abs(recomputed - np.array(cert["polygon_vertices"][i])))))
    container_error = float(np.max(np.abs(regular_polygon(nsc) * S - np.array(cert["container_vertices"]))))
    pen = penalty(values, S, nsi, nsc)
    side = cert["side_length"]
    print(f"{N} {nsi}-gons in a {nsc}-gon, side length {side}")
    if cert.get("verified"):
        print("this packing was checked exactly in Lean (no overlaps, side length exact)")
    print(f"penalty recomputed in floating point: {pen:.6e}")
    print(f"max vertex discrepancy: {vertex_error:.3e}, container: {container_error:.3e}")
    if "tolerance" in cert and pen >= cert["tolerance"]:
        print("WARNING: penalty is not below the tolerance")

    # drawing (same as polygon_packer.py)
    fig, ax = ppt.subplots()
    container = regular_polygon(nsc) * S
    container_plot = np.vstack((container, container[0]))
    ax.plot(container_plot[:, 0], container_plot[:, 1], color="#000000", linewidth=0.5)
    for i in range(N):
        polygon = transform_polygon(*values[3 * i: 3 * i + 3], unit_vertices)
        polygon_plot = np.vstack((polygon, polygon[0]))
        ax.fill(polygon_plot[:, 0], polygon_plot[:, 1], "#CCCCCC", edgecolor="black", linewidth=0.5)
    ax.set_aspect("equal")
    ppt.title(f"Side length: {side}")

    if args.output_format not in ("png", "svg"):
        raise SystemExit("output_format must be png or svg")
    name = args.output or output_name(f"{N}_{nsi}_in_{nsc}", args.output_format)
    ppt.savefig(name)
    print(f"Image written to {name}")


if __name__ == "__main__":
    main()
