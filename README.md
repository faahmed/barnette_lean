# A Spanning-Cycle Criterion for Canonical Subdivisions of Bipartite Planar 2-Cells

This repository accompanies the Zenodo preprint: https://doi.org/10.5281/zenodo.20264416

```lean
barnetteConjecture_of_fullClassPositiveRecursiveFaceSplitCertificateProvider
```

The endpoint is declared in `SpanningCycle/BarnetteDirect.lean`.

## Verification

From this directory, run:

```bash
lake build
```

For a fresh checkout, fetching mathlib cache artifacts first is recommended:

```bash
lake exe cache get
lake build
```

For the endpoint file alone:

```bash
lake env lean SpanningCycle/BarnetteDirect.lean
```

The project is pinned to Lean `v4.29.1` and mathlib `v4.29.1`.

## Included Modules

- `SpanningCycleCore.lean`: core spanning-cycle criterion and ranked induction.
- `SpanningCycle/PathBasics.lean`: finite path and list-spanning primitives.
- `SpanningCycle/MovePackage.lean`: reusable path/move and Hamiltonian-witness machinery.
- `SpanningCycle/Criterion.lean`: abstract criterion and concrete cell-system bridge.
- `SpanningCycle/GraphClasses.lean`: face-boundary, polyhedral graph, and Barnette graph interface.
- `SpanningCycle/PolyhedralFaceCells.lean`: positive face-cell certificate machinery.
- `SpanningCycle/BarnetteDirect.lean`: P4-free positive recursive certificate endpoint.
- `SpanningCycle.lean` and `Barnette.lean`: subset library roots.
