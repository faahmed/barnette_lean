# AGENTS.md

This is the paper-support subset for the Barnette Lean formalization.

## Main Endpoint

The P4-free Barnette endpoint is:

```lean
barnetteConjecture_of_fullClassPositiveRecursiveFaceSplitCertificateProvider
```

It is declared in:

```text
SpanningCycle/BarnetteDirect.lean
```

## Verification

Run these commands from this directory:

```bash
lake env lean SpanningCycle/BarnetteDirect.lean
lake build
```

## Included Source Stack

- `SpanningCycleCore.lean`
- `SpanningCycle/PathBasics.lean`
- `SpanningCycle/MovePackage.lean`
- `SpanningCycle/Criterion.lean`
- `SpanningCycle/GraphClasses.lean`
- `SpanningCycle/PolyhedralFaceCells.lean`
- `SpanningCycle/BarnetteDirect.lean`
- `SpanningCycle.lean`
- `Barnette.lean`
