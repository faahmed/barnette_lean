import SpanningCycle.Criterion

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Graph classes for the paper endpoint

This subset module contains only the graph-language needed by the recursive
face-split paper endpoint: face boundaries, polyhedral embeddings, polyhedral
graphs, and Barnette graphs.
-/

namespace SpanningCycle

universe u v

section PolyhedralGraphs

open SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/--
A face boundary recorded as a closed walk in the ambient graph. This keeps the
polyhedral layer tied to mathlib's `SimpleGraph.Walk` API instead of our ad hoc
list-based graph model.
-/
structure FaceBoundary where
  base : V
  walk : G.Walk base base
  isCycle : walk.IsCycle

namespace FaceBoundary

variable {G}

/-- The oriented edge relation induced by a face boundary, viewed undirectedly. -/
def EdgeOn (F : FaceBoundary G) (u v : V) : Prop :=
  (u, v) ∈ edgePairs F.walk.support ∨ (v, u) ∈ edgePairs F.walk.support

/-- The vertices lying on a face boundary. -/
def vertices (F : FaceBoundary G) : List V :=
  F.walk.support

/--
Build the terminal boundary witness from an explicit cyclic presentation of a
face boundary, using `t -> s` as the deleted closing edge.
-/
def toBoundaryCycleWitness
    (F : FaceBoundary G)
    {s t : V}
    (middle : List V)
    (hsupport : F.vertices = s :: (middle ++ [t, s]))
    (hnodup : List.Nodup (s :: (middle ++ [t]))) :
    OrderedSegmentFamily.BoundaryCycleWitness
      G.Adj (F.vertices.toFinset) s t where
  middle := middle
  cycle_adj := by
    intro a b hab
    have hclosed : F.walk.support = s :: (middle ++ [t, s]) := by
      simpa [FaceBoundary.vertices] using hsupport
    have habWalk : (a, b) ∈ edgePairs F.walk.support := by
      simpa [hclosed] using hab
    exact
      (SimpleGraph.Walk.toSubgraph_adj_of_mem_edgePairs_support
        (p := F.walk) habWalk).adj_sub
  nodup := hnodup
  spans := by
    intro v
    have hclosed : F.walk.support = s :: (middle ++ [t, s]) := by
      simpa [FaceBoundary.vertices] using hsupport
    rw [FaceBoundary.vertices, hclosed]
    simp [List.mem_toFinset, or_assoc, or_left_comm, or_comm]

/--
The opened face-boundary list has no repeated vertices when it comes from a
cycle support presentation.
-/
theorem openedSupport_nodup
    (F : FaceBoundary G)
    {s t : V}
    (middle : List V)
    (hsupport : F.vertices = s :: (middle ++ [t, s])) :
    List.Nodup (s :: (middle ++ [t])) := by
  have hclosed : F.walk.support = s :: (middle ++ [t, s]) := by
    simpa [FaceBoundary.vertices] using hsupport
  have htail : F.walk.support.tail = middle ++ [t, s] := by
    simp [hclosed]
  have hnTail : List.Nodup (middle ++ [t, s]) := by
    simpa [htail] using F.isCycle.support_nodup
  have hnTail' : List.Nodup ((middle ++ [t]) ++ [s]) := by
    simpa [List.append_assoc] using hnTail
  have hnOpen : List.Nodup ([s] ++ (middle ++ [t])) :=
    (List.nodup_append_comm).1 hnTail'
  simpa using hnOpen

/--
Build the terminal boundary witness from an explicit cyclic presentation of a
face boundary. The no-repeated-vertices condition follows from `IsCycle`.
-/
def toBoundaryCycleWitnessOfSupport
    (F : FaceBoundary G)
    {s t : V}
    (middle : List V)
    (hsupport : F.vertices = s :: (middle ++ [t, s])) :
    OrderedSegmentFamily.BoundaryCycleWitness
      G.Adj (F.vertices.toFinset) s t :=
  F.toBoundaryCycleWitness middle hsupport
    (F.openedSupport_nodup middle hsupport)

end FaceBoundary

/--
Minimal combinatorial polyhedral embedding data for a finite simple graph:
finite face boundaries cover all vertices, and every graph edge lies on exactly
two face boundaries.
-/
structure PolyhedralEmbedding where
  Face : Type u
  [faceFintype : Fintype Face]
  boundary : Face → FaceBoundary G
  vertex_covered : ∀ v : V, ∃ f, v ∈ (boundary f).vertices
  edge_covered_twice :
    ∀ ⦃u v : V⦄, G.Adj u v →
      ∃ f₁ f₂,
        f₁ ≠ f₂ ∧
        (boundary f₁).EdgeOn u v ∧
        (boundary f₂).EdgeOn u v ∧
        ∀ f, (boundary f).EdgeOn u v → f = f₁ ∨ f = f₂

attribute [instance] PolyhedralEmbedding.faceFintype

end PolyhedralGraphs

section GraphClasses

open SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Cubicity for a finite simple graph. -/
def IsCubicGraph (G : SimpleGraph V) : Prop := by
  classical
  exact ∀ v, (G.neighborFinset v).card = 3

/--
Vertex 3-connectivity for a finite simple graph.
-/
def IsThreeConnectedGraph (G : SimpleGraph V) : Prop :=
  G.Connected ∧
    ∀ S : Finset V, S.card < 3 → (G.induce {v | v ∉ S}).Connected

namespace IsThreeConnectedGraph

/-- A 3-connected graph is connected. -/
theorem connected {G : SimpleGraph V} (h : IsThreeConnectedGraph G) :
    G.Connected :=
  h.1

end IsThreeConnectedGraph

/--
A finite polyhedral graph, encoded as a simple graph together with the
combinatorial embedding data that exposes its faces.
-/
structure PolyhedralGraph where
  G : SimpleGraph V
  embedding : PolyhedralEmbedding G
  connected : G.Connected
  three_connected : IsThreeConnectedGraph G

/--
The target class for Barnette's conjecture: finite cubic bipartite polyhedral
graphs.
-/
structure BarnetteGraph extends PolyhedralGraph (V := V) where
  bipartite : G.IsBipartite
  cubic : IsCubicGraph G

/-- The final graph-theoretic target property for a Barnette graph. -/
def BarnetteGraph.IsHamiltonian (B : BarnetteGraph (V := V)) : Prop :=
  let G : SimpleGraph V := B.toPolyhedralGraph.G
  G.IsHamiltonian

end GraphClasses

end SpanningCycle
