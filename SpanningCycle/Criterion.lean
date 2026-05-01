import SpanningCycle.MovePackage

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Spanning-cycle criterion

Destination module for the abstract ranked induction criterion and the concrete
cell-system bridge.
-/

namespace SpanningCycle

universe u v

section AbstractProofSkeleton

variable {Cell : Type u}

/--
A Lean-friendly abstraction of the consequences of section 5 used in the proof of
Theorem 6.2.

Concretely, one should instantiate `HasSpanningPath x` with:

> there exists a simple path in the 1-skeleton of `Σ(x)` from `s(x)` to `t(x)`
> that visits every vertex of `Σ(x)` exactly once.

The field `terminal_base` corresponds to the terminal case `SP2`, and the field
`local_step` is the abstract inductive step obtained from `SP3`, `SP4`, Remark 2.2,
and Lemma 6.1.
-/
structure RankedSpanningPathSystem
    (HasSpanningPath : Cell → Prop)
    (rank : Cell → Nat)
    (terminal : Cell → Prop) : Prop where
  terminal_base : ∀ x, terminal x → HasSpanningPath x
  local_step : ∀ x, ¬ terminal x →
    (∀ y, rank y < rank x → HasSpanningPath y) →
    HasSpanningPath x

/-- Abstract version of Theorem 6.2. -/
theorem cellwiseSpanningPath
    {HasSpanningPath : Cell → Prop}
    {rank : Cell → Nat}
    {terminal : Cell → Prop}
    (hsys : RankedSpanningPathSystem HasSpanningPath rank terminal) :
    ∀ x, HasSpanningPath x := by
  intro x
  exact ranked_induction rank terminal hsys.terminal_base hsys.local_step x

/--
Abstract version of the last step in Theorem 8.1:
a spanning path together with the surviving closing edge yields a Hamiltonian cycle.
-/
structure SpanningCycleFramework
    (HasSpanningPath : Cell → Prop)
    (ClosingEdgeSurvives : Cell → Prop)
    (HasHamiltonianCycle : Cell → Prop)
    (rank : Cell → Nat)
    (terminal : Cell → Prop) : Prop extends
    RankedSpanningPathSystem HasSpanningPath rank terminal where
  close_path : ∀ x, HasSpanningPath x → ClosingEdgeSurvives x → HasHamiltonianCycle x

/-- Abstract version of the first conclusion of Theorem 8.1. -/
theorem spanningCycleCriterion
    {HasSpanningPath : Cell → Prop}
    {ClosingEdgeSurvives : Cell → Prop}
    {HasHamiltonianCycle : Cell → Prop}
    {rank : Cell → Nat}
    {terminal : Cell → Prop}
    (hfw : SpanningCycleFramework
      HasSpanningPath ClosingEdgeSurvives HasHamiltonianCycle rank terminal)
    {F : Cell}
    (hclose : ClosingEdgeSurvives F) :
    HasHamiltonianCycle F := by
  exact hfw.close_path F (cellwiseSpanningPath hfw.toRankedSpanningPathSystem F) hclose

/--
Abstract version of the properly-bipartite add-on in Theorem 8.1.
-/
structure BalancedSpanningCycleFramework
    (HasSpanningPath : Cell → Prop)
    (ClosingEdgeSurvives : Cell → Prop)
    (HasHamiltonianCycle : Cell → Prop)
    (ProperlyBipartite : Cell → Prop)
    (HasNontriviallyBalancedHamiltonianCycle : Cell → Prop)
    (rank : Cell → Nat)
    (terminal : Cell → Prop) : Prop extends
    SpanningCycleFramework HasSpanningPath ClosingEdgeSurvives HasHamiltonianCycle rank terminal where
  balanced_of_bipartite :
    ∀ x, ProperlyBipartite x → HasHamiltonianCycle x → HasNontriviallyBalancedHamiltonianCycle x

/-- Abstract version of the full conclusion of Theorem 8.1. -/
theorem spanningCycleCriterionBalanced
    {HasSpanningPath : Cell → Prop}
    {ClosingEdgeSurvives : Cell → Prop}
    {HasHamiltonianCycle : Cell → Prop}
    {ProperlyBipartite : Cell → Prop}
    {HasNontriviallyBalancedHamiltonianCycle : Cell → Prop}
    {rank : Cell → Nat}
    {terminal : Cell → Prop}
    (hfw : BalancedSpanningCycleFramework
      HasSpanningPath ClosingEdgeSurvives HasHamiltonianCycle
      ProperlyBipartite HasNontriviallyBalancedHamiltonianCycle rank terminal)
    {F : Cell}
    (hclose : ClosingEdgeSurvives F)
    (hbip : ProperlyBipartite F) :
    HasNontriviallyBalancedHamiltonianCycle F := by
  exact hfw.balanced_of_bipartite F hbip (spanningCycleCriterion hfw.toSpanningCycleFramework hclose)

end AbstractProofSkeleton

section ConcreteCellwise

variable {Cell : Type u}
variable {V : Type v} [DecidableEq V]
variable {Adj : V → V → Prop}

/-- The concrete spanning-path predicate attached to a cell system. -/
abbrev CellHasSpanningPath
    (support : Cell → Finset V)
    (datum : PathDatum Cell V)
    (x : Cell) : Prop :=
  Nonempty (ListSpanningPath Adj (support x) (datum.s x) (datum.t x))

/--
A concrete cell system reduces the cellwise theorem to two kinds of data:
terminal boundary-cycle witnesses and nonterminal move-step witnesses.
-/
structure ConcreteCellSystem where
  support : Cell → Finset V
  datum : PathDatum Cell V
  rank : Cell → Nat
  terminal : Cell → Prop
  terminal_witness :
    ∀ x, terminal x →
      OrderedSegmentFamily.BoundaryCycleWitness Adj
        (support x) (datum.s x) (datum.t x)
  move_witness :
    ∀ x, ¬ terminal x →
      (∀ y, rank y < rank x →
        ListSpanningPath Adj (support y) (datum.s y) (datum.t y)) →
      OrderedSegmentFamily.MoveStepData Adj
        (support x) (datum.s x) (datum.t x)

/-- Turn a concrete cell system into the abstract ranked path system. -/
def ConcreteCellSystem.toRankedSpanningPathSystem
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)) :
    RankedSpanningPathSystem
      (fun x => CellHasSpanningPath (Adj := Adj) sys.support sys.datum x)
      sys.rank
      sys.terminal where
  terminal_base := by
    intro x hx
    exact ⟨(sys.terminal_witness x hx).toSpanningPath⟩
  local_step := by
    intro x hx ih
    classical
    exact ⟨OrderedSegmentFamily.spanningPathOfMoveStep
      (sys.move_witness x hx (fun y hy => Classical.choice (ih y hy)))⟩

/-- Concrete cellwise spanning-path theorem. -/
noncomputable def ConcreteCellSystem.buildCellwiseSpanningPath
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)) :
    ∀ x, ListSpanningPath Adj (sys.support x) (sys.datum.s x) (sys.datum.t x) := by
  classical
  intro x
  exact Classical.choice (SpanningCycle.cellwiseSpanningPath sys.toRankedSpanningPathSystem x)

/--
A cell has a spanning path whose cyclic closure contains a marked vertex word.

The closing edge is not required at this predicate level; the list
`s :: (tail ++ [s])` is the cyclic support order that will become an actual
cycle once the root closing edge is supplied.
-/
abbrev CellHasCyclicMarkedSpanningPath
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (needle : List V)
    (x : Cell) : Prop :=
  ∃ p : ListSpanningPath Adj (sys.support x) (sys.datum.s x) (sys.datum.t x),
    needle <:+: sys.datum.s x :: (p.tail ++ [sys.datum.s x])

/--
Ranked induction data for preserving a marked cyclic infix through the same
cell system used for the ordinary spanning-path construction.
-/
structure ConcreteCellSystem.CyclicMarkedInductionData
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (needle : List V) : Prop where
  terminal_base :
    ∀ x, sys.terminal x → CellHasCyclicMarkedSpanningPath sys needle x
  local_step :
    ∀ x, ¬ sys.terminal x →
      (∀ y, sys.rank y < sys.rank x →
        CellHasCyclicMarkedSpanningPath sys needle y) →
      CellHasCyclicMarkedSpanningPath sys needle x

/-- Convert marked cell-system data into the abstract ranked induction package. -/
def ConcreteCellSystem.CyclicMarkedInductionData.toRankedSpanningPathSystem
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {needle : List V}
    (marked : sys.CyclicMarkedInductionData needle) :
    RankedSpanningPathSystem
      (CellHasCyclicMarkedSpanningPath (Adj := Adj) sys needle)
      sys.rank
      sys.terminal where
  terminal_base := marked.terminal_base
  local_step := marked.local_step

/-- Marked cellwise spanning-path theorem. -/
theorem ConcreteCellSystem.cellwiseCyclicMarkedSpanningPath
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {needle : List V}
    (marked : sys.CyclicMarkedInductionData needle) :
    ∀ x, CellHasCyclicMarkedSpanningPath sys needle x := by
  exact cellwiseSpanningPath marked.toRankedSpanningPathSystem

/-- Choose explicit marked spanning paths from marked cell-system data. -/
noncomputable def ConcreteCellSystem.buildCellwiseCyclicMarkedSpanningPath
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {needle : List V}
    (marked : sys.CyclicMarkedInductionData needle) :
    ∀ x, ListSpanningPath Adj (sys.support x) (sys.datum.s x) (sys.datum.t x) := by
  classical
  intro x
  exact Classical.choose (sys.cellwiseCyclicMarkedSpanningPath marked x)

/-- The chosen marked spanning paths contain the requested cyclic infix. -/
theorem ConcreteCellSystem.buildCellwiseCyclicMarkedSpanningPath_infix
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {needle : List V}
    (marked : sys.CyclicMarkedInductionData needle)
    (x : Cell) :
    needle <:+:
      sys.datum.s x ::
        ((sys.buildCellwiseCyclicMarkedSpanningPath marked x).tail ++
          [sys.datum.s x]) := by
  classical
  exact Classical.choose_spec (sys.cellwiseCyclicMarkedSpanningPath marked x)

/--
Terminal marked-boundary condition: every terminal boundary path already
contains the marked word in its cyclic closure.
-/
def ConcreteCellSystem.TerminalCyclicMarkData
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (needle : List V) : Prop :=
  ∀ x (hx : sys.terminal x),
    needle <:+:
      sys.datum.s x ::
        (((sys.terminal_witness x hx).toSpanningPath).tail ++
          [sys.datum.s x])

/--
Terminal marked-boundary data follows from showing the mark occurs on the
terminal boundary cycle list.
-/
theorem ConcreteCellSystem.TerminalCyclicMarkData.of_boundaryCycleInfix
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {needle : List V}
    (hboundary :
      ∀ x (hx : sys.terminal x),
        needle <:+:
          sys.datum.s x ::
            ((sys.terminal_witness x hx).middle ++
              [sys.datum.t x, sys.datum.s x])) :
    sys.TerminalCyclicMarkData needle := by
  intro x hx
  simpa [OrderedSegmentFamily.BoundaryCycleWitness.toSpanningPath,
    List.append_assoc] using hboundary x hx

/--
Local marked-move preservation: if child paths contain the mark in the required
cyclic sense, then the parent path built by `sys.move_witness` does too.
-/
def ConcreteCellSystem.MoveCyclicMarkPreservation
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (needle : List V) : Prop :=
  ∀ x (hnonterminal : ¬ sys.terminal x)
    (childPath :
      ∀ y, sys.rank y < sys.rank x →
        ListSpanningPath Adj (sys.support y) (sys.datum.s y) (sys.datum.t y)),
    (∀ y (hy : sys.rank y < sys.rank x),
      needle <:+:
        sys.datum.s y :: ((childPath y hy).tail ++ [sys.datum.s y])) →
    needle <:+:
      sys.datum.s x ::
        ((OrderedSegmentFamily.spanningPathOfMoveStep
          (sys.move_witness x hnonterminal childPath)).tail ++ [sys.datum.s x])

/--
Open parent marked-move data: the glued parent path itself contains the mark.

This is the local geometric fact one should prove when the mark survives in the
opened parent path without needing to use a child's deleted closing edge.
-/
def ConcreteCellSystem.ParentOpenCyclicMarkData
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (needle : List V) : Prop :=
  ∀ x (hnonterminal : ¬ sys.terminal x)
    (childPath :
      ∀ y, sys.rank y < sys.rank x →
        ListSpanningPath Adj (sys.support y) (sys.datum.s y) (sys.datum.t y)),
    needle <:+:
      sys.datum.s x ::
        ((OrderedSegmentFamily.spanningPathOfMoveStep
          (sys.move_witness x hnonterminal childPath)).tail ++ [sys.datum.s x])

/--
If every nonterminal move directly places the mark in the opened parent path,
then it satisfies the full marked-move preservation interface.
-/
theorem ConcreteCellSystem.MoveCyclicMarkPreservation.of_parentOpenCyclicMarkData
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {needle : List V}
    (hopen : sys.ParentOpenCyclicMarkData needle) :
    sys.MoveCyclicMarkPreservation needle := by
  intro x hnonterminal childPath _childInfix
  exact hopen x hnonterminal childPath

/--
Build marked induction data from terminal marked-boundary data and a local
marked-move preservation theorem for the existing move witnesses.
-/
noncomputable def ConcreteCellSystem.CyclicMarkedInductionData.ofTerminalAndMovePreservation
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {needle : List V}
    (hterminal : sys.TerminalCyclicMarkData needle)
    (hmove : sys.MoveCyclicMarkPreservation needle) :
    sys.CyclicMarkedInductionData needle where
  terminal_base := by
    intro x hx
    exact ⟨(sys.terminal_witness x hx).toSpanningPath, hterminal x hx⟩
  local_step := by
    intro x hnonterminal ih
    classical
    let childPath :
        ∀ y, sys.rank y < sys.rank x →
          ListSpanningPath Adj (sys.support y) (sys.datum.s y) (sys.datum.t y) :=
      fun y hy => Classical.choose (ih y hy)
    have childInfix :
        ∀ y (hy : sys.rank y < sys.rank x),
          needle <:+:
            sys.datum.s y :: ((childPath y hy).tail ++ [sys.datum.s y]) := by
      intro y hy
      exact Classical.choose_spec (ih y hy)
    exact
      ⟨OrderedSegmentFamily.spanningPathOfMoveStep
          (sys.move_witness x hnonterminal childPath),
        hmove x hnonterminal childPath childInfix⟩

/--
Localized marked induction data.

Only cells satisfying `active` are required to carry the marked word. Non-active
child cells still contribute ordinary spanning paths through the underlying
`ConcreteCellSystem`.
-/
structure ConcreteCellSystem.LocalizedCyclicMarkedInductionData
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (active : Cell → Prop)
    (needle : List V) : Prop where
  terminal_base :
    ∀ x, active x → sys.terminal x →
      CellHasCyclicMarkedSpanningPath sys needle x
  local_step :
    ∀ x, active x → ¬ sys.terminal x →
      (childPath :
        ∀ y, sys.rank y < sys.rank x →
          ListSpanningPath Adj (sys.support y) (sys.datum.s y) (sys.datum.t y)) →
      (∀ y (hy : sys.rank y < sys.rank x), active y →
        needle <:+:
          sys.datum.s y :: ((childPath y hy).tail ++ [sys.datum.s y])) →
      CellHasCyclicMarkedSpanningPath sys needle x

/-- Localized marked cellwise spanning-path theorem. -/
theorem ConcreteCellSystem.cellwiseLocalizedCyclicMarkedSpanningPath
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {active : Cell → Prop}
    {needle : List V}
    (marked : sys.LocalizedCyclicMarkedInductionData active needle) :
    ∀ x, active x → CellHasCyclicMarkedSpanningPath sys needle x := by
  classical
  let P : Cell → Prop := fun x => active x → CellHasCyclicMarkedSpanningPath sys needle x
  have ranked :
      RankedSpanningPathSystem P sys.rank sys.terminal := by
    refine
      { terminal_base := ?_
        local_step := ?_ }
    · intro x hterminal hactive
      exact marked.terminal_base x hactive hterminal
    · intro x hnonterminal ih hactive
      let childPath :
          ∀ y, sys.rank y < sys.rank x →
            ListSpanningPath Adj (sys.support y) (sys.datum.s y) (sys.datum.t y) :=
        fun y hy =>
          if hactive_y : active y then
            Classical.choose (ih y hy hactive_y)
          else
            sys.buildCellwiseSpanningPath y
      have childInfix :
          ∀ y (hy : sys.rank y < sys.rank x), active y →
            needle <:+:
              sys.datum.s y :: ((childPath y hy).tail ++ [sys.datum.s y]) := by
        intro y hy hactive_y
        have hspec := Classical.choose_spec (ih y hy hactive_y)
        simpa [childPath, hactive_y] using hspec
      exact marked.local_step x hactive hnonterminal childPath childInfix
  intro x hactive
  exact (cellwiseSpanningPath ranked x) hactive

/-- Choose an explicit marked path for an active cell. -/
noncomputable def ConcreteCellSystem.buildCellwiseLocalizedCyclicMarkedSpanningPath
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {active : Cell → Prop}
    {needle : List V}
    (marked : sys.LocalizedCyclicMarkedInductionData active needle)
    (x : Cell)
    (hactive : active x) :
    ListSpanningPath Adj (sys.support x) (sys.datum.s x) (sys.datum.t x) := by
  classical
  exact Classical.choose
    (ConcreteCellSystem.cellwiseLocalizedCyclicMarkedSpanningPath
      (sys := sys) marked x hactive)

/-- The chosen localized marked path contains the requested cyclic infix. -/
theorem ConcreteCellSystem.buildCellwiseLocalizedCyclicMarkedSpanningPath_infix
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {active : Cell → Prop}
    {needle : List V}
    (marked : sys.LocalizedCyclicMarkedInductionData active needle)
    (x : Cell)
    (hactive : active x) :
    needle <:+:
      sys.datum.s x ::
        ((sys.buildCellwiseLocalizedCyclicMarkedSpanningPath marked x hactive).tail ++
          [sys.datum.s x]) := by
  classical
  exact Classical.choose_spec
    (ConcreteCellSystem.cellwiseLocalizedCyclicMarkedSpanningPath
      (sys := sys) marked x hactive)

/-- Terminal marked data only for active terminal cells. -/
def ConcreteCellSystem.LocalizedTerminalCyclicMarkData
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (active : Cell → Prop)
    (needle : List V) : Prop :=
  ∀ x, active x → (hx : sys.terminal x) →
    needle <:+:
      sys.datum.s x ::
        (((sys.terminal_witness x hx).toSpanningPath).tail ++
          [sys.datum.s x])

/--
Localized terminal marked data follows from boundary-cycle infix data on active
terminal cells.
-/
theorem ConcreteCellSystem.LocalizedTerminalCyclicMarkData.of_boundaryCycleInfix
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {active : Cell → Prop}
    {needle : List V}
    (hboundary :
      ∀ x, active x → (hx : sys.terminal x) →
        needle <:+:
          sys.datum.s x ::
            ((sys.terminal_witness x hx).middle ++
              [sys.datum.t x, sys.datum.s x])) :
    sys.LocalizedTerminalCyclicMarkData active needle := by
  intro x hactive hx
  simpa [OrderedSegmentFamily.BoundaryCycleWitness.toSpanningPath,
    List.append_assoc] using hboundary x hactive hx

/-- Local marked-move preservation for active parent cells. -/
def ConcreteCellSystem.LocalizedMoveCyclicMarkPreservation
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (active : Cell → Prop)
    (needle : List V) : Prop :=
  ∀ x, active x → (hnonterminal : ¬ sys.terminal x) →
    (childPath :
      ∀ y, sys.rank y < sys.rank x →
        ListSpanningPath Adj (sys.support y) (sys.datum.s y) (sys.datum.t y)) →
    (∀ y (hy : sys.rank y < sys.rank x), active y →
      needle <:+:
        sys.datum.s y :: ((childPath y hy).tail ++ [sys.datum.s y])) →
    needle <:+:
      sys.datum.s x ::
        ((OrderedSegmentFamily.spanningPathOfMoveStep
          (sys.move_witness x hnonterminal childPath)).tail ++ [sys.datum.s x])

/--
Localized open parent marked data: for active nonterminal parents, the glued
parent path itself contains the mark.
-/
def ConcreteCellSystem.LocalizedParentOpenCyclicMarkData
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (active : Cell → Prop)
    (needle : List V) : Prop :=
  ∀ x, active x → (hnonterminal : ¬ sys.terminal x) →
    (childPath :
      ∀ y, sys.rank y < sys.rank x →
        ListSpanningPath Adj (sys.support y) (sys.datum.s y) (sys.datum.t y)) →
    needle <:+:
      sys.datum.s x ::
        ((OrderedSegmentFamily.spanningPathOfMoveStep
          (sys.move_witness x hnonterminal childPath)).tail ++ [sys.datum.s x])

/-- Localized open-parent data implies localized marked-move preservation. -/
theorem ConcreteCellSystem.LocalizedMoveCyclicMarkPreservation.of_parentOpenCyclicMarkData
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {active : Cell → Prop}
    {needle : List V}
    (hopen : sys.LocalizedParentOpenCyclicMarkData active needle) :
    sys.LocalizedMoveCyclicMarkPreservation active needle := by
  intro x hactive hnonterminal childPath _childInfix
  exact hopen x hactive hnonterminal childPath

/-- Build localized marked induction data from localized terminal and move facts. -/
noncomputable def
    ConcreteCellSystem.LocalizedCyclicMarkedInductionData.ofTerminalAndMovePreservation
    {sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)}
    {active : Cell → Prop}
    {needle : List V}
    (hterminal : sys.LocalizedTerminalCyclicMarkData active needle)
    (hmove : sys.LocalizedMoveCyclicMarkPreservation active needle) :
    sys.LocalizedCyclicMarkedInductionData active needle where
  terminal_base := by
    intro x hactive hx
    exact ⟨(sys.terminal_witness x hx).toSpanningPath, hterminal x hactive hx⟩
  local_step := by
    intro x hactive hnonterminal childPath childInfix
    exact
      ⟨OrderedSegmentFamily.spanningPathOfMoveStep
          (sys.move_witness x hnonterminal childPath),
        hmove x hactive hnonterminal childPath childInfix⟩

end ConcreteCellwise

section ConcreteGraphBridge

variable {Cell : Type u}
variable {V : Type v} [DecidableEq V]
variable {Adj : V → V → Prop}

/--
Turn a concrete cell system into the final spanning-cycle framework used by the
abstract criterion: a closing edge on a cell closes its cellwise spanning path
into a Hamiltonian cycle on that cell support.
-/
def ConcreteCellSystem.toSpanningCycleFramework
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj)) :
    SpanningCycleFramework
      (fun x => CellHasSpanningPath (Adj := Adj) sys.support sys.datum x)
      (fun x => Adj (sys.datum.t x) (sys.datum.s x))
      (fun x => HamiltonianOn (sys.support x) Adj)
      sys.rank
      sys.terminal where
  toRankedSpanningPathSystem := sys.toRankedSpanningPathSystem
  close_path := by
    intro x hx hclose
    rcases hx with ⟨p⟩
    exact hamiltonianOn_of_spanningPath p hclose

/--
Concrete version of the manuscript's final criterion: once the closing edge
from the cell exit back to the entry survives, the cell support is Hamiltonian.
-/
theorem ConcreteCellSystem.hamiltonianOfClosingEdge
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    {x : Cell}
    (hclose : Adj (sys.datum.t x) (sys.datum.s x)) :
    HamiltonianOn (sys.support x) Adj := by
  exact spanningCycleCriterion sys.toSpanningCycleFramework hclose

/--
Root-cell specialization of `ConcreteCellSystem.hamiltonianOfClosingEdge`.
-/
theorem ConcreteCellSystem.rootHamiltonian
    (sys : ConcreteCellSystem (Cell := Cell) (V := V) (Adj := Adj))
    (root : Cell)
    (hclose : Adj (sys.datum.t root) (sys.datum.s root)) :
    HamiltonianOn (sys.support root) Adj :=
  sys.hamiltonianOfClosingEdge hclose

end ConcreteGraphBridge

end SpanningCycle
