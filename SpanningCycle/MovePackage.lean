import SpanningCycle.PathBasics

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Spanning-cycle move package

Destination module for path segments, ordered segment families, terminal
boundary witnesses, and reusable local move packages.
-/

namespace SpanningCycle

universe u v

section ConcreteSpanningPaths

variable {V : Type v} [DecidableEq V]


structure PathSegment (Adj : V → V → Prop) where
  support : Finset V
  start : V
  finish : V
  path : ListSpanningPath Adj support start finish

namespace PathSegment

variable {Adj : V → V → Prop}

/-- Regard a concrete spanning path as a path segment. -/
def ofSpanningPath
    {support : Finset V} {s t : V}
    (p : ListSpanningPath Adj support s t) :
    PathSegment Adj where
  support := support
  start := s
  finish := t
  path := p

/-- The support covered by a list of path segments. -/
def supportUnion : List (PathSegment Adj) -> Finset V
  | [] => ∅
  | p :: ps => p.support ∪ supportUnion ps

@[simp] theorem supportUnion_nil :
    supportUnion ([] : List (PathSegment Adj)) = ∅ := rfl

@[simp] theorem supportUnion_cons (p : PathSegment Adj) (ps : List (PathSegment Adj)) :
    supportUnion (p :: ps) = p.support ∪ supportUnion ps := rfl

/-- Glue two segments whose supports meet only at the attachment vertex. -/
def append
    (p q : PathSegment Adj)
    (hlink : p.finish = q.start)
    (hinter : ∀ v, v ∈ p.support → v ∈ q.support → v = p.finish) :
    PathSegment Adj := by
  rcases p with ⟨ps, pstart, pfinish, ppath⟩
  rcases q with ⟨qs, qstart, qfinish, qpath⟩
  dsimp at hlink
  subst hlink
  exact
    { support := ps ∪ qs
      start := pstart
      finish := qfinish
      path := ListSpanningPath.append_of_support_inter ppath qpath hinter }

@[simp] theorem append_start
    (p q : PathSegment Adj)
    (hlink : p.finish = q.start)
    (hinter : ∀ v, v ∈ p.support → v ∈ q.support → v = p.finish) :
    (append p q hlink hinter).start = p.start := by
  rcases p with ⟨ps, pstart, pfinish, ppath⟩
  rcases q with ⟨qs, qstart, qfinish, qpath⟩
  dsimp at hlink
  subst hlink
  simp [append]

@[simp] theorem append_support
    (p q : PathSegment Adj)
    (hlink : p.finish = q.start)
    (hinter : ∀ v, v ∈ p.support → v ∈ q.support → v = p.finish) :
    (append p q hlink hinter).support = p.support ∪ q.support := by
  rcases p with ⟨ps, pstart, pfinish, ppath⟩
  rcases q with ⟨qs, qstart, qfinish, qpath⟩
  dsimp at hlink
  subst hlink
  simp [append]

@[simp] theorem append_finish
    (p q : PathSegment Adj)
    (hlink : p.finish = q.start)
    (hinter : ∀ v, v ∈ p.support → v ∈ q.support → v = p.finish) :
    (append p q hlink hinter).finish = q.finish := by
  rcases p with ⟨ps, pstart, pfinish, ppath⟩
  rcases q with ⟨qs, qstart, qfinish, qpath⟩
  dsimp at hlink
  subst hlink
  simp [append]

/--
A chain of path segments whose head support meets the union of the remaining
supports only at the head's exit vertex.
-/
inductive Chain : List (PathSegment Adj) -> Type v
  | nil : Chain []
  | singleton (p : PathSegment Adj) : Chain [p]
  | cons (p q : PathSegment Adj) (qs : List (PathSegment Adj))
      (hlink : p.finish = q.start)
      (hinter : ∀ v, v ∈ p.support → v ∈ supportUnion (q :: qs) → v = p.finish)
      (hchain : Chain (q :: qs)) :
      Chain (p :: q :: qs)

/--
Recursively glue a nonempty composable chain into a single path segment covering
the union of all supports in the chain.
-/
def glue : ∀ {p : PathSegment Adj} {ps : List (PathSegment Adj)}, Chain (p :: ps) →
    { r : PathSegment Adj // r.start = p.start ∧ r.support = supportUnion (p :: ps) }
  | p, [], Chain.singleton _ =>
      ⟨p, rfl, by simp [supportUnion]⟩
  | p, q :: qs, Chain.cons _ _ _ hlink hinter hchain => by
      rcases glue hchain with ⟨r, hrstart, hrsupport⟩
      let s : PathSegment Adj :=
        append p r
          (hlink.trans hrstart.symm)
          (by
            intro v hvp hvr
            exact hinter v hvp (by simpa [hrsupport] using hvr))
      refine ⟨s, ?_, ?_⟩
      · simp [s]
      · simp [s, supportUnion, hrsupport]

/-- The terminal segment of a nonempty chain. -/
def last : ∀ {p : PathSegment Adj} {ps : List (PathSegment Adj)}, Chain (p :: ps) → PathSegment Adj
  | p, [], Chain.singleton _ => p
  | _, q :: _, Chain.cons _ _ _ _ _ hchain => last hchain

/--
Concrete chain-gluing theorem: a composable chain of child spanning paths yields
one spanning path on the union support, from the first entry to the last exit.
-/
def spanningPathOfChain
    {p : PathSegment Adj} {ps : List (PathSegment Adj)}
    (hchain : Chain (p :: ps)) :
    ListSpanningPath Adj (supportUnion (p :: ps)) p.start ((last hchain).finish) :=
  match p, ps, hchain with
  | p, [], Chain.singleton _ =>
      p.path.reindex (by simp [supportUnion]) rfl rfl
  | p, q :: qs, Chain.cons _ _ _ hlink hinter htail =>
      by
        have qpath :
            ListSpanningPath Adj (supportUnion (q :: qs)) q.start ((last htail).finish) :=
          spanningPathOfChain htail
        have qpath' :
            ListSpanningPath Adj (supportUnion (q :: qs)) p.finish ((last htail).finish) := by
          exact qpath.reindex rfl hlink.symm rfl
        exact ListSpanningPath.append_of_support_inter p.path qpath' hinter

end PathSegment

inductive OrderedSegmentFamily (Adj : V → V → Prop) : List (PathSegment Adj) -> Type v
  | nil : OrderedSegmentFamily Adj []
  | singleton (p : PathSegment Adj) : OrderedSegmentFamily Adj [p]
  | cons (p q : PathSegment Adj) (qs : List (PathSegment Adj))
      (hlink : p.finish = q.start)
      (hinter : ∀ v, v ∈ p.support → v ∈ PathSegment.supportUnion (q :: qs) → v = p.finish)
      (tail : OrderedSegmentFamily Adj (q :: qs)) :
      OrderedSegmentFamily Adj (p :: q :: qs)

namespace OrderedSegmentFamily

variable {Adj : V → V → Prop}

/-- The last segment in a nonempty ordered list. -/
def lastSegment (p : PathSegment Adj) : List (PathSegment Adj) → PathSegment Adj
  | [] => p
  | q :: qs => lastSegment q qs

/-- Consecutive segments link correctly across every split of the list. -/
def LinkedAllSplits (segments : List (PathSegment Adj)) : Prop :=
  ∀ xs p q qs, segments = xs ++ p :: q :: qs → p.finish = q.start

/--
At every split of the ordered list, the distinguished head support meets the
union of the remaining supports only at its exit vertex.
-/
def OverlapAllSplits (segments : List (PathSegment Adj)) : Prop :=
  ∀ xs p qs, segments = xs ++ p :: qs →
    ∀ v, v ∈ p.support → v ∈ PathSegment.supportUnion qs → v = p.finish

/--
Convert move-local ordered segment data into the recursive `PathSegment.Chain`
witness needed by `spanningPathOfChain`.
-/
def toChain :
    ∀ {segments : List (PathSegment Adj)}, OrderedSegmentFamily Adj segments →
      PathSegment.Chain segments
  | [], .nil => PathSegment.Chain.nil
  | [p], .singleton _ => PathSegment.Chain.singleton p
  | p :: q :: qs, .cons _ _ _ hlink hinter tail =>
      PathSegment.Chain.cons p q qs hlink hinter (toChain tail)

/-- The terminal segment of a nonempty ordered family. -/
def last :
    ∀ {p : PathSegment Adj} {ps : List (PathSegment Adj)},
      OrderedSegmentFamily Adj (p :: ps) → PathSegment Adj
  | p, [], .singleton _ => p
  | _, _ :: _, .cons _ _ _ _ _ tail => last tail

@[simp] theorem last_toChain :
    ∀ {p : PathSegment Adj} {ps : List (PathSegment Adj)}
      (h : OrderedSegmentFamily Adj (p :: ps)),
      PathSegment.last (toChain h) = last h
  | p, [], .singleton _ => rfl
  | p, q :: qs, .cons _ _ _ _ _ tail => by
      simpa [toChain, PathSegment.last, last] using last_toChain tail

/--
Build ordered-segment data from the more ordinary list-level hypotheses that
appear in a local move proof.
-/
def ofSplits :
    ∀ (segments : List (PathSegment Adj)),
      LinkedAllSplits segments →
      OverlapAllSplits segments →
      OrderedSegmentFamily Adj segments
  | [], _, _ => .nil
  | [p], _, _ => .singleton p
  | p :: q :: qs, hlink, hinter =>
      .cons p q qs
        (hlink [] p q qs rfl)
        (hinter [] p (q :: qs) rfl)
        (ofSplits (q :: qs)
          (by
            intro xs q' r rs hEq
            exact hlink (p :: xs) q' r rs (by
              simpa [List.cons_append] using congrArg (List.cons p) hEq))
          (by
            intro xs q' rs hEq
            exact hinter (p :: xs) q' rs (by
              simpa [List.cons_append] using congrArg (List.cons p) hEq)))

@[simp] theorem last_ofSplits :
    ∀ {p : PathSegment Adj} {ps : List (PathSegment Adj)}
      (hlink : LinkedAllSplits (p :: ps))
      (hoverlap : OverlapAllSplits (p :: ps)),
      last (ofSplits (p :: ps) hlink hoverlap) = lastSegment p ps
  | p, [], _, _ => rfl
  | p, q :: qs, hlink, hoverlap => by
      simp [ofSplits, last, lastSegment, last_ofSplits]

/-- Membership in `supportUnion` is witnessed by membership in one segment support. -/
theorem mem_supportUnion_iff_exists_split
    {v : V} :
    ∀ {segments : List (PathSegment Adj)},
      v ∈ PathSegment.supportUnion segments ↔
        ∃ ys seg zs, segments = ys ++ seg :: zs ∧ v ∈ seg.support
  | [] => by simp [PathSegment.supportUnion]
  | p :: ps => by
      constructor
      · intro hv
        rw [PathSegment.supportUnion_cons, Finset.mem_union] at hv
        rcases hv with hv | hv
        · exact ⟨[], p, ps, rfl, hv⟩
        · rcases (mem_supportUnion_iff_exists_split (segments := ps)).1 hv with ⟨ys, seg, zs, hsplit, hmem⟩
          exact ⟨p :: ys, seg, zs, by simp [hsplit, List.cons_append], hmem⟩
      · rintro ⟨ys, seg, zs, hsplit, hmem⟩
        cases ys with
        | nil =>
            simp [PathSegment.supportUnion_cons, hsplit, hmem]
        | cons y ys =>
            cases hsplit
            rw [PathSegment.supportUnion_cons, Finset.mem_union]
            right
            exact (mem_supportUnion_iff_exists_split (segments := ys ++ seg :: zs)).2
              ⟨ys, seg, zs, rfl, hmem⟩

/--
Consecutive-overlap plus nonconsecutive-disjointness imply the splitwise overlap
condition needed by `ofSplits`.
-/
theorem overlapAllSplits_of_localIntersections
    (segments : List (PathSegment Adj))
    (hconsec :
      ∀ xs p q qs, segments = xs ++ p :: q :: qs →
        ∀ v, v ∈ p.support → v ∈ q.support → v = p.finish)
    (hnonconsec :
      ∀ xs p ms q ys, segments = xs ++ p :: ms ++ q :: ys → ms ≠ [] →
        ∀ v, v ∈ p.support → v ∈ q.support → False) :
    OverlapAllSplits segments := by
  intro xs p qs hsplit v hvp hvtail
  rcases (mem_supportUnion_iff_exists_split (segments := qs)).1 hvtail with
    ⟨ys, q, zs, hqsplit, hvq⟩
  cases ys with
  | nil =>
      exact hconsec xs p q zs (by simpa [hqsplit] using hsplit) v hvp hvq
  | cons y ys =>
      exfalso
      exact hnonconsec xs p (y :: ys) q zs
        (by simpa [hqsplit, List.append_assoc] using hsplit)
        (by simp) v hvp hvq

/--
Local geometry data in the form closest to the manuscript: consecutive child
intersections are the attachment vertices, and nonconsecutive children are disjoint.
-/
structure LocalMoveData
    (Adj : V → V → Prop)
    (parentSupport : Finset V)
    (s t : V) where
  head : PathSegment Adj
  tail : List (PathSegment Adj)
  head_start : head.start = s
  support_union : PathSegment.supportUnion (head :: tail) = parentSupport
  linked : LinkedAllSplits (head :: tail)
  consecutive_overlap :
    ∀ xs p q qs, head :: tail = xs ++ p :: q :: qs →
      ∀ v, v ∈ p.support → v ∈ q.support → v = p.finish
  nonconsecutive_disjoint :
    ∀ xs p ms q ys, head :: tail = xs ++ p :: ms ++ q :: ys → ms ≠ [] →
      ∀ v, v ∈ p.support → v ∈ q.support → False
  last_finish : (lastSegment head tail).finish = t

/--
Direct entry point for the local move step: if the ordered child list satisfies
the splitwise linking and overlap conditions, it yields a spanning path on the
union support from the first entry to the last exit.
-/
def spanningPathOfSplits
    {p : PathSegment Adj} {ps : List (PathSegment Adj)}
    (hlink : LinkedAllSplits (p :: ps))
    (hoverlap : OverlapAllSplits (p :: ps)) :
    ListSpanningPath Adj (PathSegment.supportUnion (p :: ps)) p.start
      ((last (ofSplits (p :: ps) hlink hoverlap)).finish) := by
  let hfamily : OrderedSegmentFamily Adj (p :: ps) := ofSplits (p :: ps) hlink hoverlap
  exact
    (PathSegment.spanningPathOfChain (toChain hfamily)).reindex
      rfl rfl (by simpa [hfamily, last_toChain])

/--
Data for one nonterminal move, stated in the exact form needed to manufacture
the parent spanning path from an ordered list of child spanning paths.
-/
structure MoveStepData
    (Adj : V → V → Prop)
    (parentSupport : Finset V)
    (s t : V) where
  head : PathSegment Adj
  tail : List (PathSegment Adj)
  head_start : head.start = s
  support_union : PathSegment.supportUnion (head :: tail) = parentSupport
  linked : LinkedAllSplits (head :: tail)
  overlap : OverlapAllSplits (head :: tail)
  tail_finish : (last (ofSplits (head :: tail) linked overlap)).finish = t

/--
One-step nonterminal gluing theorem: if a move supplies ordered child spanning
paths together with the splitwise compatibility hypotheses, then Lean produces
the parent spanning path.
-/
def spanningPathOfMoveStep
    {parentSupport : Finset V} {s t : V}
    (step : MoveStepData Adj parentSupport s t) :
    ListSpanningPath Adj parentSupport s t := by
  have hpath :
      ListSpanningPath Adj (PathSegment.supportUnion (step.head :: step.tail))
        step.head.start
        ((last (ofSplits (step.head :: step.tail) step.linked step.overlap)).finish) :=
    spanningPathOfSplits step.linked step.overlap
  exact hpath.reindex
    step.support_union
    step.head_start
    (by simpa [last_ofSplits] using step.tail_finish)

/-- Convert local geometric move data into the splitwise move-step package. -/
def moveStepDataOfLocalMove
    {parentSupport : Finset V} {s t : V}
    (step : LocalMoveData Adj parentSupport s t) :
    MoveStepData Adj parentSupport s t := by
  let hoverlap : OverlapAllSplits (step.head :: step.tail) :=
    overlapAllSplits_of_localIntersections (step.head :: step.tail)
      step.consecutive_overlap step.nonconsecutive_disjoint
  refine
    { head := step.head
      tail := step.tail
      head_start := step.head_start
      support_union := step.support_union
      linked := step.linked
      overlap := hoverlap
      tail_finish := ?_ }
  simpa [hoverlap, last_ofSplits] using step.last_finish

/-- A prescribed spanning path can be used as a degenerate one-child move. -/
def moveStepDataOfOnePath
    {S parentSupport : Finset V} {s t : V}
    (p : ListSpanningPath Adj S s t)
    (hsupport : S = parentSupport) :
    MoveStepData Adj parentSupport s t := by
  classical
  let seg : PathSegment Adj := PathSegment.ofSpanningPath p
  refine
    moveStepDataOfLocalMove
      { head := seg
        tail := []
        head_start := rfl
        support_union := ?_
        linked := ?_
        consecutive_overlap := ?_
        nonconsecutive_disjoint := ?_
        last_finish := ?_ }
  · simpa [seg, PathSegment.ofSpanningPath, PathSegment.supportUnion] using hsupport
  · intro xs p q qs hEq
    have hlen := congrArg List.length hEq
    simp at hlen
    omega
  · intro xs p q qs hEq v hvp hvq
    have hlen := congrArg List.length hEq
    simp at hlen
    omega
  · intro xs p ms q ys hEq hms v hvp hvq
    have hlen := congrArg List.length hEq
    simp at hlen
    omega
  · rfl

/--
Two-child move package: ordered spanning paths `u₀ -> u₁ -> u₂`
whose supports meet only at the attachment vertex form one nonterminal move
step.
-/
def moveStepDataOfTwoPaths
    {S₀ S₁ parentSupport : Finset V} {u₀ u₁ u₂ : V}
    (p₀ : ListSpanningPath Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath Adj S₁ u₁ u₂)
    (hsupport : S₀ ∪ S₁ = parentSupport)
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁) :
    MoveStepData Adj parentSupport u₀ u₂ := by
  classical
  let seg₀ : PathSegment Adj := PathSegment.ofSpanningPath p₀
  let seg₁ : PathSegment Adj := PathSegment.ofSpanningPath p₁
  refine
    moveStepDataOfLocalMove
      { head := seg₀
        tail := [seg₁]
        head_start := rfl
        support_union := ?_
        linked := ?_
        consecutive_overlap := ?_
        nonconsecutive_disjoint := ?_
        last_finish := ?_ }
  · simpa [seg₀, seg₁, PathSegment.ofSpanningPath,
      PathSegment.supportUnion] using hsupport
  · intro xs p q qs hEq
    cases xs with
    | nil =>
        cases hEq
        rfl
    | cons x xs =>
        have hlen := congrArg List.length hEq
        simp at hlen
        omega
  · intro xs p q qs hEq v hvp hvq
    cases xs with
    | nil =>
        cases hEq
        exact hinter₀₁ v hvp hvq
    | cons x xs =>
        have hlen := congrArg List.length hEq
        simp at hlen
        omega
  · intro xs p ms q ys hEq hms v hvp hvq
    cases xs with
    | nil =>
        cases ms with
        | nil =>
            exact False.elim (hms rfl)
        | cons m ms =>
            have hlen := congrArg List.length hEq
            simp at hlen
    | cons x xs =>
        have hlen := congrArg List.length hEq
        simp at hlen
        omega
  · rfl

/--
Three-child move package: ordered spanning paths `u₀ -> u₁ -> u₂ -> u₃`
whose adjacent supports meet only at the attachment vertices and whose first
and third supports are disjoint form one nonterminal move step.
-/
def moveStepDataOfThreePaths
    {S₀ S₁ S₂ parentSupport : Finset V} {u₀ u₁ u₂ u₃ : V}
    (p₀ : ListSpanningPath Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath Adj S₂ u₂ u₃)
    (hsupport : S₀ ∪ S₁ ∪ S₂ = parentSupport)
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False) :
    MoveStepData Adj parentSupport u₀ u₃ := by
  classical
  let seg₀ : PathSegment Adj := PathSegment.ofSpanningPath p₀
  let seg₁ : PathSegment Adj := PathSegment.ofSpanningPath p₁
  let seg₂ : PathSegment Adj := PathSegment.ofSpanningPath p₂
  refine
    moveStepDataOfLocalMove
      { head := seg₀
        tail := [seg₁, seg₂]
        head_start := rfl
        support_union := ?_
        linked := ?_
        consecutive_overlap := ?_
        nonconsecutive_disjoint := ?_
        last_finish := ?_ }
  · simpa [seg₀, seg₁, seg₂, PathSegment.ofSpanningPath,
      PathSegment.supportUnion, Finset.union_assoc] using hsupport
  · intro xs p q qs hEq
    cases xs with
    | nil =>
        cases hEq
        rfl
    | cons x xs =>
        cases xs with
        | nil =>
            cases hEq
            rfl
        | cons y ys =>
            have hlen := congrArg List.length hEq
            simp at hlen
            omega
  · intro xs p q qs hEq v hvp hvq
    cases xs with
    | nil =>
        cases hEq
        exact hinter₀₁ v hvp hvq
    | cons x xs =>
        cases xs with
        | nil =>
            cases hEq
            exact hinter₁₂ v hvp hvq
        | cons y ys =>
            have hlen := congrArg List.length hEq
            simp at hlen
            omega
  · intro xs p ms q ys hEq hms v hvp hvq
    cases xs with
    | nil =>
        cases ms with
        | nil =>
            exact False.elim (hms rfl)
        | cons m ms =>
            cases ms with
            | nil =>
                cases ys with
                | nil =>
                    cases hEq
                    exact hdisj₀₂ v hvp hvq
                | cons y ys =>
                    have hlen := congrArg List.length hEq
                    simp at hlen
            | cons m' ms' =>
                have hlen := congrArg List.length hEq
                simp at hlen
    | cons x xs =>
        have hlen := congrArg List.length hEq
        simp at hlen
        have hms_len : ms.length ≠ 0 := by
          cases ms with
          | nil => exact False.elim (hms rfl)
          | cons m ms => simp
        omega
  · rfl

/--
Cyclic-four move package: four spanning paths arranged around a cycle produce a
parent spanning path after truncating the fourth path just before it returns to
`u₀`.

The resulting move step runs from `u₀` to `x`; the deleted final edge of the
fourth path is intended to be supplied separately as the closing edge.
-/
def moveStepDataOfCyclicFourPaths
    {S₀ S₁ S₂ S₃ parentSupport : Finset V} {u₀ u₁ u₂ u₃ x : V}
    (p₀ : ListSpanningPath Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hsupport : S₀ ∪ S₁ ∪ S₂ ∪ S₃ = parentSupport)
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False) :
    MoveStepData Adj parentSupport u₀ x := by
  classical
  let q₀₁₂ : ListSpanningPath Adj (S₀ ∪ S₁ ∪ S₂) u₀ u₃ :=
    spanningPathOfMoveStep
      (moveStepDataOfThreePaths
        (parentSupport := S₀ ∪ S₁ ∪ S₂)
        p₀ p₁ p₂ rfl hinter₀₁ hinter₁₂ hdisj₀₂)
  let q₃ := p₃.truncateFinish middle₃ x htail₃
  have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
  have hsupportEraseFull :
      (S₀ ∪ S₁ ∪ S₂) ∪ S₃.erase u₀ = S₀ ∪ S₁ ∪ S₂ ∪ S₃ := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Finset.mem_of_mem_erase hv)
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · by_cases hvu₀ : v = u₀
        · exact Or.inl (by simpa [hvu₀, hu₀, Finset.mem_union])
        · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
  have hsupportErase :
      (S₀ ∪ S₁ ∪ S₂) ∪ S₃.erase u₀ = parentSupport :=
    hsupportEraseFull.trans hsupport
  have hinter₀₁₂₃ :
      ∀ v, v ∈ S₀ ∪ S₁ ∪ S₂ → v ∈ S₃.erase u₀ → v = u₃ := by
    intro v hv hv₃
    rcases Finset.mem_erase.mp hv₃ with ⟨hvne, hv₃'⟩
    rw [Finset.mem_union] at hv
    rcases hv with hv₀₁ | hv₂
    · rw [Finset.mem_union] at hv₀₁
      rcases hv₀₁ with hv₀ | hv₁
      · exfalso
        exact hvne (hinter₃₀ v hv₃' hv₀)
      · exact False.elim (hdisj₁₃ v hv₁ hv₃')
    · exact hinter₂₃ v hv₂ hv₃'
  exact
    moveStepDataOfTwoPaths q₀₁₂ q₃ hsupportErase hinter₀₁₂₃

/--
A terminal cell witnessed by a simple boundary cycle with designated closing edge.
Removing the closing edge yields the spanning path used in the terminal base case.
-/
structure BoundaryCycleWitness
    (Adj : V → V → Prop)
    (support : Finset V)
    (s t : V) where
  middle : List V
  cycle_adj : ∀ ⦃a b⦄, (a, b) ∈ edgePairs (s :: (middle ++ [t, s])) → Adj a b
  nodup : List.Nodup (s :: (middle ++ [t]))
  spans : ∀ v, v ∈ support ↔ v ∈ s :: (middle ++ [t])

/-- Change only the finite support index of a boundary-cycle witness. -/
def BoundaryCycleWitness.castSupport
    {support support' : Finset V}
    {s t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (h : support = support') :
    BoundaryCycleWitness Adj support' s t where
  middle := w.middle
  cycle_adj := w.cycle_adj
  nodup := w.nodup
  spans := by
    intro v
    rw [← h]
    exact w.spans v

@[simp] theorem BoundaryCycleWitness.castSupport_middle
    {support support' : Finset V}
    {s t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (h : support = support') :
    (w.castSupport h).middle = w.middle := rfl

/-- Formal version of the terminal boundary-path construction. -/
def BoundaryCycleWitness.toSpanningPath
    {support : Finset V} {s t : V}
    (w : BoundaryCycleWitness Adj support s t) :
    ListSpanningPath Adj support s t where
  tail := w.middle ++ [t]
  ends_at := by
    rw [endVertex_append]
    simp [endVertex]
  adj := by
    intro a b hab
    have hab' : (a, b) ∈ edgePairs (s :: ((w.middle ++ [t]) ++ [s])) := by
      rw [edgePairs_append]
      exact List.mem_append.2 (Or.inl hab)
    exact w.cycle_adj (by simpa using hab')
  nodup := by
    simpa using w.nodup
  spans := by
    simpa using w.spans

/--
If a `P4` occurs on the cyclic boundary list and its final edge is not the
designated closing edge `t - s`, then the same `P4` already occurs on the
opened boundary path obtained by deleting that closing edge.
-/
theorem BoundaryCycleWitness.path3_infix_of_cycleInfix_of_ne_closing
    {support : Finset V} {s t a b c d : V}
    (w : BoundaryCycleWitness Adj support s t)
    (hinfix : [a, b, c, d] <:+: s :: (w.middle ++ [t, s]))
    (hcd : (c, d) ≠ (t, s)) :
    [a, b, c, d] <:+: s :: w.toSpanningPath.tail := by
  let l : List V := s :: (w.middle ++ [t])
  have hl : s :: w.toSpanningPath.tail = l := by
    rfl
  have hcycle : s :: (w.middle ++ [t, s]) = l ++ [s] := by
    simp [l, List.append_assoc]
  by_cases hopen : [a, b, c, d] <:+: l
  · simpa [hl] using hopen
  · rcases hinfix with ⟨xs, ys, hsplit⟩
    rcases List.eq_nil_or_concat' ys with hys | ⟨ys', y, hys⟩
    · subst hys
      have hd : d = s := by
        have hlast := congrArg List.getLast? hsplit
        have hleft : (xs ++ [a, b, c, d]).getLast? = some d := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (xs ++ [a, b, c]) (by simp : ([d] : List V) ≠ []))
        have hright : (l ++ [s]).getLast? = some s := by
          simpa [l] using
            (List.getLast?_append_of_ne_nil l (by simp : ([s] : List V) ≠ []))
        have hdOpt : some d = some s := by
          calc
            some d = (xs ++ [a, b, c, d]).getLast? := by simpa using hleft.symm
            _ = (l ++ [s]).getLast? := by simpa [hcycle] using hlast
            _ = some s := hright
        exact Option.some.inj hdOpt
      have hcancel : xs ++ [a, b, c] = l := by
        apply (List.append_left_injective [s])
        simpa [l, hd, List.append_assoc] using hsplit
      have hc : c = t := by
        have hlast := congrArg List.getLast? hcancel
        have hleft : (xs ++ [a, b, c]).getLast? = some c := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (xs ++ [a, b]) (by simp : ([c] : List V) ≠ []))
        have hright : l.getLast? = some t := by
          simpa [l, List.append_assoc] using
            (List.getLast?_append_of_ne_nil (s :: w.middle) (by simp : ([t] : List V) ≠ []))
        have hcOpt : some c = some t := by
          calc
            some c = (xs ++ [a, b, c]).getLast? := by simpa using hleft.symm
            _ = l.getLast? := hlast
            _ = some t := hright
        exact Option.some.inj hcOpt
      exact False.elim (hcd <| by simpa [hc, hd])
    · have hy : y = s := by
        have hlast := congrArg List.getLast? hsplit
        have hleft :
            (xs ++ [a, b, c, d] ++ ys' ++ [y]).getLast? = some y := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (xs ++ [a, b, c, d] ++ ys')
              (by simp : ([y] : List V) ≠ []))
        have hright : (l ++ [s]).getLast? = some s := by
          simpa [l] using
            (List.getLast?_append_of_ne_nil l (by simp : ([s] : List V) ≠ []))
        have hyOpt : some y = some s := by
          calc
            some y = (xs ++ [a, b, c, d] ++ (ys' ++ [y])).getLast? := by
              simpa [hys, List.append_assoc] using hleft.symm
            _ = (l ++ [s]).getLast? := by
              simpa [hcycle, hys] using hlast
            _ = some s := hright
        exact Option.some.inj hyOpt
      have hopen' : [a, b, c, d] <:+: l := by
        refine ⟨xs, ys', ?_⟩
        apply (List.append_left_injective [s])
        simpa [l, hys, hy, List.append_assoc] using hsplit
      exact False.elim (hopen hopen')

/--
If an edge occurs on the cyclic boundary list and is not the designated closing
edge `t - s`, then it already occurs on the opened boundary path obtained by
deleting that closing edge.
-/
theorem BoundaryCycleWitness.edge_infix_of_cycleInfix_of_ne_closing
    {support : Finset V} {s t a b : V}
    (w : BoundaryCycleWitness Adj support s t)
    (hinfix : [a, b] <:+: s :: (w.middle ++ [t, s]))
    (hab : (a, b) ≠ (t, s)) :
    [a, b] <:+: s :: w.toSpanningPath.tail := by
  let l : List V := s :: (w.middle ++ [t])
  have hl : s :: w.toSpanningPath.tail = l := by
    rfl
  have hcycle : s :: (w.middle ++ [t, s]) = l ++ [s] := by
    simp [l, List.append_assoc]
  by_cases hopen : [a, b] <:+: l
  · simpa [hl] using hopen
  · rcases hinfix with ⟨xs, ys, hsplit⟩
    rcases List.eq_nil_or_concat' ys with hys | ⟨ys', y, hys⟩
    · subst hys
      have hb : b = s := by
        have hlast := congrArg List.getLast? hsplit
        have hleft : (xs ++ [a, b]).getLast? = some b := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil xs (by simp : ([a, b] : List V) ≠ []))
        have hright : (l ++ [s]).getLast? = some s := by
          simpa [l] using
            (List.getLast?_append_of_ne_nil l (by simp : ([s] : List V) ≠ []))
        have hbOpt : some b = some s := by
          calc
            some b = (xs ++ [a, b]).getLast? := by simpa using hleft.symm
            _ = (l ++ [s]).getLast? := by simpa [hcycle] using hlast
            _ = some s := hright
        exact Option.some.inj hbOpt
      have hcancel : xs ++ [a] = l := by
        apply (List.append_left_injective [s])
        simpa [l, hb, List.append_assoc] using hsplit
      have ha : a = t := by
        have hlast := congrArg List.getLast? hcancel
        have hleft : (xs ++ [a]).getLast? = some a := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil xs (by simp : ([a] : List V) ≠ []))
        have hright : l.getLast? = some t := by
          simpa [l, List.append_assoc] using
            (List.getLast?_append_of_ne_nil (s :: w.middle) (by simp : ([t] : List V) ≠ []))
        have haOpt : some a = some t := by
          calc
            some a = (xs ++ [a]).getLast? := by simpa using hleft.symm
            _ = l.getLast? := hlast
            _ = some t := hright
        exact Option.some.inj haOpt
      exact False.elim (hab <| by simpa [ha, hb])
    · have hy : y = s := by
        have hlast := congrArg List.getLast? hsplit
        have hleft : (xs ++ [a, b] ++ ys' ++ [y]).getLast? = some y := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (xs ++ [a, b] ++ ys')
              (by simp : ([y] : List V) ≠ []))
        have hright : (l ++ [s]).getLast? = some s := by
          simpa [l] using
            (List.getLast?_append_of_ne_nil l (by simp : ([s] : List V) ≠ []))
        have hyOpt : some y = some s := by
          calc
            some y = (xs ++ [a, b] ++ (ys' ++ [y])).getLast? := by
              simpa [hys, List.append_assoc] using hleft.symm
            _ = (l ++ [s]).getLast? := by
              simpa [hcycle, hys] using hlast
            _ = some s := hright
        exact Option.some.inj hyOpt
      have hopen' : [a, b] <:+: l := by
        refine ⟨xs, ys', ?_⟩
        apply (List.append_left_injective [s])
        simpa [l, hys, hy, List.append_assoc] using hsplit
      exact False.elim (hopen hopen')

/--
If an internal edge `u - v` remains on the opened boundary path, cutting there
produces the two complementary path pieces from `s` to `u` and from `v` to `t`.
-/
theorem BoundaryCycleWitness.extractPairOfInternalEdge
    {support : Finset V} {s t u v : V}
    (w : BoundaryCycleWitness Adj support s t)
    (hinfix : [u, v] <:+: s :: (w.middle ++ [t, s]))
    (huv : (u, v) ≠ (t, s))
    (hsu : s ≠ u)
    (hvt : v ≠ t) :
    ∃ xs ys,
      Nonempty
        (ListSpanningPath Adj ((s :: (xs ++ [u])).toFinset) s u ×
          ListSpanningPath Adj ((v :: (ys ++ [t])).toFinset) v t) := by
  have hopen : [u, v] <:+: s :: w.toSpanningPath.tail :=
    w.edge_infix_of_cycleInfix_of_ne_closing hinfix huv
  rcases hopen with ⟨xs, ys, hsplit⟩
  have hxs_ne : xs ≠ [] := by
    intro hnil
    have hhead := congrArg List.head? hsplit
    simp [hnil] at hhead
    exact hsu hhead.symm
  obtain ⟨x, xs', hxs⟩ := List.exists_cons_of_ne_nil hxs_ne
  have hx : x = s := by
    have hhead := congrArg List.head? hsplit
    simp [hxs] at hhead
    exact hhead
  rcases List.eq_nil_or_concat' ys with hys | ⟨ys', y, hys⟩
  · subst hys
    have hlast := congrArg List.getLast? hsplit
    have hleft : (s :: (xs' ++ [u, v])).getLast? = some v := by
      simpa [List.append_assoc] using
        (List.getLast?_append_of_ne_nil (s :: (xs' ++ [u]))
          (by simp : ([v] : List V) ≠ []))
    have hright : (s :: (w.middle ++ [t])).getLast? = some t := by
      simpa [BoundaryCycleWitness.toSpanningPath, List.append_assoc] using
        (List.getLast?_append_of_ne_nil (s :: w.middle)
          (by simp : ([t] : List V) ≠ []))
    have hvt' : some v = some t := by
      calc
        some v = (s :: (xs' ++ [u, v])).getLast? := by simpa using hleft.symm
        _ = (s :: (w.middle ++ [t])).getLast? := by simpa [BoundaryCycleWitness.toSpanningPath, hxs, hx] using hlast
        _ = some t := hright
    exact False.elim (hvt (Option.some.inj hvt'))
  · have hy : y = t := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (s :: (xs' ++ u :: v :: (ys' ++ [y]))).getLast? = some y := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (s :: (xs' ++ u :: v :: ys'))
            (by simp : ([y] : List V) ≠ []))
      have hright : (s :: (w.middle ++ [t])).getLast? = some t := by
        simpa [BoundaryCycleWitness.toSpanningPath, List.append_assoc] using
          (List.getLast?_append_of_ne_nil (s :: w.middle)
            (by simp : ([t] : List V) ≠ []))
      have hyt : some y = some t := by
        calc
          some y = (s :: (xs' ++ u :: v :: (ys' ++ [y]))).getLast? := by simpa using hleft.symm
          _ = (s :: (w.middle ++ [t])).getLast? := by
              simpa [BoundaryCycleWitness.toSpanningPath, hxs, hx, hys, List.append_assoc] using hlast
          _ = some t := hright
      exact Option.some.inj hyt
    have hmid : w.middle = xs' ++ u :: v :: ys' := by
      have htail : w.middle ++ [t] = (xs' ++ u :: v :: ys') ++ [t] := by
        simpa [BoundaryCycleWitness.toSpanningPath, hxs, hx, hys, hy, List.append_assoc] using hsplit.symm
      exact (List.append_left_injective [t]) htail
    refine ⟨xs', ys', ⟨?_, ?_⟩⟩
    · let p := w.toSpanningPath
      have htail :
          p.tail = xs' ++ u :: (v :: ys' ++ [t]) := by
        simp [p, BoundaryCycleWitness.toSpanningPath, hmid, List.append_assoc]
      simpa [p, List.append_assoc] using
        p.takePrefix xs' u (v :: ys' ++ [t]) htail
    · let p := w.toSpanningPath
      have htail :
          p.tail = (xs' ++ [u]) ++ v :: (ys' ++ [t]) := by
        simp [p, BoundaryCycleWitness.toSpanningPath, hmid, List.append_assoc]
      simpa [p, List.append_assoc] using
        p.dropPrefix (xs' ++ [u]) v (ys' ++ [t]) htail

/--
If the boundary cycle list ends with `u, t, s`, then the edge `u - t` is present.
-/
theorem BoundaryCycleWitness.closingEdge_of_split
    {support : Finset V} {s t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (middle : List V) (u : V)
    (hmid : w.middle = middle ++ [u]) :
    Adj u t := by
  have hmem : (u, t) ∈ edgePairs (s :: (w.middle ++ [t, s])) := by
    have hend : endVertex s (middle ++ [u]) = u := by
      rw [endVertex_append]
      simp [endVertex]
    have : (u, t) ∈ edgePairs (s :: ((middle ++ [u]) ++ [t, s])) := by
      rw [edgePairs_append]
      exact List.mem_append.2 (Or.inr (by simpa [hend, edgePairs]))
    simpa [hmid, List.append_assoc] using this
  exact w.cycle_adj hmem

/--
Extract the initial path segment obtained by cutting a boundary cycle witness at
an internal edge `u - v`.
-/
def BoundaryCycleWitness.takeUntilInternalEdge
    {support : Finset V} {s t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (xs : List V) (u v : V) (ys : List V)
    (hmid : w.middle = xs ++ u :: v :: ys) :
    ListSpanningPath Adj ((s :: (xs ++ [u])).toFinset) s u := by
  let p := w.toSpanningPath
  have htail : p.tail = xs ++ u :: (v :: ys ++ [t]) := by
    simp [p, BoundaryCycleWitness.toSpanningPath, hmid, List.append_assoc]
  simpa [p, List.append_assoc] using
    p.takePrefix xs u (v :: ys ++ [t]) htail

@[simp] theorem BoundaryCycleWitness.takeUntilInternalEdge_tail
    {support : Finset V} {s t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (xs : List V) (u v : V) (ys : List V)
    (hmid : w.middle = xs ++ u :: v :: ys) :
    (w.takeUntilInternalEdge xs u v ys hmid).tail = xs ++ [u] := by
  simp [BoundaryCycleWitness.takeUntilInternalEdge, ListSpanningPath.takePrefix,
    BoundaryCycleWitness.toSpanningPath, hmid, List.append_assoc]

theorem BoundaryCycleWitness.takeUntilInternalEdge_tail_of_start_eq
    {support : Finset V} {s s' t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (hs : s = s')
    (xs : List V) (u v : V) (ys : List V)
    (hmid : w.middle = xs ++ u :: v :: ys) :
    ((by
        simpa [hs] using
          w.takeUntilInternalEdge xs u v ys hmid :
        ListSpanningPath Adj ((s' :: (xs ++ [u])).toFinset) s' u)).tail = xs ++ [u] := by
  subst hs
  simpa using w.takeUntilInternalEdge_tail xs u v ys hmid

/--
Extract the terminal path segment obtained by cutting a boundary cycle witness at
an internal edge `u - v`.
-/
def BoundaryCycleWitness.dropUntilInternalEdge
    {support : Finset V} {s t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (xs : List V) (u v : V) (ys : List V)
    (hmid : w.middle = xs ++ u :: v :: ys) :
    ListSpanningPath Adj ((v :: (ys ++ [t])).toFinset) v t := by
  let p := w.toSpanningPath
  have htail : p.tail = (xs ++ [u]) ++ v :: (ys ++ [t]) := by
    simp [p, BoundaryCycleWitness.toSpanningPath, hmid, List.append_assoc]
  simpa [p, List.append_assoc] using
    p.dropPrefix (xs ++ [u]) v (ys ++ [t]) htail

@[simp] theorem BoundaryCycleWitness.dropUntilInternalEdge_tail
    {support : Finset V} {s t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (xs : List V) (u v : V) (ys : List V)
    (hmid : w.middle = xs ++ u :: v :: ys) :
    (w.dropUntilInternalEdge xs u v ys hmid).tail = ys ++ [t] := by
  simp [BoundaryCycleWitness.dropUntilInternalEdge, ListSpanningPath.dropPrefix,
    BoundaryCycleWitness.toSpanningPath, hmid, List.append_assoc]

theorem BoundaryCycleWitness.takeUntilInternalEdge_path3_infix
    {support : Finset V} {s t u v a b c d : V}
    (w : BoundaryCycleWitness Adj support s t)
    (xs : List V) (u v : V) (ys : List V)
    (hmid : w.middle = xs ++ u :: v :: ys)
    (hinfix : [a, b, c, d] <:+: s :: (xs ++ [u])) :
    [a, b, c, d] <:+:
      s :: (w.takeUntilInternalEdge xs u v ys hmid).tail := by
  simpa [BoundaryCycleWitness.takeUntilInternalEdge, hmid, List.append_assoc] using hinfix

theorem BoundaryCycleWitness.dropUntilInternalEdge_path3_infix
    {support : Finset V} {s t u v a b c d : V}
    (w : BoundaryCycleWitness Adj support s t)
    (xs : List V) (u v : V) (ys : List V)
    (hmid : w.middle = xs ++ u :: v :: ys)
    (hinfix : [a, b, c, d] <:+: v :: (ys ++ [t])) :
    [a, b, c, d] <:+:
      v :: (w.dropUntilInternalEdge xs u v ys hmid).tail := by
  simpa [BoundaryCycleWitness.dropUntilInternalEdge, hmid, List.append_assoc] using hinfix

/--
Delete the terminal vertex `t` from a boundary cycle witness and keep the last
predecessor `u` as the new endpoint.
-/
def BoundaryCycleWitness.truncateFinish
    {support : Finset V} {s t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (middle : List V) (u : V)
    (hmid : w.middle = middle ++ [u]) :
    ListSpanningPath Adj (support.erase t) s u where
  tail := middle ++ [u]
  ends_at := by
    rw [endVertex_append]
    simp [endVertex]
  adj := by
    intro a b hab
    have hab' : (a, b) ∈ edgePairs (s :: ((middle ++ [u]) ++ [t, s])) := by
      rw [edgePairs_append]
      exact List.mem_append.2 (Or.inl hab)
    exact w.cycle_adj (by simpa [hmid, List.append_assoc] using hab')
  nodup := by
    have hpref : s :: (middle ++ [u]) <+: s :: (middle ++ [u, t]) := by
      use [t]
      simp [List.append_assoc]
    exact hpref.nodup (by simpa [hmid, List.append_assoc] using w.nodup)
  spans := by
    have htNotMem : t ∉ s :: (middle ++ [u]) := by
      have hnodup :
          List.Nodup ((s :: (middle ++ [u])) ++ [t]) := by
        simpa [hmid, List.append_assoc] using w.nodup
      rw [List.nodup_append] at hnodup
      intro ht
      exact hnodup.2.2 t ht t (by simp) rfl
    intro v
    constructor
    · intro hv
      rw [Finset.mem_erase] at hv
      rcases hv with ⟨hvt, hv⟩
      have hv' : v ∈ s :: (middle ++ [u, t]) := by
        simpa [hmid, List.append_assoc] using (w.spans v).1 hv
      simpa [List.append_assoc, hvt] using hv'
    · intro hv
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hvt
        have hnodup :
            List.Nodup ((s :: (middle ++ [u])) ++ [t]) := by
          simpa [hmid, List.append_assoc] using w.nodup
        rw [List.nodup_append] at hnodup
        have hdisj := hnodup.2.2
        exact hdisj v (by simpa using hv) t (by simp) hvt
      · exact (w.spans v).2 (by
          have hv' : v ∈ s :: (middle ++ [u, t]) := by
            simpa [List.append_assoc] using
              (List.mem_append.2 (Or.inl hv) : v ∈ (s :: (middle ++ [u])) ++ [t])
          simpa [hmid, List.append_assoc] using hv')

/--
Transport a boundary-cycle witness across an implication on the cycle edges it
actually uses.
-/
def BoundaryCycleWitness.transportAdj
    {Adj' : V → V → Prop}
    {support : Finset V} {s t : V}
    (w : BoundaryCycleWitness Adj support s t)
    (htransport :
      ∀ ⦃u v⦄, (u, v) ∈ edgePairs (s :: (w.middle ++ [t, s])) → Adj u v → Adj' u v) :
    BoundaryCycleWitness Adj' support s t where
  middle := w.middle
  cycle_adj := by
    intro u v huv
    exact htransport huv (w.cycle_adj huv)
  nodup := w.nodup
  spans := w.spans

/-- A terminal child cell presented by its boundary cycle. -/
structure TerminalPiece (Adj : V → V → Prop) where
  support : Finset V
  start : V
  finish : V
  boundary : BoundaryCycleWitness Adj support start finish

namespace TerminalPiece

/-- View a terminal piece as the path segment obtained by deleting its closing edge. -/
def toPathSegment (p : TerminalPiece Adj) : PathSegment Adj where
  support := p.support
  start := p.start
  finish := p.finish
  path := p.boundary.toSpanningPath

end TerminalPiece

/--
Concrete depth-1 move data: the parent is decomposed into an ordered chain of
terminal child cells, each already certified by a boundary cycle witness.
-/
structure TerminalMoveData
    (Adj : V → V → Prop)
    (parentSupport : Finset V)
    (s t : V) where
  head : TerminalPiece Adj
  tail : List (TerminalPiece Adj)
  head_start : head.start = s
  support_union :
    PathSegment.supportUnion
      (head.toPathSegment :: tail.map TerminalPiece.toPathSegment) = parentSupport
  linked :
    LinkedAllSplits (head.toPathSegment :: tail.map TerminalPiece.toPathSegment)
  consecutive_overlap :
    ∀ xs p q qs,
      head.toPathSegment :: tail.map TerminalPiece.toPathSegment = xs ++ p :: q :: qs →
      ∀ v, v ∈ p.support → v ∈ q.support → v = p.finish
  nonconsecutive_disjoint :
    ∀ xs p ms q ys,
      head.toPathSegment :: tail.map TerminalPiece.toPathSegment = xs ++ p :: ms ++ q :: ys →
      ms ≠ [] →
      ∀ v, v ∈ p.support → v ∈ q.support → False
  last_finish :
    (lastSegment head.toPathSegment
      (tail.map TerminalPiece.toPathSegment)).finish = t

/-- Forget that the child segments come from terminal cells and recover local move data. -/
def TerminalMoveData.toLocalMoveData
    {parentSupport : Finset V} {s t : V}
    (step : TerminalMoveData Adj parentSupport s t) :
    LocalMoveData Adj parentSupport s t where
  head := step.head.toPathSegment
  tail := step.tail.map TerminalPiece.toPathSegment
  head_start := step.head_start
  support_union := step.support_union
  linked := step.linked
  consecutive_overlap := step.consecutive_overlap
  nonconsecutive_disjoint := step.nonconsecutive_disjoint
  last_finish := step.last_finish

/--
Matching-theoretic decomposition pieces. The terminology is meant to line up with
brick/brace decompositions, while deferring the actual matching-theoretic axioms.
-/
inductive BrickBraceKind
  | brick
  | brace
  deriving DecidableEq, Repr

/-- A brick/brace piece together with its local spanning segment. -/
structure BrickBracePiece (Adj : V → V → Prop) where
  kind : BrickBraceKind
  segment : PathSegment Adj

namespace BrickBrace

variable {Adj : V → V → Prop}

/-- Forget the labels and keep only the ordered segment list. -/
def segments : List (BrickBracePiece Adj) → List (PathSegment Adj)
  | [] => []
  | p :: ps => p.segment :: segments ps

@[simp] theorem segments_nil :
    segments ([] : List (BrickBracePiece Adj)) = [] := rfl

@[simp] theorem segments_cons (p : BrickBracePiece Adj) (ps : List (BrickBracePiece Adj)) :
    segments (p :: ps) = p.segment :: segments ps := rfl

/-- The last labeled piece in a nonempty list. -/
def lastPiece (p : BrickBracePiece Adj) : List (BrickBracePiece Adj) → BrickBracePiece Adj
  | [] => p
  | q :: qs => lastPiece q qs

@[simp] theorem lastSegment_of_pieces
    (p : BrickBracePiece Adj) (ps : List (BrickBracePiece Adj)) :
    OrderedSegmentFamily.lastSegment p.segment (segments ps) = (lastPiece p ps).segment := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih =>
      simpa [OrderedSegmentFamily.lastSegment, lastPiece] using ih q

/-- Consecutive-linking hypothesis for an ordered brick/brace list. -/
def LinkedAllSplits (pieces : List (BrickBracePiece Adj)) : Prop :=
  OrderedSegmentFamily.LinkedAllSplits (segments pieces)

/-- Tail-overlap hypothesis for an ordered brick/brace list. -/
def OverlapAllSplits (pieces : List (BrickBracePiece Adj)) : Prop :=
  OrderedSegmentFamily.OverlapAllSplits (segments pieces)

/-- Local move data expressed in brick/brace language. -/
structure MoveData
    (Adj : V → V → Prop)
    (parentSupport : Finset V)
    (s t : V) where
  head : BrickBracePiece Adj
  tail : List (BrickBracePiece Adj)
  head_start : head.segment.start = s
  support_union : PathSegment.supportUnion (segments (head :: tail)) = parentSupport
  linked : LinkedAllSplits (head :: tail)
  overlap : OverlapAllSplits (head :: tail)
  tail_finish : (lastPiece head tail).segment.finish = t

/-- Forget the labels and recover the segment-level one-step move data. -/
def toMoveStepData
    {parentSupport : Finset V} {s t : V}
    (step : MoveData Adj parentSupport s t) :
    OrderedSegmentFamily.MoveStepData Adj parentSupport s t := by
  refine
    { head := step.head.segment
      tail := segments step.tail
      head_start := step.head_start
      support_union := step.support_union
      linked := step.linked
      overlap := step.overlap
      tail_finish := ?_ }
  simpa [lastSegment_of_pieces, OrderedSegmentFamily.last_ofSplits] using step.tail_finish

/-- Brick/brace move theorem: a compatible ordered piece list yields the parent path. -/
def spanningPathOfMoveData
    {parentSupport : Finset V} {s t : V}
    (step : MoveData Adj parentSupport s t) :
    ListSpanningPath Adj parentSupport s t :=
  OrderedSegmentFamily.spanningPathOfMoveStep (toMoveStepData step)

end BrickBrace

end OrderedSegmentFamily

end ConcreteSpanningPaths

section MatchingTheory

variable {V : Type v} [DecidableEq V]

/--
An undirected edge recorded by its two endpoints. The order is irrelevant at the
level of graph properties; we account for that in `EdgeOn`.
-/
structure Edge (V : Type v) where
  u : V
  v : V
  distinct : u ≠ v
  deriving DecidableEq, Repr

namespace Edge

/-- The two endpoints of an edge as a finite support. -/
def support (e : Edge V) : Finset V :=
  {e.u, e.v}

@[simp] theorem mem_support_left (e : Edge V) : e.u ∈ e.support := by
  simp [support]

@[simp] theorem mem_support_right (e : Edge V) : e.v ∈ e.support := by
  simp [support]

def Disjoint (e f : Edge V) : Prop :=
  _root_.Disjoint e.support f.support

end Edge

/-- `e` is an edge of the graph induced by `Adj` on the finite support. -/
def EdgeOn (support : Finset V) (Adj : V → V → Prop) (e : Edge V) : Prop :=
  e.u ∈ support ∧ e.v ∈ support ∧ (Adj e.u e.v ∨ Adj e.v e.u)

/-- A finite set of pairwise vertex-disjoint edges. -/
def IsMatching (M : Finset (Edge V)) : Prop :=
  ∀ ⦃e f⦄, e ∈ M → f ∈ M → e ≠ f → Edge.Disjoint e f

/--
A perfect matching on a finite support: every edge lies in the graph, the edges
are pairwise disjoint, every support vertex is covered, and no outside vertex is.
-/
structure PerfectMatchingOn
    (support : Finset V)
    (Adj : V → V → Prop)
    (M : Finset (Edge V)) : Prop where
  edges_on : ∀ ⦃e⦄, e ∈ M → EdgeOn support Adj e
  matching : IsMatching M
  cover_in : ∀ v, v ∈ support → ∃ e ∈ M, v ∈ e.support
  cover_out : ∀ ⦃e v⦄, e ∈ M → v ∈ e.support → v ∈ support

/-- Every edge of the graph belongs to some perfect matching. -/
def MatchingCoveredOn (support : Finset V) (Adj : V → V → Prop) : Prop :=
  ∀ e, EdgeOn support Adj e → ∃ M, PerfectMatchingOn support Adj M ∧ e ∈ M

/-- A bipartition of the finite support compatible with the graph adjacency. -/
structure Bipartition
    (support : Finset V)
    (Adj : V → V → Prop) where
  left : Finset V
  right : Finset V
  cover : left ∪ right = support
  disjoint : Disjoint left right
  edges_cross :
    ∀ ⦃u v⦄, u ∈ support → v ∈ support → (Adj u v ∨ Adj v u) →
      (u ∈ left ∧ v ∈ right) ∨ (u ∈ right ∧ v ∈ left)

/--
Minimal brace predicate modeled on the matching-theory paper: bipartite, and any
two disjoint edges are contained in one perfect matching of the support graph.

We intentionally omit the exceptional path-of-length-three clause for now; that
exception can be added once an actual graph datatype is fixed.
-/
def BraceOn (support : Finset V) (Adj : V → V → Prop) : Prop :=
  ∃ _bip : Bipartition support Adj,
    ∀ e f, EdgeOn support Adj e → EdgeOn support Adj f → Edge.Disjoint e f →
      ∃ M, PerfectMatchingOn support Adj M ∧ e ∈ M ∧ f ∈ M

/--
Minimal brick predicate: matching-covered and not bipartite. This matches the
standard brick/brace dichotomy only at the level needed for future encoding.
-/
def BrickOn (support : Finset V) (Adj : V → V → Prop) : Prop :=
  MatchingCoveredOn support Adj ∧ ¬ Nonempty (Bipartition support Adj)

/-- A graph piece is brick-or-brace if it satisfies one of the two predicates. -/
def BrickOrBraceOn (support : Finset V) (Adj : V → V → Prop) : Prop :=
  BrickOn support Adj ∨ BraceOn support Adj

end MatchingTheory

section GraphTargets

variable {V : Type v} [DecidableEq V]

/-- A minimal finite simple graph model on a distinguished finite support. -/
structure FiniteSimpleGraph where
  support : Finset V
  Adj : V → V → Prop
  symm : Symmetric Adj
  loopless : ∀ v, ¬ Adj v v

/--
A Hamiltonian cycle on the finite support, encoded by an oriented cycle list
whose vertices are exactly the support vertices.
-/
structure HamiltonianCycleWitness
    (Adj : V → V → Prop)
    (support : Finset V) where
  start : V
  tail : List V
  cycle_adj : ∀ ⦃a b⦄, (a, b) ∈ edgePairs (start :: (tail ++ [start])) → Adj a b
  nodup : List.Nodup (start :: tail)
  spans : ∀ v, v ∈ support ↔ v ∈ start :: tail

def HamiltonianOn (support : Finset V) (Adj : V → V → Prop) : Prop :=
  Nonempty (HamiltonianCycleWitness Adj support)

/-- Transport a Hamiltonian cycle witness across an equality of support finsets. -/
def HamiltonianCycleWitness.castSupport
    {Adj : V → V → Prop} {S T : Finset V}
    (w : HamiltonianCycleWitness Adj S)
    (hST : S = T) :
    HamiltonianCycleWitness Adj T where
  start := w.start
  tail := w.tail
  cycle_adj := w.cycle_adj
  nodup := w.nodup
  spans := by
    intro v
    simpa [hST] using w.spans v

/-- Graph-level Hamiltonicity predicate. -/
def FiniteSimpleGraph.Hamiltonian (G : FiniteSimpleGraph (V := V)) : Prop :=
  HamiltonianOn G.support G.Adj

/--
Concrete closing lemma: a spanning path together with an edge from its terminal
vertex back to its initial vertex yields a Hamiltonian cycle.
-/
def hamiltonianCycleWitnessOfSpanningPath
    {support : Finset V} {Adj : V → V → Prop} {s t : V}
    (p : ListSpanningPath Adj support s t)
    (hclose : Adj t s) :
    HamiltonianCycleWitness Adj support where
  start := s
  tail := p.tail
  cycle_adj := by
    intro a b hab
    rw [edgePairs_append] at hab
    rcases List.mem_append.1 hab with hab | hab
    · exact p.adj hab
    · have : (a, b) = (t, s) := by
          simpa [edgePairs, p.ends_at] using hab
      rcases this with ⟨rfl, rfl⟩
      exact hclose
  nodup := p.nodup
  spans := p.spans

/-- The witness built from a spanning path has the expected explicit support list. -/
@[simp] theorem hamiltonianCycleWitnessOfSpanningPath_support
    {support : Finset V} {Adj : V → V → Prop} {s t : V}
    (p : ListSpanningPath Adj support s t)
    (hclose : Adj t s) :
    (hamiltonianCycleWitnessOfSpanningPath p hclose).start ::
        ((hamiltonianCycleWitnessOfSpanningPath p hclose).tail ++
          [(hamiltonianCycleWitnessOfSpanningPath p hclose).start]) =
      s :: (p.tail ++ [s]) := by
  rfl

/--
Appending extra suffix data preserves any existing contiguous infix.
-/
theorem List.infix_append_right
    {α : Type u} {l m n : List α}
    (h : l <:+: m) :
    l <:+: m ++ n := by
  rcases h with ⟨xs, ys, hsplit⟩
  refine ⟨xs, ys ++ n, ?_⟩
  simpa [List.append_assoc] using congrArg (fun t => t ++ n) hsplit

/--
Prepending extra prefix data preserves any existing contiguous infix.
-/
theorem List.infix_append_left
    {α : Type u} {l m n : List α}
    (h : l <:+: m) :
    l <:+: n ++ m := by
  rcases h with ⟨xs, ys, hsplit⟩
  refine ⟨n ++ xs, ys, ?_⟩
  simpa [List.append_assoc] using congrArg (fun t => n ++ t) hsplit

/--
If `a` is the endpoint reached after walking from `s` through `xs`, then an
infix of `a :: ys` is also an infix of `s :: (xs ++ ys)`.
-/
theorem List.infix_cons_append_of_endVertex
    {α : Type u} {needle xs ys : List α} {s a : α}
    (hend : endVertex s xs = a)
    (h : needle <:+: a :: ys) :
    needle <:+: s :: (xs ++ ys) := by
  induction xs generalizing s with
  | nil =>
      have hsa : s = a := by
        simpa [endVertex] using hend
      simpa [hsa] using h
  | cons x xs ih =>
      have htail : needle <:+: x :: (xs ++ ys) :=
        ih (s := x) (by simpa [endVertex] using hend)
      simpa [List.cons_append] using
        (List.infix_append_left (n := [s]) htail)

/--
Concrete closing lemma: a spanning path together with an edge from its terminal
vertex back to its initial vertex yields a Hamiltonian cycle.
-/
def hamiltonianOn_of_spanningPath
    {support : Finset V} {Adj : V → V → Prop} {s t : V}
    (p : ListSpanningPath Adj support s t)
    (hclose : Adj t s) :
    HamiltonianOn support Adj := by
  exact ⟨hamiltonianCycleWitnessOfSpanningPath p hclose⟩

/-- Ordered length-3 path data on four pairwise distinct vertices. -/
def Path3Vertices (G : SimpleGraph V) (a b c d : V) : Prop :=
  G.Adj a b ∧
  G.Adj b c ∧
  G.Adj c d ∧
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧
  b ≠ c ∧ b ≠ d ∧
  c ≠ d

theorem Path3Vertices.last_ne_of_eq_prefixVertex
    {G : SimpleGraph V} {a b c d x : V}
    (hp : Path3Vertices G a b c d)
    (hx : x = a ∨ x = b ∨ x = c) :
    d ≠ x := by
  rcases hp with
    ⟨_, _, _, _, _, had, _, hbd, hcd⟩
  intro hdx
  rcases hx with rfl | rfl | rfl
  · exact had hdx.symm
  · exact hbd hdx.symm
  · exact hcd hdx.symm

theorem Path3Vertices.last_ne_of_mem_prefixList
    {G : SimpleGraph V} {a b c d x : V}
    (hp : Path3Vertices G a b c d)
    (hx : x ∈ [a, b, c]) :
    d ≠ x :=
  hp.last_ne_of_eq_prefixVertex (by simpa using hx)

theorem Path3Vertices.reverse
    {G : SimpleGraph V} {a b c d : V}
    (hp : Path3Vertices G a b c d) :
    Path3Vertices G d c b a := by
  rcases hp with ⟨hab, hbc, hcd, hab_ne, hac_ne, had_ne, hbc_ne, hbd_ne, hcd_ne⟩
  exact ⟨hcd.symm, hbc.symm, hab.symm,
    hcd_ne.symm, hbd_ne.symm, had_ne.symm,
    hbc_ne.symm, hac_ne.symm, hab_ne.symm⟩

def Path3Vertices.toListSpanningPath
    {G : SimpleGraph V} {a b c d : V}
    (hp : Path3Vertices G a b c d) :
    ListSpanningPath G.Adj ([a, b, c, d].toFinset) a d := by
  rcases hp with ⟨hab, hbc, hcd, hab_ne, hac_ne, had_ne, hbc_ne, hbd_ne, hcd_ne⟩
  refine {
    tail := [b, c, d]
    ends_at := by simp [endVertex]
    adj := ?_
    nodup := by simp [hab_ne, hac_ne, had_ne, hbc_ne, hbd_ne, hcd_ne]
    spans := ?_
  }
  · intro x y hxy
    simp [edgePairs] at hxy
    rcases hxy with hxy | hxy | hxy
    · rcases hxy with ⟨rfl, rfl⟩
      exact hab
    · rcases hxy with ⟨rfl, rfl⟩
      exact hbc
    · rcases hxy with ⟨rfl, rfl⟩
      exact hcd
  · intro v
    simp [hab_ne, hac_ne, had_ne, hbc_ne, hbd_ne, hcd_ne]

/-- The initial two-edge path inside a `Path3Vertices` witness. -/
def Path3Vertices.toPrefixListSpanningPath
    {G : SimpleGraph V} {a b c d : V}
    (hp : Path3Vertices G a b c d) :
    ListSpanningPath G.Adj ([a, b, c].toFinset) a c := by
  rcases hp with ⟨hab, hbc, _, hab_ne, hac_ne, _, hbc_ne, _, _⟩
  refine {
    tail := [b, c]
    ends_at := by simp [endVertex]
    adj := ?_
    nodup := by simp [hab_ne, hac_ne, hbc_ne]
    spans := ?_
  }
  · intro x y hxy
    simp [edgePairs] at hxy
    rcases hxy with hxy | hxy
    · rcases hxy with ⟨rfl, rfl⟩
      exact hab
    · rcases hxy with ⟨rfl, rfl⟩
      exact hbc
  · intro v
    simp [hab_ne, hac_ne, hbc_ne]

@[simp] theorem Path3Vertices.toPrefixListSpanningPath_tail
    {G : SimpleGraph V} {a b c d : V}
    (hp : Path3Vertices G a b c d) :
    hp.toPrefixListSpanningPath.tail = [b, c] := by
  rcases hp with ⟨hab, hbc, hcd, hab_ne, hac_ne, had_ne, hbc_ne, hbd_ne, hcd_ne⟩
  rfl

instance instDecidablePath3Vertices
    (G : SimpleGraph V) [DecidableRel G.Adj] (a b c d : V) :
    Decidable (Path3Vertices G a b c d) := by
  unfold Path3Vertices
  infer_instance

/--
Finite list encoding of a Hamiltonian cycle: a nonempty cyclic ordering of all
vertices with the required adjacency relation along the cycle.
-/
def IsHamiltonianCycleList
    [Fintype V] (G : SimpleGraph V) (l : List V) : Prop :=
  match l with
  | [] => False
  | start :: tail =>
      List.Nodup (start :: tail) ∧
      (start :: tail).toFinset = (Finset.univ : Finset V) ∧
      (∀ ⦃a b⦄, (a, b) ∈ edgePairs (start :: (tail ++ [start])) → G.Adj a b)

/-- Close a cyclic list by repeating its initial vertex once at the end. -/
def cycleSupportList : List V → List V
  | [] => []
  | start :: tail => start :: (tail ++ [start])

instance instDecidableIsHamiltonianCycleList
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V) :
    Decidable (IsHamiltonianCycleList G l) := by
  unfold IsHamiltonianCycleList
  cases l with
  | nil =>
      infer_instance
  | cons start tail =>
      infer_instance

section MathlibBridge

open SimpleGraph

variable [Fintype V]
variable {G : SimpleGraph V}

/-- Build a walk from `u` to `t` following the intermediate list `vs`. -/
def walkOfListLast :
    ∀ (u : V) (vs : List V) (t : V),
      (∀ ⦃a b⦄, (a, b) ∈ edgePairs (u :: (vs ++ [t])) → G.Adj a b) →
      G.Walk u t
  | u, [], t, hadj =>
      .cons (hadj (by simp [edgePairs])) .nil
  | u, v :: vs, t, hadj =>
      .cons (hadj (by simp [edgePairs]))
        (walkOfListLast v vs t (by
          intro a b hab
          exact hadj (by
            simpa [edgePairs] using List.mem_cons_of_mem (u, v) hab)))

@[simp] theorem support_walkOfListLast
    (u : V) (vs : List V) (t : V)
    (hadj : ∀ ⦃a b⦄, (a, b) ∈ edgePairs (u :: (vs ++ [t])) → G.Adj a b) :
    (walkOfListLast (G := G) u vs t hadj).support = u :: (vs ++ [t]) := by
  induction vs generalizing u with
  | nil =>
      simp [walkOfListLast]
  | cons v vs ih =>
      simp [walkOfListLast, ih, List.cons_append]

@[simp] theorem length_walkOfListLast
    (u : V) (vs : List V) (t : V)
    (hadj : ∀ ⦃a b⦄, (a, b) ∈ edgePairs (u :: (vs ++ [t])) → G.Adj a b) :
    (walkOfListLast (G := G) u vs t hadj).length = vs.length + 1 := by
  induction vs generalizing u with
  | nil =>
      simp [walkOfListLast]
  | cons v vs ih =>
      simp [walkOfListLast, ih, List.cons_append]

/--
On a finite graph with at least three vertices, a list-based Hamiltonian cycle
witness on `Finset.univ` yields mathlib's `SimpleGraph.IsHamiltonian`.
-/
theorem isHamiltonian_of_hamiltonianOn_univ
    (hcard : 3 ≤ Fintype.card V)
    (hham : HamiltonianOn (Finset.univ : Finset V) G.Adj) :
    G.IsHamiltonian := by
  classical
  rcases hham with ⟨w⟩
  rcases w with ⟨start, tail, hcycleAdj, hnodup, hspans⟩
  have hsupport :
      (start :: tail).toFinset = (Finset.univ : Finset V) := by
    ext v
    simp [hspans v]
  have hlen :
      (start :: tail).length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hnodup, hsupport, Finset.card_univ]
  cases tail with
  | nil =>
      simp at hlen
      omega
  | cons next rest =>
      cases rest with
      | nil =>
          simp at hlen
          omega
      | cons mid rest =>
          have htailNodup : List.Nodup (next :: mid :: rest) :=
            (List.nodup_cons.1 hnodup).2
          have hstartNotMem : start ∉ next :: mid :: rest :=
            (List.nodup_cons.1 hnodup).1
          have hpathListNodup : List.Nodup (next :: (mid :: rest ++ [start])) := by
            rw [show next :: (mid :: rest ++ [start]) = (next :: mid :: rest) ++ [start] by rfl]
            rw [List.nodup_append]
            refine ⟨htailNodup, by simp, ?_⟩
            intro a ha b hb
            simp at hb
            subst b
            exact fun hEq => hstartNotMem (hEq ▸ ha)
          have hpathAdj :
              ∀ ⦃a b⦄, (a, b) ∈ edgePairs (next :: ((mid :: rest) ++ [start])) → G.Adj a b := by
            intro a b hab
            exact hcycleAdj (by
              simpa [edgePairs] using List.mem_cons_of_mem (start, next) hab)
          let p : G.Walk next start :=
            walkOfListLast (G := G) next (mid :: rest) start hpathAdj
          have hpSupport :
              p.support = next :: ((mid :: rest) ++ [start]) := by
            simpa [p] using
              (support_walkOfListLast (G := G) next (mid :: rest) start hpathAdj)
          have hpPath : p.IsPath := by
            refine SimpleGraph.Walk.IsPath.mk' ?_
            simpa [hpSupport] using hpathListNodup
          have hpLong : 1 < p.length := by
            simp [p, length_walkOfListLast]
          have hfirstEdge :
              G.Adj start next := hcycleAdj (by simp [edgePairs])
          have hfirstNotMem : s(start, next) ∉ p.edges := by
            intro hmem
            have hpen : next = p.penultimate := hpPath.eq_penultimate_of_mem_edges hmem
            have hverts : p.getVert 0 = p.getVert (p.length - 1) := by
              simpa [SimpleGraph.Walk.penultimate] using hpen
            have hidx :
                (0 : ℕ) = p.length - 1 :=
              hpPath.getVert_injOn (by simp) (Nat.sub_le _ _) hverts
            omega
          have hcyc : (SimpleGraph.Walk.cons hfirstEdge p).IsCycle := by
            exact (SimpleGraph.Walk.cons_isCycle_iff p hfirstEdge).2 ⟨hpPath, hfirstNotMem⟩
          have hcycLen :
              (SimpleGraph.Walk.cons hfirstEdge p).length = Fintype.card V := by
            calc
              (SimpleGraph.Walk.cons hfirstEdge p).length = p.length + 1 := by simp
              _ = ((mid :: rest).length + 1) + 1 := by simp [p, length_walkOfListLast]
              _ = Fintype.card V := by
                simpa using hlen
          intro hne
          exact
            ⟨start, SimpleGraph.Walk.cons hfirstEdge p,
              (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq).2
                ⟨hcyc, hcycLen⟩⟩

/-- Turn an explicit list witness into a `HamiltonianCycleWitness`. -/
def hamiltonianCycleWitnessOfList
    (l : List V)
    (hvalid : IsHamiltonianCycleList G l) :
    HamiltonianCycleWitness G.Adj (Finset.univ : Finset V) := by
  classical
  cases l with
  | nil =>
      cases hvalid
  | cons start tail =>
      rcases hvalid with ⟨hnodup, hspans, hadj⟩
      refine
        { start := start
          tail := tail
          cycle_adj := hadj
          nodup := hnodup
          spans := ?_ }
      intro v
      change v ∈ (Finset.univ : Finset V) ↔ v ∈ start :: tail
      rw [← hspans, List.mem_toFinset]

/-- Any consecutive pair from a list appears as a contiguous infix of that list. -/
theorem infix_of_mem_edgePairs
    {l : List V} {a b : V}
    (hab : (a, b) ∈ edgePairs l) :
    [a, b] <:+: l := by
  induction l generalizing a b with
  | nil =>
      cases hab
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases hab
      | cons y ys =>
          rw [edgePairs] at hab
          rcases List.mem_cons.1 hab with hab | hab
          · rcases Prod.mk.inj hab with ⟨rfl, rfl⟩
            exact ⟨[], ys, by simp⟩
          · rcases ih hab with ⟨s, t, hst⟩
            exact ⟨x :: s, t, by simp [hst, List.append_assoc]⟩

theorem mem_edgePairs_of_infix_pair
    {l : List V} {a b : V}
    (h : [a, b] <:+: l) :
    (a, b) ∈ edgePairs l := by
  rcases h with ⟨xs, ys, rfl⟩
  induction xs with
  | nil =>
      simp [edgePairs]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [edgePairs]
      | cons y ys' =>
          simp [edgePairs] at ih ⊢
          exact Or.inr ih

theorem List.pair_infix_reverse
    {l : List V} {a b : V}
    (h : [a, b] <:+: l) :
    [b, a] <:+: l.reverse := by
  rcases h with ⟨xs, ys, hsplit⟩
  refine ⟨ys.reverse, xs.reverse, ?_⟩
  calc
    ys.reverse ++ [b, a] ++ xs.reverse = (xs ++ [a, b] ++ ys).reverse := by
      simp [List.reverse_reverse, List.reverse_append, List.reverse_cons, List.append_assoc]
    _ = l.reverse := by rw [hsplit]

theorem List.pair_infix_of_infix_cons
    {l : List V} {z a b : V}
    (h : [a, b] <:+: z :: l)
    (haz : a ≠ z) :
    [a, b] <:+: l := by
  rcases h with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      have ha : a = z := by
        exact (Option.some.inj (by simpa using congrArg List.head? hsplit.symm)).symm
      exact False.elim (haz ha)
  | cons x xs' =>
      have hx : x = z := by
        exact (Option.some.inj (by simpa using congrArg List.head? hsplit.symm)).symm
      refine ⟨xs', ys, ?_⟩
      exact (Option.some.inj (by simpa [hx] using congrArg List.tail? hsplit.symm)).symm

theorem List.pair_head_or_tail_of_prefix5
    {x y a b c d z : V} {zs : List V}
    (hxy : [x, y] <:+: [a, b, c, d, z] ++ zs)
    (hx_ne_a : x ≠ a)
    (hx_ne_b : x ≠ b)
    (hx_ne_c : x ≠ c) :
    x = d ∨ [x, y] <:+: z :: zs := by
  by_cases hxd : x = d
  · exact Or.inl hxd
  · refine Or.inr ?_
    have hxy₁ : [x, y] <:+: [b, c, d, z] ++ zs := by
      exact List.pair_infix_of_infix_cons (by simpa using hxy) hx_ne_a
    have hxy₂ : [x, y] <:+: [c, d, z] ++ zs := by
      exact List.pair_infix_of_infix_cons (by simpa using hxy₁) hx_ne_b
    have hxy₃ : [x, y] <:+: [d, z] ++ zs := by
      exact List.pair_infix_of_infix_cons (by simpa using hxy₂) hx_ne_c
    exact List.pair_infix_of_infix_cons (by simpa using hxy₃) hxd

theorem List.second_eq_of_pair_infix_head_nodup
    {x y u : V} {zs : List V}
    (hnodup : List.Nodup (x :: y :: zs))
    (hxu : [x, u] <:+: x :: y :: zs) :
    u = y := by
  rcases hxu with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      have htail : u :: ys = y :: zs := by
        exact Option.some.inj (by simpa using congrArg List.tail? hsplit)
      exact Option.some.inj (by simpa using congrArg List.head? htail)
  | cons z zs' =>
      have hz : z = x := by
        exact (Option.some.inj (by simpa using congrArg List.head? hsplit.symm)).symm
      subst z
      have htail : y :: zs = zs' ++ [x, u] ++ ys := by
        exact Option.some.inj (by simpa [List.append_assoc] using congrArg List.tail? hsplit.symm)
      have hx_tail : x ∈ y :: zs := by
        rw [htail]
        simp [List.mem_append, or_assoc, or_left_comm, or_comm]
      exact False.elim ((List.nodup_cons.1 hnodup).1 hx_tail)

theorem List.pair_infix_of_infix_append_singleton
    {l : List V} {a b z : V}
    (h : [a, b] <:+: l ++ [z])
    (hbz : b ≠ z) :
    [a, b] <:+: l := by
  rcases h with ⟨xs, ys, hsplit⟩
  rcases List.eq_nil_or_concat' ys with hys | ⟨ys', y, hys⟩
  · subst hys
    have hb : b = z := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [a, b]).getLast? = some b := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil xs (by simp : ([a, b] : List V) ≠ []))
      have hright : (l ++ [z]).getLast? = some z := by
        simpa using
          (List.getLast?_append_of_ne_nil l (by simp : ([z] : List V) ≠ []))
      have hbOpt : some b = some z := by
        calc
          some b = (xs ++ [a, b]).getLast? := by simpa using hleft.symm
          _ = (l ++ [z]).getLast? := by simpa using hlast
          _ = some z := hright
      exact Option.some.inj hbOpt
    exact False.elim (hbz hb)
  · have hy : y = z := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [a, b] ++ ys' ++ [y]).getLast? = some y := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [a, b] ++ ys')
            (by simp : ([y] : List V) ≠ []))
      have hright : (l ++ [z]).getLast? = some z := by
        simpa using
          (List.getLast?_append_of_ne_nil l (by simp : ([z] : List V) ≠ []))
      have hyOpt : some y = some z := by
        calc
          some y = (xs ++ [a, b] ++ (ys' ++ [y])).getLast? := by
            simpa [hys, List.append_assoc] using hleft.symm
          _ = (l ++ [z]).getLast? := by
            simpa [hys] using hlast
          _ = some z := hright
      exact Option.some.inj hyOpt
    refine ⟨xs, ys', ?_⟩
    apply (List.append_left_injective [z])
    simpa [hys, hy, List.append_assoc] using hsplit

/--
If a pair occurs in `l ++ [z]` but not in `l`, then it is exactly the closing
pair from the last vertex of `l` to `z`.
-/
theorem List.eq_append_singleton_and_eq_of_pair_infix_append_singleton_not_infix
    {l : List V} {a b z : V}
    (h : [a, b] <:+: l ++ [z])
    (hnot : ¬ [a, b] <:+: l) :
    (∃ xs, l = xs ++ [a]) ∧ b = z := by
  rcases h with ⟨xs, ys, hsplit⟩
  rcases List.eq_nil_or_concat' ys with hys | ⟨ys', y, hys⟩
  · subst hys
    have hb : b = z := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [a, b]).getLast? = some b := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil xs (by simp : ([a, b] : List V) ≠ []))
      have hright : (l ++ [z]).getLast? = some z := by
        simpa using
          (List.getLast?_append_of_ne_nil l (by simp : ([z] : List V) ≠ []))
      have hbOpt : some b = some z := by
        calc
          some b = (xs ++ [a, b]).getLast? := by simpa using hleft.symm
          _ = (l ++ [z]).getLast? := by simpa using hlast
          _ = some z := hright
      exact Option.some.inj hbOpt
    have hl : l = xs ++ [a] := by
      symm
      exact List.append_cancel_right (by
        simpa [hb, List.append_assoc] using hsplit)
    exact ⟨⟨xs, hl⟩, hb⟩
  · have hy : y = z := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [a, b] ++ ys' ++ [y]).getLast? = some y := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [a, b] ++ ys')
            (by simp : ([y] : List V) ≠ []))
      have hright : (l ++ [z]).getLast? = some z := by
        simpa using
          (List.getLast?_append_of_ne_nil l (by simp : ([z] : List V) ≠ []))
      have hyOpt : some y = some z := by
        calc
          some y = (xs ++ [a, b] ++ (ys' ++ [y])).getLast? := by
            simpa [hys, List.append_assoc] using hleft.symm
          _ = (l ++ [z]).getLast? := by simpa [hys] using hlast
          _ = some z := hright
      exact Option.some.inj hyOpt
    have hopen : [a, b] <:+: l := by
      refine ⟨xs, ys', ?_⟩
      apply (List.append_left_injective [z])
      simpa [hys, hy, List.append_assoc] using hsplit
    exact False.elim (hnot hopen)

theorem mem_of_mem_edgePairs_left
    {l : List V} {a b : V}
    (hab : (a, b) ∈ edgePairs l) :
    a ∈ l := by
  rcases infix_of_mem_edgePairs hab with ⟨xs, ys, hsplit⟩
  rw [← hsplit]
  simp

theorem mem_of_mem_edgePairs_right
    {l : List V} {a b : V}
    (hab : (a, b) ∈ edgePairs l) :
    b ∈ l := by
  rcases infix_of_mem_edgePairs hab with ⟨xs, ys, hsplit⟩
  rw [← hsplit]
  simp

theorem List.exists_incident_edge_of_mem_of_ne_singleton
    {l : List V} (hpair : edgePairs l ≠ [])
    {v : V} (hv : v ∈ l) :
    ∃ a b, (a, b) ∈ edgePairs l ∧ (v = a ∨ v = b) := by
  induction l with
  | nil =>
      cases hv
  | cons a l ih =>
      cases l with
      | nil =>
          exfalso
          exact hpair (by simp [edgePairs])
      | cons b rest =>
          simp at hv
          rcases hv with rfl | rfl | hvrest
          · exact ⟨v, b, by simp [edgePairs], Or.inl rfl⟩
          · exact ⟨a, v, by simp [edgePairs], Or.inr rfl⟩
          · have hpair' : edgePairs (b :: rest) ≠ [] := by
                cases rest with
                | nil =>
                    cases hvrest
                | cons c cs =>
                    simp [edgePairs]
            rcases ih hpair' (by simp [hvrest]) with ⟨x, y, hxy, hinc⟩
            exact ⟨x, y, by simpa [edgePairs] using List.mem_cons_of_mem (a, b) hxy, hinc⟩

theorem List.exists_boundary_edge_of_exists_mem_and_not_mem
    {α : Type u} (p : α → Prop) [DecidablePred p] :
    ∀ {l : List α}, l ≠ [] →
      (∃ x, x ∈ l ∧ p x) →
      (∃ x, x ∈ l ∧ ¬ p x) →
      ∃ a b, (a, b) ∈ edgePairs l ∧ ((p a ∧ ¬ p b) ∨ (¬ p a ∧ p b))
  | [], hnil, _, _ => False.elim (hnil rfl)
  | [a], _, hmem, hnot => by
      rcases hmem with ⟨x, hx, hpx⟩
      rcases hnot with ⟨y, hy, hny⟩
      simp at hx hy
      subst hx
      subst hy
      exact False.elim (hny hpx)
  | a :: b :: l, _, hmem, hnot => by
      by_cases hpa : p a
      · by_cases hpb : p b
        · have hmem' : ∃ x, x ∈ b :: l ∧ p x := ⟨b, by simp [hpb]⟩
          have hnot' : ∃ x, x ∈ b :: l ∧ ¬ p x := by
            rcases hnot with ⟨x, hx, hnx⟩
            rcases List.mem_cons.1 hx with rfl | hx
            · exact False.elim (hnx hpa)
            · exact ⟨x, by simp [hx], hnx⟩
          rcases List.exists_boundary_edge_of_exists_mem_and_not_mem p
              (l := b :: l) (by simp) hmem' hnot' with ⟨u, v, huv, hdiff⟩
          exact ⟨u, v, by simpa [edgePairs] using List.mem_cons_of_mem (a, b) huv, hdiff⟩
        · exact ⟨a, b, by simp [edgePairs], Or.inl ⟨hpa, hpb⟩⟩
      · by_cases hpb : p b
        · exact ⟨a, b, by simp [edgePairs], Or.inr ⟨hpa, hpb⟩⟩
        · have hnot' : ∃ x, x ∈ b :: l ∧ ¬ p x := ⟨b, by simp [hpb]⟩
          have hmem' : ∃ x, x ∈ b :: l ∧ p x := by
            rcases hmem with ⟨x, hx, hpx⟩
            rcases List.mem_cons.1 hx with rfl | hx
            · exact False.elim (hpa hpx)
            · exact ⟨x, by simp [hx], hpx⟩
          rcases List.exists_boundary_edge_of_exists_mem_and_not_mem p
              (l := b :: l) (by simp) hmem' hnot' with ⟨u, v, huv, hdiff⟩
          exact ⟨u, v, by simpa [edgePairs] using List.mem_cons_of_mem (a, b) huv, hdiff⟩

theorem mem_zipWith_sym2_of_mem_edgePairs
    {l : List V} {a b : V}
    (hab : (a, b) ∈ edgePairs l) :
    s(a, b) ∈ List.zipWith (s(·, ·)) l l.tail := by
  induction l generalizing a b with
  | nil =>
      cases hab
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases hab
      | cons y ys =>
          simp [edgePairs] at hab ⊢
          rcases hab with hab | hab
          · cases hab
            aesop
          · exact Or.inr (ih hab)

theorem List.infix_or_reverse_of_mem_zipWith_sym2
    {l : List V} {a b : V}
    (hab : s(a, b) ∈ List.zipWith (s(·, ·)) l l.tail) :
    [a, b] <:+: l ∨ [b, a] <:+: l := by
  induction l generalizing a b with
  | nil =>
      cases hab
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases hab
      | cons y ys =>
          simp at hab
          rcases hab with hab | hab
          · have hab' : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
              simpa [Sym2.eq, Sym2.rel_iff'] using hab
            rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨[], ys, by simp⟩
            · exact Or.inr ⟨[], ys, by simp⟩
          · rcases ih hab with h | h
            · exact Or.inl (List.IsInfix.trans h ⟨[x], [], by simp⟩)
            · exact Or.inr (List.IsInfix.trans h ⟨[x], [], by simp⟩)

theorem edgePairs_split_pair
    (xs ys : List V) (u₀ u₁ : V) :
    edgePairs (xs ++ [u₀, u₁] ++ ys) =
      edgePairs (xs ++ [u₀]) ++ (u₀, u₁) :: edgePairs (u₁ :: ys) := by
  induction xs with
  | nil =>
      simp [edgePairs]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [edgePairs]
      | cons y ys' =>
          simpa [edgePairs, List.append_assoc] using
            congrArg (List.cons (x, y)) ih

theorem List.pair_pair_split
    {l : List V} {u₀ u₁ u₂ u₃ : V}
    (h01 : [u₀, u₁] <:+: l)
    (h23 : [u₂, u₃] <:+: l)
    (hu₂₀ : u₂ ≠ u₀)
    (hu₂₁ : u₂ ≠ u₁)
    (hu₃₀ : u₃ ≠ u₀)
    (hu₃₁ : u₃ ≠ u₁) :
    (∃ xs ys zs, l = xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) ∨
      ∃ xs ys zs, l = xs ++ [u₂, u₃] ++ ys ++ [u₀, u₁] ++ zs := by
  rcases h01 with ⟨xs, ys, hsplit⟩
  have hmem23 : (u₂, u₃) ∈ edgePairs (xs ++ [u₀, u₁] ++ ys) := by
    simpa [hsplit] using mem_edgePairs_of_infix_pair h23
  rw [edgePairs_split_pair xs ys u₀ u₁] at hmem23
  rcases List.mem_append.1 hmem23 with hpre | hrest
  · have hpre' : [u₂, u₃] <:+: xs ++ [u₀] := infix_of_mem_edgePairs hpre
    have hpre'' : [u₂, u₃] <:+: xs := by
      exact List.pair_infix_of_infix_append_singleton hpre' hu₃₀
    rcases hpre'' with ⟨xs', ys', hpreSplit⟩
    right
    refine ⟨xs', ys', ys, ?_⟩
    simpa [List.append_assoc, hpreSplit] using hsplit.symm
  · rcases List.mem_cons.1 hrest with hbridge | hsuf
    · rcases Prod.mk.inj hbridge with ⟨hu₂, hu₃⟩
      exact False.elim (hu₂₀ hu₂)
    · have hsuf' : [u₂, u₃] <:+: u₁ :: ys := infix_of_mem_edgePairs hsuf
      have hsuf'' : [u₂, u₃] <:+: ys := by
        exact List.pair_infix_of_infix_cons hsuf' hu₂₁
      rcases hsuf'' with ⟨ys', zs, hsufSplit⟩
      left
      refine ⟨xs, ys', zs, ?_⟩
      simpa [List.append_assoc, hsufSplit] using hsplit.symm

theorem List.split_pair_eq_of_nodup
    {l : List V} (hnodup : List.Nodup l)
    {xs ys xs' ys' : List V} {a b : V}
    (h1 : xs ++ [a, b] ++ ys = l)
    (h2 : xs' ++ [a, b] ++ ys' = l) :
    xs = xs' ∧ ys = ys' := by
  induction l generalizing xs ys xs' ys' with
  | nil =>
      cases xs <;> cases h1
  | cons z l ih =>
      have htailNodup : List.Nodup l := (List.nodup_cons.1 hnodup).2
      cases xs with
      | nil =>
          have hza : z = a := by
            exact (Option.some.inj (by simpa using congrArg List.head? h1)).symm
          subst z
          cases xs' with
          | nil =>
              have htail1 : b :: ys = l := by
                simpa using congrArg List.tail? h1
              have htail2 : b :: ys' = l := by
                simpa using congrArg List.tail? h2
              have hys : ys = ys' := by
                exact Option.some.inj (by simpa using congrArg List.tail? (htail1.trans htail2.symm))
              exact ⟨rfl, hys⟩
          | cons z' xs'' =>
              have hz' : a = z' := by
                exact (Option.some.inj (by simpa using congrArg List.head? h2)).symm
              have ha_mem : a ∈ l := by
                have htail2 : xs'' ++ [a, b] ++ ys' = l := by
                  simpa [hz', List.append_assoc] using congrArg List.tail? h2
                rw [← htail2]
                simp [List.mem_append, or_assoc, or_left_comm, or_comm]
              exact False.elim ((List.nodup_cons.1 hnodup).1 ha_mem)
      | cons z₀ xs₀ =>
          have hz₀ : z₀ = z := by
            simpa using congrArg List.head? h1
          subst z₀
          cases xs' with
          | nil =>
              have hza : z = a := by
                exact (Option.some.inj (by simpa using congrArg List.head? h2)).symm
              subst z
              have ha_mem : a ∈ l := by
                have htail1 : xs₀ ++ [a, b] ++ ys = l := by
                  simpa [List.append_assoc] using congrArg List.tail? h1
                rw [← htail1]
                simp [List.mem_append, or_assoc, or_left_comm, or_comm]
              exact False.elim ((List.nodup_cons.1 hnodup).1 ha_mem)
          | cons z₁ xs₁ =>
              have hz₁ : z₁ = z := by
                simpa using congrArg List.head? h2
              subst z₁
              have htail1 : xs₀ ++ [a, b] ++ ys = l := by
                simpa [List.append_assoc] using congrArg List.tail? h1
              have htail2 : xs₁ ++ [a, b] ++ ys' = l := by
                simpa [List.append_assoc] using congrArg List.tail? h2
              rcases ih htailNodup htail1 htail2 with ⟨hxs, hys⟩
              exact ⟨by simpa [hxs], hys⟩

theorem List.pair_infix_left_or_right_of_split_middle_ne
    {l : List V} (hnodup : List.Nodup l)
    {left right : List V} {x y a b : V}
    (hsplit : l = left ++ [x, y] ++ right)
    (hinfix : [a, b] <:+: l)
    (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) :
    [a, b] <:+: left ++ [x] ∨ [a, b] <:+: y :: right := by
  have hxy : [x, y] <:+: l := ⟨left, right, hsplit.symm⟩
  rcases List.pair_pair_split hxy hinfix hax hay hbx hby with hafter | hbefore
  · rcases hafter with ⟨xs, ys, zs, hafter⟩
    have hright :
        right = ys ++ [a, b] ++ zs := by
      rcases
        List.split_pair_eq_of_nodup hnodup
          (xs := xs) (ys := ys ++ [a, b] ++ zs)
          (xs' := left) (ys' := right)
          (by simpa [List.append_assoc] using hafter.symm)
          (by simpa [List.append_assoc] using hsplit.symm)
        with ⟨_, hright⟩
      exact hright.symm
    exact Or.inr ⟨y :: ys, zs, by simp [hright, List.append_assoc]⟩
  · rcases hbefore with ⟨xs, ys, zs, hbefore⟩
    have hleft :
        left = xs ++ [a, b] ++ ys := by
      rcases
        List.split_pair_eq_of_nodup hnodup
          (xs := xs ++ [a, b] ++ ys) (ys := zs)
          (xs' := left) (ys' := right)
          (by simpa [List.append_assoc] using hbefore.symm)
          (by simpa [List.append_assoc] using hsplit.symm)
        with ⟨hleft, _⟩
      exact hleft.symm
    exact Or.inl ⟨xs, ys ++ [x], by simp [hleft, List.append_assoc]⟩

theorem List.pair_infix_rotated_complement_of_path4_split
    {l : List V} (hnodup : List.Nodup l)
    {xs ys : List V} {u₃ u₀ u₁ u₂ a b : V}
    (hsplit : l = xs ++ [u₃, u₀, u₁, u₂] ++ ys)
    (hinfix : [a, b] <:+: l)
    (ha₃ : a ≠ u₃) (ha₀ : a ≠ u₀) (ha₁ : a ≠ u₁) (ha₂ : a ≠ u₂)
    (hb₃ : b ≠ u₃) (hb₀ : b ≠ u₀) (hb₁ : b ≠ u₁) (hb₂ : b ≠ u₂) :
    [a, b] <:+: u₂ :: ((ys ++ xs) ++ [u₃]) := by
  have hsplit₁₂ :
      l = (xs ++ [u₃, u₀]) ++ [u₁, u₂] ++ ys := by
    simpa [List.append_assoc] using hsplit
  rcases
      List.pair_infix_left_or_right_of_split_middle_ne
        hnodup hsplit₁₂ hinfix ha₁ ha₂ hb₁ hb₂ with hleft | hright
  · have hnodupLeft :
        List.Nodup (xs ++ [u₃, u₀] ++ [u₁]) := by
      have hnodupSplit :
          List.Nodup ((xs ++ [u₃, u₀] ++ [u₁]) ++ (u₂ :: ys)) := by
        simpa [hsplit₁₂, List.append_assoc] using hnodup
      exact List.Nodup.of_append_left hnodupSplit
    rcases
        List.pair_infix_left_or_right_of_split_middle_ne
          hnodupLeft (by rfl : xs ++ [u₃, u₀] ++ [u₁] = xs ++ [u₃, u₀] ++ [u₁])
          hleft ha₃ ha₀ hb₃ hb₀ with hpre | hmiddle
    · rcases hpre with ⟨pre, post, hpre⟩
      refine ⟨u₂ :: ys ++ pre, post, ?_⟩
      calc
        (u₂ :: ys ++ pre) ++ [a, b] ++ post =
            u₂ :: (ys ++ (pre ++ [a, b] ++ post)) := by
          simp [List.append_assoc]
        _ = u₂ :: (ys ++ (xs ++ [u₃])) := by rw [hpre]
        _ = u₂ :: ((ys ++ xs) ++ [u₃]) := by simp [List.append_assoc]
    · have ha_mem : a ∈ u₀ :: [u₁] := by
        rcases hmiddle with ⟨pre, post, hmiddle⟩
        have : a ∈ pre ++ [a, b] ++ post := by
          simp [List.mem_append]
        simpa [hmiddle] using this
      simp at ha_mem
      rcases ha_mem with ha0 | ha1
      · exact False.elim (ha₀ ha0)
      · exact False.elim (ha₁ ha1)
  · rcases hright with ⟨pre, post, hright⟩
    refine ⟨pre, post ++ xs ++ [u₃], ?_⟩
    calc
      pre ++ [a, b] ++ (post ++ xs ++ [u₃]) =
          (pre ++ [a, b] ++ post) ++ xs ++ [u₃] := by
        simp [List.append_assoc]
      _ = (u₂ :: ys) ++ xs ++ [u₃] := by rw [hright]
      _ = u₂ :: ((ys ++ xs) ++ [u₃]) := by simp [List.append_assoc]

/--
Cyclic variant of `pair_infix_rotated_complement_of_path4_split`.

If the pair is the closing edge of the cycle list, it becomes the boundary edge
between the suffix and prefix after rotating the complement.
-/
theorem List.pair_infix_rotated_complement_of_path4_split_cycle
    {s : V} {tail xs ys : List V} {u₃ u₀ u₁ u₂ a b : V}
    (hnodup : List.Nodup (s :: tail))
    (hsplit : s :: tail = xs ++ [u₃, u₀, u₁, u₂] ++ ys)
    (hcyc : [a, b] <:+: s :: (tail ++ [s]))
    (ha₃ : a ≠ u₃) (ha₀ : a ≠ u₀) (ha₁ : a ≠ u₁) (ha₂ : a ≠ u₂)
    (hb₃ : b ≠ u₃) (hb₀ : b ≠ u₀) (hb₁ : b ≠ u₁) (hb₂ : b ≠ u₂) :
    [a, b] <:+: u₂ :: ((ys ++ xs) ++ [u₃]) := by
  by_cases hopen : [a, b] <:+: s :: tail
  · exact
      List.pair_infix_rotated_complement_of_path4_split
        hnodup hsplit hopen ha₃ ha₀ ha₁ ha₂ hb₃ hb₀ hb₁ hb₂
  · have hcross :
        (∃ pre, s :: tail = pre ++ [a]) ∧ b = s :=
      List.eq_append_singleton_and_eq_of_pair_infix_append_singleton_not_infix
        (l := s :: tail) (z := s) (by simpa using hcyc) hopen
    rcases hcross with ⟨⟨pre, hlast⟩, hb⟩
    cases xs with
    | nil =>
        have hs₃ : s = u₃ := by
          exact Option.some.inj (by simpa using congrArg List.head? hsplit)
        exact False.elim (hb₃ (hb.trans hs₃))
    | cons x xs' =>
        have hx : x = s := by
          exact (Option.some.inj (by simpa using congrArg List.head? hsplit)).symm
        subst x
        rcases List.eq_nil_or_concat' ys with hys | ⟨ys', y, hys⟩
        · have ha₂' : a = u₂ := by
            have hpreLast : (pre ++ [a]).getLast? = some a := by
              simpa using
                (List.getLast?_append_of_ne_nil pre
                  (by simp : ([a] : List V) ≠ []))
            have hsplitLast :
                ((s :: xs') ++ [u₃, u₀, u₁, u₂]).getLast? = some u₂ := by
              simpa [List.append_assoc] using
                (List.getLast?_append_of_ne_nil ((s :: xs') ++ [u₃, u₀, u₁])
                  (by simp : ([u₂] : List V) ≠ []))
            have hlastOpt : some a = some u₂ := by
              calc
                some a = (pre ++ [a]).getLast? := by simpa using hpreLast.symm
                _ = (s :: tail).getLast? := by rw [← hlast]
                _ = ((s :: xs') ++ [u₃, u₀, u₁, u₂]).getLast? := by
                  rw [hsplit, hys]
                  simp [List.append_assoc]
                _ = some u₂ := hsplitLast
            exact Option.some.inj hlastOpt
          exact False.elim (ha₂ ha₂')
        · have hy : y = a := by
            have hysLast :
                ((s :: xs') ++ [u₃, u₀, u₁, u₂] ++ (ys' ++ [y])).getLast? =
                  some y := by
              simpa [List.append_assoc] using
                (List.getLast?_append_of_ne_nil
                  ((s :: xs') ++ [u₃, u₀, u₁, u₂] ++ ys')
                  (by simp : ([y] : List V) ≠ []))
            have hpreLast : (pre ++ [a]).getLast? = some a := by
              simpa using
                (List.getLast?_append_of_ne_nil pre
                  (by simp : ([a] : List V) ≠ []))
            have hyOpt : some y = some a := by
              calc
                some y =
                    ((s :: xs') ++ [u₃, u₀, u₁, u₂] ++ (ys' ++ [y])).getLast? := by
                  simpa [List.append_assoc] using hysLast.symm
                _ = (s :: tail).getLast? := by
                  rw [hsplit, hys]
                _ = (pre ++ [a]).getLast? := by rw [hlast]
                _ = some a := hpreLast
            exact Option.some.inj hyOpt
          subst y
          refine ⟨u₂ :: ys', xs' ++ [u₃], ?_⟩
          simp [hys, hb, List.append_assoc]

theorem List.path4_infix_of_pair_before_pair
    {l : List V} (hnodup : List.Nodup l)
    {a b c d x y : V}
    (hinfix : [a, b, c, d] <:+: l)
    {xs ys zs : List V}
    (hsplit : l = xs ++ [b, c] ++ ys ++ [x, y] ++ zs) :
    [a, b, c, d] <:+: xs ++ [b, c] ++ ys ++ [x] := by
  rcases hinfix with ⟨pre, post, hpath⟩
  have hbc :
      (pre ++ [a]) ++ [b, c] ++ (d :: post) = l := by
    simpa [List.append_assoc] using hpath
  rcases
    List.split_pair_eq_of_nodup hnodup
      (xs := pre ++ [a]) (ys := d :: post)
      (xs' := xs) (ys' := ys ++ [x, y] ++ zs)
      hbc (by simpa [List.append_assoc] using hsplit.symm)
    with ⟨hxs, hsuf⟩
  cases ys with
  | nil =>
      have hdx : d = x := by
        simpa [List.append_assoc] using congrArg List.head? hsuf
      refine ⟨pre, [], ?_⟩
      rw [← hxs]
      simp [hdx, List.append_assoc]
  | cons u ys' =>
      have hdu : d = u := by
        simpa [List.append_assoc] using congrArg List.head? hsuf
      refine ⟨pre, ys' ++ [x], ?_⟩
      rw [← hxs]
      simp [hdu, List.append_assoc]

theorem List.path4_infix_of_pair_after_pair
    {l : List V} (hnodup : List.Nodup l)
    {a b c d x y : V}
    (hinfix : [a, b, c, d] <:+: l)
    {xs ys zs : List V}
    (hsplit : l = xs ++ [x, y] ++ ys ++ [b, c] ++ zs) :
    [a, b, c, d] <:+: y :: (ys ++ [b, c] ++ zs) := by
  rcases hinfix with ⟨pre, post, hpath⟩
  have hbc :
      (pre ++ [a]) ++ [b, c] ++ (d :: post) = l := by
    simpa [List.append_assoc] using hpath
  rcases
    List.split_pair_eq_of_nodup hnodup
      (xs := pre ++ [a]) (ys := d :: post)
      (xs' := xs ++ [x, y] ++ ys) (ys' := zs)
      hbc (by simpa [List.append_assoc] using hsplit.symm)
    with ⟨hpre, hzs⟩
  rcases List.eq_nil_or_concat' ys with hys | ⟨ys', u, hys⟩
  · have hay : a = y := by
      have hlastA : some a = some y := by
        calc
          some a = (pre ++ [a]).getLast? := by
            simpa using
              (List.getLast?_append_of_ne_nil pre (by simp : ([a] : List V) ≠ [])).symm
          _ = (xs ++ [x, y]).getLast? := by simpa [hpre, hys, List.append_assoc]
          _ = some y := by simp
      exact Option.some.inj hlastA
    refine ⟨[], post, ?_⟩
    rw [hys] at hpre
    simp [hys, hay, hzs, List.append_assoc]
  · have hau : a = u := by
      have hlastA : some a = some u := by
        calc
          some a = (pre ++ [a]).getLast? := by
            simpa using
              (List.getLast?_append_of_ne_nil pre (by simp : ([a] : List V) ≠ [])).symm
          _ = (xs ++ [x, y] ++ (ys' ++ [u])).getLast? := by
            simpa [hpre, hys, List.append_assoc]
          _ = some u := by
            simpa [List.append_assoc] using
              (List.getLast?_append_of_ne_nil (xs ++ [x, y] ++ ys')
                (by simp : ([u] : List V) ≠ []))
      exact Option.some.inj hlastA
    refine ⟨y :: ys', post, ?_⟩
    rw [hys] at hpre
    simp [hys, hau, hzs, List.append_assoc]

theorem List.path4_infix_left_or_right_of_split_middle_ne
    {l : List V} (hnodup : List.Nodup l)
    {left right : List V} {x y a b c d : V}
    (hsplit : l = left ++ [x, y] ++ right)
    (hinfix : [a, b, c, d] <:+: l)
    (hbx : b ≠ x)
    (hby : b ≠ y)
    (hcx : c ≠ x)
    (hcy : c ≠ y) :
    [a, b, c, d] <:+: left ++ [x] ∨
      [a, b, c, d] <:+: y :: right := by
  have hbc : [b, c] <:+: l := by
    exact List.IsInfix.trans ⟨[a], [d], by simp⟩ hinfix
  have hxy : [x, y] <:+: l := by
    exact ⟨left, right, hsplit.symm⟩
  rcases List.pair_pair_split hbc hxy hbx.symm hcx.symm hby.symm hcy.symm with hbefore | hafter
  · rcases hbefore with ⟨xs, ys, zs, hbefore⟩
    have hleft :
        left = xs ++ [b, c] ++ ys := by
      rcases
        List.split_pair_eq_of_nodup hnodup
          (xs := xs ++ [b, c] ++ ys) (ys := zs)
          (xs' := left) (ys' := right)
          (by simpa [List.append_assoc] using hbefore.symm)
          (by simpa [List.append_assoc] using hsplit.symm)
        with ⟨hleft, _⟩
      exact hleft.symm
    have hinLeft :
        [a, b, c, d] <:+: xs ++ [b, c] ++ ys ++ [x] :=
      List.path4_infix_of_pair_before_pair hnodup hinfix hbefore
    exact Or.inl (by simpa [hleft, List.append_assoc] using hinLeft)
  · rcases hafter with ⟨xs, ys, zs, hafter⟩
    have hright :
        right = ys ++ [b, c] ++ zs := by
      rcases
        List.split_pair_eq_of_nodup hnodup
          (xs := xs) (ys := ys ++ [b, c] ++ zs)
          (xs' := left) (ys' := right)
          (by simpa [List.append_assoc] using hafter.symm)
          (by simpa [List.append_assoc] using hsplit.symm)
        with ⟨_, hright⟩
      exact hright.symm
    have hinRight :
        [a, b, c, d] <:+: y :: (ys ++ [b, c] ++ zs) :=
      List.path4_infix_of_pair_after_pair hnodup hinfix hafter
    exact Or.inr (by simpa [hright, List.append_assoc] using hinRight)

theorem List.path4_infix_left_or_right_of_matching_split
    {l : List V} (hnodup : List.Nodup l)
    {xs ys zs : List V} {u₀ u₁ u₂ u₃ a b c d : V}
    (hsplit : l = xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs)
    (hinfix : [a, b, c, d] <:+: l)
    (hb0 : b ≠ u₀) (hb1 : b ≠ u₁) (hb2 : b ≠ u₂) (hb3 : b ≠ u₃)
    (hc0 : c ≠ u₀) (hc1 : c ≠ u₁) (hc2 : c ≠ u₂) (hc3 : c ≠ u₃) :
    [a, b, c, d] <:+: u₁ :: (ys ++ [u₂]) ∨
      [a, b, c, d] <:+: u₃ :: ((zs ++ xs) ++ [u₀]) := by
  have hinSplit23 :
      [a, b, c, d] <:+: xs ++ [u₀, u₁] ++ ys ++ [u₂] ∨
        [a, b, c, d] <:+: u₃ :: zs := by
    have hsplit23 :
        l = (xs ++ [u₀, u₁] ++ ys) ++ [u₂, u₃] ++ zs := by
      simpa [List.append_assoc] using hsplit
    exact List.path4_infix_left_or_right_of_split_middle_ne
      hnodup hsplit23 hinfix hb2 hb3 hc2 hc3
  rcases hinSplit23 with hinLeft23 | hinRight23
  · have hnodupLeft23 : List.Nodup (xs ++ [u₀, u₁] ++ ys ++ [u₂]) := by
      have hnodupPref :
          List.Nodup ((xs ++ [u₀, u₁] ++ ys ++ [u₂]) ++ ([u₃] ++ zs)) := by
        simpa [hsplit, List.append_assoc] using hnodup
      exact (List.nodup_append.1 hnodupPref).1
    have hsplit01 :
        xs ++ [u₀, u₁] ++ (ys ++ [u₂]) =
          xs ++ [u₀, u₁] ++ ys ++ [u₂] := by
      simp [List.append_assoc]
    have hinSplit01 :
        [a, b, c, d] <:+: xs ++ [u₀] ∨
          [a, b, c, d] <:+: u₁ :: (ys ++ [u₂]) := by
      exact List.path4_infix_left_or_right_of_split_middle_ne
        hnodupLeft23 hsplit01.symm hinLeft23 hb0 hb1 hc0 hc1
    rcases hinSplit01 with hinRight30 | hinLeft12
    · rcases hinRight30 with ⟨pre, post, hpre⟩
      exact Or.inr ⟨u₃ :: (zs ++ pre), post, by simpa [List.append_assoc] using hpre⟩
    · exact Or.inl hinLeft12
  · rcases hinRight23 with ⟨pre, post, hpre⟩
    exact Or.inr ⟨pre, post ++ xs ++ [u₀], by
      calc
        pre ++ [a, b, c, d] ++ (post ++ xs ++ [u₀])
            = (pre ++ [a, b, c, d] ++ post) ++ xs ++ [u₀] := by
                simp [List.append_assoc]
        _ = (u₃ :: zs) ++ xs ++ [u₀] := by rw [hpre]
        _ = u₃ :: ((zs ++ xs) ++ [u₀]) := by simp [List.append_assoc]⟩

theorem List.path3_infix_of_pair_pair_nodup
    {l : List V} (hnodup : List.Nodup l)
    {u₀ u₁ u₂ : V}
    (h01 : [u₀, u₁] <:+: l)
    (h12 : [u₁, u₂] <:+: l)
    (hu₂₀ : u₂ ≠ u₀) :
    [u₀, u₁, u₂] <:+: l := by
  rcases h01 with ⟨xs, ys, hsplit⟩
  have hmem12 : (u₁, u₂) ∈ edgePairs (xs ++ [u₀, u₁] ++ ys) := by
    simpa [hsplit] using mem_edgePairs_of_infix_pair h12
  have hnodup' : List.Nodup (xs ++ [u₀, u₁] ++ ys) := by
    simpa [hsplit] using hnodup
  have hnodup_left : List.Nodup (xs ++ ([u₀, u₁] ++ ys)) := by
    simpa [List.append_assoc] using hnodup'
  have hnodup_right : List.Nodup ((xs ++ [u₀, u₁]) ++ ys) := by
    simpa [List.append_assoc] using hnodup'
  rw [List.nodup_append] at hnodup_left hnodup_right
  have hu₁_not_xs : u₁ ∉ xs := by
    intro hu₁
    exact hnodup_left.2.2 u₁ hu₁ u₁ (by simp [List.mem_append]) rfl
  have hu₁_not_ys : u₁ ∉ ys := by
    intro hu₁
    exact hnodup_right.2.2 u₁ (by simp [List.mem_append]) u₁ hu₁ rfl
  rw [edgePairs_split_pair xs ys u₀ u₁] at hmem12
  rcases List.mem_append.1 hmem12 with hpre | hrest
  · have hpre' : [u₁, u₂] <:+: xs ++ [u₀] := infix_of_mem_edgePairs hpre
    have hpre'' : [u₁, u₂] <:+: xs :=
      List.pair_infix_of_infix_append_singleton hpre' hu₂₀
    exact False.elim (hu₁_not_xs (mem_of_mem_edgePairs_left (mem_edgePairs_of_infix_pair hpre'')))
  · rcases List.mem_cons.1 hrest with hbridge | hsuf
    · rcases Prod.mk.inj hbridge with ⟨hu₁₀, hu₂₁⟩
      exact False.elim (hu₂₀ (hu₂₁.trans hu₁₀))
    · have hsuf' : [u₁, u₂] <:+: u₁ :: ys := infix_of_mem_edgePairs hsuf
      rcases hsuf' with ⟨ys₀, zs, hsufSplit⟩
      cases ys₀ with
      | nil =>
          refine ⟨xs, zs, ?_⟩
          have hys : ys = u₂ :: zs := by
            simpa [List.append_assoc] using hsufSplit.symm
          simpa [hys, List.append_assoc] using hsplit
      | cons y ys₀' =>
          have hy : y = u₁ := by
            exact Option.some.inj (by simpa using congrArg List.head? hsufSplit)
          subst y
          have hu₁_in_ys : u₁ ∈ ys := by
            have htail : ys₀' ++ [u₁, u₂] ++ zs = ys := by
              exact Option.some.inj (by
                simpa [List.append_assoc] using congrArg List.tail? hsufSplit)
            rw [← htail]
            simp [List.mem_append, or_assoc, or_left_comm, or_comm]
          exact False.elim (hu₁_not_ys hu₁_in_ys)

/--
If a cyclic pair enters the first vertex of a deleted four-block, the pair is
preserved as the terminal pair of the rotated complement.
-/
theorem List.pair_infix_rotated_complement_enter_first_of_path4_split_cycle
    {s : V} {tail xs ys : List V} {u₃ u₀ u₁ u₂ a : V}
    (hnodup : List.Nodup (s :: tail))
    (hsplit : s :: tail = xs ++ [u₃, u₀, u₁, u₂] ++ ys)
    (hcyc : [a, u₃] <:+: s :: (tail ++ [s]))
    (ha₀ : a ≠ u₀)
    (ha₂ : a ≠ u₂) :
    [a, u₃] <:+: u₂ :: ((ys ++ xs) ++ [u₃]) := by
  by_cases hopen : [a, u₃] <:+: s :: tail
  · have h₃₀ : [u₃, u₀] <:+: s :: tail := by
      exact ⟨xs, u₁ :: u₂ :: ys, by simpa [List.append_assoc] using hsplit.symm⟩
    have hpath : [a, u₃, u₀] <:+: s :: tail :=
      List.path3_infix_of_pair_pair_nodup hnodup hopen h₃₀
        (by intro h; exact ha₀ h.symm)
    rcases hpath with ⟨pre, post, hpath⟩
    rcases
      List.split_pair_eq_of_nodup hnodup
        (xs := pre ++ [a]) (ys := post)
        (xs' := xs) (ys' := u₁ :: u₂ :: ys)
        (by simpa [List.append_assoc] using hpath)
        (by simpa [List.append_assoc] using hsplit.symm) with
      ⟨hxs, _hpost⟩
    refine ⟨u₂ :: (ys ++ pre), [], ?_⟩
    calc
      (u₂ :: (ys ++ pre)) ++ [a, u₃] ++ [] =
          u₂ :: ((ys ++ (pre ++ [a])) ++ [u₃]) := by
            simp [List.append_assoc]
      _ = u₂ :: ((ys ++ xs) ++ [u₃]) := by
            rw [hxs]
  · have hclosing :
        (∃ pre, s :: tail = pre ++ [a]) ∧ u₃ = s :=
      List.eq_append_singleton_and_eq_of_pair_infix_append_singleton_not_infix
        (l := s :: tail) (z := s) (by simpa using hcyc) hopen
    rcases hclosing with ⟨⟨pre, hlast⟩, hu₃s⟩
    cases xs with
    | nil =>
        rcases List.eq_nil_or_concat' ys with hys | ⟨ys', y, hys⟩
        · have ha₂' : a = u₂ := by
            have hpreLast : (pre ++ [a]).getLast? = some a := by
              simpa using
                (List.getLast?_append_of_ne_nil pre
                  (by simp : ([a] : List V) ≠ []))
            have hsplitLast :
                ([u₃, u₀, u₁, u₂] : List V).getLast? = some u₂ := by
              simp
            have hlastOpt : some a = some u₂ := by
              calc
                some a = (pre ++ [a]).getLast? := by simpa using hpreLast.symm
                _ = (s :: tail).getLast? := by rw [← hlast]
                _ = ([u₃, u₀, u₁, u₂] : List V).getLast? := by
                  rw [hsplit, hys]
                  simp
                _ = some u₂ := hsplitLast
            exact Option.some.inj hlastOpt
          exact False.elim (ha₂ ha₂')
        · have hy : y = a := by
            have hysLast :
                (([u₃, u₀, u₁, u₂] : List V) ++ (ys' ++ [y])).getLast? =
                  some y := by
              simpa [List.append_assoc] using
                (List.getLast?_append_of_ne_nil
                  (([u₃, u₀, u₁, u₂] : List V) ++ ys')
                  (by simp : ([y] : List V) ≠ []))
            have hpreLast : (pre ++ [a]).getLast? = some a := by
              simpa using
                (List.getLast?_append_of_ne_nil pre
                  (by simp : ([a] : List V) ≠ []))
            have hyOpt : some y = some a := by
              calc
                some y =
                    (([u₃, u₀, u₁, u₂] : List V) ++ (ys' ++ [y])).getLast? := by
                  simpa [List.append_assoc] using hysLast.symm
                _ = (s :: tail).getLast? := by
                  rw [hsplit, hys]
                  simp
                _ = (pre ++ [a]).getLast? := by rw [hlast]
                _ = some a := hpreLast
            exact Option.some.inj hyOpt
          refine ⟨u₂ :: ys', [], ?_⟩
          simp [hys, hy, List.append_assoc]
    | cons x xs' =>
        have hx : x = s := by
          exact (Option.some.inj (by simpa using congrArg List.head? hsplit)).symm
        subst x
        have htail :
            tail = xs' ++ [u₃, u₀, u₁, u₂] ++ ys := by
          simpa [List.append_assoc] using congrArg List.tail? hsplit
        have hs_mem_tail : s ∈ tail := by
          rw [htail]
          simp [hu₃s]
        exact False.elim ((List.nodup_cons.1 hnodup).1 hs_mem_tail)

theorem List.path4_infix_of_path3_pair_nodup
    {l : List V} (hnodup : List.Nodup l)
    {u₀ u₁ u₂ u₃ : V}
    (h012 : [u₀, u₁, u₂] <:+: l)
    (h23 : [u₂, u₃] <:+: l)
    (hu₂₀ : u₂ ≠ u₀)
    (hu₃₀ : u₃ ≠ u₀)
    (hu₃₁ : u₃ ≠ u₁) :
    [u₀, u₁, u₂, u₃] <:+: l := by
  rcases h012 with ⟨xs, ys, hsplit⟩
  have hmem23 : (u₂, u₃) ∈ edgePairs (xs ++ [u₀, u₁, u₂] ++ ys) := by
    simpa [hsplit] using mem_edgePairs_of_infix_pair h23
  have hnodup' : List.Nodup (xs ++ [u₀, u₁, u₂] ++ ys) := by
    simpa [hsplit] using hnodup
  have hnodup_left : List.Nodup (xs ++ ([u₀, u₁, u₂] ++ ys)) := by
    simpa [List.append_assoc] using hnodup'
  have hnodup_right : List.Nodup ((xs ++ [u₀, u₁, u₂]) ++ ys) := by
    simpa [List.append_assoc] using hnodup'
  rw [List.nodup_append] at hnodup_left hnodup_right
  have hmiddle_nodup : List.Nodup ([u₀, u₁, u₂] : List V) := by
    exact List.Nodup.of_append_left hnodup_left.2.1
  have hu₂₁ : u₂ ≠ u₁ := by
    have hu₁₂ : u₁ ≠ u₂ := by
      simpa using (show List.Nodup ([u₁, u₂] : List V) from by
        exact hmiddle_nodup.sublist (by simp))
    exact fun h => hu₁₂ h.symm
  have hu₂_not_ys : u₂ ∉ ys := by
    intro hu₂
    exact hnodup_right.2.2 u₂ (by simp [List.mem_append]) u₂ hu₂ rfl
  have hmem23' : (u₂, u₃) ∈ edgePairs (xs ++ [u₀, u₁] ++ u₂ :: ys) := by
    simpa [List.append_assoc] using hmem23
  rw [edgePairs_split_pair xs (u₂ :: ys) u₀ u₁] at hmem23'
  rcases List.mem_append.1 hmem23' with hpre | hrest
  · have hpre' : [u₂, u₃] <:+: xs ++ [u₀] := infix_of_mem_edgePairs hpre
    have hpre'' : [u₂, u₃] <:+: xs := by
      exact List.pair_infix_of_infix_append_singleton hpre' hu₃₀
    have hu₂_in_xs : u₂ ∈ xs := mem_of_mem_edgePairs_left (mem_edgePairs_of_infix_pair hpre'')
    exact False.elim (hnodup_left.2.2 u₂ hu₂_in_xs u₂ (by simp [List.mem_append]) rfl)
  · rcases List.mem_cons.1 hrest with hbridge | hsuf
    · rcases Prod.mk.inj hbridge with ⟨hu₂eq, _⟩
      exact False.elim (hu₂₀ hu₂eq)
    · have hsuf' : [u₂, u₃] <:+: u₁ :: u₂ :: ys := infix_of_mem_edgePairs hsuf
      have hsuf'' : [u₂, u₃] <:+: u₂ :: ys := by
        exact List.pair_infix_of_infix_cons hsuf' hu₂₁
      rcases hsuf'' with ⟨zs₀, zs, hsufSplit⟩
      cases zs₀ with
      | nil =>
          refine ⟨xs, zs, ?_⟩
          have hys : ys = u₃ :: zs := by
            simpa [List.append_assoc] using hsufSplit.symm
          simpa [hys, List.append_assoc] using hsplit
      | cons z zs₀' =>
          have hz : z = u₂ := by
            exact Option.some.inj (by simpa using congrArg List.head? hsufSplit)
          subst z
          have hu₂_in_ys : u₂ ∈ ys := by
            have htail : zs₀' ++ [u₂, u₃] ++ zs = ys := by
              exact Option.some.inj (by
                simpa [List.append_assoc] using congrArg List.tail? hsufSplit)
            rw [← htail]
            simp [List.mem_append, or_assoc, or_left_comm, or_comm]
          exact False.elim (hu₂_not_ys hu₂_in_ys)

theorem List.not_pair_pair_mismatch_nodup
    {l : List V} (hnodup : List.Nodup l)
    {u₀ u₁ u₂ : V}
    (h01 : [u₀, u₁] <:+: l)
    (h21 : [u₂, u₁] <:+: l)
    (hu₂₀ : u₂ ≠ u₀) :
    False := by
  rcases h01 with ⟨xs, ys, hsplit⟩
  rcases h21 with ⟨xs', ys', hsplit'⟩
  have hnodup01 : List.Nodup (xs ++ [u₀, u₁] ++ ys) := by
    simpa [hsplit] using hnodup
  have hnodup21 : List.Nodup (xs' ++ [u₂, u₁] ++ ys') := by
    simpa [hsplit'] using hnodup
  have hu₁₀ : u₁ ≠ u₀ := by
    have hpair : List.Nodup ([u₀, u₁] : List V) := by
      have haux : List.Nodup (xs ++ ([u₀, u₁] ++ ys)) := by
        simpa [List.append_assoc] using hnodup01
      rw [List.nodup_append] at haux
      exact List.Nodup.of_append_left haux.2.1
    have hu₀₁ : u₀ ≠ u₁ := by
      simpa using (show List.Nodup ([u₀, u₁] : List V) from hpair)
    exact fun h => hu₀₁ h.symm
  have hu₂₁ : u₂ ≠ u₁ := by
    have hpair : List.Nodup ([u₂, u₁] : List V) := by
      have haux : List.Nodup (xs' ++ ([u₂, u₁] ++ ys')) := by
        simpa [List.append_assoc] using hnodup21
      rw [List.nodup_append] at haux
      exact List.Nodup.of_append_left haux.2.1
    have hu₂₁' : u₂ ≠ u₁ := by
      simpa using (show List.Nodup ([u₂, u₁] : List V) from hpair)
    exact hu₂₁'
  have hmem21 : (u₂, u₁) ∈ edgePairs (xs ++ [u₀, u₁] ++ ys) := by
    rw [hsplit]
    exact mem_edgePairs_of_infix_pair ⟨xs', ys', hsplit'⟩
  have hnodup_left : List.Nodup (xs ++ ([u₀, u₁] ++ ys)) := by
    simpa [List.append_assoc] using hnodup01
  have hnodup_right : List.Nodup ((xs ++ [u₀, u₁]) ++ ys) := by
    simpa [List.append_assoc] using hnodup01
  rw [List.nodup_append] at hnodup_left hnodup_right
  have hu₁_not_xs : u₁ ∉ xs := by
    intro hu₁
    exact hnodup_left.2.2 u₁ hu₁ u₁ (by simp [List.mem_append]) rfl
  have hu₁_not_ys : u₁ ∉ ys := by
    intro hu₁
    exact hnodup_right.2.2 u₁ (by simp [List.mem_append]) u₁ hu₁ rfl
  rw [edgePairs_split_pair xs ys u₀ u₁] at hmem21
  rcases List.mem_append.1 hmem21 with hpre | hrest
  · have hpre' : [u₂, u₁] <:+: xs ++ [u₀] := infix_of_mem_edgePairs hpre
    have hpre'' : [u₂, u₁] <:+: xs := by
      exact List.pair_infix_of_infix_append_singleton hpre' hu₁₀
    exact hu₁_not_xs (mem_of_mem_edgePairs_right (mem_edgePairs_of_infix_pair hpre''))
  · rcases List.mem_cons.1 hrest with hbridge | hsuf
    · rcases Prod.mk.inj hbridge with ⟨hu₂eq, _⟩
      exact hu₂₀ hu₂eq
    · have hsuf' : [u₂, u₁] <:+: u₁ :: ys := infix_of_mem_edgePairs hsuf
      rcases hsuf' with ⟨zs₀, zs, hsufSplit⟩
      cases zs₀ with
      | nil =>
          have hu₂eq : u₂ = u₁ := by
            exact Option.some.inj (by
              simpa [List.append_assoc] using congrArg List.head? hsufSplit)
          exact hu₂₁ hu₂eq
      | cons z zs₀' =>
          have htail : z :: zs₀' ++ [u₂, u₁] ++ zs = u₁ :: ys := hsufSplit
          have hz : z = u₁ := by
            exact Option.some.inj (by simpa using congrArg List.head? htail)
          subst z
          exact hu₁_not_ys (by
            have htail' : zs₀' ++ [u₂, u₁] ++ zs = ys := by
              exact Option.some.inj (by
                simpa [List.append_assoc] using congrArg List.tail? htail)
            rw [← htail']
            simp [List.mem_append, or_assoc, or_left_comm, or_comm])

/-- A simple vertex list cannot contain both orientations of the same edge. -/
theorem List.not_reverse_pair_infix_of_nodup
    {l : List V} (hnodup : List.Nodup l)
    {x y : V} (hxy_ne : x ≠ y)
    (hxy : [x, y] <:+: l) :
    ¬ [y, x] <:+: l := by
  intro hyx
  rcases hxy with ⟨xs, ys, hsplit⟩
  have hnodupSplit : List.Nodup (xs ++ [x, y] ++ ys) := by
    simpa [hsplit] using hnodup
  have hyxMem : (y, x) ∈ edgePairs (xs ++ [x, y] ++ ys) := by
    rw [hsplit]
    exact mem_edgePairs_of_infix_pair hyx
  rw [edgePairs_split_pair xs ys x y] at hyxMem
  rcases List.mem_append.1 hyxMem with hpre | hrest
  · have hyMemPreAppend : y ∈ xs ++ [x] :=
      mem_of_mem_edgePairs_left hpre
    have hyMemPre : y ∈ xs := by
      rcases List.mem_append.1 hyMemPreAppend with hyxs | hyx
      · exact hyxs
      · have hy_eq_x : y = x := by
          simpa using hyx
        exact False.elim (hxy_ne hy_eq_x.symm)
    have hnodupLeft : List.Nodup (xs ++ ([x, y] ++ ys)) := by
      simpa [List.append_assoc] using hnodupSplit
    rw [List.nodup_append] at hnodupLeft
    exact hnodupLeft.2.2 y hyMemPre y (by simp) rfl
  · rcases List.mem_cons.1 hrest with hbridge | hsuf
    · rcases Prod.mk.inj hbridge with ⟨hyxEq, _⟩
      exact hxy_ne hyxEq.symm
    · have hxMemSuffix : x ∈ y :: ys :=
        mem_of_mem_edgePairs_right hsuf
      have hxMemYs : x ∈ ys := by
        rcases List.mem_cons.1 hxMemSuffix with hxy | hxys
        · exact False.elim (hxy_ne hxy)
        · exact hxys
      have hnodupRight : List.Nodup ((xs ++ [x, y]) ++ ys) := by
        simpa [List.append_assoc] using hnodupSplit
      rw [List.nodup_append] at hnodupRight
      exact hnodupRight.2.2 x (by simp [List.mem_append]) x hxMemYs rfl

theorem List.path3_infix_reverse
    {l : List V} {u₀ u₁ u₂ : V}
    (h : [u₀, u₁, u₂] <:+: l) :
    [u₂, u₁, u₀] <:+: l.reverse := by
  rcases h with ⟨xs, ys, hsplit⟩
  refine ⟨ys.reverse, xs.reverse, ?_⟩
  calc
    ys.reverse ++ [u₂, u₁, u₀] ++ xs.reverse = (xs ++ [u₀, u₁, u₂] ++ ys).reverse := by
      simp [List.reverse_reverse, List.reverse_append, List.reverse_cons, List.append_assoc]
    _ = l.reverse := by rw [hsplit]

theorem List.path4_infix_reverse
    {l : List V} {u₀ u₁ u₂ u₃ : V}
    (h : [u₀, u₁, u₂, u₃] <:+: l) :
    [u₃, u₂, u₁, u₀] <:+: l.reverse := by
  rcases h with ⟨xs, ys, hsplit⟩
  refine ⟨ys.reverse, xs.reverse, ?_⟩
  calc
    ys.reverse ++ [u₃, u₂, u₁, u₀] ++ xs.reverse =
        (xs ++ [u₀, u₁, u₂, u₃] ++ ys).reverse := by
      simp [List.reverse_reverse, List.reverse_append, List.reverse_cons, List.append_assoc]
    _ = l.reverse := by rw [hsplit]

theorem List.path3_infix_or_reverse_of_pair_pair_nodup
    {l : List V} (hnodup : List.Nodup l)
    {u₀ u₁ u₂ : V}
    (h01 : [u₀, u₁] <:+: l ∨ [u₁, u₀] <:+: l)
    (h12 : [u₁, u₂] <:+: l ∨ [u₂, u₁] <:+: l)
    (hu₂₀ : u₂ ≠ u₀) :
    [u₀, u₁, u₂] <:+: l ∨ [u₂, u₁, u₀] <:+: l := by
  rcases h01 with h01 | h10
  · rcases h12 with h12 | h21
    · exact Or.inl (List.path3_infix_of_pair_pair_nodup hnodup h01 h12 hu₂₀)
    · exact False.elim (List.not_pair_pair_mismatch_nodup hnodup h01 h21 hu₂₀)
  · rcases h12 with h12 | h21
    · have hnodup_rev : List.Nodup l.reverse := List.nodup_reverse.2 hnodup
      have h01_rev : [u₀, u₁] <:+: l.reverse := by
        simpa using List.pair_infix_reverse h10
      have h21_rev : [u₂, u₁] <:+: l.reverse := by
        simpa using List.pair_infix_reverse h12
      exact False.elim (List.not_pair_pair_mismatch_nodup hnodup_rev h01_rev h21_rev hu₂₀)
    · have hnodup_rev : List.Nodup l.reverse := List.nodup_reverse.2 hnodup
      have h01_rev : [u₀, u₁] <:+: l.reverse := by
        simpa using List.pair_infix_reverse h10
      have h12_rev : [u₁, u₂] <:+: l.reverse := by
        simpa using List.pair_infix_reverse h21
      have h012_rev : [u₀, u₁, u₂] <:+: l.reverse :=
        List.path3_infix_of_pair_pair_nodup hnodup_rev h01_rev h12_rev hu₂₀
      exact Or.inr (by simpa [List.reverse_reverse] using List.path3_infix_reverse h012_rev)

theorem List.path4_infix_or_reverse_of_three_pairs_nodup
    {l : List V} (hnodup : List.Nodup l)
    {u₀ u₁ u₂ u₃ : V}
    (h01 : [u₀, u₁] <:+: l ∨ [u₁, u₀] <:+: l)
    (h12 : [u₁, u₂] <:+: l ∨ [u₂, u₁] <:+: l)
    (h23 : [u₂, u₃] <:+: l ∨ [u₃, u₂] <:+: l)
    (hu₂₀ : u₂ ≠ u₀)
    (hu₃₀ : u₃ ≠ u₀)
    (hu₃₁ : u₃ ≠ u₁) :
    [u₀, u₁, u₂, u₃] <:+: l ∨ [u₃, u₂, u₁, u₀] <:+: l := by
  rcases List.path3_infix_or_reverse_of_pair_pair_nodup hnodup h01 h12 hu₂₀ with h012 | h210
  · rcases h23 with h23 | h32
    · exact Or.inl (List.path4_infix_of_path3_pair_nodup hnodup h012 h23 hu₂₀ hu₃₀ hu₃₁)
    · have h12' : [u₁, u₂] <:+: l := List.IsInfix.trans ⟨[u₀], [], by simp⟩ h012
      exact False.elim (List.not_pair_pair_mismatch_nodup hnodup h12' h32 hu₃₁)
  · rcases h23 with h23 | h32
    · have hnodup_rev : List.Nodup l.reverse := List.nodup_reverse.2 hnodup
      have h21 : [u₂, u₁] <:+: l := List.IsInfix.trans ⟨[], [u₀], by simp⟩ h210
      have h12_rev : [u₁, u₂] <:+: l.reverse := by
        simpa using List.pair_infix_reverse h21
      have h32_rev : [u₃, u₂] <:+: l.reverse := by
        simpa using List.pair_infix_reverse h23
      exact False.elim (List.not_pair_pair_mismatch_nodup hnodup_rev h12_rev h32_rev hu₃₁)
    · have hnodup_rev : List.Nodup l.reverse := List.nodup_reverse.2 hnodup
      have h012_rev : [u₀, u₁, u₂] <:+: l.reverse := by
        simpa [List.reverse_reverse] using List.path3_infix_reverse h210
      have h23_rev : [u₂, u₃] <:+: l.reverse := by
        simpa using List.pair_infix_reverse h32
      have h0123_rev : [u₀, u₁, u₂, u₃] <:+: l.reverse :=
        List.path4_infix_of_path3_pair_nodup hnodup_rev h012_rev h23_rev hu₂₀ hu₃₀ hu₃₁
      exact Or.inr (by simpa [List.reverse_reverse] using List.path4_infix_reverse h0123_rev)

theorem List.not_pair_infix_of_nodup_append_singleton
    {l : List V} {t u : V}
    (hnodup : List.Nodup (l ++ [t]))
    (htu : t ≠ u) :
    ¬ [t, u] <:+: l ++ [t] := by
  intro htu_infix
  have htu_infix' : [t, u] <:+: l := by
    exact List.pair_infix_of_infix_append_singleton htu_infix (fun h => htu h.symm)
  have ht_mem_l : t ∈ l := mem_of_mem_edgePairs_left (mem_edgePairs_of_infix_pair htu_infix')
  rw [List.nodup_append] at hnodup
  exact hnodup.2.2 t ht_mem_l t (by simp) rfl

theorem List.path3_infix_of_edge_or_reverse_with_last_nodup
    {l : List V} {u₁ u₂ u₃ : V}
    (hnodup : List.Nodup (l ++ [u₃]))
    (h12 : [u₁, u₂] <:+: l ++ [u₃] ∨ [u₂, u₁] <:+: l ++ [u₃])
    (h23 : [u₂, u₃] <:+: l ++ [u₃] ∨ [u₃, u₂] <:+: l ++ [u₃])
    (hu₃₂ : u₃ ≠ u₂)
    (hu₃₁ : u₃ ≠ u₁) :
    [u₁, u₂, u₃] <:+: l ++ [u₃] := by
  rcases h23 with h23 | h32
  · rcases h12 with h12 | h21
    · exact List.path3_infix_of_pair_pair_nodup hnodup h12 h23 hu₃₁
    · have hnodup_rev : List.Nodup ((l ++ [u₃]).reverse) := List.nodup_reverse.2 hnodup
      have h12_rev : [u₁, u₂] <:+: (l ++ [u₃]).reverse := List.pair_infix_reverse h21
      have h32_rev : [u₃, u₂] <:+: (l ++ [u₃]).reverse := List.pair_infix_reverse h23
      exact False.elim (List.not_pair_pair_mismatch_nodup hnodup_rev h12_rev h32_rev hu₃₁)
  · exact False.elim (List.not_pair_infix_of_nodup_append_singleton hnodup hu₃₂ h32)

theorem OrderedSegmentFamily.BoundaryCycleWitness.path3_infix_of_edge_or_reverse_with_terminal
    {Adj : V → V → Prop}
    {support : Finset V} {s u₁ u₂ u₃ : V}
    (w : OrderedSegmentFamily.BoundaryCycleWitness Adj support s u₃)
    (h12 : [u₁, u₂] <:+: s :: w.toSpanningPath.tail ∨
      [u₂, u₁] <:+: s :: w.toSpanningPath.tail)
    (h23 : [u₂, u₃] <:+: s :: w.toSpanningPath.tail ∨
      [u₃, u₂] <:+: s :: w.toSpanningPath.tail)
    (hu₃₂ : u₃ ≠ u₂)
    (hu₃₁ : u₃ ≠ u₁) :
    [u₁, u₂, u₃] <:+: s :: w.toSpanningPath.tail := by
  have hnodup : List.Nodup ((s :: w.middle) ++ [u₃]) := by
    simpa [OrderedSegmentFamily.BoundaryCycleWitness.toSpanningPath, List.append_assoc] using w.nodup
  simpa [OrderedSegmentFamily.BoundaryCycleWitness.toSpanningPath, List.append_assoc] using
    List.path3_infix_of_edge_or_reverse_with_last_nodup hnodup h12 h23 hu₃₂ hu₃₁

/--
If a contiguous triple starts with the head of a nodup list, it must occur as
an actual prefix rather than later in the list.
-/
theorem List.path3_prefix_of_head_infix_nodup
    {l : List V} {s u v : V}
    (hnodup : List.Nodup (s :: l))
    (hinfix : [s, u, v] <:+: s :: l) :
    ∃ ys, s :: l = [s, u, v] ++ ys := by
  rcases hinfix with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      exact ⟨ys, by simpa using hsplit.symm⟩
  | cons x xs' =>
      have hx : x = s := by
        exact Option.some.inj (by simpa using congrArg List.head? hsplit)
      subst x
      have htail : l = xs' ++ [s, u, v] ++ ys := by
        exact (Option.some.inj (by
          simpa [List.append_assoc] using congrArg List.tail? hsplit)).symm
      have hs_mem_l : s ∈ l := by
        rw [htail]
        simp [List.mem_append, or_assoc, or_left_comm, or_comm]
      exact False.elim ((List.nodup_cons.1 hnodup).1 hs_mem_l)

theorem List.pair_prefix_of_head_infix_nodup
    {l : List V} {s u : V}
    (hnodup : List.Nodup (s :: l))
    (hinfix : [s, u] <:+: s :: l) :
    ∃ ys, s :: l = [s, u] ++ ys := by
  rcases hinfix with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      exact ⟨ys, by simpa using hsplit.symm⟩
  | cons x xs' =>
      have hx : x = s := by
        exact Option.some.inj (by simpa using congrArg List.head? hsplit)
      subst x
      have htail : l = xs' ++ [s, u] ++ ys := by
        exact (Option.some.inj (by
          simpa [List.append_assoc] using congrArg List.tail? hsplit)).symm
      have hs_mem_l : s ∈ l := by
        rw [htail]
        simp [List.mem_append, or_assoc, or_left_comm, or_comm]
      exact False.elim ((List.nodup_cons.1 hnodup).1 hs_mem_l)

theorem List.path4_prefix_of_head_infix_nodup
    {l : List V} {s u v w : V}
    (hnodup : List.Nodup (s :: l))
    (hinfix : [s, u, v, w] <:+: s :: l) :
    ∃ ys, s :: l = [s, u, v, w] ++ ys := by
  rcases hinfix with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      exact ⟨ys, by simpa using hsplit.symm⟩
  | cons x xs' =>
      have hx : x = s := by
        exact Option.some.inj (by simpa using congrArg List.head? hsplit)
      subst x
      have htail : l = xs' ++ [s, u, v, w] ++ ys := by
        exact (Option.some.inj (by
          simpa [List.append_assoc] using congrArg List.tail? hsplit)).symm
      have hs_mem_l : s ∈ l := by
        rw [htail]
        simp [List.mem_append, or_assoc, or_left_comm, or_comm]
      exact False.elim ((List.nodup_cons.1 hnodup).1 hs_mem_l)

/--
If a reversed open witness begins with `[u₀, c, b, a]` while the original open
split is `u₀-u₁ ... u₂-u₃ ...`, then the unreversed `P4` lies on the `u₃-u₀`
side. The only excluded short crossings are the two cases that would force one
of the internal `P4` vertices to be the seam vertex `u₃`.
-/
theorem List.path4_infix_rightSide_of_reverse_prefix_split
    {u₀ u₁ u₂ u₃ a b c : V} {ys zs rs : List V}
    (hprefix :
      (u₁ :: ys ++ [u₂, u₃] ++ zs).reverse = [c, b, a] ++ rs)
    (hc3 : c ≠ u₃)
    (hb3 : b ≠ u₃) :
    [a, b, c, u₀] <:+: u₃ :: (zs ++ [u₀]) := by
  rcases List.eq_nil_or_concat' zs with hzs | ⟨zs₁, zc, hzs⟩
  · have hcu3 : c = u₃ := by
      have hhead := congrArg List.head? hprefix
      have hsome : some u₃ = some c := by
        simpa [hzs, List.reverse_append, List.append_assoc] using hhead
      exact (Option.some.inj hsome).symm
    exact False.elim (hc3 hcu3)
  · have hzc : zc = c := by
      have hhead := congrArg List.head? hprefix
      have hsome : some zc = some c := by
        simpa [hzs, List.reverse_append, List.append_assoc] using hhead
      exact Option.some.inj hsome
    have htail :
        zs₁.reverse ++ [u₃, u₂] ++ ys.reverse ++ [u₁] = [b, a] ++ rs := by
      have htail? := congrArg List.tail? hprefix
      exact Option.some.inj (by
        simpa [hzs, hzc, List.reverse_append, List.append_assoc] using htail?)
    rcases List.eq_nil_or_concat' zs₁ with hzs₁ | ⟨zs₂, zb, hzs₁⟩
    · have hbu3 : b = u₃ := by
        have hhead := congrArg List.head? htail
        have hsome : some u₃ = some b := by
          simpa [hzs₁, List.reverse_append, List.append_assoc] using hhead
        exact (Option.some.inj hsome).symm
      exact False.elim (hb3 hbu3)
    · have hzb : zb = b := by
        have hhead := congrArg List.head? htail
        have hsome : some zb = some b := by
          simpa [hzs₁, List.reverse_append, List.append_assoc] using hhead
        exact Option.some.inj hsome
      have htail₂ :
          zs₂.reverse ++ [u₃, u₂] ++ ys.reverse ++ [u₁] = [a] ++ rs := by
        have htail? := congrArg List.tail? htail
        exact Option.some.inj (by
          simpa [hzs₁, hzb, List.reverse_append, List.append_assoc] using htail?)
      rcases List.eq_nil_or_concat' zs₂ with hzs₂ | ⟨zs₃, za, hzs₂⟩
      · have hau3 : a = u₃ := by
          have hhead := congrArg List.head? htail₂
          have hsome : some u₃ = some a := by
            simpa [hzs₂, List.reverse_append, List.append_assoc] using hhead
          exact (Option.some.inj hsome).symm
        refine ⟨[], [], ?_⟩
        simp [hzs, hzs₁, hzs₂, hzc, hzb, hau3]
      · have hza : za = a := by
          have hhead := congrArg List.head? htail₂
          have hsome : some za = some a := by
            simpa [hzs₂, List.reverse_append, List.append_assoc] using hhead
          exact Option.some.inj hsome
        refine ⟨u₃ :: zs₃, [], ?_⟩
        simp [hzs, hzs₁, hzs₂, hzc, hzb, hza, List.append_assoc]

/--
Endpoint-incompatible variant of
`List.path4_infix_rightSide_of_reverse_prefix_split`.

If a reverse-open prefix starts with `s,c,b,a`, and the original open split has
an initial non-seam segment `s :: xs` before the first seam edge, the unreversed
`P4` lies on the cyclic right side `u₃ ... s ... u₀`.
-/
theorem List.path4_infix_rightSide_of_reverse_prefix_open_split
    {s u₀ u₁ u₂ u₃ a b c : V} {xs ys zs rs : List V}
    (hprefix :
      (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs).reverse = [c, b, a] ++ rs)
    (hc3 : c ≠ u₃)
    (hb3 : b ≠ u₃) :
    [a, b, c, s] <:+: u₃ :: ((zs ++ (s :: xs)) ++ [u₀]) := by
  rcases List.eq_nil_or_concat' zs with hzs | ⟨zs₁, zc, hzs⟩
  · have hcu3 : c = u₃ := by
      have hhead := congrArg List.head? hprefix
      have hsome : some u₃ = some c := by
        simpa [hzs, List.reverse_append, List.append_assoc] using hhead
      exact (Option.some.inj hsome).symm
    exact False.elim (hc3 hcu3)
  · have hzc : zc = c := by
      have hhead := congrArg List.head? hprefix
      have hsome : some zc = some c := by
        simpa [hzs, List.reverse_append, List.append_assoc] using hhead
      exact Option.some.inj hsome
    have htail :
        zs₁.reverse ++ [u₃, u₂] ++ ys.reverse ++ [u₁, u₀] ++ xs.reverse =
          [b, a] ++ rs := by
      have htail? := congrArg List.tail? hprefix
      exact Option.some.inj (by
        simpa [hzs, hzc, List.reverse_append, List.append_assoc] using htail?)
    rcases List.eq_nil_or_concat' zs₁ with hzs₁ | ⟨zs₂, zb, hzs₁⟩
    · have hbu3 : b = u₃ := by
        have hhead := congrArg List.head? htail
        have hsome : some u₃ = some b := by
          simpa [hzs₁, List.reverse_append, List.append_assoc] using hhead
        exact (Option.some.inj hsome).symm
      exact False.elim (hb3 hbu3)
    · have hzb : zb = b := by
        have hhead := congrArg List.head? htail
        have hsome : some zb = some b := by
          simpa [hzs₁, List.reverse_append, List.append_assoc] using hhead
        exact Option.some.inj hsome
      have htail₂ :
          zs₂.reverse ++ [u₃, u₂] ++ ys.reverse ++ [u₁, u₀] ++ xs.reverse =
            [a] ++ rs := by
        have htail? := congrArg List.tail? htail
        exact Option.some.inj (by
          simpa [hzs₁, hzb, List.reverse_append, List.append_assoc] using htail?)
      rcases List.eq_nil_or_concat' zs₂ with hzs₂ | ⟨zs₃, za, hzs₂⟩
      · have hau3 : a = u₃ := by
          have hhead := congrArg List.head? htail₂
          have hsome : some u₃ = some a := by
            simpa [hzs₂, List.reverse_append, List.append_assoc] using hhead
          exact (Option.some.inj hsome).symm
        refine ⟨[], xs ++ [u₀], ?_⟩
        simp [hzs, hzs₁, hzs₂, hzc, hzb, hau3, List.append_assoc]
      · have hza : za = a := by
          have hhead := congrArg List.head? htail₂
          have hsome : some za = some a := by
            simpa [hzs₂, List.reverse_append, List.append_assoc] using hhead
          exact Option.some.inj hsome
        refine ⟨u₃ :: zs₃, xs ++ [u₀], ?_⟩
        simp [hzs, hzs₁, hzs₂, hzc, hzb, hza, List.append_assoc]

/-- A nodup list cannot contain its head as the last vertex of a length-four infix. -/
theorem List.not_path4_infix_last_eq_head_nodup
    {l : List V} {s u v w : V}
    (hnodup : List.Nodup (s :: l))
    (hinfix : [u, v, w, s] <:+: s :: l) :
    False := by
  rcases hinfix with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      have htail : l = v :: w :: s :: ys := by
        exact Option.some.inj (by
          simpa [List.append_assoc] using congrArg List.tail? hsplit.symm)
      have hs_mem_l : s ∈ l := by
        rw [htail]
        simp
      exact (List.nodup_cons.1 hnodup).1 hs_mem_l
  | cons x xs' =>
      have hx : x = s := by
        exact Option.some.inj (by simpa using congrArg List.head? hsplit)
      subst x
      have htail : l = xs' ++ [u, v, w, s] ++ ys := by
        exact (Option.some.inj (by
          simpa [List.append_assoc] using congrArg List.tail? hsplit)).symm
      have hs_mem_l : s ∈ l := by
        rw [htail]
        simp [List.mem_append, or_assoc, or_left_comm, or_comm]
      exact (List.nodup_cons.1 hnodup).1 hs_mem_l

/--
If the opened boundary path begins with a seam triple `s-u-v`, then the middle
list of the boundary witness begins with `u-v`.
-/
theorem OrderedSegmentFamily.BoundaryCycleWitness.middle_split_of_head_path3_infix
    {Adj : V → V → Prop}
    {support : Finset V} {s t u v : V}
    (w : OrderedSegmentFamily.BoundaryCycleWitness Adj support s t)
    (hinfix : [s, u, v] <:+: s :: w.toSpanningPath.tail)
    (hvt : v ≠ t) :
    ∃ ys, w.middle = u :: v :: ys := by
  have hnodup : List.Nodup (s :: w.toSpanningPath.tail) := by
    simpa [OrderedSegmentFamily.BoundaryCycleWitness.toSpanningPath, List.append_assoc] using w.nodup
  obtain ⟨zs, hprefix⟩ := List.path3_prefix_of_head_infix_nodup hnodup hinfix
  have htail : w.middle ++ [t] = [u, v] ++ zs := by
    exact Option.some.inj (by
      simpa [OrderedSegmentFamily.BoundaryCycleWitness.toSpanningPath, List.append_assoc] using
        congrArg List.tail? hprefix)
  have hzs_ne : zs ≠ [] := by
    intro hzs
    have htv : some t = some v := by
      calc
        some t = (w.middle ++ [t]).getLast? := by
          simpa using
            (List.getLast?_append_of_ne_nil w.middle (by simp : ([t] : List V) ≠ []))
        _ = ([u, v] : List V).getLast? := by simpa [hzs] using congrArg List.getLast? htail
        _ = some v := by simp
    exact hvt (Option.some.inj htv).symm
  rcases List.eq_nil_or_concat' zs with hzs | ⟨ys, z, hzs⟩
  · exact False.elim (hzs_ne hzs)
  have htz : some t = some z := by
    calc
      some t = (w.middle ++ [t]).getLast? := by
        simpa using
          (List.getLast?_append_of_ne_nil w.middle (by simp : ([t] : List V) ≠ []))
      _ = ([u, v] ++ ys ++ [z]).getLast? := by
        simpa [hzs, List.append_assoc] using congrArg List.getLast? htail
      _ = some z := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil ([u, v] ++ ys) (by simp : ([z] : List V) ≠ []))
  have hz : z = t := (Option.some.inj htz).symm
  refine ⟨ys, ?_⟩
  exact (List.append_left_injective [t]) (by
    simpa [hzs, hz, List.append_assoc] using htail)

/--
If a length-`4` infix lies in a list with a designated two-vertex prefix, and
its second vertex is not the second vertex of that prefix, then the infix
already lies in the tail after the first vertex.
-/
theorem List.path4_infix_tail_of_second_ne
    {l : List V} {x y a b c d : V}
    (hinfix : [a, b, c, d] <:+: x :: y :: l)
    (hby : b ≠ y) :
    [a, b, c, d] <:+: y :: l := by
  rcases hinfix with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      have hby_eq : b = y := by
        exact Option.some.inj (by
          simpa [List.append_assoc] using congrArg (fun t => t.tail?.bind List.head?) hsplit)
      exact False.elim (hby hby_eq)
  | cons z xs' =>
      have hz : z = x := by
        exact Option.some.inj (by simpa using congrArg List.head? hsplit)
      subst z
      refine ⟨xs', ys, ?_⟩
      exact Option.some.inj (by
        simpa [List.append_assoc] using congrArg List.tail? hsplit)

/--
If a length-`4` infix lies in a list with a designated head vertex, and its first
vertex is not that head, then the infix already lies in the tail.
-/
theorem List.path4_infix_of_infix_cons
    {l : List V} {z a b c d : V}
    (h : [a, b, c, d] <:+: z :: l)
    (haz : a ≠ z) :
    [a, b, c, d] <:+: l := by
  rcases h with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      have ha : a = z := by
        exact (Option.some.inj (by simpa using congrArg List.head? hsplit.symm)).symm
      exact False.elim (haz ha)
  | cons x xs' =>
      have hx : x = z := by
        exact (Option.some.inj (by simpa using congrArg List.head? hsplit.symm)).symm
      refine ⟨xs', ys, ?_⟩
      exact (Option.some.inj (by simpa [hx] using congrArg List.tail? hsplit.symm)).symm

/--
If a length-`4` infix lies in a list with a designated final vertex, and its last
vertex is not that final vertex, then the infix already lies in the prefix before it.
-/
theorem List.path4_infix_of_infix_append_singleton
    {l : List V} {a b c d z : V}
    (h : [a, b, c, d] <:+: l ++ [z])
    (hdz : d ≠ z) :
    [a, b, c, d] <:+: l := by
  rcases h with ⟨xs, ys, hsplit⟩
  rcases List.eq_nil_or_concat' ys with hys | ⟨ys', y, hys⟩
  · subst hys
    have hd : d = z := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [a, b, c, d]).getLast? = some d := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil xs (by simp : ([a, b, c, d] : List V) ≠ []))
      have hright : (l ++ [z]).getLast? = some z := by
        simpa using
          (List.getLast?_append_of_ne_nil l (by simp : ([z] : List V) ≠ []))
      have hdOpt : some d = some z := by
        calc
          some d = (xs ++ [a, b, c, d]).getLast? := by simpa using hleft.symm
          _ = (l ++ [z]).getLast? := by simpa using hlast
          _ = some z := hright
      exact Option.some.inj hdOpt
    exact False.elim (hdz hd)
  · have hy : y = z := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [a, b, c, d] ++ ys' ++ [y]).getLast? = some y := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [a, b, c, d] ++ ys')
            (by simp : ([y] : List V) ≠ []))
      have hright : (l ++ [z]).getLast? = some z := by
        simpa using
          (List.getLast?_append_of_ne_nil l (by simp : ([z] : List V) ≠ []))
      have hyOpt : some y = some z := by
        calc
          some y = (xs ++ [a, b, c, d] ++ (ys' ++ [y])).getLast? := by
            simpa [hys, List.append_assoc] using hleft.symm
          _ = (l ++ [z]).getLast? := by
            simpa [hys] using hlast
          _ = some z := hright
      exact Option.some.inj hyOpt
    refine ⟨xs, ys', ?_⟩
    apply (List.append_left_injective [z])
    simpa [hys, hy, List.append_assoc] using hsplit

/--
A cyclic occurrence of a length-four mark is already open if its last vertex is
not the closing/start vertex.
-/
theorem List.path4_open_of_cyclic_append_of_last_ne_start
    {tail : List V} {s a b c d : V}
    (h : [a, b, c, d] <:+: s :: (tail ++ [s]))
    (hds : d ≠ s) :
    [a, b, c, d] <:+: s :: tail := by
  simpa using
    (List.path4_infix_of_infix_append_singleton
      (l := s :: tail) (z := s) h hds)

/--
The reversed endpoint pair can never occur as a consecutive edge in a simple
spanning path: the start vertex does not reappear later in the list.
-/
theorem ListSpanningPath.not_mem_edgePairs_end_start
    {Adj : V → V → Prop} {S₁ : Finset V} {s t : V}
    (p : ListSpanningPath Adj S₁ s t) :
    (t, s) ∉ edgePairs (s :: p.tail) := by
  intro hts
  have hs_not_tail : s ∉ p.tail := (List.nodup_cons.1 p.nodup).1
  rcases infix_of_mem_edgePairs hts with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      have htail : p.tail = s :: ys := by
        exact Option.some.inj (by simpa using congrArg List.tail? hsplit.symm)
      exact hs_not_tail (by simpa [htail])
  | cons x xs' =>
      have hx : s = x := by
        exact Option.some.inj (by simpa using congrArg List.head? hsplit.symm)
      subst x
      have htail : p.tail = xs' ++ [t, s] ++ ys := by
        exact Option.some.inj (by simpa [List.append_assoc] using congrArg List.tail? hsplit.symm)
      exact hs_not_tail (by simp [htail, List.mem_append, or_assoc, or_left_comm, or_comm])

/--
If the endpoint pair appears as a consecutive edge at the start of a simple
spanning path, then the path is exactly that single edge.
-/
theorem ListSpanningPath.tail_eq_singleton_of_mem_edgePairs_start_end
    {Adj : V → V → Prop} {S₁ : Finset V} {s t : V}
    (p : ListSpanningPath Adj S₁ s t)
    (hst : (s, t) ∈ edgePairs (s :: p.tail)) :
    p.tail = [t] := by
  have hs_not_tail : s ∉ p.tail := (List.nodup_cons.1 p.nodup).1
  rcases infix_of_mem_edgePairs hst with ⟨xs, ys, hsplit⟩
  cases xs with
  | nil =>
      have htail : p.tail = t :: ys := by
        exact Option.some.inj (by simpa using congrArg List.tail? hsplit.symm)
      cases ys with
      | nil =>
          simpa [htail]
      | cons y ys' =>
          have hyend : endVertex y ys' = t := by
            simpa [htail, endVertex] using p.ends_at
          have ht_in_rest : t ∈ y :: ys' := by
            simpa [hyend] using (endVertex_mem_cons y ys')
          have htail_nodup : List.Nodup (t :: y :: ys') := by
            simpa [htail] using List.Nodup.of_cons p.nodup
          exact False.elim ((List.nodup_cons.1 htail_nodup).1 ht_in_rest)
  | cons x xs' =>
      have hx : s = x := by
        exact Option.some.inj (by simpa using congrArg List.head? hsplit.symm)
      subst x
      have htail : p.tail = xs' ++ [s, t] ++ ys := by
        exact Option.some.inj (by simpa [List.append_assoc] using congrArg List.tail? hsplit.symm)
      exact False.elim (hs_not_tail (by simp [htail, List.mem_append, or_assoc, or_left_comm, or_comm]))

/--
Any support vertex distinct from both endpoints certifies that the path is not
the single edge from `s` to `t`.
-/
theorem ListSpanningPath.tail_ne_singleton_of_support_vertex_ne_endpoints
    {Adj : V → V → Prop} {S₁ : Finset V} {s t v : V}
    (p : ListSpanningPath Adj S₁ s t)
    (hv : v ∈ S₁)
    (hvs : v ≠ s)
    (hvt : v ≠ t) :
    p.tail ≠ [t] := by
  intro htail
  have hv' : v ∈ s :: p.tail := (p.spans v).1 hv
  simp [htail, hvs, hvt] at hv'

/--
If the endpoints are not adjacent, the path cannot be the direct one-edge path.
-/
theorem ListSpanningPath.tail_ne_singleton_of_not_adj
    {Adj : V → V → Prop} {S₁ : Finset V} {s t : V}
    (p : ListSpanningPath Adj S₁ s t)
    (hnot : ¬ Adj s t) :
    p.tail ≠ [t] := by
  intro htail
  have hmem : (s, t) ∈ edgePairs (s :: p.tail) := by
    rw [htail]
    simp [edgePairs]
  exact hnot (p.adj hmem)

/--
View a Hamiltonian cycle witness as a boundary-cycle witness once its tail is
explicitly split as `middle ++ [t]`, so the closing edge is `t -> start`.
-/
def HamiltonianCycleWitness.toBoundaryCycleWitness
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (middle : List V) (t : V)
    (htail : w.tail = middle ++ [t]) :
    OrderedSegmentFamily.BoundaryCycleWitness G.Adj (Finset.univ : Finset V) w.start t where
  middle := middle
  cycle_adj := by
    intro a b hab
    have hab' : (a, b) ∈ edgePairs (w.start :: (w.tail ++ [w.start])) := by
      simpa [htail, List.append_assoc] using hab
    exact w.cycle_adj hab'
  nodup := by
    simpa [htail] using w.nodup
  spans := by
    intro v
    rw [w.spans v]
    simp [htail]

/--
Rotate an explicit Hamiltonian cycle witness forward by one vertex.

If the open support list is `start :: v :: vs`, the rotated witness starts at
`v` and ends with the former start vertex.
-/
def HamiltonianCycleWitness.rotateOnce
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    (v : V) (vs : List V)
    (htail : w.tail = v :: vs) :
    HamiltonianCycleWitness G.Adj S where
  start := v
  tail := vs ++ [w.start]
  cycle_adj := by
    intro a b hab
    rw [edgePairs_append] at hab
    rcases List.mem_append.1 hab with hab | hab
    · have hab' : (a, b) ∈ edgePairs (w.start :: w.tail ++ [w.start]) := by
        rw [htail]
        exact List.mem_cons_of_mem _ hab
      exact w.cycle_adj hab'
    · have hab' : (a, b) = (w.start, v) := by
        have hend : endVertex v (vs ++ [w.start]) = w.start := by
          rw [endVertex_append]
          simp [endVertex]
        simpa [htail, hend, edgePairs] using hab
      rcases hab' with ⟨rfl, rfl⟩
      exact w.cycle_adj (by simpa [htail, edgePairs])
  nodup := by
    have hrot :
        List.Nodup ((w.start :: w.tail).rotate 1) := by
      exact (List.nodup_rotate (l := w.start :: w.tail) (n := 1)).2 w.nodup
    simpa [htail] using hrot
  spans := by
    intro x
    rw [w.spans x]
    have hmem :
        x ∈ (w.start :: w.tail).rotate 1 ↔ x ∈ w.start :: w.tail :=
      List.mem_rotate (l := w.start :: w.tail) (a := x) (n := 1)
    simpa [htail] using hmem.symm

@[simp] theorem HamiltonianCycleWitness.openList_rotateOnce
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    (v : V) (vs : List V)
    (htail : w.tail = v :: vs) :
    (w.rotateOnce v vs htail).start :: (w.rotateOnce v vs htail).tail =
      w.tail ++ [w.start] := by
  simp [HamiltonianCycleWitness.rotateOnce, htail]

/-- The endpoint of a nonempty tail is its last vertex. -/
theorem endVertex_eq_getLast
    (u : V) {vs : List V} (h : vs ≠ []) :
    endVertex u vs = vs.getLast h := by
  induction vs generalizing u with
  | nil =>
      contradiction
  | cons v vs ih =>
      cases vs with
      | nil =>
          simp [endVertex]
      | cons w ws =>
          simpa [endVertex] using (ih (u := v) (h := List.cons_ne_nil _ _))

theorem ListSpanningPath.tail_eq_dropLast_append_end
    {Adj : V → V → Prop} {S : Finset V} {s t : V}
    (p : ListSpanningPath Adj S s t)
    (htail_ne : p.tail ≠ []) :
    p.tail = p.tail.dropLast ++ [t] := by
  have hlast : p.tail.getLast htail_ne = t := by
    rw [← endVertex_eq_getLast (u := s) htail_ne, p.ends_at]
  simpa [hlast] using (List.dropLast_append_getLast htail_ne).symm

/-- A spanning path with distinct endpoints has a nonempty tail. -/
theorem ListSpanningPath.tail_ne_nil_of_start_ne_end
    {Adj : V → V → Prop} {S : Finset V} {s t : V}
    (p : ListSpanningPath Adj S s t)
    (hst : s ≠ t) :
    p.tail ≠ [] := by
  intro hnil
  have hEq : s = t := by
    simpa [hnil, endVertex] using p.ends_at
  exact hst hEq

/--
A non-direct spanning path with distinct endpoints has a penultimate vertex
before its endpoint.
-/
theorem ListSpanningPath.exists_tail_eq_append_pair_of_tail_ne_singleton
    {Adj : V → V → Prop} {S : Finset V} {s t : V}
    (p : ListSpanningPath Adj S s t)
    (hst : s ≠ t)
    (hnot : p.tail ≠ [t]) :
    ∃ middle x, p.tail = middle ++ [x, t] := by
  have htail_ne : p.tail ≠ [] := by
    intro hnil
    have hEq : s = t := by
      simpa [hnil, endVertex] using p.ends_at
    exact hst hEq
  have hdrop_ne : p.tail.dropLast ≠ [] := by
    intro hdrop
    exact hnot (by simpa [hdrop] using p.tail_eq_dropLast_append_end htail_ne)
  rcases List.eq_nil_or_concat' p.tail.dropLast with hdrop | ⟨middle, x, hmiddle⟩
  · exact False.elim (hdrop_ne hdrop)
  refine ⟨middle, x, ?_⟩
  calc
    p.tail = p.tail.dropLast ++ [t] := p.tail_eq_dropLast_append_end htail_ne
    _ = (middle ++ [x]) ++ [t] := by rw [hmiddle]
    _ = middle ++ [x, t] := by simp [List.append_assoc]

/--
Reverse a concrete spanning path in a simple graph.

The reversed path traverses the same vertex set in the opposite order.
-/
def ListSpanningPath.reverse
    {G : SimpleGraph V} {S : Finset V} {s t : V}
    (p : ListSpanningPath G.Adj S s t)
    (htail_ne : p.tail ≠ []) :
    ListSpanningPath G.Adj ((t :: (p.tail.dropLast.reverse ++ [s])).toFinset) t s where
  tail := p.tail.dropLast.reverse ++ [s]
  ends_at := by
    rw [endVertex_append]
    simp [endVertex]
  adj := by
    intro a b hab
    have hrev : [a, b] <:+: t :: (p.tail.dropLast.reverse ++ [s]) :=
      infix_of_mem_edgePairs hab
    have htail : p.tail = p.tail.dropLast ++ [t] :=
      p.tail_eq_dropLast_append_end htail_ne
    have hrev' : [a, b] <:+: (s :: p.tail).reverse := by
      have hEq : t :: (p.tail.dropLast.reverse ++ [s]) = (s :: p.tail).reverse := by
        rw [htail, List.reverse_cons, List.reverse_append]
        simp [List.append_assoc]
      rw [hEq] at hrev
      exact hrev
    have horig : [b, a] <:+: s :: p.tail := by
      simpa [List.reverse_reverse] using List.pair_infix_reverse hrev'
    exact (p.adj (mem_edgePairs_of_infix_pair horig)).symm
  nodup := by
    have htail : p.tail = p.tail.dropLast ++ [t] :=
      p.tail_eq_dropLast_append_end htail_ne
    have hrev :
        t :: (p.tail.dropLast.reverse ++ [s]) = (s :: p.tail).reverse := by
      rw [htail, List.reverse_cons, List.reverse_append]
      simp [List.append_assoc]
    rw [hrev]
    exact List.nodup_reverse.2 p.nodup
  spans := by
    intro v
    rw [List.mem_toFinset]

/--
If a path ends with `x, t`, then the reversed path starts by going from `t` to
`x`. This avoids redoing `dropLast`/`reverse` list arithmetic at each seam
splice.
-/
theorem ListSpanningPath.reverse_tail_eq_cons_of_tail_eq_append_pair
    {G : SimpleGraph V} {S : Finset V} {s t x : V}
    (p : ListSpanningPath G.Adj S s t)
    (htail_ne : p.tail ≠ [])
    {middle : List V}
    (htail : p.tail = middle ++ [x, t]) :
    (p.reverse htail_ne).tail = x :: (middle.reverse ++ [s]) := by
  simp [ListSpanningPath.reverse, htail, List.reverse_append, List.append_assoc]

/--
Prefix bridge for a target `P4` crossing into a reversed side path.

If `p₀` is `a -> ... -> c` with explicit tail `[b, c]`, and `p₁` ends with
`d, c`, then `p₀` followed by the reverse of `p₁` contains the ordered path
`a,b,c,d` at the splice boundary.
-/
theorem ListSpanningPath.path4_infix_firstTwo_of_tail_eq_pair_and_reverse_tail_eq_append_pair
    {G₀ G₁ : SimpleGraph V} {S₀ S₁ : Finset V} {a b c d s : V}
    (p₀ : ListSpanningPath G₀.Adj S₀ a c)
    (p₁ : ListSpanningPath G₁.Adj S₁ s c)
    (htail₀ : p₀.tail = [b, c])
    (htail₁_ne : p₁.tail ≠ [])
    {middle : List V}
    (htail₁ : p₁.tail = middle ++ [d, c]) :
    [a, b, c, d] <:+: a :: (p₀.tail ++ (p₁.reverse htail₁_ne).tail) := by
  have hrev :
      (p₁.reverse htail₁_ne).tail = d :: (middle.reverse ++ [s]) :=
    p₁.reverse_tail_eq_cons_of_tail_eq_append_pair htail₁_ne htail₁
  rw [htail₀, hrev]
  exact ⟨[], middle.reverse ++ [s], by simp⟩

/-- Reversing a path does not change its represented vertex set. -/
theorem ListSpanningPath.mem_support_of_mem_reverse
    {G : SimpleGraph V} {S : Finset V} {s t v : V}
    (p : ListSpanningPath G.Adj S s t)
    (htail_ne : p.tail ≠ [])
    (hv : v ∈ ((t :: (p.tail.dropLast.reverse ++ [s])).toFinset)) :
    v ∈ S := by
  rw [List.mem_toFinset] at hv
  have htail : p.tail = p.tail.dropLast ++ [t] :=
    p.tail_eq_dropLast_append_end htail_ne
  have hrev :
      t :: (p.tail.dropLast.reverse ++ [s]) = (s :: p.tail).reverse := by
    rw [htail, List.reverse_cons, List.reverse_append]
    simp [List.append_assoc]
  rw [hrev] at hv
  have hvOrig : v ∈ s :: p.tail := by
    simpa using List.mem_reverse.mp hv
  exact (p.spans v).2 hvOrig

/-- Reversing a path preserves its support. -/
theorem ListSpanningPath.reverse_support_eq
    {G : SimpleGraph V} {S : Finset V} {s t : V}
    (p : ListSpanningPath G.Adj S s t)
    (htail_ne : p.tail ≠ []) :
    ((t :: (p.tail.dropLast.reverse ++ [s])).toFinset) = S := by
  ext v
  constructor
  · intro hv
    exact p.mem_support_of_mem_reverse htail_ne hv
  · intro hv
    rw [List.mem_toFinset]
    have hvOrig : v ∈ s :: p.tail := (p.spans v).1 hv
    have htail : p.tail = p.tail.dropLast ++ [t] :=
      p.tail_eq_dropLast_append_end htail_ne
    have hrev :
        t :: (p.tail.dropLast.reverse ++ [s]) = (s :: p.tail).reverse := by
      rw [htail, List.reverse_cons, List.reverse_append]
      simp [List.append_assoc]
    rw [hrev]
    exact List.mem_reverse.mpr hvOrig

/-- A non-direct path remains non-direct after reversing. -/
theorem ListSpanningPath.reverse_tail_ne_singleton_of_tail_ne_singleton
    {G : SimpleGraph V} {S : Finset V} {s t : V}
    (p : ListSpanningPath G.Adj S s t)
    (htail_ne : p.tail ≠ [])
    (hnot : p.tail ≠ [t]) :
    (p.reverse htail_ne).tail ≠ [s] := by
  intro hq
  have hq' : p.tail.dropLast.reverse ++ [s] = [s] := by
    simpa [ListSpanningPath.reverse] using hq
  have hdrop_rev_nil : p.tail.dropLast.reverse = [] := by
    cases hrev : p.tail.dropLast.reverse with
    | nil =>
        simpa [hrev] using hq'
    | cons u us =>
        exfalso
        simp [hrev] at hq'
  have hdrop_nil : p.tail.dropLast = [] := by
    have := congrArg List.reverse hdrop_rev_nil
    simpa using this
  have htail_singleton : p.tail = [t] := by
    simpa [hdrop_nil] using p.tail_eq_dropLast_append_end htail_ne
  exact hnot htail_singleton

/--
Rotate an explicit Hamiltonian cycle witness so that a chosen internal cycle edge
`(t, s)` becomes the closing edge.
-/
theorem HamiltonianCycleWitness.rotateToEdge
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (t s : V)
    (hsplit : w.start :: w.tail = xs ++ t :: s :: ys) :
    ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      w'.start = s ∧ w'.tail = ys ++ xs ++ [t] := by
  induction xs generalizing w ys with
  | nil =>
      have hstart : w.start = t := by
        rcases List.cons.inj hsplit with ⟨hstart, _⟩
        simpa using hstart
      have htail : w.tail = s :: ys := by
        rcases List.cons.inj hsplit with ⟨_, htail⟩
        simpa using htail
      refine ⟨w.rotateOnce s ys htail, rfl, ?_⟩
      simpa [hstart, htail, HamiltonianCycleWitness.rotateOnce]
  | cons x xs ih =>
      rcases List.cons.inj hsplit with ⟨hstart, htail⟩
      have hnonempty : xs ++ t :: s :: ys ≠ [] := by simp
      rcases List.exists_cons_of_ne_nil hnonempty with ⟨v, vs, hvs⟩
      have htail' : w.tail = v :: vs := by
        simpa [hvs] using htail
      let w₁ := w.rotateOnce v vs htail'
      have hsplit₁ :
          w₁.start :: w₁.tail = xs ++ t :: s :: (ys ++ [x]) := by
        calc
          w₁.start :: w₁.tail = w.tail ++ [w.start] := by
            simpa [w₁] using (HamiltonianCycleWitness.openList_rotateOnce (w := w) v vs htail')
          _ = xs ++ t :: s :: (ys ++ [x]) := by
            rw [hstart, htail]
            simp [List.append_assoc]
      rcases ih w₁ (ys := ys ++ [x]) hsplit₁ with ⟨w', hw'start, hw'tail⟩
      refine ⟨w', hw'start, ?_⟩
      simpa [List.append_assoc] using hw'tail


/--
Cut an explicit Hamiltonian cycle witness at a chosen cycle edge.

This is the seam-edge placement bridge needed for the cubic-trisum proof: once a
factor Hamiltonian cycle is available explicitly, any designated cycle edge can
be made the closing edge consumed by `toBoundaryCycleWitness`.
-/
noncomputable def HamiltonianCycleWitness.toBoundaryCycleWitness_of_cycleEdge
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {t s : V}
    (hedge : (t, s) ∈ edgePairs (w.start :: (w.tail ++ [w.start]))) :
    OrderedSegmentFamily.BoundaryCycleWitness G.Adj (Finset.univ : Finset V) s t := by
  classical
  rw [edgePairs_append] at hedge
  by_cases hint : (t, s) ∈ edgePairs (w.start :: w.tail)
  · let xs := Classical.choose (infix_of_mem_edgePairs hint)
    let ys := Classical.choose (Classical.choose_spec (infix_of_mem_edgePairs hint))
    have hsplit : w.start :: w.tail = xs ++ [t, s] ++ ys := by
      simpa [xs, ys] using
        (Classical.choose_spec (Classical.choose_spec (infix_of_mem_edgePairs hint))).symm
    have hrot :
        ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
          w'.start = s ∧ w'.tail = ys ++ xs ++ [t] := by
      simpa [List.append_assoc] using w.rotateToEdge xs ys t s (by simpa [List.append_assoc] using hsplit)
    let w' := Classical.choose hrot
    have hw'start : w'.start = s := (Classical.choose_spec hrot).1
    have hw'tail : w'.tail = ys ++ xs ++ [t] := (Classical.choose_spec hrot).2
    simpa [hw'start, hw'tail, List.append_assoc] using
      w'.toBoundaryCycleWitness (ys ++ xs) t (by simpa [hw'tail, List.append_assoc])
  · have hcloseMem : (t, s) ∈ edgePairs [endVertex w.start w.tail, w.start] := by
      exact (List.mem_append.1 hedge).resolve_left hint
    have hclosing : (t, s) = (endVertex w.start w.tail, w.start) := by
      simpa [edgePairs] using hcloseMem
    have ht : t = endVertex w.start w.tail := by
      simpa using congrArg Prod.fst hclosing
    have hs : s = w.start := by
      simpa using congrArg Prod.snd hclosing
    have htail_ne : w.tail ≠ [] := by
      intro hnil
      have hloop : G.Adj w.start w.start := w.cycle_adj (by simpa [hnil, edgePairs] using hcloseMem)
      exact G.loopless.irrefl _ hloop
    have htail :
        w.tail = w.tail.dropLast ++ [t] := by
      rw [ht, endVertex_eq_getLast (u := w.start) htail_ne]
      exact (List.dropLast_append_getLast htail_ne).symm
    rw [hs]
    simpa [htail, List.append_assoc] using
      w.toBoundaryCycleWitness w.tail.dropLast t htail

/--
If a Hamiltonian cycle uses two disjoint seam edges in cyclic order, deleting
those edges yields the two seam-to-seam spanning paths needed in the matching
case of the cubic-trisum splice.
-/
noncomputable def HamiltonianCycleWitness.extractMatchingPair
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys zs : List V) (u₀ u₁ u₂ u₃ : V)
    (hsplit :
      w.start :: w.tail = xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) :
    ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂ ×
      ListSpanningPath G.Adj ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) u₃ u₀ := by
  classical
  have hrot :
      ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
        w'.start = u₁ ∧
          w'.tail = ((ys ++ [u₂, u₃] ++ zs) ++ xs) ++ [u₀] := by
    simpa [List.append_assoc] using
      w.rotateToEdge xs (ys ++ [u₂, u₃] ++ zs) u₀ u₁ (by
        simpa [List.append_assoc] using hsplit)
  let w' := Classical.choose hrot
  have hw'start : w'.start = u₁ := (Classical.choose_spec hrot).1
  have hw'tail :
      w'.tail = ((ys ++ [u₂, u₃] ++ zs) ++ xs) ++ [u₀] :=
    (Classical.choose_spec hrot).2
  let b :=
    w'.toBoundaryCycleWitness (ys ++ u₂ :: u₃ :: (zs ++ xs)) u₀ (by
      simpa [hw'tail, List.append_assoc])
  have hmid : b.middle = ys ++ u₂ :: u₃ :: (zs ++ xs) := by
    rfl
  simpa [hw'start, List.append_assoc] using
    (show
      ListSpanningPath G.Adj ((w'.start :: (ys ++ [u₂])).toFinset) w'.start u₂ ×
        ListSpanningPath G.Adj ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) u₃ u₀ from
      ⟨b.takeUntilInternalEdge ys u₂ u₃ (zs ++ xs) hmid,
        b.dropUntilInternalEdge ys u₂ u₃ (zs ++ xs) hmid⟩)

/--
If a Hamiltonian cycle uses three consecutive seam edges in cyclic order,
deleting them yields the remaining seam-to-seam spanning path.
-/
noncomputable def HamiltonianCycleWitness.extractThreeEdgePath
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (u₃ u₀ u₁ u₂ : V)
    (hsplit :
      w.start :: w.tail = xs ++ [u₃, u₀, u₁, u₂] ++ ys) :
    ListSpanningPath G.Adj ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) u₂ u₃ := by
  classical
  have hrot :
      ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
        w'.start = u₀ ∧
          w'.tail = (([u₁, u₂] ++ ys) ++ xs) ++ [u₃] := by
    simpa [List.append_assoc] using
      w.rotateToEdge xs ([u₁, u₂] ++ ys) u₃ u₀ (by
        simpa [List.append_assoc] using hsplit)
  let w' := Classical.choose hrot
  have hw'tail :
      w'.tail = (([u₁, u₂] ++ ys) ++ xs) ++ [u₃] :=
    (Classical.choose_spec hrot).2
  let b :=
    w'.toBoundaryCycleWitness (u₁ :: u₂ :: (ys ++ xs)) u₃ (by
      simpa [hw'tail, List.append_assoc])
  have hmid : b.middle = [] ++ u₁ :: u₂ :: (ys ++ xs) := by
    rfl
  simpa [List.append_assoc] using
    b.dropUntilInternalEdge [] u₁ u₂ (ys ++ xs) hmid

theorem HamiltonianCycleWitness.extractThreeEdgePath_support_seamSubset
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (u₃ u₀ u₁ u₂ : V)
    (hsplit :
      w.start :: w.tail = xs ++ [u₃, u₀, u₁, u₂] ++ ys) :
    ∀ v, v ∈ ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) →
      v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset →
      v = u₂ ∨ v = u₃ := by
  have hnodup : List.Nodup (xs ++ [u₃, u₀, u₁, u₂] ++ ys) := by
    simpa [hsplit, List.append_assoc] using w.nodup
  have hnodup_left : List.Nodup (xs ++ ([u₃, u₀, u₁, u₂] ++ ys)) := by
    simpa [List.append_assoc] using hnodup
  have hnodup_right : List.Nodup ((xs ++ [u₃, u₀, u₁, u₂]) ++ ys) := by
    simpa [List.append_assoc] using hnodup
  rw [List.nodup_append] at hnodup_left hnodup_right
  have hxs_disj := hnodup_left.2.2
  have hys_disj := hnodup_right.2.2
  have hmiddle_nodup : List.Nodup ([u₃, u₀, u₁, u₂] : List V) := by
    exact List.Nodup.of_append_left hnodup_left.2.1
  have hu₃_ne_u₀ : u₃ ≠ u₀ := by
    simpa using (show List.Nodup ([u₃, u₀] : List V) from List.Nodup.of_append_left hmiddle_nodup)
  have hu₃_ne_u₁ : u₃ ≠ u₁ := by
    simpa using (show List.Nodup ([u₃, u₁] : List V) from by
      exact hmiddle_nodup.sublist (by simp))
  have hu₃_ne_u₂ : u₃ ≠ u₂ := by
    simpa using (show List.Nodup ([u₃, u₂] : List V) from by
      exact hmiddle_nodup.sublist (by simp))
  have hu₀_ne_u₁ : u₀ ≠ u₁ := by
    simpa using (show List.Nodup ([u₀, u₁] : List V) from by
      exact hmiddle_nodup.sublist (by simp))
  have hu₀_ne_u₂ : u₀ ≠ u₂ := by
    simpa using (show List.Nodup ([u₀, u₂] : List V) from by
      exact hmiddle_nodup.sublist (by simp))
  have hu₁_ne_u₂ : u₁ ≠ u₂ := by
    simpa using (show List.Nodup ([u₁, u₂] : List V) from by
      exact hmiddle_nodup.sublist (by simp))
  have hu₀_ne_u₃ : u₀ ≠ u₃ := fun h => hu₃_ne_u₀ h.symm
  have hu₁_ne_u₃ : u₁ ≠ u₃ := fun h => hu₃_ne_u₁ h.symm
  have hu₀_not_xs : u₀ ∉ xs := by
    intro hu₀
    exact hxs_disj u₀ hu₀ u₀ (by simp [List.mem_append]) rfl
  have hu₁_not_xs : u₁ ∉ xs := by
    intro hu₁
    exact hxs_disj u₁ hu₁ u₁ (by simp [List.mem_append]) rfl
  have hu₀_not_ys : u₀ ∉ ys := by
    intro hu₀
    exact hys_disj u₀ (by simp [List.mem_append]) u₀ hu₀ rfl
  have hu₁_not_ys : u₁ ∉ ys := by
    intro hu₁
    exact hys_disj u₁ (by simp [List.mem_append]) u₁ hu₁ rfl
  have hu₀_not_yx : u₀ ∉ ys ++ xs := by
    intro hu₀
    rw [List.mem_append] at hu₀
    exact hu₀.elim hu₀_not_ys hu₀_not_xs
  have hu₁_not_yx : u₁ ∉ ys ++ xs := by
    intro hu₁
    rw [List.mem_append] at hu₁
    exact hu₁.elim hu₁_not_ys hu₁_not_xs
  have hu₀_not_support : u₀ ∉ u₂ :: ((ys ++ xs) ++ [u₃]) := by
    simp [List.mem_append, hu₀_ne_u₂, hu₀_not_ys, hu₀_not_xs, hu₀_ne_u₃]
  have hu₁_not_support : u₁ ∉ u₂ :: ((ys ++ xs) ++ [u₃]) := by
    simp [List.mem_append, hu₁_ne_u₂, hu₁_not_ys, hu₁_not_xs, hu₁_ne_u₃]
  intro v hv hseam
  have hv' : v ∈ u₂ :: ((ys ++ xs) ++ [u₃]) := by
    simpa [List.mem_toFinset, List.mem_append, or_assoc, or_left_comm, or_comm] using hv
  have hseam' : v = u₀ ∨ v = u₁ ∨ v = u₂ ∨ v = u₃ := by
    simpa [List.mem_toFinset, or_assoc] using hseam
  rcases hseam' with h | h | h | h
  · subst h
    exact False.elim (hu₀_not_support hv')
  · subst h
    exact False.elim (hu₁_not_support hv')
  · exact h ▸ Or.inl rfl
  · exact h ▸ Or.inr rfl

theorem HamiltonianCycleWitness.extractThreeEdgePath_tail_ne_singleton_of_side_nonempty
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (u₃ u₀ u₁ u₂ : V)
    (hsplit :
      w.start :: w.tail = xs ++ [u₃, u₀, u₁, u₂] ++ ys)
    (hside : ys ++ xs ≠ []) :
    (w.extractThreeEdgePath xs ys u₃ u₀ u₁ u₂ hsplit).tail ≠ [u₃] := by
  rcases List.eq_nil_or_concat' (ys ++ xs) with hnil | ⟨zs, x, hzx⟩
  · exact False.elim (hside hnil)
  have hx_side : x ∈ ys ++ xs := by
    simp [hzx]
  have hnodup : List.Nodup (xs ++ [u₃, u₀, u₁, u₂] ++ ys) := by
    simpa [hsplit, List.append_assoc] using w.nodup
  have hnodup_left : List.Nodup (xs ++ ([u₃, u₀, u₁, u₂] ++ ys)) := by
    simpa [List.append_assoc] using hnodup
  have hnodup_right : List.Nodup ((xs ++ [u₃, u₀, u₁, u₂]) ++ ys) := by
    simpa [List.append_assoc] using hnodup
  rw [List.nodup_append] at hnodup_left hnodup_right
  have hxs_disj := hnodup_left.2.2
  have hys_disj := hnodup_right.2.2
  have hx_ne_u₂ : x ≠ u₂ := by
    rcases (List.mem_append.1 hx_side) with hx | hx
    · intro h
      exact hys_disj u₂ (by simp [List.mem_append]) x hx h.symm
    · exact hxs_disj x hx u₂ (by simp [List.mem_append])
  have hx_ne_u₃ : x ≠ u₃ := by
    rcases (List.mem_append.1 hx_side) with hx | hx
    · intro h
      exact hys_disj u₃ (by simp [List.mem_append]) x hx h.symm
    · exact hxs_disj x hx u₃ (by simp [List.mem_append])
  have hx_support : x ∈ ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) := by
    rw [List.mem_toFinset]
    rcases (List.mem_append.1 hx_side) with hx | hx <;>
      simp [List.mem_append, hx, or_assoc, or_left_comm, or_comm]
  exact ListSpanningPath.tail_ne_singleton_of_support_vertex_ne_endpoints
    (p := w.extractThreeEdgePath xs ys u₃ u₀ u₁ u₂ hsplit)
    hx_support hx_ne_u₂ hx_ne_u₃

theorem HamiltonianCycleWitness.extractThreeEdgePath_of_openInfix
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₃ u₀ u₁ u₂ : V}
    (hinfix : [u₃, u₀, u₁, u₂] <:+: w.start :: w.tail) :
    ∃ xs ys,
      Nonempty (ListSpanningPath G.Adj
        ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) u₂ u₃) := by
  rcases hinfix with ⟨xs, ys, hsplit⟩
  refine ⟨xs, ys, ⟨?_⟩⟩
  exact w.extractThreeEdgePath xs ys u₃ u₀ u₁ u₂ hsplit.symm

theorem HamiltonianCycleWitness.extractThreeEdgePath_of_cycleSupportInfix
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₃ u₀ u₁ u₂ : V}
    (hneq : u₂ ≠ u₃)
    (hinfix : [u₃, u₀, u₁, u₂] <:+: w.start :: (w.tail ++ [w.start])) :
    ∃ xs ys,
      Nonempty (ListSpanningPath G.Adj
        ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) u₂ u₃) := by
  by_cases hopen : [u₃, u₀, u₁, u₂] <:+: w.start :: w.tail
  · exact w.extractThreeEdgePath_of_openInfix hopen
  · rcases hinfix with ⟨xs, ys, hsplit⟩
    rcases List.eq_nil_or_concat' ys with rfl | ⟨ys', y, hys⟩
    · have hu₂ : u₂ = w.start := by
        have hlast := congrArg List.getLast? hsplit
        have hleft : (xs ++ [u₃, u₀, u₁, u₂]).getLast? = some u₂ := by
          simpa using
            (List.getLast?_append_of_ne_nil xs (by simp : ([u₃, u₀, u₁, u₂] : List V) ≠ []))
        have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
        have hu₂Opt : some u₂ = some w.start := by
          calc
            some u₂ = (xs ++ [u₃, u₀, u₁, u₂] ++ []).getLast? := by
              simpa [List.append_assoc] using hleft.symm
            _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
              simpa using hlast
            _ = some w.start := hright
        exact Option.some.inj hu₂Opt
      have hopenSuffix : xs ++ [u₃, u₀, u₁] = w.start :: w.tail := by
        apply (List.append_left_injective [w.start])
        simpa [hu₂, List.append_assoc] using hsplit
      cases xs with
      | nil =>
          have hu₃ : u₃ = w.start := by
            exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
          exact False.elim (hneq (hu₂.trans hu₃.symm))
      | cons x xs' =>
          have hx : x = w.start := by
            exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
          have htail : w.tail = xs' ++ [u₃, u₀, u₁] := by
            exact (Option.some.inj (by simpa using congrArg List.tail? hopenSuffix)).symm
          have htail_ne : w.tail ≠ [] := by
            intro hnil
            simp [hnil] at htail
          obtain ⟨v, vs, hcons⟩ := List.exists_cons_of_ne_nil htail_ne
          let w' := w.rotateOnce v vs hcons
          have hw'open :
              w'.start :: w'.tail = xs' ++ [u₃, u₀, u₁, u₂] := by
            calc
              w'.start :: w'.tail = w.tail ++ [w.start] := by
                simpa [w'] using w.openList_rotateOnce v vs hcons
              _ = (xs' ++ [u₃, u₀, u₁]) ++ [u₂] := by
                simp [htail, hu₂, List.append_assoc]
              _ = xs' ++ [u₃, u₀, u₁, u₂] := by
                simp [List.append_assoc]
          refine ⟨xs', [], ?_⟩
          refine ⟨w'.extractThreeEdgePath xs' [] u₃ u₀ u₁ u₂ ?_⟩
          simpa using hw'open
    · have hy : y = w.start := by
        have hlast := congrArg List.getLast? hsplit
        have hleft :
            (xs ++ [u₃, u₀, u₁, u₂] ++ ys' ++ [y]).getLast? = some y := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (xs ++ [u₃, u₀, u₁, u₂] ++ ys')
              (by simp : ([y] : List V) ≠ []))
        have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
        have hyOpt : some y = some w.start := by
          calc
            some y = (xs ++ [u₃, u₀, u₁, u₂] ++ (ys' ++ [y])).getLast? := by
              simpa [hys, List.append_assoc] using hleft.symm
            _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
              simpa [hys] using hlast
            _ = some w.start := hright
        exact Option.some.inj hyOpt
      have hopen' : [u₃, u₀, u₁, u₂] <:+: w.start :: w.tail := by
        refine ⟨xs, ys', ?_⟩
        apply (List.append_left_injective [w.start])
        simpa [hys, hy, List.append_assoc] using hsplit
      exact False.elim (hopen hopen')

theorem HamiltonianCycleWitness.extractThreeEdgePath_support_union_seam_eq_univ
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (u₃ u₀ u₁ u₂ : V)
    (hsplit :
      w.start :: w.tail = xs ++ [u₃, u₀, u₁, u₂] ++ ys) :
    ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) ∪
        ([u₀, u₁] : List V).toFinset =
      (Finset.univ : Finset V) := by
  ext v
  constructor
  · intro hv
    simp
  · intro _
    have hvOpen : v ∈ w.start :: w.tail := by
      simpa using (w.spans v).1 (by simp)
    have hvSplit : v ∈ xs ++ [u₃, u₀, u₁, u₂] ++ ys := by
      simpa [hsplit] using hvOpen
    rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
    simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hvSplit

theorem HamiltonianCycleWitness.extractMatchingPair_of_cycleSupportSplit
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₀ u₁ u₂ u₃ : V}
    (hneq : u₃ ≠ u₀)
    {xs ys zs : List V}
    (hsplit :
      xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs =
        w.start :: (w.tail ++ [w.start])) :
    ∃ xs' zs', Nonempty
      (ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂ ×
        ListSpanningPath G.Adj ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) u₃ u₀) := by
  by_cases hzs : zs = []
  · subst hzs
    have hu₃ : u₃ = w.start := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]).getLast? = some u₃ := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [u₀, u₁] ++ ys ++ [u₂])
            (by simp : ([u₃] : List V) ≠ []))
      have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
      have hu₃Opt : some u₃ = some w.start := by
        calc
          some u₃ = (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]).getLast? := by
            simpa [List.append_assoc] using hleft.symm
          _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
            simpa using hlast
          _ = some w.start := hright
      exact Option.some.inj hu₃Opt
    have hopenSuffix : xs ++ [u₀, u₁] ++ ys ++ [u₂] = w.start :: w.tail := by
      apply (List.append_left_injective [w.start])
      simpa [hu₃, List.append_assoc] using hsplit
    cases xs with
    | nil =>
        have hu₀ : u₀ = w.start := by
          exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
        exact False.elim (hneq (hu₃.trans hu₀.symm))
    | cons x xs' =>
        have hx : x = w.start := by
          exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
        have htail : w.tail = xs' ++ [u₀, u₁] ++ ys ++ [u₂] := by
          exact (Option.some.inj (by simpa using congrArg List.tail? hopenSuffix)).symm
        have htail_ne : w.tail ≠ [] := by
          intro hnil
          simp [hnil] at htail
        obtain ⟨v, vs, hcons⟩ := List.exists_cons_of_ne_nil htail_ne
        let w' := w.rotateOnce v vs hcons
        have hw'open :
            w'.start :: w'.tail = xs' ++ [u₀, u₁] ++ ys ++ [u₂, u₃] := by
          calc
            w'.start :: w'.tail = w.tail ++ [w.start] := by
              simpa [w'] using w.openList_rotateOnce v vs hcons
            _ = (xs' ++ [u₀, u₁] ++ ys ++ [u₂]) ++ [u₃] := by
              simp [htail, hu₃, List.append_assoc]
            _ = xs' ++ [u₀, u₁] ++ ys ++ [u₂, u₃] := by
              simp [List.append_assoc]
        refine ⟨xs', [], ?_⟩
        refine ⟨?_⟩
        simpa [List.append_assoc] using
          w'.extractMatchingPair xs' ys [] u₀ u₁ u₂ u₃ (by
            simpa [List.append_assoc] using hw'open)
  · rcases List.eq_nil_or_concat' zs with _ | ⟨zs', z, hzs'⟩
    · contradiction
    have hz : z = w.start := by
      have hlast := congrArg List.getLast? hsplit
      have hleft :
          (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs' ++ [z]).getLast? = some z := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs')
            (by simp : ([z] : List V) ≠ []))
      have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
      have hzOpt : some z = some w.start := by
        calc
          some z = (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ (zs' ++ [z])).getLast? := by
            simpa [hzs', List.append_assoc] using hleft.symm
          _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
            simpa [hzs'] using hlast
          _ = some w.start := hright
      exact Option.some.inj hzOpt
    have hopenSplit : xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs' = w.start :: w.tail := by
      apply (List.append_left_injective [w.start])
      simpa [hzs', hz, List.append_assoc] using hsplit
    refine ⟨xs, zs', ?_⟩
    refine ⟨?_⟩
    simpa [List.append_assoc] using
      w.extractMatchingPair xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm

theorem HamiltonianCycleWitness.extractMatchingPair_right_support_seamSubset
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys zs : List V) (u₀ u₁ u₂ u₃ : V)
    (hsplit :
      w.start :: w.tail =
        xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) :
    ∀ v, v ∈ ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) →
      v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset →
      v = u₃ ∨ v = u₀ := by
  have hnodup : List.Nodup (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) := by
    simpa [hsplit, List.append_assoc] using w.nodup
  have hnodup_left : List.Nodup (xs ++ (([u₀, u₁] ++ ys ++ [u₂, u₃]) ++ zs)) := by
    simpa [List.append_assoc] using hnodup
  have hnodup_right : List.Nodup ((xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]) ++ zs) := by
    simpa [List.append_assoc] using hnodup
  rw [List.nodup_append] at hnodup_left hnodup_right
  have hxs_disj := hnodup_left.2.2
  have hzs_disj := hnodup_right.2.2
  have hmiddle :
      List.Nodup (([u₀, u₁] ++ ys) ++ ([u₂, u₃] ++ zs)) := by
    simpa [List.append_assoc] using hnodup_left.2.1
  rw [List.nodup_append] at hmiddle
  have hmiddle_disj := hmiddle.2.2
  have hu₀_ne_u₁ : u₀ ≠ u₁ := by
    simpa using
      (show List.Nodup ([u₀, u₁] : List V) from List.Nodup.of_append_left hmiddle.1)
  have hu₂_ne_u₃ : u₂ ≠ u₃ := by
    simpa using
      (show List.Nodup ([u₂, u₃] : List V) from List.Nodup.of_append_left hmiddle.2.1)
  have hu₁_ne_u₃ : u₁ ≠ u₃ := by
    exact hmiddle_disj u₁ (by simp) u₃ (by simp)
  have hu₀_ne_u₂ : u₀ ≠ u₂ := by
    exact hmiddle_disj u₀ (by simp) u₂ (by simp)
  have hu₁_ne_u₀ : u₁ ≠ u₀ := fun h => hu₀_ne_u₁ h.symm
  have hu₂_ne_u₀ : u₂ ≠ u₀ := fun h => hu₀_ne_u₂ h.symm
  have hu₁_not_xs : u₁ ∉ xs := by
    intro hu₁
    exact hxs_disj u₁ hu₁ u₁ (by simp [List.mem_append]) rfl
  have hu₂_not_xs : u₂ ∉ xs := by
    intro hu₂
    exact hxs_disj u₂ hu₂ u₂ (by simp [List.mem_append]) rfl
  have hu₁_not_zs : u₁ ∉ zs := by
    intro hu₁
    exact hzs_disj u₁ (by simp [List.mem_append]) u₁ hu₁ rfl
  have hu₂_not_zs : u₂ ∉ zs := by
    intro hu₂
    exact hzs_disj u₂ (by simp [List.mem_append]) u₂ hu₂ rfl
  have hu₁_not_zx : u₁ ∉ zs ++ xs := by
    intro hu₁
    rw [List.mem_append] at hu₁
    exact hu₁.elim hu₁_not_zs hu₁_not_xs
  have hu₂_not_zx : u₂ ∉ zs ++ xs := by
    intro hu₂
    rw [List.mem_append] at hu₂
    exact hu₂.elim hu₂_not_zs hu₂_not_xs
  have hu₁_not_support : u₁ ∉ u₃ :: ((zs ++ xs) ++ [u₀]) := by
    simp [List.mem_append, hu₁_ne_u₃, hu₁_not_zs, hu₁_not_xs, hu₁_ne_u₀]
  have hu₂_not_support : u₂ ∉ u₃ :: ((zs ++ xs) ++ [u₀]) := by
    simp [List.mem_append, hu₂_ne_u₃, hu₂_not_zs, hu₂_not_xs, hu₂_ne_u₀]
  intro v hv hseam
  have hv' : v ∈ u₃ :: ((zs ++ xs) ++ [u₀]) := by
    simpa [List.mem_toFinset, List.mem_append, or_assoc, or_left_comm, or_comm] using hv
  have hseam' : v = u₀ ∨ v = u₁ ∨ v = u₂ ∨ v = u₃ := by
    simpa [List.mem_toFinset, or_assoc] using hseam
  rcases hseam' with h | h | h | h
  · exact h ▸ Or.inr rfl
  · subst h
    exact False.elim (hu₁_not_support hv')
  · subst h
    exact False.elim (hu₂_not_support hv')
  · exact h ▸ Or.inl rfl

theorem HamiltonianCycleWitness.extractMatchingPair_support_disjoint
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys zs : List V) (u₀ u₁ u₂ u₃ : V)
    (hsplit :
      w.start :: w.tail =
        xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) :
    ∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
      v ∈ ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) → False := by
  classical
  have hrot :
      ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
        w'.start = u₁ ∧
          w'.tail = ((ys ++ [u₂, u₃] ++ zs) ++ xs) ++ [u₀] := by
    simpa [List.append_assoc] using
      w.rotateToEdge xs (ys ++ [u₂, u₃] ++ zs) u₀ u₁ (by
        simpa [List.append_assoc] using hsplit)
  let w' := Classical.choose hrot
  have hw'start : w'.start = u₁ := (Classical.choose_spec hrot).1
  have hw'tail :
      w'.tail = ((ys ++ [u₂, u₃] ++ zs) ++ xs) ++ [u₀] :=
    (Classical.choose_spec hrot).2
  have hw'nodup : List.Nodup (w'.start :: w'.tail) := w'.nodup
  have hnodup :
      List.Nodup
        ((u₁ :: (ys ++ [u₂])) ++ (u₃ :: ((zs ++ xs) ++ [u₀]))) := by
    simpa [hw'start, hw'tail, List.append_assoc] using hw'nodup
  rw [List.nodup_append] at hnodup
  have hdisj := hnodup.2.2
  intro v hvL hvR
  rw [List.mem_toFinset] at hvL hvR
  exact hdisj v hvL v hvR rfl

theorem HamiltonianCycleWitness.extractMatchingPair_left_support_seamSubset
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys zs : List V) (u₀ u₁ u₂ u₃ : V)
    (hsplit :
      w.start :: w.tail =
        xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) :
    ∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
      v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset →
      v = u₁ ∨ v = u₂ := by
  have hnodup : List.Nodup (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) := by
    simpa [hsplit, List.append_assoc] using w.nodup
  have hnodup_left : List.Nodup (xs ++ (([u₀, u₁] ++ ys ++ [u₂, u₃]) ++ zs)) := by
    simpa [List.append_assoc] using hnodup
  rw [List.nodup_append] at hnodup_left
  have hmiddle :
      List.Nodup (([u₀, u₁] ++ ys) ++ ([u₂, u₃] ++ zs)) := by
    simpa [List.append_assoc] using hnodup_left.2.1
  rw [List.nodup_append] at hmiddle
  have hleft := hmiddle.1
  have hmiddle_disj := hmiddle.2.2
  rw [List.nodup_append] at hleft
  have hu₀_ne_u₁ : u₀ ≠ u₁ := by
    simpa using (show List.Nodup ([u₀, u₁] : List V) from hleft.1)
  have hu₀_ne_u₂ : u₀ ≠ u₂ := by
    exact hmiddle_disj u₀ (by simp) u₂ (by simp)
  have hu₁_ne_u₃ : u₁ ≠ u₃ := by
    exact hmiddle_disj u₁ (by simp) u₃ (by simp)
  have hu₃_ne_u₁ : u₃ ≠ u₁ := fun h => hu₁_ne_u₃ h.symm
  have hu₂_ne_u₃ : u₂ ≠ u₃ := by
    simpa using
      (show List.Nodup ([u₂, u₃] : List V) from List.Nodup.of_append_left hmiddle.2.1)
  have hu₃_ne_u₂ : u₃ ≠ u₂ := fun h => hu₂_ne_u₃ h.symm
  have hu₀_not_ys : u₀ ∉ ys := by
    intro hu₀
    exact hleft.2.2 u₀ (by simp) u₀ hu₀ rfl
  have hu₁_not_ys : u₁ ∉ ys := by
    intro hu₁
    exact hleft.2.2 u₁ (by simp) u₁ hu₁ rfl
  have hu₃_not_ys : u₃ ∉ ys := by
    intro hu₃
    exact hmiddle_disj u₃ (by simp [hu₃]) u₃ (by simp) rfl
  have hu₀_not_support : u₀ ∉ u₁ :: (ys ++ [u₂]) := by
    simp [List.mem_append, hu₀_ne_u₁, hu₀_not_ys, hu₀_ne_u₂]
  have hu₃_not_support : u₃ ∉ u₁ :: (ys ++ [u₂]) := by
    simp [List.mem_append, hu₃_ne_u₁, hu₃_not_ys, hu₃_ne_u₂]
  intro v hv hseam
  have hv' : v ∈ u₁ :: (ys ++ [u₂]) := by
    simpa [List.mem_toFinset, List.mem_append, or_assoc, or_left_comm, or_comm] using hv
  have hseam' : v = u₀ ∨ v = u₁ ∨ v = u₂ ∨ v = u₃ := by
    simpa [List.mem_toFinset, or_assoc] using hseam
  rcases hseam' with h | h | h | h
  · subst h
    exact False.elim (hu₀_not_support hv')
  · exact h ▸ Or.inl rfl
  · exact h ▸ Or.inr rfl
  · subst h
    exact False.elim (hu₃_not_support hv')

theorem HamiltonianCycleWitness.extractMatchingPair_left_tail_ne_singleton_of_middle_nonempty
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys zs : List V) (u₀ u₁ u₂ u₃ : V)
    (hsplit :
      w.start :: w.tail =
        xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs)
    (hmid : ys ≠ []) :
    ((w.extractMatchingPair xs ys zs u₀ u₁ u₂ u₃ hsplit).1).tail ≠ [u₂] := by
  rcases List.eq_nil_or_concat' ys with hnil | ⟨ws, x, hwx⟩
  · exact False.elim (hmid hnil)
  have hx_mid : x ∈ ys := by
    simp [hwx]
  have hnodup : List.Nodup (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) := by
    simpa [hsplit, List.append_assoc] using w.nodup
  have hnodup_left : List.Nodup (xs ++ (([u₀, u₁] ++ ys ++ [u₂, u₃]) ++ zs)) := by
    simpa [List.append_assoc] using hnodup
  rw [List.nodup_append] at hnodup_left
  have hmiddle :
      List.Nodup (([u₀, u₁] ++ ys) ++ ([u₂, u₃] ++ zs)) := by
    simpa [List.append_assoc] using hnodup_left.2.1
  rw [List.nodup_append] at hmiddle
  have hleft := hmiddle.1
  have hmiddle_disj := hmiddle.2.2
  rw [List.nodup_append] at hleft
  have hu₁_not_ys : u₁ ∉ ys := by
    intro hu₁
    exact hleft.2.2 u₁ (by simp) u₁ hu₁ rfl
  have hu₂_not_ys : u₂ ∉ ys := by
    intro hu₂
    exact hmiddle_disj u₂ (by simp [hu₂]) u₂ (by simp) rfl
  have hx_ne_u₁ : x ≠ u₁ := by
    intro h
    exact hu₁_not_ys (h ▸ hx_mid)
  have hx_ne_u₂ : x ≠ u₂ := by
    intro h
    exact hu₂_not_ys (h ▸ hx_mid)
  have hx_support : x ∈ ((u₁ :: (ys ++ [u₂])).toFinset) := by
    rw [List.mem_toFinset]
    simp [List.mem_append, hx_mid, or_assoc, or_left_comm, or_comm]
  exact ListSpanningPath.tail_ne_singleton_of_support_vertex_ne_endpoints
    (p := (w.extractMatchingPair xs ys zs u₀ u₁ u₂ u₃ hsplit).1)
    hx_support hx_ne_u₁ hx_ne_u₂

theorem HamiltonianCycleWitness.extractMatchingPair_right_tail_ne_singleton_of_side_nonempty
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys zs : List V) (u₀ u₁ u₂ u₃ : V)
    (hsplit :
      w.start :: w.tail =
        xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs)
    (hside : zs ++ xs ≠ []) :
    ((w.extractMatchingPair xs ys zs u₀ u₁ u₂ u₃ hsplit).2).tail ≠ [u₀] := by
  rcases List.eq_nil_or_concat' (zs ++ xs) with hnil | ⟨ws, x, hwx⟩
  · exact False.elim (hside hnil)
  have hx_side : x ∈ zs ++ xs := by
    simp [hwx]
  have hnodup : List.Nodup (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) := by
    simpa [hsplit, List.append_assoc] using w.nodup
  have hnodup_left : List.Nodup (xs ++ (([u₀, u₁] ++ ys ++ [u₂, u₃]) ++ zs)) := by
    simpa [List.append_assoc] using hnodup
  have hnodup_right : List.Nodup ((xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]) ++ zs) := by
    simpa [List.append_assoc] using hnodup
  rw [List.nodup_append] at hnodup_left hnodup_right
  have hxs_disj := hnodup_left.2.2
  have hzs_disj := hnodup_right.2.2
  have hx_ne_u₃ : x ≠ u₃ := by
    rcases (List.mem_append.1 hx_side) with hx | hx
    · intro h
      exact hzs_disj u₃ (by simp [List.mem_append]) x hx h.symm
    · exact hxs_disj x hx u₃ (by simp [List.mem_append])
  have hx_ne_u₀ : x ≠ u₀ := by
    rcases (List.mem_append.1 hx_side) with hx | hx
    · intro h
      exact hzs_disj u₀ (by simp [List.mem_append]) x hx h.symm
    · exact hxs_disj x hx u₀ (by simp [List.mem_append])
  have hx_support : x ∈ ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) := by
    rw [List.mem_toFinset]
    rcases (List.mem_append.1 hx_side) with hx | hx <;>
      simp [List.mem_append, hx, or_assoc, or_left_comm, or_comm]
  exact ListSpanningPath.tail_ne_singleton_of_support_vertex_ne_endpoints
    (p := (w.extractMatchingPair xs ys zs u₀ u₁ u₂ u₃ hsplit).2)
    hx_support hx_ne_u₃ hx_ne_u₀

theorem HamiltonianCycleWitness.extractMatchingPair_of_cycleSupportInfix
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₀ u₁ u₂ u₃ : V}
    (hneq : u₃ ≠ u₀)
    (hinfix : [u₀, u₁, u₂, u₃] <:+: w.start :: (w.tail ++ [w.start])) :
    ∃ xs' zs', Nonempty
      (ListSpanningPath G.Adj ((u₁ :: [u₂]).toFinset) u₁ u₂ ×
        ListSpanningPath G.Adj ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) u₃ u₀) := by
  rcases hinfix with ⟨xs, zs, hsplit⟩
  refine ?_
  simpa [List.append_assoc] using
    HamiltonianCycleWitness.extractMatchingPair_of_cycleSupportSplit
      w (u₀ := u₀) (u₁ := u₁) (u₂ := u₂) (u₃ := u₃)
      hneq (xs := xs) (ys := []) (zs := zs) (by
        simpa [List.append_assoc] using hsplit)

theorem HamiltonianCycleWitness.extractMatchingPair_support_union_eq_univ
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys zs : List V) (u₀ u₁ u₂ u₃ : V)
    (hsplit :
      w.start :: w.tail =
        xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs) :
    ((u₁ :: (ys ++ [u₂])).toFinset) ∪
        ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) =
      (Finset.univ : Finset V) := by
  ext v
  constructor
  · intro hv
    simp
  · intro _
    have hvOpen : v ∈ w.start :: w.tail := by
      simpa using (w.spans v).1 (by simp)
    have hvSplit : v ∈ xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs := by
      simpa [hsplit] using hvOpen
    rw [Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
    simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hvSplit

/--
Convert a mathlib Hamiltonian cycle walk into the repo's explicit list witness.

This is the splice-side bridge from `SimpleGraph.Walk.IsHamiltonianCycle` to the
list-encoded cycle machinery used by `HamiltonianCycleWitness`.
-/
def SimpleGraph.Walk.IsHamiltonianCycle.toHamiltonianCycleWitness
    {a : V} {c : G.Walk a a}
    [Fintype V]
    (hc : c.IsHamiltonianCycle) :
    HamiltonianCycleWitness G.Adj (Finset.univ : Finset V) where
  start := a
  tail := c.tail.support.dropLast
  cycle_adj := by
    intro x y hxy
    have hsupport :
        a :: (c.tail.support.dropLast ++ [a]) = c.support := by
      have htail :
          c.tail.support.dropLast ++ [a] = c.tail.support := by
        simpa [List.concat_eq_append] using
          (SimpleGraph.Walk.support_eq_concat c.tail).symm
      calc
        a :: (c.tail.support.dropLast ++ [a]) = a :: c.tail.support := by
          rw [htail]
        _ = c.support := by
          simpa using (SimpleGraph.Walk.cons_support_tail c hc.isCycle.not_nil)
    have hinfix :
        [x, y] <:+: c.support := by
      rw [← hsupport]
      exact infix_of_mem_edgePairs hxy
    exact SimpleGraph.Walk.adj_of_infix_support hinfix
  nodup := by
    have htailNodup : c.tail.support.Nodup :=
      hc.isCycle.isPath_tail.support_nodup
    have hconcatNodup : (c.tail.support.dropLast.concat a).Nodup := by
      rw [← SimpleGraph.Walk.support_eq_concat c.tail]
      exact htailNodup
    rcases (List.nodup_concat _ _).1 hconcatNodup with ⟨ha, hdrop⟩
    exact List.nodup_cons.2 ⟨ha, hdrop⟩
  spans := by
    intro v
    change v ∈ (Finset.univ : Finset V) ↔ v ∈ a :: c.tail.support.dropLast
    constructor
    · intro _
      have hsupport :
          a :: (c.tail.support.dropLast ++ [a]) = c.support := by
        have htail :
            c.tail.support.dropLast ++ [a] = c.tail.support := by
          simpa [List.concat_eq_append] using
            (SimpleGraph.Walk.support_eq_concat c.tail).symm
        calc
          a :: (c.tail.support.dropLast ++ [a]) = a :: c.tail.support := by
            rw [htail]
          _ = c.support := by
            simpa using (SimpleGraph.Walk.cons_support_tail c hc.isCycle.not_nil)
      have hv : v ∈ c.support := hc.mem_support v
      rw [← hsupport] at hv
      rcases List.mem_cons.1 hv with rfl | hv
      · simp
      · rw [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | hv
        · exact List.mem_cons_of_mem _ hv
        · simp [hv]
    · intro _
      simp

/-- Build the actual closed walk encoded by a `HamiltonianCycleWitness`. -/
def HamiltonianCycleWitness.toWalk
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V)) :
    G.Walk w.start w.start :=
  walkOfListLast (G := G) w.start w.tail w.start (by
    intro a b hab
    exact w.cycle_adj hab)

/-- The support of the walk built from a `HamiltonianCycleWitness`. -/
@[simp] theorem HamiltonianCycleWitness.support_toWalk
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V)) :
    w.toWalk.support = w.start :: (w.tail ++ [w.start]) := by
  simpa [HamiltonianCycleWitness.toWalk] using
    support_walkOfListLast (G := G) w.start w.tail w.start w.cycle_adj

/--
Reverse the cyclic ordering of an explicit Hamiltonian cycle witness.

The start vertex is kept fixed, while the tail is traversed in reverse order.
-/
def HamiltonianCycleWitness.reverse
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S) :
    HamiltonianCycleWitness G.Adj S where
  start := w.start
  tail := w.tail.reverse
  cycle_adj := by
    intro a b hab
    have hrev :
        [a, b] <:+: w.start :: (w.tail.reverse ++ [w.start]) :=
      infix_of_mem_edgePairs hab
    have horig : [b, a] <:+: w.start :: (w.tail ++ [w.start]) := by
      simpa [List.reverse_reverse, List.reverse_cons, List.reverse_append, List.append_assoc]
        using List.pair_infix_reverse hrev
    exact (w.cycle_adj (mem_edgePairs_of_infix_pair horig)).symm
  nodup := by
    rcases List.nodup_cons.1 w.nodup with ⟨hstart, htail⟩
    refine List.nodup_cons.2 ?_
    constructor
    · simpa using hstart
    · exact List.nodup_reverse.2 htail
  spans := by
    intro x
    rw [w.spans x]
    simp

@[simp] theorem HamiltonianCycleWitness.cycleSupport_reverse
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S) :
    (w.reverse).start :: ((w.reverse).tail ++ [(w.reverse).start]) =
      (w.start :: (w.tail ++ [w.start])).reverse := by
  simp [HamiltonianCycleWitness.reverse, List.reverse_reverse, List.reverse_cons,
    List.reverse_append, List.append_assoc]

/--
Rotate an explicit Hamiltonian cycle witness so that the last tail vertex becomes
the new start vertex.

If the open support list is `start :: middle ++ [t]`, the rotated witness starts
at `t` and continues with `start :: middle`.
-/
def HamiltonianCycleWitness.rotateLast
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    (middle : List V) (t : V)
    (htail : w.tail = middle ++ [t]) :
    HamiltonianCycleWitness G.Adj S :=
  ((w.reverse).rotateOnce t middle.reverse (by
      simpa [HamiltonianCycleWitness.reverse, htail, List.reverse_append]
        using show w.tail.reverse = t :: middle.reverse by
          rw [htail, List.reverse_append]
          simp)).reverse

@[simp] theorem HamiltonianCycleWitness.openList_rotateLast
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    (middle : List V) (t : V)
    (htail : w.tail = middle ++ [t]) :
    (w.rotateLast middle t htail).start :: (w.rotateLast middle t htail).tail =
      t :: (w.start :: middle) := by
  have hrev : w.tail.reverse = t :: middle.reverse := by
    rw [htail, List.reverse_append]
    simp
  simp [HamiltonianCycleWitness.rotateLast, HamiltonianCycleWitness.reverse,
    HamiltonianCycleWitness.rotateOnce, hrev, htail, List.reverse_append,
    List.append_assoc]

theorem HamiltonianCycleWitness.path4_infix_reverse
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    {a b c d : V}
    (hinfix : [d, c, b, a] <:+: w.start :: (w.tail ++ [w.start])) :
    [a, b, c, d] <:+:
      (w.reverse).start :: ((w.reverse).tail ++ [(w.reverse).start]) := by
  rw [HamiltonianCycleWitness.cycleSupport_reverse]
  simpa [List.reverse_reverse] using List.path4_infix_reverse hinfix

theorem HamiltonianCycleWitness.path4_open_or_reverse_of_cycleInfix
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    {a b c d : V}
    (hinfix : [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]))
    (had : a ≠ d) :
    [a, b, c, d] <:+: w.start :: w.tail ∨
      [d, c, b, a] <:+: (w.reverse).start :: (w.reverse).tail := by
  by_cases hd : d = w.start
  · right
    have ha : a ≠ (w.reverse).start := by
      simpa [HamiltonianCycleWitness.reverse, hd] using
        (fun h => had (h.trans hd.symm))
    have hrev :
        [d, c, b, a] <:+:
          (w.reverse).start :: ((w.reverse).tail ++ [(w.reverse).start]) :=
      w.path4_infix_reverse hinfix
    exact List.path4_infix_of_infix_append_singleton hrev ha
  · left
    exact List.path4_infix_of_infix_append_singleton hinfix hd

/--
Rotate a Hamiltonian cycle witness so a cyclic ordered `P4` appears as an open
block in the witness list.
-/
theorem HamiltonianCycleWitness.exists_open_path4_witness_of_cycleInfix
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {a b c d : V}
    (had : a ≠ d)
    (hinfix : [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start])) :
    ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      ∃ xs ys : List V,
        w'.start :: w'.tail = xs ++ [a, b, c, d] ++ ys := by
  by_cases hopen : [a, b, c, d] <:+: w.start :: w.tail
  · rcases hopen with ⟨xs, ys, hsplit⟩
    exact ⟨w, xs, ys, hsplit.symm⟩
  · rcases hinfix with ⟨xs, ys, hsplit⟩
    rcases List.eq_nil_or_concat' ys with rfl | ⟨ys', y, hys⟩
    · have hd : d = w.start := by
        have hlast := congrArg List.getLast? hsplit
        have hleft : (xs ++ [a, b, c, d]).getLast? = some d := by
          simpa using
            (List.getLast?_append_of_ne_nil xs
              (by simp : ([a, b, c, d] : List V) ≠ []))
        have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (w.start :: w.tail)
              (by simp : ([w.start] : List V) ≠ []))
        have hdOpt : some d = some w.start := by
          calc
            some d = (xs ++ [a, b, c, d] ++ []).getLast? := by
              simpa [List.append_assoc] using hleft.symm
            _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
              simpa using hlast
            _ = some w.start := hright
        exact Option.some.inj hdOpt
      have hopenSuffix : xs ++ [a, b, c] = w.start :: w.tail := by
        apply (List.append_left_injective [w.start])
        simpa [hd, List.append_assoc] using hsplit
      cases xs with
      | nil =>
          have ha : a = w.start := by
            exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
          exact False.elim (had (ha.trans hd.symm))
      | cons x xs' =>
          have hx : x = w.start := by
            exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
          have htail : w.tail = xs' ++ [a, b, c] := by
            exact (Option.some.inj (by simpa using congrArg List.tail? hopenSuffix)).symm
          have htail_ne : w.tail ≠ [] := by
            intro hnil
            simp [hnil] at htail
          obtain ⟨v, vs, hcons⟩ := List.exists_cons_of_ne_nil htail_ne
          let w' := w.rotateOnce v vs hcons
          have hw'open :
              w'.start :: w'.tail = xs' ++ [a, b, c, d] := by
            calc
              w'.start :: w'.tail = w.tail ++ [w.start] := by
                simpa [w'] using w.openList_rotateOnce v vs hcons
              _ = (xs' ++ [a, b, c]) ++ [d] := by
                simp [htail, hd, List.append_assoc]
              _ = xs' ++ [a, b, c, d] := by
                simp [List.append_assoc]
          exact ⟨w', xs', [], by simpa using hw'open⟩
    · have hy : y = w.start := by
        have hlast := congrArg List.getLast? hsplit
        have hleft :
            (xs ++ [a, b, c, d] ++ ys' ++ [y]).getLast? = some y := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (xs ++ [a, b, c, d] ++ ys')
              (by simp : ([y] : List V) ≠ []))
        have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (w.start :: w.tail)
              (by simp : ([w.start] : List V) ≠ []))
        have hyOpt : some y = some w.start := by
          calc
            some y = (xs ++ [a, b, c, d] ++ (ys' ++ [y])).getLast? := by
              simpa [hys, List.append_assoc] using hleft.symm
            _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
              simpa [hys] using hlast
            _ = some w.start := hright
        exact Option.some.inj hyOpt
      have hopen' : [a, b, c, d] <:+: w.start :: w.tail := by
        refine ⟨xs, ys', ?_⟩
        apply (List.append_left_injective [w.start])
        simpa [hys, hy, List.append_assoc] using hsplit
      exact False.elim (hopen hopen')

theorem HamiltonianCycleWitness.path4_open_of_cycleInfix_of_start_eq_first
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    {a b c d : V}
    (hstart : w.start = a)
    (hinfix : [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]))
    (had : a ≠ d) :
    [a, b, c, d] <:+: w.start :: w.tail := by
  have hd : d ≠ w.start := by
    simpa [hstart] using had.symm
  exact List.path4_infix_of_infix_append_singleton hinfix hd

theorem HamiltonianCycleWitness.openList_split_of_open_start_eq_first
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    {a b c d : V}
    (hstart : w.start = a)
    (hinfix : [a, b, c, d] <:+: w.start :: w.tail) :
    ∃ ys, w.start :: w.tail = [a, b, c, d] ++ ys := by
  simpa [hstart] using List.path4_prefix_of_head_infix_nodup w.nodup (by simpa [hstart] using hinfix)

theorem HamiltonianCycleWitness.pair_open_reverse
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    {a b : V}
    (hab : [b, a] <:+: w.start :: w.tail)
    (hsb : w.start ≠ b)
    (hsa : w.start ≠ a) :
    [a, b] <:+: (w.reverse).start :: (w.reverse).tail := by
  have habClosed : [b, a] <:+: w.start :: (w.tail ++ [w.start]) :=
    List.infix_append_right (n := [w.start]) hab
  have hrevClosed : [a, b] <:+:
      (w.reverse).start :: ((w.reverse).tail ++ [(w.reverse).start]) := by
    rw [HamiltonianCycleWitness.cycleSupport_reverse]
    simpa [List.reverse_reverse] using List.pair_infix_reverse habClosed
  exact List.pair_infix_of_infix_append_singleton hrevClosed hsb.symm

theorem HamiltonianCycleWitness.path4_open_reverse
    {S : Finset V}
    (w : HamiltonianCycleWitness G.Adj S)
    {a b c d : V}
    (hinfix : [d, c, b, a] <:+: w.start :: w.tail)
    (hsd : w.start ≠ d)
    (hsa : w.start ≠ a) :
    [a, b, c, d] <:+: (w.reverse).start :: (w.reverse).tail := by
  have hclosed : [d, c, b, a] <:+: w.start :: (w.tail ++ [w.start]) :=
    List.infix_append_right (n := [w.start]) hinfix
  have hrevClosed : [a, b, c, d] <:+:
      (w.reverse).start :: ((w.reverse).tail ++ [(w.reverse).start]) := by
    exact w.path4_infix_reverse hclosed
  exact List.path4_infix_of_infix_append_singleton hrevClosed hsd.symm

theorem HamiltonianCycleWitness.edge_infix_or_reverse_of_toSubgraphAdj
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {a b : V}
    (hab : w.toWalk.toSubgraph.Adj a b) :
    [a, b] <:+: w.start :: (w.tail ++ [w.start]) ∨
      [b, a] <:+: w.start :: (w.tail ++ [w.start]) := by
  rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges,
    SimpleGraph.Walk.edges_eq_zipWith_support, w.support_toWalk] at hab
  exact List.infix_or_reverse_of_mem_zipWith_sym2 hab

theorem HamiltonianCycleWitness.edge_openInfix_or_reverse_of_toSubgraphAdj_of_start_ne
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {a b : V}
    (hab : w.toWalk.toSubgraph.Adj a b)
    (hsa : w.start ≠ a)
    (hsb : w.start ≠ b) :
    [a, b] <:+: w.start :: w.tail ∨
      [b, a] <:+: w.start :: w.tail := by
  rcases w.edge_infix_or_reverse_of_toSubgraphAdj hab with hab' | hba'
  · exact Or.inl <| List.pair_infix_of_infix_append_singleton hab' hsb.symm
  · exact Or.inr <| List.pair_infix_of_infix_append_singleton hba' hsa.symm

/--
Normalize the cyclic orientations of two selected cycle edges.

This is the seam-agnostic orientation split used by trisum matching consumers:
solver-family code should consume this package instead of redoing the same
edge-orientation case split locally.
-/
theorem HamiltonianCycleWitness.twoEdge_cycleInfixOrientation_of_toSubgraphAdj
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₀ u₁ u₂ u₃ : V}
    (h01 : w.toWalk.toSubgraph.Adj u₀ u₁)
    (h23 : w.toWalk.toSubgraph.Adj u₂ u₃) :
    (([u₀, u₁] <:+: w.start :: (w.tail ++ [w.start]) ∧
        [u₂, u₃] <:+: w.start :: (w.tail ++ [w.start])) ∨
      ([u₀, u₁] <:+: w.start :: (w.tail ++ [w.start]) ∧
        [u₃, u₂] <:+: w.start :: (w.tail ++ [w.start])) ∨
      ([u₁, u₀] <:+: w.start :: (w.tail ++ [w.start]) ∧
        [u₂, u₃] <:+: w.start :: (w.tail ++ [w.start])) ∨
      ([u₁, u₀] <:+: w.start :: (w.tail ++ [w.start]) ∧
        [u₃, u₂] <:+: w.start :: (w.tail ++ [w.start]))) := by
  rcases w.edge_infix_or_reverse_of_toSubgraphAdj h01 with h01cyc | h10cyc
  · rcases w.edge_infix_or_reverse_of_toSubgraphAdj h23 with h23cyc | h32cyc
    · exact Or.inl ⟨h01cyc, h23cyc⟩
    · exact Or.inr <| Or.inl ⟨h01cyc, h32cyc⟩
  · rcases w.edge_infix_or_reverse_of_toSubgraphAdj h23 with h23cyc | h32cyc
    · exact Or.inr <| Or.inr <| Or.inl ⟨h10cyc, h23cyc⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨h10cyc, h32cyc⟩

/--
Normalize two selected cycle-edge orientations together with the only generic
closed/open issue for a `P4` carried by the same Hamiltonian cycle.

The result deliberately stops at a reusable package: trisum consumers can decide
which oriented move package to invoke without expanding witness-start cases.
-/
theorem HamiltonianCycleWitness.twoEdge_cycleInfixOrientation_and_path4_open_or_reverse
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₀ u₁ u₂ u₃ a b c d : V}
    (h01 : w.toWalk.toSubgraph.Adj u₀ u₁)
    (h23 : w.toWalk.toSubgraph.Adj u₂ u₃)
    (hinfix : [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]))
    (had : a ≠ d) :
    ((([u₀, u₁] <:+: w.start :: (w.tail ++ [w.start]) ∧
        [u₂, u₃] <:+: w.start :: (w.tail ++ [w.start])) ∨
      ([u₀, u₁] <:+: w.start :: (w.tail ++ [w.start]) ∧
        [u₃, u₂] <:+: w.start :: (w.tail ++ [w.start])) ∨
      ([u₁, u₀] <:+: w.start :: (w.tail ++ [w.start]) ∧
        [u₂, u₃] <:+: w.start :: (w.tail ++ [w.start])) ∨
      ([u₁, u₀] <:+: w.start :: (w.tail ++ [w.start]) ∧
        [u₃, u₂] <:+: w.start :: (w.tail ++ [w.start]))) ∧
      ([a, b, c, d] <:+: w.start :: w.tail ∨
        [d, c, b, a] <:+: (w.reverse).start :: (w.reverse).tail)) := by
  exact
    ⟨w.twoEdge_cycleInfixOrientation_of_toSubgraphAdj h01 h23,
      w.path4_open_or_reverse_of_cycleInfix hinfix had⟩

theorem HamiltonianCycleWitness.toSubgraphAdj_of_infix_pair
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {a b : V}
    (hab : [a, b] <:+: w.start :: (w.tail ++ [w.start])) :
    w.toWalk.toSubgraph.Adj a b := by
  rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges,
    SimpleGraph.Walk.edges_eq_zipWith_support, w.support_toWalk]
  exact mem_zipWith_sym2_of_mem_edgePairs (mem_edgePairs_of_infix_pair hab)

theorem HamiltonianCycleWitness.extractMatchingPair_of_cycleSupportSplit_with_props
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₀ u₁ u₂ u₃ : V}
    (hneq : u₃ ≠ u₀)
    {xs ys zs : List V}
    (hsplit :
      xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs =
        w.start :: (w.tail ++ [w.start]))
    (hnot12 : ¬ w.toWalk.toSubgraph.Adj u₁ u₂)
    (hnot30 : ¬ w.toWalk.toSubgraph.Adj u₃ u₀) :
    ∃ xs' zs',
      ∃ p₁₂ : ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂,
      ∃ p₃₀ : ListSpanningPath G.Adj ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) u₃ u₀,
        (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₁ ∨ v = u₂) ∧
        (∀ v, v ∈ ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₃ ∨ v = u₀) ∧
        p₁₂.tail ≠ [u₂] ∧
        p₃₀.tail ≠ [u₀] ∧
        (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) → False) := by
  by_cases hzs : zs = []
  · subst hzs
    have hu₃ : u₃ = w.start := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]).getLast? = some u₃ := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [u₀, u₁] ++ ys ++ [u₂])
            (by simp : ([u₃] : List V) ≠ []))
      have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
      have hu₃Opt : some u₃ = some w.start := by
        calc
          some u₃ = (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]).getLast? := by
            simpa [List.append_assoc] using hleft.symm
          _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
            simpa using hlast
          _ = some w.start := hright
      exact Option.some.inj hu₃Opt
    have hmid : ys ≠ [] := by
      intro hys
      have h12infix : [u₁, u₂] <:+: w.start :: (w.tail ++ [w.start]) := by
        refine ⟨xs ++ [u₀], [u₃], ?_⟩
        simpa [hys, List.append_assoc] using hsplit
      exact hnot12 (w.toSubgraphAdj_of_infix_pair h12infix)
    have hopenSuffix : xs ++ [u₀, u₁] ++ ys ++ [u₂] = w.start :: w.tail := by
      apply (List.append_left_injective [w.start])
      simpa [hu₃, List.append_assoc] using hsplit
    cases xs with
    | nil =>
        have hu₀ : u₀ = w.start := by
          exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
        exact False.elim (hneq (hu₃.trans hu₀.symm))
    | cons x xs' =>
        have hx : x = w.start := by
          exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
        have htail : w.tail = xs' ++ [u₀, u₁] ++ ys ++ [u₂] := by
          exact (Option.some.inj (by simpa using congrArg List.tail? hopenSuffix)).symm
        have htail_ne : w.tail ≠ [] := by
          intro hnil
          simp [hnil] at htail
        obtain ⟨v, vs, hcons⟩ := List.exists_cons_of_ne_nil htail_ne
        let w' := w.rotateOnce v vs hcons
        have hw'open :
            w'.start :: w'.tail = xs' ++ [u₀, u₁] ++ ys ++ [u₂, u₃] := by
          calc
            w'.start :: w'.tail = w.tail ++ [w.start] := by
              simpa [w'] using w.openList_rotateOnce v vs hcons
            _ = (xs' ++ [u₀, u₁] ++ ys ++ [u₂]) ++ [u₃] := by
              simp [htail, hu₃, List.append_assoc]
            _ = xs' ++ [u₀, u₁] ++ ys ++ [u₂, u₃] := by
              simp [List.append_assoc]
        have hside : xs' ≠ [] := by
          intro hxs'
          have h30infix : [u₃, u₀] <:+: w.start :: (w.tail ++ [w.start]) := by
            refine ⟨[], u₁ :: (ys ++ [u₂, u₃]), ?_⟩
            simpa [hxs', hx, hu₃, List.append_assoc] using hsplit
          exact hnot30 (w.toSubgraphAdj_of_infix_pair h30infix)
        let p₁₂ :=
          (w'.extractMatchingPair xs' ys [] u₀ u₁ u₂ u₃ (by
            simpa [List.append_assoc] using hw'open)).1
        let p₃₀ :=
          (w'.extractMatchingPair xs' ys [] u₀ u₁ u₂ u₃ (by
            simpa [List.append_assoc] using hw'open)).2
        refine ⟨xs', [], p₁₂, p₃₀, ?_⟩
        constructor
        · intro v hv hseam
          exact w'.extractMatchingPair_left_support_seamSubset xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) v hv hseam
        constructor
        · intro v hv hseam
          exact w'.extractMatchingPair_right_support_seamSubset xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) v hv hseam
        constructor
        · exact w'.extractMatchingPair_left_tail_ne_singleton_of_middle_nonempty
            xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) hmid
        constructor
        · exact w'.extractMatchingPair_right_tail_ne_singleton_of_side_nonempty
            xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) (by simpa using hside)
        · intro v hv₁ hv₃
          exact w'.extractMatchingPair_support_disjoint xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) v hv₁ hv₃
  · rcases List.eq_nil_or_concat' zs with _ | ⟨zs', z, hzs'⟩
    · contradiction
    have hz : z = w.start := by
      have hlast := congrArg List.getLast? hsplit
      have hleft :
          (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs' ++ [z]).getLast? = some z := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs')
            (by simp : ([z] : List V) ≠ []))
      have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
      have hzOpt : some z = some w.start := by
        calc
          some z = (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ (zs' ++ [z])).getLast? := by
            simpa [hzs', List.append_assoc] using hleft.symm
          _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
            simpa [hzs'] using hlast
          _ = some w.start := hright
      exact Option.some.inj hzOpt
    have hmid : ys ≠ [] := by
      intro hys
      have h12infix : [u₁, u₂] <:+: w.start :: (w.tail ++ [w.start]) := by
        refine ⟨xs ++ [u₀], [u₃] ++ zs' ++ [w.start], ?_⟩
        simpa [hys, hzs', hz, List.append_assoc] using hsplit
      exact hnot12 (w.toSubgraphAdj_of_infix_pair h12infix)
    have hopenSplit : xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs' = w.start :: w.tail := by
      apply (List.append_left_injective [w.start])
      simpa [hzs', hz, List.append_assoc] using hsplit
    have hside : zs' ++ xs ≠ [] := by
      intro hzx
      have hzxs : zs' = [] ∧ xs = [] := by
        simpa using hzx
      rcases hzxs with ⟨hzsNil, hxsNil⟩
      have hu₀ : u₀ = w.start := by
        exact Option.some.inj
          (by simpa [hzsNil, hxsNil, List.append_assoc] using congrArg List.head? hopenSplit)
      have h30infix : [u₃, u₀] <:+: w.start :: (w.tail ++ [w.start]) := by
        refine ⟨[u₀, u₁] ++ ys ++ [u₂], [], ?_⟩
        simpa [hzs', hz, hzsNil, hxsNil, hu₀, List.append_assoc] using hsplit
      exact hnot30 (w.toSubgraphAdj_of_infix_pair h30infix)
    let p₁₂ :=
      (w.extractMatchingPair xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm).1
    let p₃₀ :=
      (w.extractMatchingPair xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm).2
    refine ⟨xs, zs', p₁₂, p₃₀, ?_⟩
    constructor
    · intro v hv hseam
      exact w.extractMatchingPair_left_support_seamSubset xs ys zs' u₀ u₁ u₂ u₃
        hopenSplit.symm v hv hseam
    constructor
    · intro v hv hseam
      exact w.extractMatchingPair_right_support_seamSubset xs ys zs' u₀ u₁ u₂ u₃
        hopenSplit.symm v hv hseam
    constructor
    · exact w.extractMatchingPair_left_tail_ne_singleton_of_middle_nonempty
        xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm hmid
    constructor
    · exact w.extractMatchingPair_right_tail_ne_singleton_of_side_nonempty
        xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm hside
    · intro v hv₁ hv₃
      exact w.extractMatchingPair_support_disjoint xs ys zs' u₀ u₁ u₂ u₃
        hopenSplit.symm v hv₁ hv₃

theorem HamiltonianCycleWitness.extractMatchingPair_of_cycleSupportSplit_with_props_cover
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₀ u₁ u₂ u₃ : V}
    (hneq : u₃ ≠ u₀)
    {xs ys zs : List V}
    (hsplit :
      xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs =
        w.start :: (w.tail ++ [w.start]))
    (hnot12 : ¬ w.toWalk.toSubgraph.Adj u₁ u₂)
    (hnot30 : ¬ w.toWalk.toSubgraph.Adj u₃ u₀) :
    ∃ xs' zs',
      ∃ p₁₂ : ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂,
      ∃ p₃₀ : ListSpanningPath G.Adj ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) u₃ u₀,
        (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₁ ∨ v = u₂) ∧
        (∀ v, v ∈ ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₃ ∨ v = u₀) ∧
        p₁₂.tail ≠ [u₂] ∧
        p₃₀.tail ≠ [u₀] ∧
        (((u₁ :: (ys ++ [u₂])).toFinset) ∪
          ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) =
            (Finset.univ : Finset V)) ∧
        (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) → False) := by
  by_cases hzs : zs = []
  · subst hzs
    have hu₃ : u₃ = w.start := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]).getLast? = some u₃ := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [u₀, u₁] ++ ys ++ [u₂])
            (by simp : ([u₃] : List V) ≠ []))
      have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
      have hu₃Opt : some u₃ = some w.start := by
        calc
          some u₃ = (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]).getLast? := by
            simpa [List.append_assoc] using hleft.symm
          _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
            simpa using hlast
          _ = some w.start := hright
      exact Option.some.inj hu₃Opt
    have hmid : ys ≠ [] := by
      intro hys
      have h12infix : [u₁, u₂] <:+: w.start :: (w.tail ++ [w.start]) := by
        refine ⟨xs ++ [u₀], [u₃], ?_⟩
        simpa [hys, List.append_assoc] using hsplit
      exact hnot12 (w.toSubgraphAdj_of_infix_pair h12infix)
    have hopenSuffix : xs ++ [u₀, u₁] ++ ys ++ [u₂] = w.start :: w.tail := by
      apply (List.append_left_injective [w.start])
      simpa [hu₃, List.append_assoc] using hsplit
    cases xs with
    | nil =>
        have hu₀ : u₀ = w.start := by
          exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
        exact False.elim (hneq (hu₃.trans hu₀.symm))
    | cons x xs' =>
        have hx : x = w.start := by
          exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
        have htail : w.tail = xs' ++ [u₀, u₁] ++ ys ++ [u₂] := by
          exact (Option.some.inj (by simpa using congrArg List.tail? hopenSuffix)).symm
        have htail_ne : w.tail ≠ [] := by
          intro hnil
          simp [hnil] at htail
        obtain ⟨v, vs, hcons⟩ := List.exists_cons_of_ne_nil htail_ne
        let w' := w.rotateOnce v vs hcons
        have hw'open :
            w'.start :: w'.tail = xs' ++ [u₀, u₁] ++ ys ++ [u₂, u₃] := by
          calc
            w'.start :: w'.tail = w.tail ++ [w.start] := by
              simpa [w'] using w.openList_rotateOnce v vs hcons
            _ = (xs' ++ [u₀, u₁] ++ ys ++ [u₂]) ++ [u₃] := by
              simp [htail, hu₃, List.append_assoc]
            _ = xs' ++ [u₀, u₁] ++ ys ++ [u₂, u₃] := by
              simp [List.append_assoc]
        have hside : xs' ≠ [] := by
          intro hxs'
          have h30infix : [u₃, u₀] <:+: w.start :: (w.tail ++ [w.start]) := by
            refine ⟨[], u₁ :: (ys ++ [u₂, u₃]), ?_⟩
            simpa [hxs', hx, hu₃, List.append_assoc] using hsplit
          exact hnot30 (w.toSubgraphAdj_of_infix_pair h30infix)
        let p₁₂ :=
          (w'.extractMatchingPair xs' ys [] u₀ u₁ u₂ u₃ (by
            simpa [List.append_assoc] using hw'open)).1
        let p₃₀ :=
          (w'.extractMatchingPair xs' ys [] u₀ u₁ u₂ u₃ (by
            simpa [List.append_assoc] using hw'open)).2
        refine ⟨xs', [], p₁₂, p₃₀, ?_⟩
        constructor
        · intro v hv hseam
          exact w'.extractMatchingPair_left_support_seamSubset xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) v hv hseam
        constructor
        · intro v hv hseam
          exact w'.extractMatchingPair_right_support_seamSubset xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) v hv hseam
        constructor
        · exact w'.extractMatchingPair_left_tail_ne_singleton_of_middle_nonempty
            xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) hmid
        constructor
        · exact w'.extractMatchingPair_right_tail_ne_singleton_of_side_nonempty
            xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) (by simpa using hside)
        constructor
        · simpa [List.append_assoc] using
            w'.extractMatchingPair_support_union_eq_univ
              xs' ys [] u₀ u₁ u₂ u₃
              (by simpa [List.append_assoc] using hw'open)
        · intro v hv₁ hv₃
          exact w'.extractMatchingPair_support_disjoint xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) v hv₁ hv₃
  · rcases List.eq_nil_or_concat' zs with _ | ⟨zs', z, hzs'⟩
    · contradiction
    have hz : z = w.start := by
      have hlast := congrArg List.getLast? hsplit
      have hleft :
          (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs' ++ [z]).getLast? = some z := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs')
            (by simp : ([z] : List V) ≠ []))
      have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
      have hzOpt : some z = some w.start := by
        calc
          some z = (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ (zs' ++ [z])).getLast? := by
            simpa [hzs', List.append_assoc] using hleft.symm
          _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
            simpa [hzs'] using hlast
          _ = some w.start := hright
      exact Option.some.inj hzOpt
    have hmid : ys ≠ [] := by
      intro hys
      have h12infix : [u₁, u₂] <:+: w.start :: (w.tail ++ [w.start]) := by
        refine ⟨xs ++ [u₀], [u₃] ++ zs' ++ [w.start], ?_⟩
        simpa [hys, hzs', hz, List.append_assoc] using hsplit
      exact hnot12 (w.toSubgraphAdj_of_infix_pair h12infix)
    have hopenSplit : xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs' = w.start :: w.tail := by
      apply (List.append_left_injective [w.start])
      simpa [hzs', hz, List.append_assoc] using hsplit
    have hside : zs' ++ xs ≠ [] := by
      intro hzx
      have hzxs : zs' = [] ∧ xs = [] := by
        simpa using hzx
      rcases hzxs with ⟨hzsNil, hxsNil⟩
      have hu₀ : u₀ = w.start := by
        exact Option.some.inj
          (by simpa [hzsNil, hxsNil, List.append_assoc] using congrArg List.head? hopenSplit)
      have h30infix : [u₃, u₀] <:+: w.start :: (w.tail ++ [w.start]) := by
        refine ⟨[u₀, u₁] ++ ys ++ [u₂], [], ?_⟩
        simpa [hzs', hz, hzsNil, hxsNil, hu₀, List.append_assoc] using hsplit
      exact hnot30 (w.toSubgraphAdj_of_infix_pair h30infix)
    let p₁₂ :=
      (w.extractMatchingPair xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm).1
    let p₃₀ :=
      (w.extractMatchingPair xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm).2
    refine ⟨xs, zs', p₁₂, p₃₀, ?_⟩
    constructor
    · intro v hv hseam
      exact w.extractMatchingPair_left_support_seamSubset xs ys zs' u₀ u₁ u₂ u₃
        hopenSplit.symm v hv hseam
    constructor
    · intro v hv hseam
      exact w.extractMatchingPair_right_support_seamSubset xs ys zs' u₀ u₁ u₂ u₃
        hopenSplit.symm v hv hseam
    constructor
    · exact w.extractMatchingPair_left_tail_ne_singleton_of_middle_nonempty
        xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm hmid
    constructor
    · exact w.extractMatchingPair_right_tail_ne_singleton_of_side_nonempty
        xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm hside
    constructor
    · exact w.extractMatchingPair_support_union_eq_univ
        xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm
    · intro v hv₁ hv₃
      exact w.extractMatchingPair_support_disjoint xs ys zs' u₀ u₁ u₂ u₃
        hopenSplit.symm v hv₁ hv₃

theorem HamiltonianCycleWitness.extractMatchingPair_of_cycleSupportSplit_with_props_cover_and_infix
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₀ u₁ u₂ u₃ a b c d : V}
    (hneq : u₃ ≠ u₀)
    {xs ys zs : List V}
    (hsplit :
      xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs =
        w.start :: (w.tail ++ [w.start]))
    (hnot12 : ¬ w.toWalk.toSubgraph.Adj u₁ u₂)
    (hnot30 : ¬ w.toWalk.toSubgraph.Adj u₃ u₀)
    (hinfix : [a, b, c, d] <:+: w.start :: w.tail)
    (hb0 : b ≠ u₀) (hb1 : b ≠ u₁) (hb2 : b ≠ u₂) (hb3 : b ≠ u₃)
    (hc0 : c ≠ u₀) (hc1 : c ≠ u₁) (hc2 : c ≠ u₂) (hc3 : c ≠ u₃) :
    (∃ xs' zs',
      ∃ p₁₂ : ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂,
      ∃ p₃₀ : ListSpanningPath G.Adj ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) u₃ u₀,
        (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₁ ∨ v = u₂) ∧
        (∀ v, v ∈ ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₃ ∨ v = u₀) ∧
        p₁₂.tail ≠ [u₂] ∧
        p₃₀.tail ≠ [u₀] ∧
        p₁₂.tail = ys ++ [u₂] ∧
        p₃₀.tail = (zs' ++ xs') ++ [u₀] ∧
        (((u₁ :: (ys ++ [u₂])).toFinset) ∪
          ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) =
            (Finset.univ : Finset V)) ∧
        (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) → False) ∧
        [a, b, c, d] <:+: u₁ :: (ys ++ [u₂])) ∨
      (∃ xs' zs',
        ∃ p₁₂ : ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂,
        ∃ p₃₀ : ListSpanningPath G.Adj ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) u₃ u₀,
          (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
            v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₁ ∨ v = u₂) ∧
          (∀ v, v ∈ ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) →
            v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₃ ∨ v = u₀) ∧
          p₁₂.tail ≠ [u₂] ∧
          p₃₀.tail ≠ [u₀] ∧
          p₁₂.tail = ys ++ [u₂] ∧
          p₃₀.tail = (zs' ++ xs') ++ [u₀] ∧
          (((u₁ :: (ys ++ [u₂])).toFinset) ∪
            ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) =
              (Finset.univ : Finset V)) ∧
          (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
            v ∈ ((u₃ :: ((zs' ++ xs') ++ [u₀])).toFinset) → False) ∧
          [a, b, c, d] <:+: u₃ :: ((zs' ++ xs') ++ [u₀])) := by
  by_cases hzs : zs = []
  · subst hzs
    have hu₃ : u₃ = w.start := by
      have hlast := congrArg List.getLast? hsplit
      have hleft : (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]).getLast? = some u₃ := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [u₀, u₁] ++ ys ++ [u₂])
            (by simp : ([u₃] : List V) ≠ []))
      have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (w.start :: w.tail)
            (by simp : ([w.start] : List V) ≠ []))
      have hu₃Opt : some u₃ = some w.start := by
        calc
          some u₃ = (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃]).getLast? := by
            simpa [List.append_assoc] using hleft.symm
          _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
            simpa using hlast
          _ = some w.start := hright
      exact Option.some.inj hu₃Opt
    have hmid : ys ≠ [] := by
      intro hys
      have h12infix : [u₁, u₂] <:+: w.start :: (w.tail ++ [w.start]) := by
        refine ⟨xs ++ [u₀], [u₃], ?_⟩
        simpa [hys, List.append_assoc] using hsplit
      exact hnot12 (w.toSubgraphAdj_of_infix_pair h12infix)
    have hopenSuffix : xs ++ [u₀, u₁] ++ ys ++ [u₂] = w.start :: w.tail := by
      apply (List.append_left_injective [w.start])
      simpa [hu₃, List.append_assoc] using hsplit
    cases xs with
    | nil =>
        have hu₀ : u₀ = w.start := by
          exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
        exact False.elim (hneq (hu₃.trans hu₀.symm))
    | cons x xs' =>
        have hx : x = w.start := by
          exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
        have htail : w.tail = xs' ++ [u₀, u₁] ++ ys ++ [u₂] := by
          exact (Option.some.inj (by simpa using congrArg List.tail? hopenSuffix)).symm
        have htail_ne : w.tail ≠ [] := by
          intro hnil
          simp [hnil] at htail
        obtain ⟨v, vs, hcons⟩ := List.exists_cons_of_ne_nil htail_ne
        let w' := w.rotateOnce v vs hcons
        have hw'open :
            w'.start :: w'.tail = xs' ++ [u₀, u₁] ++ ys ++ [u₂, u₃] := by
          calc
            w'.start :: w'.tail = w.tail ++ [w.start] := by
              simpa [w'] using w.openList_rotateOnce v vs hcons
            _ = (xs' ++ [u₀, u₁] ++ ys ++ [u₂]) ++ [u₃] := by
              simp [htail, hu₃, List.append_assoc]
            _ = xs' ++ [u₀, u₁] ++ ys ++ [u₂, u₃] := by
              simp [List.append_assoc]
        have hside : xs' ≠ [] := by
          intro hxs'
          have h30infix : [u₃, u₀] <:+: w.start :: (w.tail ++ [w.start]) := by
            refine ⟨[], u₁ :: (ys ++ [u₂, u₃]), ?_⟩
            simpa [hxs', hx, hu₃, List.append_assoc] using hsplit
          exact hnot30 (w.toSubgraphAdj_of_infix_pair h30infix)
        obtain ⟨w'', hw''start, hw''tail⟩ :=
          w'.rotateToEdge xs' (ys ++ [u₂, u₃] ++ []) u₀ u₁ (by
            simpa [List.append_assoc] using hw'open)
        let bdy :=
          w''.toBoundaryCycleWitness (ys ++ u₂ :: u₃ :: ([] ++ xs')) u₀ (by
            simpa [hw''tail, List.append_assoc])
        have hbdy_mid : bdy.middle = ys ++ u₂ :: u₃ :: ([] ++ xs') := by
          rfl
        let p₁₂ : ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂ := by
          simpa [hw''start, List.append_assoc] using
            bdy.takeUntilInternalEdge ys u₂ u₃ ([] ++ xs') hbdy_mid
        let p₃₀ : ListSpanningPath G.Adj ((u₃ :: (([] ++ xs') ++ [u₀])).toFinset) u₃ u₀ := by
          simpa [List.append_assoc] using
            bdy.dropUntilInternalEdge ys u₂ u₃ ([] ++ xs') hbdy_mid
        have htailEq₁₂ : p₁₂.tail = ys ++ [u₂] := by
          simpa [p₁₂, bdy, List.append_assoc] using
            bdy.takeUntilInternalEdge_tail_of_start_eq
              hw''start ys u₂ u₃ ([] ++ xs') hbdy_mid
        have htailEq₃₀ : p₃₀.tail = ([] ++ xs') ++ [u₀] := by
          simpa [p₃₀, bdy, List.append_assoc] using
            bdy.dropUntilInternalEdge_tail ys u₂ u₃ ([] ++ xs') hbdy_mid
        have hloc :
            [a, b, c, d] <:+: u₃ :: (xs' ++ [u₀]) ∨
              [a, b, c, d] <:+: u₁ :: (ys ++ [u₂]) := by
          have hopen :
              w.start :: w.tail = (u₃ :: xs') ++ [u₀, u₁] ++ (ys ++ [u₂]) := by
            simpa [hx, hu₃, htail, List.append_assoc]
          exact
            List.path4_infix_left_or_right_of_split_middle_ne
              w.nodup hopen hinfix hb0 hb1 hc0 hc1
        have hp₁₂ :
            ∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
              v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₁ ∨ v = u₂ := by
          intro v hv hseam
          exact w'.extractMatchingPair_left_support_seamSubset xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) v hv hseam
        have hp₃₀ :
            ∀ v, v ∈ ((u₃ :: (([] ++ xs') ++ [u₀])).toFinset) →
              v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₃ ∨ v = u₀ := by
          intro v hv hseam
          exact w'.extractMatchingPair_right_support_seamSubset xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) v hv hseam
        have htail₁₂ : p₁₂.tail ≠ [u₂] := by
          intro h
          have : ys = [] := by
            simpa [htailEq₁₂] using h
          exact hmid this
        have htail₃₀ : p₃₀.tail ≠ [u₀] := by
          intro h
          have : xs' = [] := by
            cases xs' with
            | nil => rfl
            | cons x xs'' =>
                exfalso
                simp [htailEq₃₀] at h
          exact hside this
        have hcover :
            ((u₁ :: (ys ++ [u₂])).toFinset) ∪
              ((u₃ :: (([] ++ xs') ++ [u₀])).toFinset) =
                (Finset.univ : Finset V) := by
          simpa [List.append_assoc] using
            w'.extractMatchingPair_support_union_eq_univ
              xs' ys [] u₀ u₁ u₂ u₃
              (by simpa [List.append_assoc] using hw'open)
        have hdisj :
            ∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
              v ∈ ((u₃ :: (([] ++ xs') ++ [u₀])).toFinset) → False := by
          intro v hv₁ hv₃
          exact w'.extractMatchingPair_support_disjoint xs' ys [] u₀ u₁ u₂ u₃
            (by simpa [List.append_assoc] using hw'open) v hv₁ hv₃
        rcases hloc with hright | hleft
        · right
          refine ⟨xs', [], p₁₂, p₃₀, hp₁₂, hp₃₀,
            htail₁₂, htail₃₀, htailEq₁₂, htailEq₃₀, hcover, hdisj, ?_⟩
          simpa [List.append_assoc] using hright
        · left
          exact ⟨xs', [], p₁₂, p₃₀, hp₁₂, hp₃₀,
            htail₁₂, htail₃₀, htailEq₁₂, htailEq₃₀, hcover, hdisj, hleft⟩
  · rcases List.eq_nil_or_concat' zs with _ | ⟨zs', z, hzs'⟩
    · contradiction
    have hz : z = w.start := by
      have hlast := congrArg List.getLast? hsplit
      have hleft :
          (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs' ++ [z]).getLast? = some z := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs')
            (by simp : ([z] : List V) ≠ []))
      have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (w.start :: w.tail)
            (by simp : ([w.start] : List V) ≠ []))
      have hzOpt : some z = some w.start := by
        calc
          some z = (xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ (zs' ++ [z])).getLast? := by
            simpa [hzs', List.append_assoc] using hleft.symm
          _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
            simpa [hzs'] using hlast
          _ = some w.start := hright
      exact Option.some.inj hzOpt
    have hmid : ys ≠ [] := by
      intro hys
      have h12infix : [u₁, u₂] <:+: w.start :: (w.tail ++ [w.start]) := by
        refine ⟨xs ++ [u₀], [u₃] ++ zs' ++ [w.start], ?_⟩
        simpa [hys, hzs', hz, List.append_assoc] using hsplit
      exact hnot12 (w.toSubgraphAdj_of_infix_pair h12infix)
    have hopenSplit : xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs' = w.start :: w.tail := by
      apply (List.append_left_injective [w.start])
      simpa [hzs', hz, List.append_assoc] using hsplit
    have hside : zs' ++ xs ≠ [] := by
      intro hzx
      have hzxs : zs' = [] ∧ xs = [] := by
        simpa using hzx
      rcases hzxs with ⟨hzsNil, hxsNil⟩
      have hu₀ : u₀ = w.start := by
        exact Option.some.inj
          (by simpa [hzsNil, hxsNil, List.append_assoc] using congrArg List.head? hopenSplit)
      have h30infix : [u₃, u₀] <:+: w.start :: (w.tail ++ [w.start]) := by
        refine ⟨[u₀, u₁] ++ ys ++ [u₂], [], ?_⟩
        simpa [hzs', hz, hzsNil, hxsNil, hu₀, List.append_assoc] using hsplit
      exact hnot30 (w.toSubgraphAdj_of_infix_pair h30infix)
    have hrot :
        ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
          w'.start = u₁ ∧
            w'.tail = ((ys ++ [u₂, u₃] ++ zs') ++ xs) ++ [u₀] := by
      simpa [List.append_assoc] using
        w.rotateToEdge xs (ys ++ [u₂, u₃] ++ zs') u₀ u₁ (by
          simpa [List.append_assoc] using hopenSplit.symm)
    let w' := Classical.choose hrot
    have hw'start : w'.start = u₁ := (Classical.choose_spec hrot).1
    have hw'tail :
        w'.tail = ((ys ++ [u₂, u₃] ++ zs') ++ xs) ++ [u₀] :=
      (Classical.choose_spec hrot).2
    let bdy :=
      w'.toBoundaryCycleWitness (ys ++ u₂ :: u₃ :: (zs' ++ xs)) u₀ (by
        simpa [hw'tail, List.append_assoc])
    have hbdy_mid : bdy.middle = ys ++ u₂ :: u₃ :: (zs' ++ xs) := by
      rfl
    let p₁₂ : ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂ := by
      simpa [hw'start, List.append_assoc] using
        bdy.takeUntilInternalEdge ys u₂ u₃ (zs' ++ xs) hbdy_mid
    let p₃₀ : ListSpanningPath G.Adj ((u₃ :: ((zs' ++ xs) ++ [u₀])).toFinset) u₃ u₀ := by
      simpa [List.append_assoc] using
        bdy.dropUntilInternalEdge ys u₂ u₃ (zs' ++ xs) hbdy_mid
    have htailEq₁₂ : p₁₂.tail = ys ++ [u₂] := by
      simpa [p₁₂, bdy, List.append_assoc] using
        bdy.takeUntilInternalEdge_tail_of_start_eq
          hw'start ys u₂ u₃ (zs' ++ xs) hbdy_mid
    have htailEq₃₀ : p₃₀.tail = (zs' ++ xs) ++ [u₀] := by
      simpa [p₃₀, bdy, List.append_assoc] using
        bdy.dropUntilInternalEdge_tail ys u₂ u₃ (zs' ++ xs) hbdy_mid
    have hloc :
        [a, b, c, d] <:+: u₁ :: (ys ++ [u₂]) ∨
          [a, b, c, d] <:+: u₃ :: ((zs' ++ xs) ++ [u₀]) := by
      exact
        List.path4_infix_left_or_right_of_matching_split
          w.nodup hopenSplit.symm hinfix
          hb0 hb1 hb2 hb3 hc0 hc1 hc2 hc3
    have hp₁₂ :
        ∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₁ ∨ v = u₂ := by
      intro v hv hseam
      exact w.extractMatchingPair_left_support_seamSubset xs ys zs' u₀ u₁ u₂ u₃
        hopenSplit.symm v hv hseam
    have hp₃₀ :
        ∀ v, v ∈ ((u₃ :: ((zs' ++ xs) ++ [u₀])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₃ ∨ v = u₀ := by
      intro v hv hseam
      exact w.extractMatchingPair_right_support_seamSubset xs ys zs' u₀ u₁ u₂ u₃
        hopenSplit.symm v hv hseam
    have htail₁₂ : p₁₂.tail ≠ [u₂] := by
      intro h
      have : ys = [] := by
        simpa [htailEq₁₂] using h
      exact hmid this
    have htail₃₀ : p₃₀.tail ≠ [u₀] := by
      intro h
      have : zs' ++ xs = [] := by
        cases hzx : zs' ++ xs with
        | nil =>
            exact rfl
        | cons z zs'' =>
            exfalso
            simp [htailEq₃₀, hzx, List.append_assoc] at h
      exact hside this
    have hcover :
        ((u₁ :: (ys ++ [u₂])).toFinset) ∪
          ((u₃ :: ((zs' ++ xs) ++ [u₀])).toFinset) =
            (Finset.univ : Finset V) := by
      exact w.extractMatchingPair_support_union_eq_univ
        xs ys zs' u₀ u₁ u₂ u₃ hopenSplit.symm
    have hdisj :
        ∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ((u₃ :: ((zs' ++ xs) ++ [u₀])).toFinset) → False := by
      intro v hv₁ hv₃
      exact w.extractMatchingPair_support_disjoint xs ys zs' u₀ u₁ u₂ u₃
        hopenSplit.symm v hv₁ hv₃
    rcases hloc with hleft | hright
    · left
      exact ⟨xs, zs', p₁₂, p₃₀, hp₁₂, hp₃₀,
        htail₁₂, htail₃₀, htailEq₁₂, htailEq₃₀, hcover, hdisj, hleft⟩
    · right
      exact ⟨xs, zs', p₁₂, p₃₀, hp₁₂, hp₃₀,
        htail₁₂, htail₃₀, htailEq₁₂, htailEq₃₀, hcover, hdisj, hright⟩

theorem HamiltonianCycleWitness.extractMatchingPair_of_openCycleSupportSplit_with_props_and_infix
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₀ u₁ u₂ u₃ a b c d : V}
    {xs ys zs : List V}
    (hsplit :
      w.start :: w.tail =
        xs ++ [u₀, u₁] ++ ys ++ [u₂, u₃] ++ zs)
    (hmid : ys ≠ [])
    (hside : zs ++ xs ≠ [])
    (hinfix : [a, b, c, d] <:+: w.start :: w.tail)
    (hb0 : b ≠ u₀) (hb1 : b ≠ u₁) (hb2 : b ≠ u₂) (hb3 : b ≠ u₃)
    (hc0 : c ≠ u₀) (hc1 : c ≠ u₁) (hc2 : c ≠ u₂) (hc3 : c ≠ u₃) :
    (∃ p₁₂ : ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂,
      ∃ p₃₀ : ListSpanningPath G.Adj ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) u₃ u₀,
        (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₁ ∨ v = u₂) ∧
        (∀ v, v ∈ ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₃ ∨ v = u₀) ∧
        p₁₂.tail ≠ [u₂] ∧
        p₃₀.tail ≠ [u₀] ∧
        (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
          v ∈ ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) → False) ∧
        [a, b, c, d] <:+: u₁ :: (ys ++ [u₂])) ∨
      (∃ p₁₂ : ListSpanningPath G.Adj ((u₁ :: (ys ++ [u₂])).toFinset) u₁ u₂,
        ∃ p₃₀ : ListSpanningPath G.Adj ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) u₃ u₀,
          (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
            v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₁ ∨ v = u₂) ∧
          (∀ v, v ∈ ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) →
            v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₃ ∨ v = u₀) ∧
          p₁₂.tail ≠ [u₂] ∧
          p₃₀.tail ≠ [u₀] ∧
          (∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
            v ∈ ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) → False) ∧
          [a, b, c, d] <:+: u₃ :: ((zs ++ xs) ++ [u₀])) := by
  let p₁₂ := (w.extractMatchingPair xs ys zs u₀ u₁ u₂ u₃ hsplit).1
  let p₃₀ := (w.extractMatchingPair xs ys zs u₀ u₁ u₂ u₃ hsplit).2
  have hp₁₂ :
      ∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
        v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₁ ∨ v = u₂ := by
    exact w.extractMatchingPair_left_support_seamSubset xs ys zs u₀ u₁ u₂ u₃ hsplit
  have hp₃₀ :
      ∀ v, v ∈ ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) →
        v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₃ ∨ v = u₀ := by
    exact w.extractMatchingPair_right_support_seamSubset xs ys zs u₀ u₁ u₂ u₃ hsplit
  have htail₁₂ : p₁₂.tail ≠ [u₂] := by
    exact w.extractMatchingPair_left_tail_ne_singleton_of_middle_nonempty
      xs ys zs u₀ u₁ u₂ u₃ hsplit hmid
  have htail₃₀ : p₃₀.tail ≠ [u₀] := by
    exact w.extractMatchingPair_right_tail_ne_singleton_of_side_nonempty
      xs ys zs u₀ u₁ u₂ u₃ hsplit hside
  have hdisj :
      ∀ v, v ∈ ((u₁ :: (ys ++ [u₂])).toFinset) →
        v ∈ ((u₃ :: ((zs ++ xs) ++ [u₀])).toFinset) → False := by
    exact w.extractMatchingPair_support_disjoint xs ys zs u₀ u₁ u₂ u₃ hsplit
  have hloc :
      [a, b, c, d] <:+: u₁ :: (ys ++ [u₂]) ∨
        [a, b, c, d] <:+: u₃ :: ((zs ++ xs) ++ [u₀]) := by
    exact
      List.path4_infix_left_or_right_of_matching_split
        w.nodup hsplit hinfix hb0 hb1 hb2 hb3 hc0 hc1 hc2 hc3
  rcases hloc with hleft | hright
  · left
    refine ⟨p₁₂, p₃₀, hp₁₂, hp₃₀, htail₁₂, htail₃₀, hdisj, ?_⟩
    exact hleft
  · right
    refine ⟨p₁₂, p₃₀, hp₁₂, hp₃₀, htail₁₂, htail₃₀, hdisj, ?_⟩
    exact hright

theorem HamiltonianCycleWitness.extractThreeEdgePath_of_cycleSupportInfix_with_props
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₃ u₀ u₁ u₂ : V}
    (hneq : u₂ ≠ u₃)
    (hinfix : [u₃, u₀, u₁, u₂] <:+: w.start :: (w.tail ++ [w.start]))
    (hnot23 : ¬ w.toWalk.toSubgraph.Adj u₂ u₃) :
    ∃ xs ys,
      ∃ p : ListSpanningPath G.Adj ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) u₂ u₃,
        (∀ v, v ∈ ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₂ ∨ v = u₃) ∧
        p.tail ≠ [u₃] := by
  by_cases hopen : [u₃, u₀, u₁, u₂] <:+: w.start :: w.tail
  · rcases hopen with ⟨xs, ys, hsplit⟩
    have hside : ys ++ xs ≠ [] := by
      intro hyx
      have hys : ys = [] := by
        cases ys with
        | nil => rfl
        | cons y ys' =>
            simp at hyx
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons x xs' =>
            simp [hys] at hyx
      have h23infix : [u₂, u₃] <:+: w.start :: (w.tail ++ [w.start]) := by
        have hstart : u₃ = w.start := by
          exact Option.some.inj (by simpa [hxs, hys] using congrArg List.head? hsplit)
        have htail : [u₀, u₁, u₂] = w.tail := by
          exact Option.some.inj (by simpa [hxs, hys] using congrArg List.tail? hsplit)
        refine ⟨[u₃, u₀, u₁], [], ?_⟩
        simpa [hstart, htail.symm, List.append_assoc]
      exact hnot23 (w.toSubgraphAdj_of_infix_pair h23infix)
    let p := w.extractThreeEdgePath xs ys u₃ u₀ u₁ u₂ hsplit.symm
    refine ⟨xs, ys, p, ?_, ?_⟩
    · intro v hv hseam
      exact w.extractThreeEdgePath_support_seamSubset xs ys u₃ u₀ u₁ u₂
        hsplit.symm v hv hseam
    · exact w.extractThreeEdgePath_tail_ne_singleton_of_side_nonempty
        xs ys u₃ u₀ u₁ u₂ hsplit.symm hside
  · rcases hinfix with ⟨xs, ys, hsplit⟩
    rcases List.eq_nil_or_concat' ys with rfl | ⟨ys', y, hys⟩
    · have hu₂ : u₂ = w.start := by
        have hlast := congrArg List.getLast? hsplit
        have hleft : (xs ++ [u₃, u₀, u₁, u₂]).getLast? = some u₂ := by
          simpa using
            (List.getLast?_append_of_ne_nil xs (by simp : ([u₃, u₀, u₁, u₂] : List V) ≠ []))
        have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
        have hu₂Opt : some u₂ = some w.start := by
          calc
            some u₂ = (xs ++ [u₃, u₀, u₁, u₂] ++ []).getLast? := by
              simpa [List.append_assoc] using hleft.symm
            _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
              simpa using hlast
            _ = some w.start := hright
        exact Option.some.inj hu₂Opt
      have hopenSuffix : xs ++ [u₃, u₀, u₁] = w.start :: w.tail := by
        apply (List.append_left_injective [w.start])
        simpa [hu₂, List.append_assoc] using hsplit
      cases xs with
      | nil =>
          have hu₃ : u₃ = w.start := by
            exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
          exact False.elim (hneq (hu₂.trans hu₃.symm))
      | cons x xs' =>
          have hx : x = w.start := by
            exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
          have htail : w.tail = xs' ++ [u₃, u₀, u₁] := by
            exact (Option.some.inj (by simpa using congrArg List.tail? hopenSuffix)).symm
          have htail_ne : w.tail ≠ [] := by
            intro hnil
            simp [hnil] at htail
          obtain ⟨v, vs, hcons⟩ := List.exists_cons_of_ne_nil htail_ne
          let w' := w.rotateOnce v vs hcons
          have hw'open :
              w'.start :: w'.tail = xs' ++ [u₃, u₀, u₁, u₂] := by
            calc
              w'.start :: w'.tail = w.tail ++ [w.start] := by
                simpa [w'] using w.openList_rotateOnce v vs hcons
              _ = (xs' ++ [u₃, u₀, u₁]) ++ [u₂] := by
                simp [htail, hu₂, List.append_assoc]
              _ = xs' ++ [u₃, u₀, u₁, u₂] := by
                simp [List.append_assoc]
          have hside : xs' ≠ [] := by
            intro hxs'
            have h23infix : [u₂, u₃] <:+: w.start :: (w.tail ++ [w.start]) := by
              refine ⟨[], [u₀, u₁, u₂], ?_⟩
              simpa [hxs', hx, hu₂, List.append_assoc] using hsplit
            exact hnot23 (w.toSubgraphAdj_of_infix_pair h23infix)
          let p := w'.extractThreeEdgePath xs' [] u₃ u₀ u₁ u₂ (by simpa using hw'open)
          refine ⟨xs', [], p, ?_, ?_⟩
          · intro v hv hseam
            exact w'.extractThreeEdgePath_support_seamSubset xs' [] u₃ u₀ u₁ u₂
              (by simpa using hw'open) v hv hseam
          · exact w'.extractThreeEdgePath_tail_ne_singleton_of_side_nonempty
              xs' [] u₃ u₀ u₁ u₂ (by simpa using hw'open) (by simpa using hside)
    · have hy : y = w.start := by
        have hlast := congrArg List.getLast? hsplit
        have hleft :
            (xs ++ [u₃, u₀, u₁, u₂] ++ ys' ++ [y]).getLast? = some y := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (xs ++ [u₃, u₀, u₁, u₂] ++ ys')
              (by simp : ([y] : List V) ≠ []))
        have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
        have hyOpt : some y = some w.start := by
          calc
            some y = (xs ++ [u₃, u₀, u₁, u₂] ++ (ys' ++ [y])).getLast? := by
              simpa [hys, List.append_assoc] using hleft.symm
            _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
              simpa [hys] using hlast
            _ = some w.start := hright
        exact Option.some.inj hyOpt
      have hopen' : [u₃, u₀, u₁, u₂] <:+: w.start :: w.tail := by
        refine ⟨xs, ys', ?_⟩
        apply (List.append_left_injective [w.start])
        simpa [hys, hy, List.append_assoc] using hsplit
      exact False.elim (hopen hopen')

theorem HamiltonianCycleWitness.extractThreeEdgePath_of_cycleSupportInfix_with_props_cover
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {u₃ u₀ u₁ u₂ : V}
    (hneq : u₂ ≠ u₃)
    (hinfix : [u₃, u₀, u₁, u₂] <:+: w.start :: (w.tail ++ [w.start]))
    (hnot23 : ¬ w.toWalk.toSubgraph.Adj u₂ u₃) :
    ∃ xs ys,
      ∃ p : ListSpanningPath G.Adj ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) u₂ u₃,
        (∀ v, v ∈ ((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) →
          v ∈ ([u₀, u₁, u₂, u₃] : List V).toFinset → v = u₂ ∨ v = u₃) ∧
        p.tail ≠ [u₃] ∧
        (((u₂ :: ((ys ++ xs) ++ [u₃])).toFinset) ∪
          ([u₀, u₁] : List V).toFinset = (Finset.univ : Finset V)) := by
  by_cases hopen : [u₃, u₀, u₁, u₂] <:+: w.start :: w.tail
  · rcases hopen with ⟨xs, ys, hsplit⟩
    have hside : ys ++ xs ≠ [] := by
      intro hyx
      have hys : ys = [] := by
        cases ys with
        | nil => rfl
        | cons y ys' =>
            simp at hyx
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons x xs' =>
            simp [hys] at hyx
      have h23infix : [u₂, u₃] <:+: w.start :: (w.tail ++ [w.start]) := by
        have hstart : u₃ = w.start := by
          exact Option.some.inj (by simpa [hxs, hys] using congrArg List.head? hsplit)
        have htail : [u₀, u₁, u₂] = w.tail := by
          exact Option.some.inj (by simpa [hxs, hys] using congrArg List.tail? hsplit)
        refine ⟨[u₃, u₀, u₁], [], ?_⟩
        simpa [hstart, htail.symm, List.append_assoc]
      exact hnot23 (w.toSubgraphAdj_of_infix_pair h23infix)
    let p := w.extractThreeEdgePath xs ys u₃ u₀ u₁ u₂ hsplit.symm
    refine ⟨xs, ys, p, ?_, ?_, ?_⟩
    · intro v hv hseam
      exact w.extractThreeEdgePath_support_seamSubset xs ys u₃ u₀ u₁ u₂
        hsplit.symm v hv hseam
    · exact w.extractThreeEdgePath_tail_ne_singleton_of_side_nonempty
        xs ys u₃ u₀ u₁ u₂ hsplit.symm hside
    · exact w.extractThreeEdgePath_support_union_seam_eq_univ
        xs ys u₃ u₀ u₁ u₂ hsplit.symm
  · rcases hinfix with ⟨xs, ys, hsplit⟩
    rcases List.eq_nil_or_concat' ys with rfl | ⟨ys', y, hys⟩
    · have hu₂ : u₂ = w.start := by
        have hlast := congrArg List.getLast? hsplit
        have hleft : (xs ++ [u₃, u₀, u₁, u₂]).getLast? = some u₂ := by
          simpa using
            (List.getLast?_append_of_ne_nil xs (by simp : ([u₃, u₀, u₁, u₂] : List V) ≠ []))
        have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
        have hu₂Opt : some u₂ = some w.start := by
          calc
            some u₂ = (xs ++ [u₃, u₀, u₁, u₂] ++ []).getLast? := by
              simpa [List.append_assoc] using hleft.symm
            _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
              simpa using hlast
            _ = some w.start := hright
        exact Option.some.inj hu₂Opt
      have hopenSuffix : xs ++ [u₃, u₀, u₁] = w.start :: w.tail := by
        apply (List.append_left_injective [w.start])
        simpa [hu₂, List.append_assoc] using hsplit
      cases xs with
      | nil =>
          have hu₃ : u₃ = w.start := by
            exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
          exact False.elim (hneq (hu₂.trans hu₃.symm))
      | cons x xs' =>
          have hx : x = w.start := by
            exact Option.some.inj (by simpa using congrArg List.head? hopenSuffix)
          have htail : w.tail = xs' ++ [u₃, u₀, u₁] := by
            exact (Option.some.inj (by simpa using congrArg List.tail? hopenSuffix)).symm
          have htail_ne : w.tail ≠ [] := by
            intro hnil
            simp [hnil] at htail
          obtain ⟨v, vs, hcons⟩ := List.exists_cons_of_ne_nil htail_ne
          let w' := w.rotateOnce v vs hcons
          have hw'open :
              w'.start :: w'.tail = xs' ++ [u₃, u₀, u₁, u₂] := by
            calc
              w'.start :: w'.tail = w.tail ++ [w.start] := by
                simpa [w'] using w.openList_rotateOnce v vs hcons
              _ = (xs' ++ [u₃, u₀, u₁]) ++ [u₂] := by
                simp [htail, hu₂, List.append_assoc]
              _ = xs' ++ [u₃, u₀, u₁, u₂] := by
                simp [List.append_assoc]
          have hside : xs' ≠ [] := by
            intro hxs'
            have h23infix : [u₂, u₃] <:+: w.start :: (w.tail ++ [w.start]) := by
              refine ⟨[], [u₀, u₁, u₂], ?_⟩
              simpa [hxs', hx, hu₂, List.append_assoc] using hsplit
            exact hnot23 (w.toSubgraphAdj_of_infix_pair h23infix)
          let p := w'.extractThreeEdgePath xs' [] u₃ u₀ u₁ u₂ (by simpa using hw'open)
          refine ⟨xs', [], p, ?_, ?_, ?_⟩
          · intro v hv hseam
            exact w'.extractThreeEdgePath_support_seamSubset xs' [] u₃ u₀ u₁ u₂
              (by simpa using hw'open) v hv hseam
          · exact w'.extractThreeEdgePath_tail_ne_singleton_of_side_nonempty
              xs' [] u₃ u₀ u₁ u₂ (by simpa using hw'open) (by simpa using hside)
          · exact w'.extractThreeEdgePath_support_union_seam_eq_univ
              xs' [] u₃ u₀ u₁ u₂ (by simpa using hw'open)
    · have hy : y = w.start := by
        have hlast := congrArg List.getLast? hsplit
        have hleft :
            (xs ++ [u₃, u₀, u₁, u₂] ++ ys' ++ [y]).getLast? = some y := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (xs ++ [u₃, u₀, u₁, u₂] ++ ys')
              (by simp : ([y] : List V) ≠ []))
        have hright : (w.start :: (w.tail ++ [w.start])).getLast? = some w.start := by
          simpa [List.append_assoc] using
            (List.getLast?_append_of_ne_nil (w.start :: w.tail) (by simp : ([w.start] : List V) ≠ []))
        have hyOpt : some y = some w.start := by
          calc
            some y = (xs ++ [u₃, u₀, u₁, u₂] ++ (ys' ++ [y])).getLast? := by
              simpa [hys, List.append_assoc] using hleft.symm
            _ = (w.start :: (w.tail ++ [w.start])).getLast? := by
              simpa [hys] using hlast
            _ = some w.start := hright
        exact Option.some.inj hyOpt
      have hopen' : [u₃, u₀, u₁, u₂] <:+: w.start :: w.tail := by
        refine ⟨xs, ys', ?_⟩
        apply (List.append_left_injective [w.start])
        simpa [hys, hy, List.append_assoc] using hsplit
      exact False.elim (hopen hopen')

theorem HamiltonianCycleWitness.toSubgraph_adj_reverse
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {a b : V}
    (hab : w.toWalk.toSubgraph.Adj a b) :
    (w.reverse).toWalk.toSubgraph.Adj a b := by
  rcases w.edge_infix_or_reverse_of_toSubgraphAdj hab with hab' | hba'
  · have hrev : [b, a] <:+:
        (w.reverse).start :: ((w.reverse).tail ++ [(w.reverse).start]) := by
      rw [HamiltonianCycleWitness.cycleSupport_reverse]
      simpa [List.reverse_reverse] using List.pair_infix_reverse hab'
    have hadj' : (w.reverse).toWalk.toSubgraph.Adj b a := by
      rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges,
        SimpleGraph.Walk.edges_eq_zipWith_support]
      simpa [w.reverse.support_toWalk] using
        mem_zipWith_sym2_of_mem_edgePairs (mem_edgePairs_of_infix_pair hrev)
    exact (w.reverse).toWalk.toSubgraph.symm hadj'
  · have hrev : [a, b] <:+:
        (w.reverse).start :: ((w.reverse).tail ++ [(w.reverse).start]) := by
      rw [HamiltonianCycleWitness.cycleSupport_reverse]
      simpa [List.reverse_reverse] using List.pair_infix_reverse hba'
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges,
      SimpleGraph.Walk.edges_eq_zipWith_support]
    simpa [w.reverse.support_toWalk] using
      mem_zipWith_sym2_of_mem_edgePairs (mem_edgePairs_of_infix_pair hrev)

@[simp] theorem support_toWalk_hamiltonianCycleWitnessOfList
    (l : List V)
    (hvalid : IsHamiltonianCycleList G l) :
    (hamiltonianCycleWitnessOfList (G := G) l hvalid).toWalk.support = cycleSupportList l := by
  classical
  cases l with
  | nil =>
      cases hvalid
  | cons start tail =>
      rcases hvalid with ⟨hnodup, hspans, hadj⟩
      simp [hamiltonianCycleWitnessOfList, cycleSupportList]

theorem SimpleGraph.Walk.toSubgraph_adj_of_mem_edgePairs_support
    {u v a b : V} {p : G.Walk u v}
    (hab : (a, b) ∈ edgePairs p.support) :
    p.toSubgraph.Adj a b := by
  rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges, SimpleGraph.Walk.edges_eq_zipWith_support]
  exact mem_zipWith_sym2_of_mem_edgePairs hab

theorem HamiltonianCycleWitness.mem_cycleEdgePairs_of_rotateOnce_mem
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (v : V) (vs : List V)
    (htail : w.tail = v :: vs)
    {a b : V}
    (hmem :
      (a, b) ∈ edgePairs
        ((w.rotateOnce v vs htail).start ::
          ((w.rotateOnce v vs htail).tail ++ [(w.rotateOnce v vs htail).start]))) :
    (a, b) ∈ edgePairs (w.start :: (w.tail ++ [w.start])) := by
  have hmem' : (a, b) ∈ edgePairs (v :: ((vs ++ [w.start]) ++ [v])) := by
    simpa [HamiltonianCycleWitness.rotateOnce, htail, List.append_assoc] using hmem
  rw [edgePairs_append] at hmem'
  rcases List.mem_append.1 hmem' with hmid | hclose
  · have horig' : (a, b) ∈ edgePairs (v :: (vs ++ [w.start])) := by
      exact hmid
    have horig : (a, b) ∈ edgePairs (w.start :: v :: (vs ++ [w.start])) := by
      simpa [edgePairs] using List.mem_cons_of_mem (w.start, v) horig'
    simpa [htail, List.append_assoc] using horig
  · have hclose' : (a, b) = (w.start, v) := by
      have hend : endVertex v (vs ++ [w.start]) = w.start := by
        rw [endVertex_append]
        simp [endVertex]
      simpa [hend, edgePairs] using hclose
    rw [hclose']
    have horig : (w.start, v) ∈ edgePairs (w.start :: v :: (vs ++ [w.start])) := by
      simp [edgePairs]
    simpa [htail, List.append_assoc] using horig

theorem HamiltonianCycleWitness.rotateOnce_toSubgraphAdj
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (v : V) (vs : List V)
    (htail : w.tail = v :: vs)
    {a b : V}
    (hab : (w.rotateOnce v vs htail).toWalk.toSubgraph.Adj a b) :
    w.toWalk.toSubgraph.Adj a b := by
  rcases (w.rotateOnce v vs htail).edge_infix_or_reverse_of_toSubgraphAdj hab with hab' | hba'
  · have habmem :
        (a, b) ∈ edgePairs
          ((w.rotateOnce v vs htail).start ::
            ((w.rotateOnce v vs htail).tail ++ [(w.rotateOnce v vs htail).start])) :=
      mem_edgePairs_of_infix_pair hab'
    have horigmem : (a, b) ∈ edgePairs w.toWalk.support := by
      simpa [w.support_toWalk] using
        (w.mem_cycleEdgePairs_of_rotateOnce_mem v vs htail habmem)
    exact SimpleGraph.Walk.toSubgraph_adj_of_mem_edgePairs_support (p := w.toWalk) horigmem
  · have hbamem :
        (b, a) ∈ edgePairs
          ((w.rotateOnce v vs htail).start ::
            ((w.rotateOnce v vs htail).tail ++ [(w.rotateOnce v vs htail).start])) :=
      mem_edgePairs_of_infix_pair hba'
    have horigmem : (b, a) ∈ edgePairs w.toWalk.support := by
      simpa [w.support_toWalk] using
        (w.mem_cycleEdgePairs_of_rotateOnce_mem v vs htail hbamem)
    exact w.toWalk.toSubgraph.symm <|
      SimpleGraph.Walk.toSubgraph_adj_of_mem_edgePairs_support (p := w.toWalk) horigmem

theorem HamiltonianCycleWitness.rotateToEdge_preserving_toSubgraph
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (t s : V)
    (hsplit : w.start :: w.tail = xs ++ t :: s :: ys) :
    ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      w'.start = s ∧
      w'.tail = ys ++ xs ++ [t] ∧
      (∀ {a b}, w'.toWalk.toSubgraph.Adj a b → w.toWalk.toSubgraph.Adj a b) := by
  induction xs generalizing w ys with
  | nil =>
      have hstart : w.start = t := by
        rcases List.cons.inj hsplit with ⟨hstart, _⟩
        simpa using hstart
      have htail : w.tail = s :: ys := by
        rcases List.cons.inj hsplit with ⟨_, htail⟩
        simpa using htail
      refine ⟨w.rotateOnce s ys htail, rfl, ?_, ?_⟩
      · simpa [hstart, htail, HamiltonianCycleWitness.rotateOnce]
      · intro a b hab
        exact w.rotateOnce_toSubgraphAdj s ys htail hab
  | cons x xs ih =>
      rcases List.cons.inj hsplit with ⟨hstart, htail⟩
      have hnonempty : xs ++ t :: s :: ys ≠ [] := by simp
      rcases List.exists_cons_of_ne_nil hnonempty with ⟨v, vs, hvs⟩
      have htail' : w.tail = v :: vs := by
        simpa [hvs] using htail
      let w₁ := w.rotateOnce v vs htail'
      have hsplit₁ :
          w₁.start :: w₁.tail = xs ++ t :: s :: (ys ++ [x]) := by
        calc
          w₁.start :: w₁.tail = w.tail ++ [w.start] := by
            simpa [w₁] using (HamiltonianCycleWitness.openList_rotateOnce (w := w) v vs htail')
          _ = xs ++ t :: s :: (ys ++ [x]) := by
            rw [hstart, htail]
            simp [List.append_assoc]
      rcases ih w₁ (ys := ys ++ [x]) hsplit₁ with ⟨w', hw'start, hw'tail, hpres⟩
      refine ⟨w', hw'start, ?_, ?_⟩
      · simpa [List.append_assoc] using hw'tail
      · intro a b hab
        exact w.rotateOnce_toSubgraphAdj v vs htail' (hpres hab)

theorem HamiltonianCycleWitness.rotateToEdge_openList
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (t s : V)
    (hsplit : w.start :: w.tail = xs ++ t :: s :: ys) :
    ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      w'.start :: w'.tail = s :: (ys ++ xs ++ [t]) := by
  obtain ⟨w', hw'start, hw'tail⟩ := w.rotateToEdge xs ys t s hsplit
  refine ⟨w', ?_⟩
  simp [hw'start, hw'tail]

theorem HamiltonianCycleWitness.rotateToEdge_preserving_openList
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (t s : V)
    (hsplit : w.start :: w.tail = xs ++ t :: s :: ys) :
    ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      w'.start :: w'.tail = s :: (ys ++ xs ++ [t]) ∧
      (∀ {a b}, w'.toWalk.toSubgraph.Adj a b → w.toWalk.toSubgraph.Adj a b) := by
  obtain ⟨w', hw'start, hw'tail, hpres⟩ :=
    w.rotateToEdge_preserving_toSubgraph xs ys t s hsplit
  refine ⟨w', ?_, hpres⟩
  simp [hw'start, hw'tail]

theorem HamiltonianCycleWitness.rotateToEdge_infix_of_rotated
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (t s : V)
    (hsplit : w.start :: w.tail = xs ++ t :: s :: ys)
    {l : List V}
    (hinfix : l <:+: s :: (ys ++ xs ++ [t])) :
    ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      l <:+: w'.start :: w'.tail := by
  obtain ⟨w', hopen⟩ := w.rotateToEdge_openList xs ys t s hsplit
  exact ⟨w', by simpa [hopen] using hinfix⟩

theorem HamiltonianCycleWitness.rotateToEdge_preserving_infix_of_rotated
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    (xs ys : List V) (t s : V)
    (hsplit : w.start :: w.tail = xs ++ t :: s :: ys)
    {l : List V}
    (hinfix : l <:+: s :: (ys ++ xs ++ [t])) :
    ∃ w' : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      l <:+: w'.start :: w'.tail ∧
      (∀ {a b}, w'.toWalk.toSubgraph.Adj a b → w.toWalk.toSubgraph.Adj a b) := by
  obtain ⟨w', hopen, hpres⟩ :=
    w.rotateToEdge_preserving_openList xs ys t s hsplit
  exact ⟨w', by simpa [hopen] using hinfix, hpres⟩

/--
Any Hamiltonian cycle witness whose cyclic support contains an ordered `P4`
contains the corresponding length-`3` walk as a subwalk.
-/
theorem HamiltonianCycleWitness.toWalk_subwalk_of_path3_infix
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V))
    {a b c d : V}
    (hp : Path3Vertices G a b c d)
    (hinfix : [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start])) :
    (SimpleGraph.Walk.cons hp.1
      (SimpleGraph.Walk.cons hp.2.1
        (SimpleGraph.Walk.cons hp.2.2.1 SimpleGraph.Walk.nil))).IsSubwalk w.toWalk := by
  refine (SimpleGraph.Walk.isSubwalk_iff_support_isInfix).2 ?_
  simpa [w.support_toWalk]

/-- The length of the walk built from a `HamiltonianCycleWitness`. -/
@[simp] theorem HamiltonianCycleWitness.length_toWalk
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V)) :
    w.toWalk.length = w.tail.length + 1 := by
  simpa [HamiltonianCycleWitness.toWalk] using
    length_walkOfListLast (G := G) w.start w.tail w.start w.cycle_adj

/--
On graphs with at least three vertices, an explicit `HamiltonianCycleWitness`
produces a concrete mathlib Hamiltonian cycle walk.
-/
theorem HamiltonianCycleWitness.toWalk_isHamiltonianCycle
    (hcard : 3 ≤ Fintype.card V)
    (w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V)) :
    w.toWalk.IsHamiltonianCycle := by
  classical
  have hsupport :
      (w.start :: w.tail).toFinset = (Finset.univ : Finset V) := by
    ext v
    simp [w.spans v]
  have hlen :
      (w.start :: w.tail).length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup w.nodup, hsupport, Finset.card_univ]
  cases w with
  | mk start tail hcycleAdj hnodup hspans =>
      cases tail with
      | nil =>
          simp at hlen
          omega
      | cons next rest =>
          cases rest with
          | nil =>
              simp at hlen
              omega
          | cons mid rest =>
              have htailNodup : List.Nodup (next :: mid :: rest) :=
                (List.nodup_cons.1 hnodup).2
              have hstartNotMem : start ∉ next :: mid :: rest :=
                (List.nodup_cons.1 hnodup).1
              have hpathListNodup : List.Nodup (next :: (mid :: rest ++ [start])) := by
                rw [show next :: (mid :: rest ++ [start]) = (next :: mid :: rest) ++ [start] by rfl]
                rw [List.nodup_append]
                refine ⟨htailNodup, by simp, ?_⟩
                intro a ha b hb
                simp at hb
                subst b
                exact fun hEq => hstartNotMem (hEq ▸ ha)
              have hpathAdj :
                  ∀ ⦃a b⦄, (a, b) ∈ edgePairs (next :: ((mid :: rest) ++ [start])) → G.Adj a b := by
                intro a b hab
                exact hcycleAdj (by
                  simpa [edgePairs] using List.mem_cons_of_mem (start, next) hab)
              let p : G.Walk next start :=
                walkOfListLast (G := G) next (mid :: rest) start hpathAdj
              have hpSupport :
                  p.support = next :: ((mid :: rest) ++ [start]) := by
                simpa [p] using
                  (support_walkOfListLast (G := G) next (mid :: rest) start hpathAdj)
              have hpPath : p.IsPath := by
                refine SimpleGraph.Walk.IsPath.mk' ?_
                simpa [hpSupport] using hpathListNodup
              have hpLong : 1 < p.length := by
                simp [p, length_walkOfListLast]
              have hfirstEdge :
                  G.Adj start next := hcycleAdj (by simp [edgePairs])
              have hfirstNotMem : s(start, next) ∉ p.edges := by
                intro hmem
                have hpen : next = p.penultimate := hpPath.eq_penultimate_of_mem_edges hmem
                have hverts : p.getVert 0 = p.getVert (p.length - 1) := by
                  simpa [SimpleGraph.Walk.penultimate] using hpen
                have hidx :
                    (0 : ℕ) = p.length - 1 :=
                  hpPath.getVert_injOn (by simp) (Nat.sub_le _ _) hverts
                omega
              have hcyc : (SimpleGraph.Walk.cons hfirstEdge p).IsCycle := by
                exact (SimpleGraph.Walk.cons_isCycle_iff p hfirstEdge).2 ⟨hpPath, hfirstNotMem⟩
              have hcycLen :
                  (SimpleGraph.Walk.cons hfirstEdge p).length = Fintype.card V := by
                calc
                  (SimpleGraph.Walk.cons hfirstEdge p).length = p.length + 1 := by simp
                  _ = ((mid :: rest).length + 1) + 1 := by simp [p, length_walkOfListLast]
                  _ = Fintype.card V := by
                    simpa using hlen
              simpa [HamiltonianCycleWitness.toWalk, p] using
                (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq).2
                  ⟨hcyc, hcycLen⟩

end MathlibBridge

end GraphTargets

section LocalHamiltonianTargets

variable {V : Type v} [DecidableEq V]
variable {Adj : V → V → Prop}

/--
Terminal base case at the graph level: a boundary cycle witness already carries
the whole Hamiltonian cycle once the closing edge is retained.
-/
theorem OrderedSegmentFamily.BoundaryCycleWitness.hamiltonianOfClosingEdge
    {support : Finset V} {s t : V}
    (w : OrderedSegmentFamily.BoundaryCycleWitness Adj support s t)
    (hclose : Adj t s) :
    HamiltonianOn support Adj :=
  hamiltonianOn_of_spanningPath w.toSpanningPath hclose

/--
First explicit local move: if a parent cell is the union of two terminal child
cells meeting only at their attachment vertex, then the parent is Hamiltonian
once the closing edge survives.
-/
theorem OrderedSegmentFamily.hamiltonianOfTwoTerminalPieces
    {S₁ S₂ support : Finset V} {s a t : V}
    (p : OrderedSegmentFamily.BoundaryCycleWitness Adj S₁ s a)
    (q : OrderedSegmentFamily.BoundaryCycleWitness Adj S₂ a t)
    (hinter : ∀ v, v ∈ S₁ → v ∈ S₂ → v = a)
    (hsupport : S₁ ∪ S₂ = support)
    (hclose : Adj t s) :
    HamiltonianOn support Adj := by
  let path :=
    ListSpanningPath.append_of_support_inter p.toSpanningPath q.toSpanningPath hinter
  simpa [path, hsupport] using hamiltonianOn_of_spanningPath path hclose

/--
Splice four spanning paths arranged cyclically into one Hamiltonian cycle.

This is the path-level version of the cubic-trisum splice pattern: the last path
is truncated just before returning to the initial vertex, and its final edge
supplies the closing edge of the resulting Hamiltonian cycle.
-/
theorem ListSpanningPath.hamiltonianOfCyclicFour
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x : V}
    (p₀ : ListSpanningPath Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False) :
    HamiltonianOn (S₀ ∪ S₁ ∪ S₂ ∪ S₃) Adj := by
  let q₀₁ := ListSpanningPath.append_of_support_inter p₀ p₁ hinter₀₁
  let q₀₁₂ :=
    ListSpanningPath.append_of_support_inter q₀₁ p₂ (by
      intro v hv hv₂
      rw [Finset.mem_union] at hv
      rcases hv with hv₀ | hv₁
      · exact False.elim (hdisj₀₂ v hv₀ hv₂)
      · exact hinter₁₂ v hv₁ hv₂)
  let q₃ := p₃.truncateFinish middle₃ x htail₃
  have hinter₀₁₂₃ :
      ∀ v, v ∈ ((S₀ ∪ S₁) ∪ S₂) → v ∈ S₃.erase u₀ → v = u₃ := by
    intro v hv hv₃
    rcases Finset.mem_erase.mp hv₃ with ⟨hvne, hv₃'⟩
    rw [Finset.mem_union] at hv
    rcases hv with hv₀₁ | hv₂
    · rw [Finset.mem_union] at hv₀₁
      rcases hv₀₁ with hv₀ | hv₁
      · exfalso
        exact hvne (hinter₃₀ v hv₃' hv₀)
      · exact False.elim (hdisj₁₃ v hv₁ hv₃')
    · exact hinter₂₃ v hv₂ hv₃'
  let q := ListSpanningPath.append_of_support_inter q₀₁₂ q₃ hinter₀₁₂₃
  have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
  have hsupport :
      (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀) = S₀ ∪ S₁ ∪ S₂ ∪ S₃ := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Finset.mem_of_mem_erase hv)
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · by_cases hvu₀ : v = u₀
        · exact Or.inl <| by simpa [hvu₀, hu₀, Finset.mem_union, or_true]
        · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
  have hclose : Adj x u₀ := p₃.finalEdge_of_split middle₃ x htail₃
  have hsupport' :
      S₀ ∪ (S₁ ∪ (S₂ ∪ S₃.erase u₀)) = S₀ ∪ (S₁ ∪ (S₂ ∪ S₃)) := by
    simpa [Finset.union_assoc] using hsupport
  have q' : ListSpanningPath Adj (S₀ ∪ (S₁ ∪ (S₂ ∪ S₃.erase u₀))) u₀ x := by
    simpa [Finset.union_assoc] using q
  simpa [hsupport'] using
    (show HamiltonianOn (S₀ ∪ (S₁ ∪ (S₂ ∪ S₃.erase u₀))) Adj from
      hamiltonianOn_of_spanningPath q' hclose)

/--
Splice three spanning paths arranged cyclically into one Hamiltonian cycle.

This is the degenerate cyclic splice needed when the fourth side of the usual
cyclic-four package collapses to the initial vertex.
-/
theorem ListSpanningPath.hamiltonianOfCyclicThree
    {S₀ S₁ S₂ : Finset V} {u₀ u₁ u₂ x : V}
    (p₀ : ListSpanningPath Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath Adj S₂ u₂ u₀)
    (middle₂ : List V)
    (htail₂ : p₂.tail = middle₂ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₀ : ∀ v, v ∈ S₂ → v ∈ S₀ → v = u₀) :
    HamiltonianOn (S₀ ∪ S₁ ∪ S₂) Adj := by
  let q₀₁ := ListSpanningPath.append_of_support_inter p₀ p₁ hinter₀₁
  let q₂ := p₂.truncateFinish middle₂ x htail₂
  have hinter₀₁₂ :
      ∀ v, v ∈ (S₀ ∪ S₁) → v ∈ S₂.erase u₀ → v = u₂ := by
    intro v hv hv₂
    rcases Finset.mem_erase.mp hv₂ with ⟨hvne, hv₂'⟩
    rw [Finset.mem_union] at hv
    rcases hv with hv₀ | hv₁
    · exfalso
      exact hvne (hinter₂₀ v hv₂' hv₀)
    · exact hinter₁₂ v hv₁ hv₂'
  let q := ListSpanningPath.append_of_support_inter q₀₁ q₂ hinter₀₁₂
  have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
  have hsupport :
      (S₀ ∪ S₁) ∪ S₂.erase u₀ = S₀ ∪ S₁ ∪ S₂ := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Finset.mem_of_mem_erase hv)
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · by_cases hvu₀ : v = u₀
        · exact Or.inl <| by simpa [hvu₀, hu₀, Finset.mem_union, or_true]
        · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
  have hclose : Adj x u₀ := p₂.finalEdge_of_split middle₂ x htail₂
  have hsupport' :
      S₀ ∪ (S₁ ∪ S₂.erase u₀) = S₀ ∪ (S₁ ∪ S₂) := by
    simpa [Finset.union_assoc] using hsupport
  have q' : ListSpanningPath Adj (S₀ ∪ (S₁ ∪ S₂.erase u₀)) u₀ x := by
    simpa [Finset.union_assoc] using q
  simpa [hsupport'] using
    (show HamiltonianOn (S₀ ∪ (S₁ ∪ S₂.erase u₀)) Adj from
      hamiltonianOn_of_spanningPath q' hclose)

/--
The cyclic-three splice can be exposed as an explicit Hamiltonian-cycle witness
whose tail is the concatenation of the three path pieces, with the last path
truncated just before returning to `u₀`.
-/
theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicThree
    {S₀ S₁ S₂ : Finset V} {u₀ u₁ u₂ x : V}
    (p₀ : ListSpanningPath Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath Adj S₂ u₂ u₀)
    (middle₂ : List V)
    (htail₂ : p₂.tail = middle₂ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₀ : ∀ v, v ∈ S₂ → v ∈ S₀ → v = u₀) :
    ∃ w : HamiltonianCycleWitness (Adj := Adj) ((S₀ ∪ S₁) ∪ S₂.erase u₀),
      w.start = u₀ ∧
      w.tail = p₀.tail ++ p₁.tail ++ (middle₂ ++ [x]) := by
  let q₀₁ := ListSpanningPath.append_of_support_inter p₀ p₁ hinter₀₁
  let q₂ := p₂.truncateFinish middle₂ x htail₂
  have hinter₀₁₂ :
      ∀ v, v ∈ (S₀ ∪ S₁) → v ∈ S₂.erase u₀ → v = u₂ := by
    intro v hv hv₂
    rcases Finset.mem_erase.mp hv₂ with ⟨hvne, hv₂'⟩
    rw [Finset.mem_union] at hv
    rcases hv with hv₀ | hv₁
    · exfalso
      exact hvne (hinter₂₀ v hv₂' hv₀)
    · exact hinter₁₂ v hv₁ hv₂'
  let q := ListSpanningPath.append_of_support_inter q₀₁ q₂ hinter₀₁₂
  have hclose : Adj x u₀ := p₂.finalEdge_of_split middle₂ x htail₂
  let w : HamiltonianCycleWitness Adj ((S₀ ∪ S₁) ∪ S₂.erase u₀) :=
    hamiltonianCycleWitnessOfSpanningPath q hclose
  refine ⟨w, ?_, ?_⟩
  · rfl
  · change q₀₁.tail ++ q₂.tail = p₀.tail ++ p₁.tail ++ (middle₂ ++ [x])
    rw [show q₂.tail = middle₂ ++ [x] by rfl]
    simp [q₀₁, ListSpanningPath.append_of_support_inter,
      ListSpanningPath.append, List.append_assoc]

/--
If the first path in a cyclic-three splice already contains an ordered `P4`,
then the resulting Hamiltonian cycle witness contains the same `P4`.
-/
theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicThree_of_infix
    {G : SimpleGraph V}
    {S₀ S₁ S₂ : Finset V} {u₀ u₁ u₂ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₀)
    (middle₂ : List V)
    (htail₂ : p₂.tail = middle₂ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₀ : ∀ v, v ∈ S₂ → v ∈ S₀ → v = u₀)
    (hinfix₀ : [a, b, c, d] <:+: u₀ :: p₀.tail) :
    ∃ w : HamiltonianCycleWitness G.Adj ((S₀ ∪ S₁) ∪ S₂.erase u₀),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hwstart, hwtail⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicThree
      p₁ p₂ middle₂ htail₂ hinter₀₁ hinter₁₂ hinter₂₀
  refine ⟨w, ?_⟩
  rw [hwstart, hwtail]
  simpa [List.append_assoc] using
    (List.infix_append_right
      (n := p₁.tail ++ (middle₂ ++ [x, u₀]))
      hinfix₀)

/--
Variant of the cyclic-three splice where the ordered `P4` may straddle the first
two path pieces instead of lying entirely inside the first one.
-/
theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicThree_of_infix_firstTwo
    {G : SimpleGraph V}
    {S₀ S₁ S₂ : Finset V} {u₀ u₁ u₂ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₀)
    (middle₂ : List V)
    (htail₂ : p₂.tail = middle₂ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₀ : ∀ v, v ∈ S₂ → v ∈ S₀ → v = u₀)
    (hinfix₀₁ : [a, b, c, d] <:+: u₀ :: (p₀.tail ++ p₁.tail)) :
    ∃ w : HamiltonianCycleWitness G.Adj ((S₀ ∪ S₁) ∪ S₂.erase u₀),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hwstart, hwtail⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicThree
      p₁ p₂ middle₂ htail₂ hinter₀₁ hinter₁₂ hinter₂₀
  refine ⟨w, ?_⟩
  rw [hwstart, hwtail]
  simpa [List.append_assoc] using
    (List.infix_append_right
      (n := middle₂ ++ [x, u₀])
      hinfix₀₁)

/--
Variant of the cyclic-three splice where the ordered `P4` straddles the
wrap-around boundary between the last and first path pieces.
-/
theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicThree_of_infix_wrapAround
    {G : SimpleGraph V}
    [Fintype V]
    {S₀ S₁ S₂ : Finset V} {u₀ u₁ u₂ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₀)
    (middle₂ : List V)
    (htail₂ : p₂.tail = middle₂ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₀ : ∀ v, v ∈ S₂ → v ∈ S₀ → v = u₀)
    (hinfix₂₀ : [a, b, c, d] <:+: x :: (u₀ :: p₀.tail)) :
    ∃ w : HamiltonianCycleWitness G.Adj ((S₀ ∪ S₁) ∪ S₂.erase u₀),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hwstart, hwtail⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicThree
      p₁ p₂ middle₂ htail₂ hinter₀₁ hinter₁₂ hinter₂₀
  have hwtail' :
      w.tail = p₀.tail ++ p₁.tail ++ middle₂ ++ [x] := by
    simpa [List.append_assoc] using hwtail
  let w' :=
    w.rotateLast (p₀.tail ++ p₁.tail ++ middle₂) x hwtail'
  have hw'open :
      w'.start :: w'.tail =
        x :: (u₀ :: p₀.tail ++ p₁.tail ++ middle₂) := by
    dsimp [w']
    simpa [hwstart, List.append_assoc] using
      (HamiltonianCycleWitness.openList_rotateLast
        w (p₀.tail ++ p₁.tail ++ middle₂) x hwtail')
  refine ⟨w', ?_⟩
  rw [show w'.start :: (w'.tail ++ [w'.start]) = (w'.start :: w'.tail) ++ [w'.start] by rfl]
  rw [hw'open]
  simpa [List.append_assoc] using
    (List.infix_append_right (n := p₁.tail ++ middle₂ ++ [x]) hinfix₂₀)

theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicThree_of_infix_of_support_eq_univ
    {G : SimpleGraph V}
    [Fintype V]
    {S₀ S₁ S₂ : Finset V} {u₀ u₁ u₂ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₀)
    (middle₂ : List V)
    (htail₂ : p₂.tail = middle₂ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₀ : ∀ v, v ∈ S₂ → v ∈ S₀ → v = u₀)
    (hinfix₀ : [a, b, c, d] <:+: u₀ :: p₀.tail)
    (hcover : S₀ ∪ S₁ ∪ S₂ = (Finset.univ : Finset V)) :
    ∃ w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hinfix⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicThree_of_infix
      p₁ p₂ middle₂ htail₂ hinter₀₁ hinter₁₂ hinter₂₀ hinfix₀
  refine ⟨w.castSupport ?_, ?_⟩
  · calc
      ((S₀ ∪ S₁) ∪ S₂.erase u₀) = S₀ ∪ S₁ ∪ S₂ := by
        have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
        ext v
        constructor
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · exact Or.inr (Finset.mem_of_mem_erase hv)
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · by_cases hvu₀ : v = u₀
            · exact Or.inl <| by simpa [hvu₀, hu₀, Finset.mem_union, or_true]
            · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
      _ = (Finset.univ : Finset V) := hcover
  · simpa [HamiltonianCycleWitness.castSupport] using hinfix

theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicThree_of_infix_firstTwo_of_support_eq_univ
    {G : SimpleGraph V}
    [Fintype V]
    {S₀ S₁ S₂ : Finset V} {u₀ u₁ u₂ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₀)
    (middle₂ : List V)
    (htail₂ : p₂.tail = middle₂ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₀ : ∀ v, v ∈ S₂ → v ∈ S₀ → v = u₀)
    (hinfix₀₁ : [a, b, c, d] <:+: u₀ :: (p₀.tail ++ p₁.tail))
    (hcover : S₀ ∪ S₁ ∪ S₂ = (Finset.univ : Finset V)) :
    ∃ w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hinfix⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicThree_of_infix_firstTwo
      p₁ p₂ middle₂ htail₂ hinter₀₁ hinter₁₂ hinter₂₀ hinfix₀₁
  refine ⟨w.castSupport ?_, ?_⟩
  · calc
      ((S₀ ∪ S₁) ∪ S₂.erase u₀) = S₀ ∪ S₁ ∪ S₂ := by
        have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
        ext v
        constructor
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · exact Or.inr (Finset.mem_of_mem_erase hv)
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · by_cases hvu₀ : v = u₀
            · exact Or.inl <| by simpa [hvu₀, hu₀, Finset.mem_union, or_true]
            · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
      _ = (Finset.univ : Finset V) := hcover
  · simpa [HamiltonianCycleWitness.castSupport] using hinfix

theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicThree_of_infix_wrapAround_of_support_eq_univ
    {G : SimpleGraph V}
    [Fintype V]
    {S₀ S₁ S₂ : Finset V} {u₀ u₁ u₂ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₀)
    (middle₂ : List V)
    (htail₂ : p₂.tail = middle₂ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₀ : ∀ v, v ∈ S₂ → v ∈ S₀ → v = u₀)
    (hinfix₂₀ : [a, b, c, d] <:+: x :: (u₀ :: p₀.tail))
    (hcover : S₀ ∪ S₁ ∪ S₂ = (Finset.univ : Finset V)) :
    ∃ w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hinfix⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicThree_of_infix_wrapAround
      p₁ p₂ middle₂ htail₂ hinter₀₁ hinter₁₂ hinter₂₀ hinfix₂₀
  refine ⟨w.castSupport ?_, ?_⟩
  · calc
      ((S₀ ∪ S₁) ∪ S₂.erase u₀) = S₀ ∪ S₁ ∪ S₂ := by
        have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
        ext v
        constructor
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · exact Or.inr (Finset.mem_of_mem_erase hv)
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · by_cases hvu₀ : v = u₀
            · exact Or.inl <| by simpa [hvu₀, hu₀, Finset.mem_union, or_true]
            · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
      _ = (Finset.univ : Finset V) := hcover
  · simpa [HamiltonianCycleWitness.castSupport] using hinfix

/--
The cyclic-four splice can be exposed as an explicit Hamiltonian-cycle witness
whose tail is the concatenation of the four path pieces, with the last path
truncated just before returning to `u₀`.
-/
theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicFour
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x : V}
    (p₀ : ListSpanningPath Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False) :
    ∃ w : HamiltonianCycleWitness (Adj := Adj) (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀),
      w.start = u₀ ∧
      w.tail = p₀.tail ++ p₁.tail ++ p₂.tail ++ (middle₃ ++ [x]) := by
  let q₀₁ := ListSpanningPath.append_of_support_inter p₀ p₁ hinter₀₁
  let q₀₁₂ :=
    ListSpanningPath.append_of_support_inter q₀₁ p₂ (by
      intro v hv hv₂
      rw [Finset.mem_union] at hv
      rcases hv with hv₀ | hv₁
      · exact False.elim (hdisj₀₂ v hv₀ hv₂)
      · exact hinter₁₂ v hv₁ hv₂)
  let q₃ := p₃.truncateFinish middle₃ x htail₃
  have hinter₀₁₂₃ :
      ∀ v, v ∈ ((S₀ ∪ S₁) ∪ S₂) → v ∈ S₃.erase u₀ → v = u₃ := by
    intro v hv hv₃
    rcases Finset.mem_erase.mp hv₃ with ⟨hvne, hv₃'⟩
    rw [Finset.mem_union] at hv
    rcases hv with hv₀₁ | hv₂
    · rw [Finset.mem_union] at hv₀₁
      rcases hv₀₁ with hv₀ | hv₁
      · exfalso
        exact hvne (hinter₃₀ v hv₃' hv₀)
      · exact False.elim (hdisj₁₃ v hv₁ hv₃')
    · exact hinter₂₃ v hv₂ hv₃'
  let q := ListSpanningPath.append_of_support_inter q₀₁₂ q₃ hinter₀₁₂₃
  have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
  have hsupport :
      (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀) = S₀ ∪ S₁ ∪ S₂ ∪ S₃ := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Finset.mem_of_mem_erase hv)
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · by_cases hvu₀ : v = u₀
        · exact Or.inl <| by simpa [hvu₀, hu₀, Finset.mem_union, or_true]
        · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
  have hclose : Adj x u₀ := p₃.finalEdge_of_split middle₃ x htail₃
  let w : HamiltonianCycleWitness Adj (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀) :=
    hamiltonianCycleWitnessOfSpanningPath q hclose
  refine ⟨w, ?_, ?_⟩
  · rfl
  · change q₀₁₂.tail ++ q₃.tail = p₀.tail ++ p₁.tail ++ p₂.tail ++ (middle₃ ++ [x])
    rw [show q₃.tail = middle₃ ++ [x] by rfl]
    simp [q₀₁₂, q₀₁, ListSpanningPath.append_of_support_inter,
      ListSpanningPath.append, List.append_assoc]

/--
If the first path in a cyclic-four splice already contains an ordered `P4`,
then the resulting Hamiltonian cycle witness contains the same `P4`.
-/
theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix
    {G : SimpleGraph V}
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath G.Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False)
    (hinfix₀ : [a, b, c, d] <:+: u₀ :: p₀.tail) :
    ∃ w : HamiltonianCycleWitness G.Adj (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hwstart, hwtail⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicFour
      p₁ p₂ p₃ middle₃ htail₃
      hinter₀₁ hinter₁₂ hinter₂₃ hinter₃₀ hdisj₀₂ hdisj₁₃
  refine ⟨w, ?_⟩
  rw [hwstart, hwtail]
  simpa [List.append_assoc] using
    (List.infix_append_right
      (n := p₁.tail ++ p₂.tail ++ (middle₃ ++ [x, u₀]))
      hinfix₀)

/--
Variant of the cyclic-four splice where the ordered `P4` may straddle the first
two path pieces instead of lying entirely inside the first one.
-/
theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_firstTwo
    {G : SimpleGraph V}
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath G.Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False)
    (hinfix₀₁ : [a, b, c, d] <:+: u₀ :: (p₀.tail ++ p₁.tail)) :
    ∃ w : HamiltonianCycleWitness G.Adj (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hwstart, hwtail⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicFour
      p₁ p₂ p₃ middle₃ htail₃
      hinter₀₁ hinter₁₂ hinter₂₃ hinter₃₀ hdisj₀₂ hdisj₁₃
  refine ⟨w, ?_⟩
  rw [hwstart, hwtail]
  simpa [List.append_assoc] using
    (List.infix_append_right
      (n := p₂.tail ++ (middle₃ ++ [x, u₀]))
      hinfix₀₁)

/--
Variant of the cyclic-four splice where the ordered `P4` straddles the
wrap-around boundary between the last and first path pieces.
-/
theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_wrapAround
    {G : SimpleGraph V}
    [Fintype V]
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath G.Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False)
    (hinfix₃₀ : [a, b, c, d] <:+: x :: (u₀ :: p₀.tail)) :
    ∃ w : HamiltonianCycleWitness G.Adj (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hwstart, hwtail⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicFour
      p₁ p₂ p₃ middle₃ htail₃
      hinter₀₁ hinter₁₂ hinter₂₃ hinter₃₀ hdisj₀₂ hdisj₁₃
  have hwtail' :
      w.tail = p₀.tail ++ p₁.tail ++ p₂.tail ++ middle₃ ++ [x] := by
    simpa [List.append_assoc] using hwtail
  let w' :=
    w.rotateLast (p₀.tail ++ p₁.tail ++ p₂.tail ++ middle₃) x hwtail'
  have hw'open :
      w'.start :: w'.tail =
        x :: (u₀ :: p₀.tail ++ p₁.tail ++ p₂.tail ++ middle₃) := by
    dsimp [w']
    simpa [hwstart, List.append_assoc] using
      (HamiltonianCycleWitness.openList_rotateLast
        w (p₀.tail ++ p₁.tail ++ p₂.tail ++ middle₃) x hwtail')
  refine ⟨w', ?_⟩
  rw [show w'.start :: (w'.tail ++ [w'.start]) = (w'.start :: w'.tail) ++ [w'.start] by rfl]
  rw [hw'open]
  simpa [List.append_assoc] using
    (List.infix_append_right (n := p₁.tail ++ p₂.tail ++ middle₃ ++ [x]) hinfix₃₀)

theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_of_support_eq_univ
    {G : SimpleGraph V}
    [Fintype V]
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath G.Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False)
    (hinfix₀ : [a, b, c, d] <:+: u₀ :: p₀.tail)
    (hcover : S₀ ∪ S₁ ∪ S₂ ∪ S₃ = (Finset.univ : Finset V)) :
    ∃ w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hinfix⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix
      p₁ p₂ p₃ middle₃ htail₃
      hinter₀₁ hinter₁₂ hinter₂₃ hinter₃₀ hdisj₀₂ hdisj₁₃ hinfix₀
  refine ⟨w.castSupport ?_, ?_⟩
  · calc
      (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀) = S₀ ∪ S₁ ∪ S₂ ∪ S₃ := by
        have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
        ext v
        constructor
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · exact Or.inr (Finset.mem_of_mem_erase hv)
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · by_cases hvu₀ : v = u₀
            · exact Or.inl <| by simpa [hvu₀, hu₀, Finset.mem_union, or_true]
            · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
      _ = (Finset.univ : Finset V) := hcover
  · simpa [HamiltonianCycleWitness.castSupport] using hinfix

theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_firstTwo_of_support_eq_univ
    {G : SimpleGraph V}
    [Fintype V]
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath G.Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False)
    (hinfix₀₁ : [a, b, c, d] <:+: u₀ :: (p₀.tail ++ p₁.tail))
    (hcover : S₀ ∪ S₁ ∪ S₂ ∪ S₃ = (Finset.univ : Finset V)) :
    ∃ w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hinfix⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_firstTwo
      p₁ p₂ p₃ middle₃ htail₃
      hinter₀₁ hinter₁₂ hinter₂₃ hinter₃₀ hdisj₀₂ hdisj₁₃ hinfix₀₁
  refine ⟨w.castSupport ?_, ?_⟩
  · calc
      (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀) = S₀ ∪ S₁ ∪ S₂ ∪ S₃ := by
        have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
        ext v
        constructor
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · exact Or.inr (Finset.mem_of_mem_erase hv)
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · by_cases hvu₀ : v = u₀
            · exact Or.inl <| by simpa [hvu₀, hu₀, Finset.mem_union, or_true]
            · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
      _ = (Finset.univ : Finset V) := hcover
  · simpa [HamiltonianCycleWitness.castSupport] using hinfix

theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_wrapAround_of_support_eq_univ
    {G : SimpleGraph V}
    [Fintype V]
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath G.Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False)
    (hinfix₃₀ : [a, b, c, d] <:+: x :: (u₀ :: p₀.tail))
    (hcover : S₀ ∪ S₁ ∪ S₂ ∪ S₃ = (Finset.univ : Finset V)) :
    ∃ w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hinfix⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_wrapAround
      p₁ p₂ p₃ middle₃ htail₃
      hinter₀₁ hinter₁₂ hinter₂₃ hinter₃₀ hdisj₀₂ hdisj₁₃ hinfix₃₀
  refine ⟨w.castSupport ?_, ?_⟩
  · calc
      (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀) = S₀ ∪ S₁ ∪ S₂ ∪ S₃ := by
        have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
        ext v
        constructor
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · exact Or.inr (Finset.mem_of_mem_erase hv)
        · intro hv
          rw [Finset.mem_union] at hv ⊢
          rcases hv with hv | hv
          · exact Or.inl hv
          · by_cases hvu₀ : v = u₀
            · exact Or.inl <| by simpa [hvu₀, hu₀, Finset.mem_union, or_true]
            · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv⟩)
      _ = (Finset.univ : Finset V) := hcover
  · simpa [HamiltonianCycleWitness.castSupport] using hinfix

/--
Variant of the cyclic-four splice where the ordered `P4` may straddle the last
two path pieces instead of lying in the first piece.
-/
theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_lastTwo
    {G : SimpleGraph V}
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath G.Adj S₃ u₃ u₀)
    (middle₁ : List V)
    (htail₁ : p₁.tail = middle₁ ++ [x, u₂])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False)
    (hinfix₂₃ : [a, b, c, d] <:+: u₂ :: (p₂.tail ++ p₃.tail)) :
    ∃ w : HamiltonianCycleWitness G.Adj (((S₂ ∪ S₃) ∪ S₀) ∪ S₁.erase u₂),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  exact
    p₂.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_firstTwo
      p₃ p₀ p₁ middle₁ htail₁
      hinter₂₃ hinter₃₀ hinter₀₁ hinter₁₂
      (by
        intro v hv₂ hv₀
        exact hdisj₀₂ v hv₀ hv₂)
      (by
        intro v hv₃ hv₁
        exact hdisj₁₃ v hv₁ hv₃)
      hinfix₂₃

theorem ListSpanningPath.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_lastTwo_of_support_eq_univ
    {G : SimpleGraph V}
    [Fintype V]
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x a b c d : V}
    (p₀ : ListSpanningPath G.Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath G.Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath G.Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath G.Adj S₃ u₃ u₀)
    (middle₁ : List V)
    (htail₁ : p₁.tail = middle₁ ++ [x, u₂])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False)
    (hinfix₂₃ : [a, b, c, d] <:+: u₂ :: (p₂.tail ++ p₃.tail))
    (hcover : S₀ ∪ S₁ ∪ S₂ ∪ S₃ = (Finset.univ : Finset V)) :
    ∃ w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      [a, b, c, d] <:+: w.start :: (w.tail ++ [w.start]) := by
  obtain ⟨w, hinfix⟩ :=
    p₀.exists_hamiltonianCycleWitnessOfCyclicFour_of_infix_lastTwo
      p₁ p₂ p₃ middle₁ htail₁
      hinter₀₁ hinter₁₂ hinter₂₃ hinter₃₀
      hdisj₀₂ hdisj₁₃ hinfix₂₃
  refine ⟨w.castSupport ?_, ?_⟩
  · calc
      (((S₂ ∪ S₃) ∪ S₀) ∪ S₁.erase u₂) = S₂ ∪ S₃ ∪ S₀ ∪ S₁ := by
        have hu₂ : u₂ ∈ S₂ := (p₂.spans u₂).2 (by simp)
        ext v
        by_cases hvu₂ : v = u₂
        · subst hvu₂
          simp [hu₂, Finset.mem_erase, or_assoc, or_left_comm, or_comm]
        · simp [Finset.mem_erase, hvu₂, or_assoc, or_left_comm, or_comm]
      _ = (Finset.univ : Finset V) := by
        simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hcover
  · simpa [HamiltonianCycleWitness.castSupport] using hinfix

/--
Splice four boundary-path witnesses arranged cyclically into one Hamiltonian
cycle.

This packages the list-level cycle-splicing pattern needed for the cubic-trisum
argument: the last boundary witness is truncated just before returning to the
initial vertex, and its final edge supplies the closing edge of the global
Hamiltonian cycle.
-/
theorem OrderedSegmentFamily.BoundaryCycleWitness.hamiltonianOfCyclicFour
    {S₀ S₁ S₂ S₃ : Finset V} {u₀ u₁ u₂ u₃ x : V}
    (p₀ : OrderedSegmentFamily.BoundaryCycleWitness Adj S₀ u₀ u₁)
    (p₁ : OrderedSegmentFamily.BoundaryCycleWitness Adj S₁ u₁ u₂)
    (p₂ : OrderedSegmentFamily.BoundaryCycleWitness Adj S₂ u₂ u₃)
    (p₃ : OrderedSegmentFamily.BoundaryCycleWitness Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (hmid₃ : p₃.middle = middle₃ ++ [x])
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False) :
    HamiltonianOn (S₀ ∪ S₁ ∪ S₂ ∪ S₃) Adj := by
  let q₀₁ :=
    ListSpanningPath.append_of_support_inter p₀.toSpanningPath p₁.toSpanningPath hinter₀₁
  let q₀₁₂ :=
    ListSpanningPath.append_of_support_inter q₀₁ p₂.toSpanningPath (by
      intro v hv hv₂
      rw [Finset.mem_union] at hv
      rcases hv with hv₀ | hv₁
      · exact False.elim (hdisj₀₂ v hv₀ hv₂)
      · exact hinter₁₂ v hv₁ hv₂)
  let q₃ := p₃.truncateFinish middle₃ x hmid₃
  have hinter₀₁₂₃ :
      ∀ v, v ∈ ((S₀ ∪ S₁) ∪ S₂) → v ∈ S₃.erase u₀ → v = u₃ := by
    intro v hv hv₃
    rcases Finset.mem_erase.mp hv₃ with ⟨hvne, hv₃'⟩
    rw [Finset.mem_union] at hv
    rcases hv with hv₀₁ | hv₂
    · rw [Finset.mem_union] at hv₀₁
      rcases hv₀₁ with hv₀ | hv₁
      · exfalso
        exact hvne (hinter₃₀ v hv₃' hv₀)
      · exact False.elim (hdisj₁₃ v hv₁ hv₃')
    · exact hinter₂₃ v hv₂ hv₃'
  let q :=
    ListSpanningPath.append_of_support_inter q₀₁₂ q₃ hinter₀₁₂₃
  have hu₀ : u₀ ∈ S₀ := (p₀.spans u₀).2 (by simp)
  have hsupport :
      (((S₀ ∪ S₁) ∪ S₂) ∪ S₃.erase u₀) = S₀ ∪ S₁ ∪ S₂ ∪ S₃ := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Finset.mem_erase.mp hv).2
    · intro hv
      rw [Finset.mem_union] at hv ⊢
      rcases hv with hv | hv₃
      · exact Or.inl hv
      · by_cases hvu₀ : v = u₀
        · subst v
          exact Or.inl (by simp [Finset.mem_union, hu₀])
        · exact Or.inr (Finset.mem_erase.mpr ⟨hvu₀, hv₃⟩)
  have hclose : Adj x u₀ :=
    p₃.closingEdge_of_split middle₃ x hmid₃
  convert (hamiltonianOn_of_spanningPath q hclose) using 1
  simpa [q, Finset.union_assoc] using hsupport.symm

/--
One-step nonterminal Hamiltonicity: an explicit move-step witness plus the
closing edge already gives a Hamiltonian cycle on the parent support.
-/
theorem OrderedSegmentFamily.hamiltonianOfMoveStep
    {support : Finset V} {s t : V}
    (step : OrderedSegmentFamily.MoveStepData Adj support s t)
    (hclose : Adj t s) :
    HamiltonianOn support Adj :=
  hamiltonianOn_of_spanningPath
    (OrderedSegmentFamily.spanningPathOfMoveStep step) hclose

/--
One-step Hamiltonicity corollary for the cyclic-four move package. The closing
edge is the final edge of the fourth path before it returns to `u₀`.
-/
theorem OrderedSegmentFamily.hamiltonianOn_of_cyclicFourPathMove
    {S₀ S₁ S₂ S₃ parentSupport : Finset V} {u₀ u₁ u₂ u₃ x : V}
    (p₀ : ListSpanningPath Adj S₀ u₀ u₁)
    (p₁ : ListSpanningPath Adj S₁ u₁ u₂)
    (p₂ : ListSpanningPath Adj S₂ u₂ u₃)
    (p₃ : ListSpanningPath Adj S₃ u₃ u₀)
    (middle₃ : List V)
    (htail₃ : p₃.tail = middle₃ ++ [x, u₀])
    (hsupport : S₀ ∪ S₁ ∪ S₂ ∪ S₃ = parentSupport)
    (hinter₀₁ : ∀ v, v ∈ S₀ → v ∈ S₁ → v = u₁)
    (hinter₁₂ : ∀ v, v ∈ S₁ → v ∈ S₂ → v = u₂)
    (hinter₂₃ : ∀ v, v ∈ S₂ → v ∈ S₃ → v = u₃)
    (hinter₃₀ : ∀ v, v ∈ S₃ → v ∈ S₀ → v = u₀)
    (hdisj₀₂ : ∀ v, v ∈ S₀ → v ∈ S₂ → False)
    (hdisj₁₃ : ∀ v, v ∈ S₁ → v ∈ S₃ → False) :
    HamiltonianOn parentSupport Adj :=
  OrderedSegmentFamily.hamiltonianOfMoveStep
    (OrderedSegmentFamily.moveStepDataOfCyclicFourPaths
      p₀ p₁ p₂ p₃ middle₃ htail₃ hsupport
      hinter₀₁ hinter₁₂ hinter₂₃ hinter₃₀ hdisj₀₂ hdisj₁₃)
    (p₃.finalEdge_of_split middle₃ x htail₃)

/--
Local geometric move data can be used directly to close the parent spanning
path into a Hamiltonian cycle.
-/
theorem OrderedSegmentFamily.hamiltonianOfLocalMove
    {support : Finset V} {s t : V}
    (step : OrderedSegmentFamily.LocalMoveData Adj support s t)
    (hclose : Adj t s) :
    HamiltonianOn support Adj :=
  OrderedSegmentFamily.hamiltonianOfMoveStep
    (OrderedSegmentFamily.moveStepDataOfLocalMove step) hclose

/--
Depth-1 decomposition theorem: if a parent cell splits into an ordered chain of
terminal child cells, then the parent is Hamiltonian once the closing edge survives.
-/
theorem OrderedSegmentFamily.TerminalMoveData.hamiltonianOfClosingEdge
    {support : Finset V} {s t : V}
    (step : OrderedSegmentFamily.TerminalMoveData Adj support s t)
    (hclose : Adj t s) :
    HamiltonianOn support Adj :=
  OrderedSegmentFamily.hamiltonianOfLocalMove step.toLocalMoveData hclose

/--
Manuscript-style terminal chain theorem: an ordered list of terminal child cells
satisfying the SP3 intersection pattern already yields a Hamiltonian cycle on
the parent support once the closing edge survives.
-/
theorem OrderedSegmentFamily.hamiltonianOfTerminalChain
    {support : Finset V} {s t : V}
    (head : OrderedSegmentFamily.TerminalPiece Adj)
    (tail : List (OrderedSegmentFamily.TerminalPiece Adj))
    (hstart : head.start = s)
    (hsupport :
      PathSegment.supportUnion
        (head.toPathSegment :: tail.map OrderedSegmentFamily.TerminalPiece.toPathSegment) =
          support)
    (hlink :
      OrderedSegmentFamily.LinkedAllSplits
        (head.toPathSegment :: tail.map OrderedSegmentFamily.TerminalPiece.toPathSegment))
    (hconsecutive :
      ∀ xs p q qs,
        head.toPathSegment :: tail.map OrderedSegmentFamily.TerminalPiece.toPathSegment =
          xs ++ p :: q :: qs →
        ∀ v, v ∈ p.support → v ∈ q.support → v = p.finish)
    (hnonconsecutive :
      ∀ xs p ms q ys,
        head.toPathSegment :: tail.map OrderedSegmentFamily.TerminalPiece.toPathSegment =
          xs ++ p :: ms ++ q :: ys →
        ms ≠ [] →
        ∀ v, v ∈ p.support → v ∈ q.support → False)
    (hlast :
      (OrderedSegmentFamily.lastSegment head.toPathSegment
        (tail.map OrderedSegmentFamily.TerminalPiece.toPathSegment)).finish = t)
    (hclose : Adj t s) :
    HamiltonianOn support Adj := by
  let step : OrderedSegmentFamily.TerminalMoveData Adj support s t :=
    { head := head
      tail := tail
      head_start := hstart
      support_union := hsupport
      linked := hlink
      consecutive_overlap := hconsecutive
      nonconsecutive_disjoint := hnonconsecutive
      last_finish := hlast }
  exact step.hamiltonianOfClosingEdge hclose

/--
Brick/brace-flavored local data also closes directly to a Hamiltonian cycle.
-/
theorem OrderedSegmentFamily.BrickBrace.hamiltonianOfMoveData
    {support : Finset V} {s t : V}
    (step : OrderedSegmentFamily.BrickBrace.MoveData Adj support s t)
    (hclose : Adj t s) :
    HamiltonianOn support Adj :=
  hamiltonianOn_of_spanningPath
    (OrderedSegmentFamily.BrickBrace.spanningPathOfMoveData step) hclose

end LocalHamiltonianTargets

end SpanningCycle
