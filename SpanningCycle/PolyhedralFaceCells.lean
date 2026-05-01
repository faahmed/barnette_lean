import SpanningCycle.GraphClasses

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Polyhedral face cells

Concrete bridges from polyhedral face/cell data to the abstract cell-system and
move-package interfaces.
-/

namespace SpanningCycle

universe u v

section PolyhedralFaceCells

open SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace FaceBoundary

/--
A concrete cyclic presentation of a face boundary.

The presentation chooses the boundary start `s`, the vertex `t` immediately
before the deleted closing edge, and the opened middle list. The equality says
that the embedding's recorded cyclic boundary is exactly
`s :: middle ++ [t, s]`.
-/
structure CyclicPresentation (F : FaceBoundary G) where
  s : V
  t : V
  middle : List V
  vertices_eq : F.vertices = s :: (middle ++ [t, s])

namespace CyclicPresentation

/-- A cyclic presentation gives the terminal boundary witness for its face. -/
def toBoundaryCycleWitness
    {F : FaceBoundary G}
    (presentation : CyclicPresentation F) :
    OrderedSegmentFamily.BoundaryCycleWitness
      G.Adj (F.vertices.toFinset) presentation.s presentation.t :=
  F.toBoundaryCycleWitnessOfSupport
    presentation.middle presentation.vertices_eq

@[simp] theorem toBoundaryCycleWitness_middle
    {F : FaceBoundary G}
    (presentation : CyclicPresentation F) :
    presentation.toBoundaryCycleWitness.middle = presentation.middle := rfl

end CyclicPresentation

/--
Every recorded face boundary admits a cyclic presentation.

The presentation starts at the boundary walk base and deletes the final edge
returning to that base.
-/
theorem nonempty_cyclicPresentation (F : FaceBoundary G) :
    Nonempty (CyclicPresentation F) := by
  classical
  let tail : List V := F.walk.support.tail
  have hwalk_nonempty : ¬ F.walk.Nil := F.isCycle.not_nil
  have htail_ne : tail ≠ [] := by
    have htail_support :
        F.walk.tail.support = F.walk.support.tail :=
      F.walk.support_tail_of_not_nil hwalk_nonempty
    have hsupport_ne : F.walk.tail.support ≠ [] :=
      SimpleGraph.Walk.support_ne_nil F.walk.tail
    simpa [tail, ← htail_support] using hsupport_ne
  have hsupport_cons : F.walk.support = F.base :: tail := by
    simpa [tail] using F.walk.support_eq_cons
  rcases List.eq_nil_or_concat' tail with htail_empty | ⟨init, last, htail_eq⟩
  · exact False.elim (htail_ne htail_empty)
  have hsupport : F.walk.support = F.base :: (init ++ [last]) := by
    rw [hsupport_cons, htail_eq]
  have hlast_eq : last = F.base := by
    have hget :
        (F.base :: (init ++ [last])).getLast (by simp) = F.base := by
      simpa [hsupport] using F.walk.getLast_support
    simpa using hget
  rcases List.eq_nil_or_concat' init with hinit_empty | ⟨middle, t, hinit_eq⟩
  · have hsupport_length : F.walk.support.length = 2 := by
      simp [hsupport, hinit_empty]
    have hwalk_length : F.walk.length = 1 := by
      have hlen := F.walk.length_support
      omega
    have hadj_self : G.Adj F.base F.base :=
      SimpleGraph.Walk.adj_of_length_eq_one hwalk_length
    exact False.elim (G.irrefl hadj_self)
  · refine
      ⟨{ s := F.base,
          t := t,
          middle := middle,
          vertices_eq := ?_ }⟩
    simp [FaceBoundary.vertices, hsupport, hlast_eq, hinit_eq, List.append_assoc]

/-- A canonical cyclic presentation, chosen from the stored boundary cycle. -/
noncomputable def cyclicPresentation (F : FaceBoundary G) :
    CyclicPresentation F :=
  Classical.choice (nonempty_cyclicPresentation F)

end FaceBoundary

namespace PolyhedralEmbedding

/-- Face equality is decidable for the finite face type, used in finite-set splits. -/
noncomputable instance faceDecidableEq (P : PolyhedralEmbedding G) :
    DecidableEq P.Face :=
  Classical.decEq _

/-- The finite support of a face boundary, extracted from its boundary walk. -/
def faceSupport (P : PolyhedralEmbedding G) (f : P.Face) : Finset V :=
  (P.boundary f).vertices.toFinset

/--
Cyclic boundary presentations for every face of a polyhedral embedding.

This is the graph-level data needed to build `FacePathDatum`: each face gets a
chosen opened boundary path plus its deleted closing edge.
-/
structure FaceBoundaryPresentations (P : PolyhedralEmbedding G) where
  presentation :
    ∀ f : P.Face, FaceBoundary.CyclicPresentation (P.boundary f)

/-- Canonical cyclic boundary presentations induced by the stored face walks. -/
noncomputable def faceBoundaryPresentations
    (P : PolyhedralEmbedding G) :
    FaceBoundaryPresentations P where
  presentation := fun f => (P.boundary f).cyclicPresentation

namespace FaceBoundaryPresentations

variable {P : PolyhedralEmbedding G}

/-- The chosen start vertex of a face boundary presentation. -/
def s (presentations : FaceBoundaryPresentations P) (f : P.Face) : V :=
  (presentations.presentation f).s

/-- The chosen final vertex before the deleted closing edge. -/
def t (presentations : FaceBoundaryPresentations P) (f : P.Face) : V :=
  (presentations.presentation f).t

/-- The opened middle list between the chosen face endpoints. -/
def middle (presentations : FaceBoundaryPresentations P) (f : P.Face) : List V :=
  (presentations.presentation f).middle

/-- The recorded boundary list for each face matches its cyclic presentation. -/
theorem vertices_eq
    (presentations : FaceBoundaryPresentations P)
    (f : P.Face) :
    (P.boundary f).vertices =
      presentations.s f ::
        (presentations.middle f ++ [presentations.t f, presentations.s f]) :=
  (presentations.presentation f).vertices_eq

end FaceBoundaryPresentations

/-- A polyhedral cell modeled as a finite union of faces. -/
structure Cell (P : PolyhedralEmbedding G) where
  faces : Finset P.Face

namespace Cell

variable (P : PolyhedralEmbedding G)

noncomputable instance : DecidableEq (Cell P) := Classical.decEq _

/-- The finite support of a cell is the union of the supports of its faces. -/
def support (c : Cell P) : Finset V := by
  classical
  exact c.faces.biUnion P.faceSupport

/-- The root cell containing all faces. -/
def full : Cell P :=
  { faces := Finset.univ }

/-- The empty face-set cell. This is not part of the intended recursive universe. -/
def empty : Cell P :=
  { faces := ∅ }

/-- The cell consisting of one face. -/
def singleton (f : P.Face) : Cell P :=
  { faces := {f} }

/-- The cell containing all faces has full vertex support. -/
theorem support_univ_faces :
    ({ faces := Finset.univ } : Cell P).support P = (Finset.univ : Finset V) := by
  classical
  ext v
  constructor
  · intro _hv
    exact Finset.mem_univ v
  · intro _hv
    rcases P.vertex_covered v with ⟨f, hf⟩
    simpa [support, faceSupport] using ⟨f, hf⟩

@[simp] theorem support_full :
    (full P).support P = (Finset.univ : Finset V) :=
  support_univ_faces P

@[simp] theorem support_singleton (f : P.Face) :
    (singleton P f).support P = P.faceSupport f := by
  classical
  ext v
  simp [singleton, support]

/-- Default recursive rank: the number of faces in a cell. -/
def faceRank (c : Cell P) : Nat :=
  c.faces.card

/-- A terminal cell for the default recursive construction is a singleton face. -/
def IsSingletonFace (c : Cell P) : Prop :=
  ∃ f : P.Face, c = singleton P f

/-- Singleton cells are terminal for the default recursive construction. -/
@[simp] theorem isSingletonFace_singleton (f : P.Face) :
    IsSingletonFace P (singleton P f) :=
  ⟨f, rfl⟩

/-- Singleton face cells determine their face. -/
theorem singleton_injective :
    Function.Injective (singleton P) := by
  intro f g h
  have hfaces := congrArg Cell.faces h
  simpa [singleton] using hfaces

/-- The empty face-set cell is not a singleton face. -/
theorem not_isSingletonFace_empty :
    ¬ IsSingletonFace P (empty P) := by
  intro h
  rcases h with ⟨f, hf⟩
  have hfaces := congrArg Cell.faces hf
  simpa [empty, singleton] using hfaces

/-- The face contained in a terminal singleton cell. -/
noncomputable def singletonFace
    (c : Cell P)
    (h : IsSingletonFace P c) : P.Face :=
  Classical.choose h

/-- A terminal singleton cell is exactly the singleton over its chosen face. -/
theorem eq_singleton_singletonFace
    (c : Cell P)
    (h : IsSingletonFace P c) :
    c = singleton P (singletonFace P c h) :=
  Classical.choose_spec h

/-- If a terminal cell is known to be a concrete singleton, its chosen face is that face. -/
theorem singletonFace_eq_of_eq_singleton
    {c : Cell P}
    (h : IsSingletonFace P c)
    {f : P.Face}
    (hc : c = singleton P f) :
    singletonFace P c h = f :=
  singleton_injective P ((eq_singleton_singletonFace P c h).symm.trans hc)

@[simp] theorem singletonFace_singleton
    (f : P.Face)
    (h : IsSingletonFace P (singleton P f)) :
    singletonFace P (singleton P f) h = f :=
  singletonFace_eq_of_eq_singleton P h rfl

/-- If the graph has an edge, the all-faces cell is not a singleton face. -/
theorem singleton_ne_full_of_adj
    {a b : V}
    (hab : G.Adj a b)
    (f : P.Face) :
    singleton P f ≠ full P := by
  intro h
  rcases P.edge_covered_twice hab with
    ⟨f₁, f₂, hne, _hf₁, _hf₂, _hcover⟩
  have hfaces : ({f} : Finset P.Face) = Finset.univ := by
    simpa [singleton, full] using congrArg Cell.faces h
  have hf₁ : f₁ ∈ ({f} : Finset P.Face) := by
    rw [hfaces]
    exact Finset.mem_univ f₁
  have hf₂ : f₂ ∈ ({f} : Finset P.Face) := by
    rw [hfaces]
    exact Finset.mem_univ f₂
  have hf₁_eq : f₁ = f := by
    simpa using hf₁
  have hf₂_eq : f₂ = f := by
    simpa using hf₂
  exact hne (hf₁_eq.trans hf₂_eq.symm)

theorem full_ne_singleton_of_adj
    {a b : V}
    (hab : G.Adj a b)
    (f : P.Face) :
    full P ≠ singleton P f := by
  intro h
  exact singleton_ne_full_of_adj P hab f h.symm

@[simp] theorem faceRank_singleton (f : P.Face) :
    faceRank P (singleton P f) = 1 := by
  simp [faceRank, singleton]

/-- Proper inclusion of face sets gives the default rank decrease. -/
theorem faceRank_lt_of_faces_ssubset
    {child parent : Cell P}
    (hfaces : child.faces ⊂ parent.faces) :
    faceRank P child < faceRank P parent := by
  simpa [faceRank] using Finset.card_lt_card hfaces

/-- If two child face sets cover the parent face set, their supports cover the parent support. -/
theorem support_union_of_faces_cover
    {left right parent : Cell P}
    (hfaces : ∀ f, f ∈ parent.faces ↔ f ∈ left.faces ∨ f ∈ right.faces) :
    left.support P ∪ right.support P = parent.support P := by
  classical
  ext v
  constructor
  · intro hv
    simp [support] at hv ⊢
    rcases hv with ⟨f, hf, hvf⟩ | ⟨f, hf, hvf⟩
    · exact ⟨f, (hfaces f).2 (Or.inl hf), hvf⟩
    · exact ⟨f, (hfaces f).2 (Or.inr hf), hvf⟩
  · intro hv
    simp [support] at hv ⊢
    rcases hv with ⟨f, hf, hvf⟩
    rcases (hfaces f).1 hf with hfLeft | hfRight
    · exact Or.inl ⟨f, hfLeft, hvf⟩
    · exact Or.inr ⟨f, hfRight, hvf⟩

/--
It is enough to prove the parent-to-children direction when both children are
already known to be contained in the parent. This avoids needing decidable
equality on faces just to form a finite-set union.
-/
theorem faces_cover_of_parent_subset_or
    {left right parent : Cell P}
    (hleft : ∀ f, f ∈ left.faces → f ∈ parent.faces)
    (hright : ∀ f, f ∈ right.faces → f ∈ parent.faces)
    (hparent : ∀ f, f ∈ parent.faces → f ∈ left.faces ∨ f ∈ right.faces) :
    ∀ f, f ∈ parent.faces ↔ f ∈ left.faces ∨ f ∈ right.faces := by
  intro f
  constructor
  · intro hf
    exact hparent f hf
  · intro hf
    rcases hf with hfleft | hfright
    · exact hleft f hfleft
    · exact hright f hfright

/-- Union of the supports of an ordered list of cells. -/
def supportUnion : List (Cell P) → Finset V
  | [] => ∅
  | c :: cs => c.support P ∪ supportUnion cs

@[simp] theorem supportUnion_nil :
    supportUnion P ([] : List (Cell P)) = ∅ := rfl

@[simp] theorem supportUnion_cons (c : Cell P) (cs : List (Cell P)) :
    supportUnion P (c :: cs) = c.support P ∪ supportUnion P cs := rfl

/-- The last cell in a nonempty ordered list. -/
def lastCell (c : Cell P) : List (Cell P) → Cell P
  | [] => c
  | d :: ds => lastCell d ds

end Cell

/--
Nonempty polyhedral cells.

The recursive split route should use this universe rather than all finite face
sets: the empty face set cannot be split into proper face-subset children and
cannot carry a terminal boundary witness.
-/
structure PositiveCell (P : PolyhedralEmbedding G) where
  cell : Cell P
  faces_nonempty : cell.faces.Nonempty

namespace PositiveCell

variable (P : PolyhedralEmbedding G)

noncomputable instance : DecidableEq (PositiveCell P) := Classical.decEq _

instance : Coe (PositiveCell P) (Cell P) where
  coe c := c.cell

@[simp] theorem coe_cell (c : PositiveCell P) :
    (c : Cell P) = c.cell := rfl

/-- The finite vertex support of a nonempty cell. -/
def support (c : PositiveCell P) : Finset V :=
  c.cell.support P

@[simp] theorem support_coe (c : PositiveCell P) :
    c.support P = c.cell.support P := rfl

/-- The nonempty cell consisting of one face. -/
def singleton (f : P.Face) : PositiveCell P where
  cell := Cell.singleton P f
  faces_nonempty := by
    simp [Cell.singleton]

/-- The all-faces cell, using an explicitly supplied face. -/
def fullOfFace (f : P.Face) : PositiveCell P where
  cell := Cell.full P
  faces_nonempty := ⟨f, Finset.mem_univ f⟩

/-- The all-faces cell is nonempty whenever a covered vertex is supplied. -/
noncomputable def fullOfVertex (v : V) : PositiveCell P :=
  let f := Classical.choose (P.vertex_covered v)
  fullOfFace P f

@[simp] theorem cell_fullOfFace (f : P.Face) :
    (fullOfFace P f).cell = Cell.full P := rfl

@[simp] theorem cell_fullOfVertex (v : V) :
    (fullOfVertex P v).cell = Cell.full P := by
  simp [fullOfVertex, fullOfFace]

@[simp] theorem support_singleton (f : P.Face) :
    (singleton P f).support P = P.faceSupport f :=
  Cell.support_singleton P f

@[simp] theorem support_fullOfFace (f : P.Face) :
    (fullOfFace P f).support P = (Finset.univ : Finset V) :=
  Cell.support_full P

@[simp] theorem support_fullOfVertex (v : V) :
    (fullOfVertex P v).support P = (Finset.univ : Finset V) := by
  change (Cell.full P).support P = (Finset.univ : Finset V)
  exact Cell.support_full P

/-- Default recursive rank on nonempty cells: the number of faces. -/
def faceRank (c : PositiveCell P) : Nat :=
  c.cell.faces.card

theorem faceRank_pos (c : PositiveCell P) :
    0 < faceRank P c := by
  simpa [faceRank] using Finset.card_pos.2 c.faces_nonempty

/-- Terminal nonempty cells are singleton faces. -/
def IsSingletonFace (c : PositiveCell P) : Prop :=
  ∃ f : P.Face, c.cell = Cell.singleton P f

/-- Singleton positive cells are terminal. -/
@[simp] theorem isSingletonFace_singleton (f : P.Face) :
    IsSingletonFace P (singleton P f) :=
  ⟨f, rfl⟩

/-- The face contained in a terminal positive singleton cell. -/
noncomputable def singletonFace
    (c : PositiveCell P)
    (h : IsSingletonFace P c) : P.Face :=
  Classical.choose h

/-- A terminal positive singleton cell is exactly the singleton over its chosen face. -/
theorem eq_singleton_singletonFace
    (c : PositiveCell P)
    (h : IsSingletonFace P c) :
    c.cell = Cell.singleton P (singletonFace P c h) :=
  Classical.choose_spec h

/-- If a terminal positive cell is known to be a concrete singleton, its chosen face is that face. -/
theorem singletonFace_eq_of_eq_singleton
    {c : PositiveCell P}
    (h : IsSingletonFace P c)
    {f : P.Face}
    (hc : c.cell = Cell.singleton P f) :
    singletonFace P c h = f :=
  Cell.singleton_injective P
    ((eq_singleton_singletonFace P c h).symm.trans hc)

@[simp] theorem singletonFace_singleton
    (f : P.Face)
    (h : IsSingletonFace P (singleton P f)) :
    singletonFace P (singleton P f) h = f :=
  singletonFace_eq_of_eq_singleton P h rfl

@[simp] theorem faceRank_singleton (f : P.Face) :
    faceRank P (singleton P f) = 1 := by
  simp [faceRank, singleton, Cell.singleton]

/-- Proper inclusion of face sets gives the default rank decrease. -/
theorem faceRank_lt_of_faces_ssubset
    {child parent : PositiveCell P}
    (hfaces : child.cell.faces ⊂ parent.cell.faces) :
    faceRank P child < faceRank P parent := by
  simpa [faceRank] using Finset.card_lt_card hfaces

/-- A nonterminal positive cell's face set is not a singleton. -/
theorem faces_ne_singleton_of_not_isSingletonFace
    (c : PositiveCell P)
    (hnonterminal : ¬ IsSingletonFace P c)
    (f : P.Face) :
    c.cell.faces ≠ {f} := by
  intro hfaces
  apply hnonterminal
  refine ⟨f, ?_⟩
  cases c with
  | mk cell faces_nonempty =>
      cases cell with
      | mk faces =>
          simpa [Cell.singleton] using hfaces

/-- In a nonterminal positive cell, any chosen face has a distinct companion face. -/
theorem exists_face_ne_of_not_isSingletonFace
    (c : PositiveCell P)
    (hnonterminal : ¬ IsSingletonFace P c)
    {f : P.Face}
    (hf : f ∈ c.cell.faces) :
    ∃ g : P.Face, g ∈ c.cell.faces ∧ g ≠ f := by
  classical
  by_contra hnone
  have hsubset : c.cell.faces ⊆ ({f} : Finset P.Face) := by
    intro g hg
    by_cases hgf : g = f
    · simpa [hgf]
    · exact False.elim (hnone ⟨g, hg, hgf⟩)
  have hsingleton_subset : ({f} : Finset P.Face) ⊆ c.cell.faces := by
    intro g hg
    have hgf : g = f := by
      simpa using hg
    simpa [hgf] using hf
  have hfaces : c.cell.faces = ({f} : Finset P.Face) :=
    le_antisymm hsubset hsingleton_subset
  exact faces_ne_singleton_of_not_isSingletonFace P c hnonterminal f hfaces

/-- Erasing any face from a nonterminal positive cell leaves a nonempty face set. -/
theorem erase_faces_nonempty_of_not_isSingletonFace
    (c : PositiveCell P)
    (hnonterminal : ¬ IsSingletonFace P c)
    {f : P.Face}
    (hf : f ∈ c.cell.faces) :
    (c.cell.faces.erase f).Nonempty := by
  rcases exists_face_ne_of_not_isSingletonFace P c hnonterminal hf with
    ⟨g, hg, hgf⟩
  exact ⟨g, by simpa [Finset.mem_erase, hgf, hg]⟩

/--
The finite face-set part of a two-child split of a positive cell.

This contains the data that follows from nonempty finite face combinatorics:
positive children, proper face-subset proofs, and the parent-to-child face-cover
direction.
-/
structure FaceSplitChildren (parent : PositiveCell P) where
  left : PositiveCell P
  right : PositiveCell P
  left_faces : left.cell.faces ⊂ parent.cell.faces
  right_faces : right.cell.faces ⊂ parent.cell.faces
  parent_faces_cover :
    ∀ f, f ∈ parent.cell.faces → f ∈ left.cell.faces ∨ f ∈ right.cell.faces

/--
Canonical finite face-set split: choose one face for the left child and put all
remaining faces in the right child.
-/
noncomputable def splitOffFace
    (parent : PositiveCell P)
    (hnonterminal : ¬ IsSingletonFace P parent) :
    FaceSplitChildren P parent := by
  classical
  let f : P.Face := Classical.choose parent.faces_nonempty
  have hf : f ∈ parent.cell.faces :=
    Classical.choose_spec parent.faces_nonempty
  let rightCell : Cell P := { faces := parent.cell.faces.erase f }
  have hright_nonempty : rightCell.faces.Nonempty := by
    simpa [rightCell] using
      erase_faces_nonempty_of_not_isSingletonFace P parent hnonterminal hf
  refine
    { left := singleton P f
      right := { cell := rightCell, faces_nonempty := hright_nonempty }
      left_faces := ?_
      right_faces := ?_
      parent_faces_cover := ?_ }
  · constructor
    · intro g hg
      have hgf : g = f := by
        simpa [singleton, Cell.singleton] using hg
      simpa [hgf] using hf
    · intro hparent_subset
      rcases exists_face_ne_of_not_isSingletonFace P parent hnonterminal hf with
        ⟨g, hg, hgf⟩
      have hgleft : g ∈ (singleton P f).cell.faces := hparent_subset hg
      have hgf' : g = f := by
        simpa [singleton, Cell.singleton] using hgleft
      exact hgf hgf'
  · simpa [rightCell] using Finset.erase_ssubset hf
  · intro g hg
    by_cases hgf : g = f
    · left
      simpa [singleton, Cell.singleton, hgf]
    · right
      simpa [rightCell, Finset.mem_erase, hgf, hg]

end PositiveCell

/--
Entry/exit data for the faces of a polyhedral embedding, together with the
terminal boundary witness needed by the existing spanning-path machinery.
-/
structure FacePathDatum (P : PolyhedralEmbedding G) where
  s : P.Face → V
  t : P.Face → V
  witness :
    ∀ f, OrderedSegmentFamily.BoundaryCycleWitness G.Adj
      (P.faceSupport f) (s f) (t f)

namespace FacePathDatum

/--
Build face path data from explicit cyclic presentations of every face boundary.

Each presentation chooses the deleted closing edge `t f -> s f`; the remaining
opened boundary gives the terminal spanning path for that face.
-/
def ofBoundaryPresentations
    (P : PolyhedralEmbedding G)
    (s t : P.Face → V)
    (middle : ∀ f, List V)
    (hsupport :
      ∀ f, (P.boundary f).vertices =
        s f :: (middle f ++ [t f, s f])) :
    FacePathDatum P where
  s := s
  t := t
  witness := by
    intro f
    simpa [PolyhedralEmbedding.faceSupport] using
      (P.boundary f).toBoundaryCycleWitnessOfSupport
        (middle f) (hsupport f)

/-- Build face path data from bundled cyclic presentations for every face. -/
def ofFaceBoundaryPresentations
    {P : PolyhedralEmbedding G}
    (presentations : FaceBoundaryPresentations P) :
    FacePathDatum P :=
  ofBoundaryPresentations P presentations.s presentations.t presentations.middle
    presentations.vertices_eq

/--
A face-boundary witness, reindexed as a terminal witness for the singleton cell
containing that face.
-/
def terminalWitnessOnSingleton
    {P : PolyhedralEmbedding G}
    (datum : FacePathDatum P)
    (f : P.Face) :
    OrderedSegmentFamily.BoundaryCycleWitness
      G.Adj ((Cell.singleton P f).support P) (datum.s f) (datum.t f) :=
  (datum.witness f).castSupport ((Cell.support_singleton P f).symm)

end FacePathDatum

namespace FaceBoundaryPresentations

variable {P : PolyhedralEmbedding G}

/-- Convert bundled cyclic face-boundary presentations to terminal face path data. -/
def toFacePathDatum
    (presentations : FaceBoundaryPresentations P) :
    FacePathDatum P :=
  FacePathDatum.ofFaceBoundaryPresentations presentations

@[simp] theorem toFacePathDatum_s
    (presentations : FaceBoundaryPresentations P)
    (f : P.Face) :
    presentations.toFacePathDatum.s f = presentations.s f := rfl

@[simp] theorem toFacePathDatum_t
    (presentations : FaceBoundaryPresentations P)
    (f : P.Face) :
    presentations.toFacePathDatum.t f = presentations.t f := rfl

@[simp] theorem toFacePathDatum_witness_middle
    (presentations : FaceBoundaryPresentations P)
    (f : P.Face) :
    (presentations.toFacePathDatum.witness f).middle =
      presentations.middle f := rfl

/--
An infix proof on the recorded boundary vertices transfers to the chosen cyclic
presentation of that face.
-/
theorem infix_chosenBoundary_of_boundary_vertices
    (presentations : FaceBoundaryPresentations P)
    {needle : List V}
    (f : P.Face)
    (hinfix : needle <:+: (P.boundary f).vertices) :
    needle <:+:
      presentations.s f ::
        (presentations.middle f ++ [presentations.t f, presentations.s f]) := by
  simpa [presentations.vertices_eq f] using hinfix

/--
Terminal-boundary data for active positive singleton cells follows from
face-level infix proofs on their recorded boundary vertices.
-/
theorem activeSingletonBoundaryInfix_of_boundary_vertices
    (presentations : FaceBoundaryPresentations P)
    {active : PositiveCell P → Prop}
    {needle : List V}
    (hinfix :
      ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
        needle <:+:
          (P.boundary (PositiveCell.singletonFace P x hx)).vertices) :
    ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
      needle <:+:
        presentations.s (PositiveCell.singletonFace P x hx) ::
          (presentations.middle (PositiveCell.singletonFace P x hx) ++
            [presentations.t (PositiveCell.singletonFace P x hx),
              presentations.s (PositiveCell.singletonFace P x hx)]) := by
  intro x hactive hx
  exact
    presentations.infix_chosenBoundary_of_boundary_vertices
      (PositiveCell.singletonFace P x hx)
      (hinfix x hactive hx)

end FaceBoundaryPresentations

/--
Every face can be treated as a terminal cell. This is the first concrete bridge
from `SimpleGraph`-based polyhedral data to `ConcreteCellSystem`.
-/
def toFaceCellSystem
    (P : PolyhedralEmbedding G)
    (datum : FacePathDatum P) :
    ConcreteCellSystem (Cell := P.Face) (V := V) (Adj := G.Adj) where
  support := P.faceSupport
  datum := { s := datum.s, t := datum.t }
  rank := fun _ => 0
  terminal := fun _ => True
  terminal_witness := by
    intro f _
    exact datum.witness f
  move_witness := by
    intro f hfalse
    exact False.elim (hfalse trivial)

/-- Facewise spanning paths obtained directly from boundary-cycle witnesses. -/
noncomputable def buildFaceSpanningPath
    (P : PolyhedralEmbedding G)
    (datum : FacePathDatum P) :
    ∀ f, ListSpanningPath G.Adj (P.faceSupport f) (datum.s f) (datum.t f) :=
  (toFaceCellSystem P datum).buildCellwiseSpanningPath

/--
If the chosen closing edge on a face is present, the face support carries a
Hamiltonian cycle in the ambient graph.
-/
theorem faceHamiltonianOfClosingEdge
    (P : PolyhedralEmbedding G)
    (datum : FacePathDatum P)
    (f : P.Face)
    (hclose : G.Adj (datum.t f) (datum.s f)) :
    HamiltonianOn (P.faceSupport f) G.Adj := by
  exact (toFaceCellSystem P datum).hamiltonianOfClosingEdge hclose

/--
Entry/exit data for polyhedral union-cells. This is the target-side analogue of
the abstract path datum used earlier in the file.
-/
structure CellPathDatum (P : PolyhedralEmbedding G) where
  s : Cell P → V
  t : Cell P → V

namespace CellPathDatum

/--
Force the singleton-cell endpoints of a cell datum to agree with chosen
face-boundary presentations.

Non-singleton endpoint choices are inherited from `base`; singleton cells use
the presented face endpoints by construction.
-/
noncomputable def withSingletonFaceEndpoints
    {P : PolyhedralEmbedding G}
    (presentations : FaceBoundaryPresentations P)
    (base : CellPathDatum P) :
    CellPathDatum P := by
  classical
  exact
    { s := fun c =>
        if h : Cell.IsSingletonFace P c then
          presentations.s (Cell.singletonFace P c h)
        else
          base.s c
      t := fun c =>
        if h : Cell.IsSingletonFace P c then
          presentations.t (Cell.singletonFace P c h)
        else
          base.t c }

@[simp] theorem withSingletonFaceEndpoints_s_singleton
    {P : PolyhedralEmbedding G}
    (presentations : FaceBoundaryPresentations P)
    (base : CellPathDatum P)
    (f : P.Face) :
    (withSingletonFaceEndpoints presentations base).s (Cell.singleton P f) =
      presentations.s f := by
  classical
  simp [withSingletonFaceEndpoints]

@[simp] theorem withSingletonFaceEndpoints_t_singleton
    {P : PolyhedralEmbedding G}
    (presentations : FaceBoundaryPresentations P)
    (base : CellPathDatum P)
    (f : P.Face) :
    (withSingletonFaceEndpoints presentations base).t (Cell.singleton P f) =
      presentations.t f := by
  classical
  simp [withSingletonFaceEndpoints]

/--
Cell endpoint data packaged together with the singleton compatibility proofs
needed by terminal face witnesses.
-/
structure SingletonCompatible
    {P : PolyhedralEmbedding G}
    (presentations : FaceBoundaryPresentations P) where
  datum : CellPathDatum P
  s_singleton :
    ∀ f, datum.s (Cell.singleton P f) = presentations.s f
  t_singleton :
    ∀ f, datum.t (Cell.singleton P f) = presentations.t f

namespace SingletonCompatible

/--
Any cell endpoint datum can be made singleton-compatible by overriding only its
singleton-cell endpoints.
-/
noncomputable def ofBase
    {P : PolyhedralEmbedding G}
    (presentations : FaceBoundaryPresentations P)
    (base : CellPathDatum P) :
    SingletonCompatible presentations where
  datum := withSingletonFaceEndpoints presentations base
  s_singleton := by
    intro f
    simp
  t_singleton := by
    intro f
    simp

end SingletonCompatible

/--
Force the all-faces cell endpoints to use the closing edge `a - b`.

The resulting full-cell path starts at `b` and ends at `a`, so the closing edge
needed by the root cycle is the first edge of the marked path.
-/
noncomputable def withFullRootClosingEndpoints
    {P : PolyhedralEmbedding G}
    (a b : V)
    (base : CellPathDatum P) :
    CellPathDatum P := by
  classical
  exact
    { s := fun c => if c = Cell.full P then b else base.s c
      t := fun c => if c = Cell.full P then a else base.t c }

@[simp] theorem withFullRootClosingEndpoints_s_full
    {P : PolyhedralEmbedding G}
    (a b : V)
    (base : CellPathDatum P) :
    (withFullRootClosingEndpoints a b base).s (Cell.full P) = b := by
  classical
  simp [withFullRootClosingEndpoints]

@[simp] theorem withFullRootClosingEndpoints_t_full
    {P : PolyhedralEmbedding G}
    (a b : V)
    (base : CellPathDatum P) :
    (withFullRootClosingEndpoints a b base).t (Cell.full P) = a := by
  classical
  simp [withFullRootClosingEndpoints]

/--
Cell endpoint data packaged with both singleton endpoint compatibility and the
chosen all-faces positive root closing edge.
-/
structure FullRootSingletonCompatible
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (presentations : FaceBoundaryPresentations P)
    (hpath : Path3Vertices G a b c d) where
  datum : CellPathDatum P
  s_singleton :
    ∀ f, datum.s (Cell.singleton P f) = presentations.s f
  t_singleton :
    ∀ f, datum.t (Cell.singleton P f) = presentations.t f
  root_support :
    (PositiveCell.fullOfVertex P a).support P = (Finset.univ : Finset V)
  root_closing :
    G.Adj (datum.t (PositiveCell.fullOfVertex P a).cell)
      (datum.s (PositiveCell.fullOfVertex P a).cell)

namespace FullRootSingletonCompatible

/--
Any base endpoint datum can be made compatible with singleton faces and with the
all-faces root closing edge from the first edge of `[a,b,c,d]`.
-/
noncomputable def ofBase
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (presentations : FaceBoundaryPresentations P)
    (hpath : Path3Vertices G a b c d)
    (base : CellPathDatum P) :
    FullRootSingletonCompatible presentations hpath where
  datum :=
    withFullRootClosingEndpoints a b
      (withSingletonFaceEndpoints presentations base)
  s_singleton := by
    intro f
    classical
    have hne : Cell.singleton P f ≠ Cell.full P :=
      Cell.singleton_ne_full_of_adj P hpath.1 f
    simp [withFullRootClosingEndpoints, hne]
  t_singleton := by
    intro f
    classical
    have hne : Cell.singleton P f ≠ Cell.full P :=
      Cell.singleton_ne_full_of_adj P hpath.1 f
    simp [withFullRootClosingEndpoints, hne]
  root_support := PositiveCell.support_fullOfVertex P a
  root_closing := by
    simpa [withFullRootClosingEndpoints] using hpath.1

end FullRootSingletonCompatible

/--
Use face path data to discharge the terminal witness for a cell known to be a
singleton face, provided the cell endpoints agree with the chosen face endpoints.
-/
def terminalWitnessOfSingletonFace
    {P : PolyhedralEmbedding G}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    {c : Cell P}
    (f : P.Face)
    (hc : c = Cell.singleton P f)
    (hs : datum.s c = faceDatum.s f)
    (ht : datum.t c = faceDatum.t f) :
    OrderedSegmentFamily.BoundaryCycleWitness
      G.Adj (c.support P) (datum.s c) (datum.t c) := by
  subst c
  let w := faceDatum.terminalWitnessOnSingleton f
  refine
    { middle := w.middle
      cycle_adj := ?_
      nodup := ?_
      spans := ?_ }
  · intro a b hab
    exact w.cycle_adj (by simpa [w, hs, ht] using hab)
  · simpa [w, hs, ht] using w.nodup
  · intro v
    simpa [w, hs, ht] using w.spans v

/--
Transport a marked boundary infix proof from face path data to the terminal
boundary obligation for a singleton face cell.
-/
theorem terminalBoundaryInfixOfSingletonFace
    {P : PolyhedralEmbedding G}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    {c : Cell P}
    (f : P.Face)
    (hc : c = Cell.singleton P f)
    (hs : datum.s c = faceDatum.s f)
    (ht : datum.t c = faceDatum.t f)
    {needle : List V}
    (hinfix :
      needle <:+:
        faceDatum.s f ::
          ((faceDatum.witness f).middle ++ [faceDatum.t f, faceDatum.s f])) :
    needle <:+:
      datum.s c ::
        (((CellPathDatum.terminalWitnessOfSingletonFace
          (P := P) datum faceDatum f hc hs ht).middle) ++
          [datum.t c, datum.s c]) := by
  subst c
  simpa [terminalWitnessOfSingletonFace, FacePathDatum.terminalWitnessOnSingleton,
    OrderedSegmentFamily.BoundaryCycleWitness.castSupport, hs, ht] using hinfix

/--
Build the full terminal-witness field when every terminal cell is known to be a
singleton face cell.
-/
def terminalWitnessesOfSingletonFaces
    {P : PolyhedralEmbedding G}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    {terminal : Cell P → Prop}
    (faceOf : ∀ c, terminal c → P.Face)
    (hcell : ∀ c hx, c = Cell.singleton P (faceOf c hx))
    (hs : ∀ c hx, datum.s c = faceDatum.s (faceOf c hx))
    (ht : ∀ c hx, datum.t c = faceDatum.t (faceOf c hx)) :
    ∀ c, terminal c →
      OrderedSegmentFamily.BoundaryCycleWitness
        G.Adj (c.support P) (datum.s c) (datum.t c) :=
  fun c hx =>
    datum.terminalWitnessOfSingletonFace
      faceDatum (faceOf c hx) (hcell c hx) (hs c hx) (ht c hx)

/--
Build the provider's terminal-boundary field when terminal cells are singleton
faces and the marked word is known to occur in the chosen face boundary.
-/
theorem terminalBoundaryInfixOfSingletonFaces
    {P : PolyhedralEmbedding G}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    {terminal active : Cell P → Prop}
    (faceOf : ∀ c, terminal c → P.Face)
    (hcell : ∀ c hx, c = Cell.singleton P (faceOf c hx))
    (hs : ∀ c hx, datum.s c = faceDatum.s (faceOf c hx))
    (ht : ∀ c hx, datum.t c = faceDatum.t (faceOf c hx))
    {needle : List V}
    (hinfix :
      ∀ c, active c → (hx : terminal c) →
        needle <:+:
          faceDatum.s (faceOf c hx) ::
            ((faceDatum.witness (faceOf c hx)).middle ++
              [faceDatum.t (faceOf c hx), faceDatum.s (faceOf c hx)])) :
    ∀ c, active c → (hx : terminal c) →
      needle <:+:
        datum.s c ::
          (((CellPathDatum.terminalWitnessesOfSingletonFaces
            (P := P) datum faceDatum faceOf hcell hs ht c hx).middle) ++
            [datum.t c, datum.s c]) := by
  intro c hactive hx
  exact
    datum.terminalBoundaryInfixOfSingletonFace
      faceDatum (faceOf c hx) (hcell c hx) (hs c hx) (ht c hx)
      (hinfix c hactive hx)

end CellPathDatum

/-- Convert a spanning path on a cell into the `PathSegment` used by gluing. -/
def cellToSegment
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (pathOf : ∀ c : Cell P,
      ListSpanningPath G.Adj (c.support P) (datum.s c) (datum.t c))
    (c : Cell P) :
    PathSegment G.Adj where
  support := c.support P
  start := datum.s c
  finish := datum.t c
  path := pathOf c

/-- Ordered cell list converted to ordered path segments using supplied child paths. -/
def cellSegments
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (pathOf : ∀ c : Cell P,
      ListSpanningPath G.Adj (c.support P) (datum.s c) (datum.t c)) :
    List (Cell P) → List (PathSegment G.Adj)
  | [] => []
  | c :: cs => cellToSegment P datum pathOf c :: cellSegments P datum pathOf cs

@[simp] theorem cellSegments_nil
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (pathOf : ∀ c : Cell P,
      ListSpanningPath G.Adj (c.support P) (datum.s c) (datum.t c)) :
    cellSegments P datum pathOf ([] : List (Cell P)) = [] := rfl

@[simp] theorem cellSegments_cons
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (pathOf : ∀ c : Cell P,
      ListSpanningPath G.Adj (c.support P) (datum.s c) (datum.t c))
    (c : Cell P) (cs : List (Cell P)) :
    cellSegments P datum pathOf (c :: cs) =
      cellToSegment P datum pathOf c :: cellSegments P datum pathOf cs := rfl

@[simp] theorem supportUnion_cellSegments
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (pathOf : ∀ c : Cell P,
      ListSpanningPath G.Adj (c.support P) (datum.s c) (datum.t c)) :
    ∀ cells,
      PathSegment.supportUnion (cellSegments P datum pathOf cells) =
        Cell.supportUnion P cells
  | [] => rfl
  | c :: cs => by
      simp [cellSegments, Cell.supportUnion, cellToSegment, supportUnion_cellSegments]

/--
Target-side move data on actual polyhedral union-cells. The geometric conditions
are stated on actual child cells, each equipped with its spanning path.
-/
structure CellSegmentDatum
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P) where
  cell : Cell P
  path : ListSpanningPath G.Adj (cell.support P) (datum.s cell) (datum.t cell)

/-- Forget the ambient cell label and keep the underlying path segment. -/
def CellSegmentDatum.toPathSegment
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (seg : CellSegmentDatum P datum) :
    PathSegment G.Adj where
  support := seg.cell.support P
  start := datum.s seg.cell
  finish := datum.t seg.cell
  path := seg.path

structure CellMoveData
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (parent : Cell P) where
  head : CellSegmentDatum P datum
  tail : List (CellSegmentDatum P datum)
  head_start : datum.s head.cell = datum.s parent
  support_union :
    PathSegment.supportUnion
      (head.toPathSegment P datum :: tail.map (CellSegmentDatum.toPathSegment P datum)) =
        parent.support P
  linked :
    OrderedSegmentFamily.LinkedAllSplits
      (head.toPathSegment P datum :: tail.map (CellSegmentDatum.toPathSegment P datum))
  consecutive_overlap :
    ∀ xs p q qs,
      head.toPathSegment P datum :: tail.map (CellSegmentDatum.toPathSegment P datum) =
        xs ++ p :: q :: qs →
      ∀ v, v ∈ p.support → v ∈ q.support → v = p.finish
  nonconsecutive_disjoint :
    ∀ xs p ms q ys,
      head.toPathSegment P datum :: tail.map (CellSegmentDatum.toPathSegment P datum) =
        xs ++ p :: ms ++ q :: ys →
      ms ≠ [] →
      ∀ v, v ∈ p.support → v ∈ q.support → False
  last_finish :
    (OrderedSegmentFamily.lastSegment
      (head.toPathSegment P datum)
      (tail.map (CellSegmentDatum.toPathSegment P datum))).finish = datum.t parent

/-- Convert target-side cell move data into the generic move-step package. -/
def CellMoveData.toMoveStepData
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    {parent : Cell P}
    (step : CellMoveData P datum parent)
    : OrderedSegmentFamily.MoveStepData G.Adj
        (parent.support P) (datum.s parent) (datum.t parent) := by
  classical
  let hoverlap :
      OrderedSegmentFamily.OverlapAllSplits
        (step.head.toPathSegment P datum ::
          step.tail.map (CellSegmentDatum.toPathSegment P datum)) :=
    OrderedSegmentFamily.overlapAllSplits_of_localIntersections
      (step.head.toPathSegment P datum ::
        step.tail.map (CellSegmentDatum.toPathSegment P datum))
      step.consecutive_overlap step.nonconsecutive_disjoint
  refine
    { head := step.head.toPathSegment P datum
      tail := step.tail.map (CellSegmentDatum.toPathSegment P datum)
      head_start := step.head_start
      support_union := step.support_union
      linked := step.linked
      overlap := hoverlap
      tail_finish := by
        simpa [hoverlap, OrderedSegmentFamily.last_ofSplits] using step.last_finish }

/-- Build the parent spanning path from target-side cell move data. -/
def CellMoveData.spanningPath
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    {parent : Cell P}
    (step : CellMoveData P datum parent) :
    ListSpanningPath G.Adj (parent.support P) (datum.s parent) (datum.t parent) :=
  OrderedSegmentFamily.spanningPathOfMoveStep (step.toMoveStepData P datum)

/-- Closing-edge version of `CellMoveData.spanningPath`. -/
theorem CellMoveData.hamiltonianOfClosingEdge
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    {parent : Cell P}
    (step : CellMoveData P datum parent)
    (hclose : G.Adj (datum.t parent) (datum.s parent)) :
    HamiltonianOn (parent.support P) G.Adj :=
  hamiltonianOn_of_spanningPath (step.spanningPath P datum) hclose

/--
Specialized constructor for the first nonterminal move on target-side cells:
the parent is built from exactly two child cells meeting at one attachment vertex.
-/
def CellMoveData.ofTwoChildren
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (parent : Cell P)
    (left right : CellSegmentDatum P datum)
    (hstart : datum.s left.cell = datum.s parent)
    (hsupport :
      PathSegment.supportUnion
        [left.toPathSegment P datum, right.toPathSegment P datum] =
          parent.support P)
    (hlink : datum.t left.cell = datum.s right.cell)
    (hoverlap :
      ∀ v, v ∈ left.cell.support P → v ∈ right.cell.support P → v = datum.t left.cell)
    (hfinish : datum.t right.cell = datum.t parent) :
    CellMoveData P datum parent := by
  classical
  refine
    { head := left
      tail := [right]
      head_start := hstart
      support_union := hsupport
      linked := ?_
      consecutive_overlap := ?_
      nonconsecutive_disjoint := ?_
      last_finish := ?_ }
  · intro xs p q qs hEq
    have hlen : xs.length + qs.length = 0 := by
      have := congrArg List.length hEq
      simp at this
      omega
    have hxs : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x xs => simp at hlen
    have hqs : qs = [] := by
      cases qs with
      | nil => rfl
      | cons x xs => simp at hlen
    subst hxs
    subst hqs
    simp [CellSegmentDatum.toPathSegment] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    simpa using hlink
  · intro xs p q qs hEq
    have hlen : xs.length + qs.length = 0 := by
      have := congrArg List.length hEq
      simp at this
      omega
    have hxs : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x xs => simp at hlen
    have hqs : qs = [] := by
      cases qs with
      | nil => rfl
      | cons x xs => simp at hlen
    subst hxs
    subst hqs
    simp [CellSegmentDatum.toPathSegment] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    simpa [CellSegmentDatum.toPathSegment] using hoverlap
  · intro xs p ms q ys hEq hms v hvp hvq
    cases ms with
    | nil => exact hms rfl
    | cons m ms =>
        have hfalse : False := by
          have hlen := congrArg List.length hEq
          simp at hlen
          omega
        exact hfalse
  · simpa [OrderedSegmentFamily.lastSegment, CellSegmentDatum.toPathSegment] using hfinish

/--
Geometry for a rank-decreasing two-child nonterminal step.

This is the recursive-construction data before child paths have been built. The
child paths are supplied later by the ranked induction.
-/
structure TwoChildMoveGeometry
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (rank : Cell P → Nat)
    (parent : Cell P) where
  left : Cell P
  right : Cell P
  left_rank : rank left < rank parent
  right_rank : rank right < rank parent
  head_start : datum.s left = datum.s parent
  support_union : left.support P ∪ right.support P = parent.support P
  linked : datum.t left = datum.s right
  consecutive_overlap :
    ∀ v, v ∈ left.support P → v ∈ right.support P → v = datum.t left
  last_finish : datum.t right = datum.t parent

namespace TwoChildMoveGeometry

/-- Turn rank-decreasing two-child geometry into the actual move data. -/
def toCellMoveData
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {rank : Cell P → Nat}
    {parent : Cell P}
    (split : TwoChildMoveGeometry P datum rank parent)
    (childPath :
      ∀ y, rank y < rank parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) :
    CellMoveData P datum parent :=
  let leftSeg : CellSegmentDatum P datum :=
    { cell := split.left
      path := childPath split.left split.left_rank }
  let rightSeg : CellSegmentDatum P datum :=
    { cell := split.right
      path := childPath split.right split.right_rank }
  CellMoveData.ofTwoChildren P datum parent leftSeg rightSeg
    split.head_start
    (by
      simpa [leftSeg, rightSeg, CellSegmentDatum.toPathSegment,
        PathSegment.supportUnion] using split.support_union)
    split.linked
    split.consecutive_overlap
    split.last_finish

/--
For a two-child split, the opened parent cycle used by `parent_open` is the
explicit concatenation of the two recursively supplied child paths.
-/
theorem parentOpenOfInfixAppend
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {rank : Cell P → Nat}
    {parent : Cell P}
    (split : TwoChildMoveGeometry P datum rank parent)
    (childPath :
      ∀ y, rank y < rank parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s parent ::
          (((childPath split.left split.left_rank).tail ++
            (childPath split.right split.right_rank).tail) ++
              [datum.s parent])) :
    needle <:+:
      datum.s parent ::
        (((split.toCellMoveData childPath).spanningPath P datum).tail ++
          [datum.s parent]) := by
  simpa [toCellMoveData, CellMoveData.spanningPath, CellMoveData.toMoveStepData,
    CellMoveData.ofTwoChildren, OrderedSegmentFamily.spanningPathOfMoveStep,
    OrderedSegmentFamily.spanningPathOfSplits, OrderedSegmentFamily.ofSplits,
    OrderedSegmentFamily.toChain, PathSegment.spanningPathOfChain,
    ListSpanningPath.append_of_support_inter, ListSpanningPath.append,
    CellSegmentDatum.toPathSegment, PathSegment.supportUnion,
    OrderedSegmentFamily.lastSegment] using hinfix

end TwoChildMoveGeometry

/--
Two-child split geometry using the default face-count rank.

The rank-decrease fields are stated as proper face-set inclusions; converting to
`TwoChildMoveGeometry` turns those inclusions into rank inequalities.
-/
structure FaceSubsetTwoChildMoveGeometry
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (parent : Cell P) where
  left : Cell P
  right : Cell P
  left_faces : left.faces ⊂ parent.faces
  right_faces : right.faces ⊂ parent.faces
  head_start : datum.s left = datum.s parent
  support_union : left.support P ∪ right.support P = parent.support P
  linked : datum.t left = datum.s right
  consecutive_overlap :
    ∀ v, v ∈ left.support P → v ∈ right.support P → v = datum.t left
  last_finish : datum.t right = datum.t parent

namespace FaceSubsetTwoChildMoveGeometry

/-- Convert proper face-subset split geometry to rank-decreasing move geometry. -/
def toTwoChildMoveGeometry
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceSubsetTwoChildMoveGeometry P datum parent) :
    TwoChildMoveGeometry P datum (Cell.faceRank P) parent where
  left := split.left
  right := split.right
  left_rank := Cell.faceRank_lt_of_faces_ssubset P split.left_faces
  right_rank := Cell.faceRank_lt_of_faces_ssubset P split.right_faces
  head_start := split.head_start
  support_union := split.support_union
  linked := split.linked
  consecutive_overlap := split.consecutive_overlap
  last_finish := split.last_finish

/--
For a face-subset two-child split, parent-open preservation can be proved on the
explicit concatenation of the two child path tails.
-/
theorem parentOpenOfInfixAppend
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceSubsetTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, Cell.faceRank P y < Cell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s parent ::
          (((childPath split.left
              (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ++
            (childPath split.right
              (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail) ++
              [datum.s parent])) :
    needle <:+:
      datum.s parent ::
        ((((split.toTwoChildMoveGeometry).toCellMoveData childPath).spanningPath
          P datum).tail ++ [datum.s parent]) :=
  split.toTwoChildMoveGeometry.parentOpenOfInfixAppend childPath hinfix

end FaceSubsetTwoChildMoveGeometry

/--
Two-child split geometry where support coverage is proved at the face-set level.

The support-union field of `FaceSubsetTwoChildMoveGeometry` is derived from the
face-set cover `left.faces ∪ right.faces = parent.faces`.
-/
structure FaceCoverTwoChildMoveGeometry
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (parent : Cell P) where
  left : Cell P
  right : Cell P
  left_faces : left.faces ⊂ parent.faces
  right_faces : right.faces ⊂ parent.faces
  faces_cover :
    ∀ f, f ∈ parent.faces ↔ f ∈ left.faces ∨ f ∈ right.faces
  head_start : datum.s left = datum.s parent
  linked : datum.t left = datum.s right
  consecutive_overlap :
    ∀ v, v ∈ left.support P → v ∈ right.support P → v = datum.t left
  last_finish : datum.t right = datum.t parent

/-- The empty face-set cell cannot support the proper two-child split geometry. -/
theorem false_of_faceCoverTwoChildMoveGeometry_empty
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    (split : FaceCoverTwoChildMoveGeometry P datum (Cell.empty P)) :
    False := by
  exact Finset.not_ssubset_empty split.left.faces
    (by simpa [Cell.empty] using split.left_faces)

namespace FaceCoverTwoChildMoveGeometry

/--
Build face-cover split geometry from a finite-set support-intersection
containment. This is often the cleaner planar obligation behind the pointwise
overlap field.
-/
def ofSupportInterSubset
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (left right : Cell P)
    (left_faces : left.faces ⊂ parent.faces)
    (right_faces : right.faces ⊂ parent.faces)
    (faces_cover :
      ∀ f, f ∈ parent.faces ↔ f ∈ left.faces ∨ f ∈ right.faces)
    (head_start : datum.s left = datum.s parent)
    (linked : datum.t left = datum.s right)
    (support_inter_subset :
      left.support P ∩ right.support P ⊆ {datum.t left})
    (last_finish : datum.t right = datum.t parent) :
    FaceCoverTwoChildMoveGeometry P datum parent where
  left := left
  right := right
  left_faces := left_faces
  right_faces := right_faces
  faces_cover := faces_cover
  head_start := head_start
  linked := linked
  consecutive_overlap := by
    intro v hvleft hvright
    have hv : v ∈ left.support P ∩ right.support P := by
      simp [hvleft, hvright]
    have hv_singleton : v ∈ ({datum.t left} : Finset V) :=
      support_inter_subset hv
    simpa using hv_singleton
  last_finish := last_finish

/--
Build face-cover split geometry from an exact finite-set support-intersection
statement.
-/
def ofSupportInterEq
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (left right : Cell P)
    (left_faces : left.faces ⊂ parent.faces)
    (right_faces : right.faces ⊂ parent.faces)
    (faces_cover :
      ∀ f, f ∈ parent.faces ↔ f ∈ left.faces ∨ f ∈ right.faces)
    (head_start : datum.s left = datum.s parent)
    (linked : datum.t left = datum.s right)
    (support_inter :
      left.support P ∩ right.support P = {datum.t left})
    (last_finish : datum.t right = datum.t parent) :
    FaceCoverTwoChildMoveGeometry P datum parent :=
  ofSupportInterSubset left right left_faces right_faces faces_cover
    head_start linked
    (by
      intro v hv
      simpa [support_inter] using hv)
    last_finish

/--
Build split geometry from the parent-to-children face-cover direction plus a
finite-set support-intersection containment. The reverse face-cover direction is
derived from the proper child-face inclusions.
-/
def ofParentFaceCoverAndSupportInterSubset
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (left right : Cell P)
    (left_faces : left.faces ⊂ parent.faces)
    (right_faces : right.faces ⊂ parent.faces)
    (parent_faces_cover :
      ∀ f, f ∈ parent.faces → f ∈ left.faces ∨ f ∈ right.faces)
    (head_start : datum.s left = datum.s parent)
    (linked : datum.t left = datum.s right)
    (support_inter_subset :
      left.support P ∩ right.support P ⊆ {datum.t left})
    (last_finish : datum.t right = datum.t parent) :
    FaceCoverTwoChildMoveGeometry P datum parent :=
  ofSupportInterSubset left right left_faces right_faces
    (Cell.faces_cover_of_parent_subset_or P
      (fun f hf => left_faces.1 hf)
      (fun f hf => right_faces.1 hf)
      parent_faces_cover)
    head_start linked support_inter_subset last_finish

/--
Build split geometry from the parent-to-children face-cover direction plus an
exact support-intersection statement.
-/
def ofParentFaceCoverAndSupportInterEq
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (left right : Cell P)
    (left_faces : left.faces ⊂ parent.faces)
    (right_faces : right.faces ⊂ parent.faces)
    (parent_faces_cover :
      ∀ f, f ∈ parent.faces → f ∈ left.faces ∨ f ∈ right.faces)
    (head_start : datum.s left = datum.s parent)
    (linked : datum.t left = datum.s right)
    (support_inter :
      left.support P ∩ right.support P = {datum.t left})
    (last_finish : datum.t right = datum.t parent) :
    FaceCoverTwoChildMoveGeometry P datum parent :=
  ofParentFaceCoverAndSupportInterSubset left right left_faces right_faces
    parent_faces_cover head_start linked
    (by
      intro v hv
      simpa [support_inter] using hv)
    last_finish

/-- Convert face-cover split geometry to the face-subset split surface. -/
def toFaceSubsetTwoChildMoveGeometry
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceCoverTwoChildMoveGeometry P datum parent) :
    FaceSubsetTwoChildMoveGeometry P datum parent where
  left := split.left
  right := split.right
  left_faces := split.left_faces
  right_faces := split.right_faces
  head_start := split.head_start
  support_union := Cell.support_union_of_faces_cover P split.faces_cover
  linked := split.linked
  consecutive_overlap := split.consecutive_overlap
  last_finish := split.last_finish

/-- Convert face-cover split geometry to rank-decreasing two-child geometry. -/
def toTwoChildMoveGeometry
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceCoverTwoChildMoveGeometry P datum parent) :
    TwoChildMoveGeometry P datum (Cell.faceRank P) parent :=
  split.toFaceSubsetTwoChildMoveGeometry.toTwoChildMoveGeometry

/--
For a face-cover two-child split, parent-open preservation can be proved on the
explicit concatenation of the two child path tails.
-/
theorem parentOpenOfInfixAppend
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, Cell.faceRank P y < Cell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s parent ::
          (((childPath split.left
              (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ++
            (childPath split.right
              (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail) ++
              [datum.s parent])) :
    needle <:+:
      datum.s parent ::
        ((((split.toTwoChildMoveGeometry).toCellMoveData childPath).spanningPath
          P datum).tail ++ [datum.s parent]) :=
  split.toFaceSubsetTwoChildMoveGeometry.parentOpenOfInfixAppend childPath hinfix

/--
If the marked word occurs on the left child's open path, it occurs on the
explicit parent path obtained by appending the right child tail.
-/
theorem parentAppendOfLeftOpenInfix
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, Cell.faceRank P y < Cell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s split.left ::
          (childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail) :
    needle <:+:
      datum.s parent ::
        (((childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ++
          (childPath split.right
            (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail) ++
          [datum.s parent]) := by
  have hleft :
      needle <:+:
        datum.s split.left ::
          ((childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ++
            ((childPath split.right
              (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail ++
              [datum.s parent])) :=
    List.infix_append_right
      (n :=
        (childPath split.right
          (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail ++
          [datum.s parent])
      hinfix
  simpa [split.head_start, List.append_assoc] using hleft

/--
If the marked word occurs on the right child's open path, it occurs on the
explicit parent path after the left child tail reaches the right child's start.
-/
theorem parentAppendOfRightOpenInfix
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, Cell.faceRank P y < Cell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s split.right ::
          (childPath split.right
            (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail) :
    needle <:+:
      datum.s parent ::
        (((childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ++
          (childPath split.right
            (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail) ++
          [datum.s parent]) := by
  have hright :
      needle <:+:
        datum.s split.right ::
          ((childPath split.right
            (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail ++
            [datum.s parent]) :=
    List.infix_append_right
      (n := [datum.s parent])
      hinfix
  have hend :
      endVertex (datum.s parent)
          (childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail =
        datum.s split.right := by
    calc
      endVertex (datum.s parent)
          (childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail
          = endVertex (datum.s split.left)
              (childPath split.left
                (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail := by
              rw [← split.head_start]
      _ = datum.t split.left :=
              (childPath split.left
                (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).ends_at
      _ = datum.s split.right := split.linked
  simpa [List.append_assoc] using
    (List.infix_cons_append_of_endVertex
      (xs :=
        (childPath split.left
          (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail)
      (ys :=
        (childPath split.right
          (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail ++
          [datum.s parent])
      hend hright)

/--
Open occurrence on either child is enough to prove the explicit parent append
infix obligation for a two-child split.
-/
theorem parentAppendOfChildOpenInfix
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, Cell.faceRank P y < Cell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s split.left ::
          (childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ∨
      needle <:+:
        datum.s split.right ::
          (childPath split.right
            (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail) :
    needle <:+:
      datum.s parent ::
        (((childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ++
          (childPath split.right
            (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail) ++
          [datum.s parent]) := by
  rcases hinfix with hleft | hright
  · exact split.parentAppendOfLeftOpenInfix childPath hleft
  · exact split.parentAppendOfRightOpenInfix childPath hright

/--
For a length-four mark, a cyclic occurrence on the left child is open whenever
the mark's last vertex is not the left child's start.
-/
theorem parentAppendOfLeftCyclicPath4InfixOfLastNeStart
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, Cell.faceRank P y < Cell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y))
    {a b c d : V}
    (hinfix :
      [a, b, c, d] <:+:
        datum.s split.left ::
          ((childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ++
            [datum.s split.left]))
    (hd : d ≠ datum.s split.left) :
    [a, b, c, d] <:+:
      datum.s parent ::
        (((childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ++
          (childPath split.right
            (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail) ++
          [datum.s parent]) :=
  split.parentAppendOfLeftOpenInfix childPath
    (List.path4_open_of_cyclic_append_of_last_ne_start hinfix hd)

/--
For a length-four mark, a cyclic occurrence on the right child is open whenever
the mark's last vertex is not the right child's start.
-/
theorem parentAppendOfRightCyclicPath4InfixOfLastNeStart
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : Cell P}
    (split : FaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, Cell.faceRank P y < Cell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y))
    {a b c d : V}
    (hinfix :
      [a, b, c, d] <:+:
        datum.s split.right ::
          ((childPath split.right
            (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail ++
            [datum.s split.right]))
    (hd : d ≠ datum.s split.right) :
    [a, b, c, d] <:+:
      datum.s parent ::
        (((childPath split.left
            (Cell.faceRank_lt_of_faces_ssubset P split.left_faces)).tail ++
          (childPath split.right
            (Cell.faceRank_lt_of_faces_ssubset P split.right_faces)).tail) ++
          [datum.s parent]) :=
  split.parentAppendOfRightOpenInfix childPath
    (List.path4_open_of_cyclic_append_of_last_ne_start hinfix hd)

end FaceCoverTwoChildMoveGeometry

/--
Two-child split geometry on nonempty cells.

This is the final-route version of `FaceCoverTwoChildMoveGeometry`: children are
nonempty by construction, and the face cover is stated only in the
parent-to-children direction because the reverse direction follows from the
proper child-face inclusions.
-/
structure PositiveFaceCoverTwoChildMoveGeometry
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (parent : PositiveCell P) where
  left : PositiveCell P
  right : PositiveCell P
  left_faces : left.cell.faces ⊂ parent.cell.faces
  right_faces : right.cell.faces ⊂ parent.cell.faces
  parent_faces_cover :
    ∀ f, f ∈ parent.cell.faces → f ∈ left.cell.faces ∨ f ∈ right.cell.faces
  head_start : datum.s left.cell = datum.s parent.cell
  linked : datum.t left.cell = datum.s right.cell
  support_inter_subset :
    left.support P ∩ right.support P ⊆ {datum.t left.cell}
  last_finish : datum.t right.cell = datum.t parent.cell

namespace PositiveFaceCoverTwoChildMoveGeometry

/--
Build positive face-cover split geometry from the finite face-set children plus
the remaining endpoint and support-intersection geometry.
-/
def ofFaceSplitChildren
    {P : PolyhedralEmbedding G}
    (datum : CellPathDatum P)
    {parent : PositiveCell P}
    (children : PositiveCell.FaceSplitChildren P parent)
    (head_start : datum.s children.left.cell = datum.s parent.cell)
    (linked : datum.t children.left.cell = datum.s children.right.cell)
    (support_inter_subset :
      children.left.support P ∩ children.right.support P ⊆
        {datum.t children.left.cell})
    (last_finish : datum.t children.right.cell = datum.t parent.cell) :
    PositiveFaceCoverTwoChildMoveGeometry P datum parent where
  left := children.left
  right := children.right
  left_faces := children.left_faces
  right_faces := children.right_faces
  parent_faces_cover := children.parent_faces_cover
  head_start := head_start
  linked := linked
  support_inter_subset := support_inter_subset
  last_finish := last_finish

/--
Build positive face-cover split geometry from the canonical one-face/erased-rest
children of a nonterminal positive cell plus the remaining endpoint and support
geometry.
-/
noncomputable def ofSplitOffFace
    {P : PolyhedralEmbedding G}
    (datum : CellPathDatum P)
    (parent : PositiveCell P)
    (hnonterminal : ¬ PositiveCell.IsSingletonFace P parent)
    (head_start :
      datum.s (PositiveCell.splitOffFace P parent hnonterminal).left.cell =
        datum.s parent.cell)
    (linked :
      datum.t (PositiveCell.splitOffFace P parent hnonterminal).left.cell =
        datum.s (PositiveCell.splitOffFace P parent hnonterminal).right.cell)
    (support_inter_subset :
      (PositiveCell.splitOffFace P parent hnonterminal).left.support P ∩
          (PositiveCell.splitOffFace P parent hnonterminal).right.support P ⊆
        {datum.t (PositiveCell.splitOffFace P parent hnonterminal).left.cell})
    (last_finish :
      datum.t (PositiveCell.splitOffFace P parent hnonterminal).right.cell =
        datum.t parent.cell) :
    PositiveFaceCoverTwoChildMoveGeometry P datum parent :=
  ofFaceSplitChildren datum (PositiveCell.splitOffFace P parent hnonterminal)
    head_start linked support_inter_subset last_finish

/-- The pointwise face-cover field derived from proper child inclusions. -/
theorem faces_cover
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent) :
    ∀ f, f ∈ parent.cell.faces ↔
      f ∈ split.left.cell.faces ∨ f ∈ split.right.cell.faces :=
  Cell.faces_cover_of_parent_subset_or P
    (fun f hf => split.left_faces.1 hf)
    (fun f hf => split.right_faces.1 hf)
    split.parent_faces_cover

/-- The child supports cover the parent support. -/
theorem support_union
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent) :
    split.left.support P ∪ split.right.support P = parent.support P := by
  simpa [PositiveCell.support] using
    Cell.support_union_of_faces_cover P split.faces_cover

/-- The support-intersection field as a pointwise overlap statement. -/
theorem consecutive_overlap
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent) :
    ∀ v, v ∈ split.left.support P → v ∈ split.right.support P →
      v = datum.t split.left.cell := by
  intro v hvleft hvright
  have hv : v ∈ split.left.support P ∩ split.right.support P := by
    exact Finset.mem_inter.2 ⟨hvleft, hvright⟩
  have hv_singleton : v ∈ ({datum.t split.left.cell} : Finset V) :=
    split.support_inter_subset hv
  simpa using hv_singleton

/-- Rank decrease for the left positive child. -/
theorem left_rank
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent) :
    PositiveCell.faceRank P split.left < PositiveCell.faceRank P parent :=
  PositiveCell.faceRank_lt_of_faces_ssubset P split.left_faces

/-- Rank decrease for the right positive child. -/
theorem right_rank
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent) :
    PositiveCell.faceRank P split.right < PositiveCell.faceRank P parent :=
  PositiveCell.faceRank_lt_of_faces_ssubset P split.right_faces

/-- Convert a positive two-child split into ordinary target-side move data. -/
def toCellMoveData
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, PositiveCell.faceRank P y < PositiveCell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y.cell) (datum.t y.cell)) :
    CellMoveData P datum parent.cell := by
  let leftSeg : CellSegmentDatum P datum :=
    { cell := split.left.cell
      path := childPath split.left split.left_rank }
  let rightSeg : CellSegmentDatum P datum :=
    { cell := split.right.cell
      path := childPath split.right split.right_rank }
  exact
    CellMoveData.ofTwoChildren P datum parent.cell leftSeg rightSeg
      split.head_start
      (by
        simpa [leftSeg, rightSeg, PositiveCell.support, PathSegment.supportUnion,
          List.append_assoc] using split.support_union)
      split.linked
      (by
        intro v hvleft hvright
        exact split.consecutive_overlap v hvleft hvright)
      split.last_finish

/-- Convert a positive two-child split into the generic move-step witness. -/
def toMoveStepData
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, PositiveCell.faceRank P y < PositiveCell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y.cell) (datum.t y.cell)) :
    OrderedSegmentFamily.MoveStepData G.Adj
      (parent.support P) (datum.s parent.cell) (datum.t parent.cell) :=
  (split.toCellMoveData childPath).toMoveStepData P datum

/--
For a positive two-child split, parent marked preservation can be proved on the
explicit concatenation of the two child path tails.
-/
theorem parentOpenOfInfixAppend
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, PositiveCell.faceRank P y < PositiveCell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y.cell) (datum.t y.cell))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s parent.cell ::
          (((childPath split.left split.left_rank).tail ++
            (childPath split.right split.right_rank).tail) ++
            [datum.s parent.cell])) :
    needle <:+:
      datum.s parent.cell ::
        (((OrderedSegmentFamily.spanningPathOfMoveStep
          (split.toMoveStepData childPath)).tail) ++ [datum.s parent.cell]) := by
  simpa [toMoveStepData, toCellMoveData, CellMoveData.spanningPath,
    CellMoveData.toMoveStepData, CellMoveData.ofTwoChildren,
    OrderedSegmentFamily.spanningPathOfMoveStep,
    OrderedSegmentFamily.spanningPathOfSplits, OrderedSegmentFamily.ofSplits,
    OrderedSegmentFamily.toChain, PathSegment.spanningPathOfChain,
    ListSpanningPath.append_of_support_inter, ListSpanningPath.append,
    CellSegmentDatum.toPathSegment, PathSegment.supportUnion,
    OrderedSegmentFamily.lastSegment] using hinfix

/-- If the mark occurs on the left child open path, it occurs on the parent append path. -/
theorem parentAppendOfLeftOpenInfix
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, PositiveCell.faceRank P y < PositiveCell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y.cell) (datum.t y.cell))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s split.left.cell :: (childPath split.left split.left_rank).tail) :
    needle <:+:
      datum.s parent.cell ::
        (((childPath split.left split.left_rank).tail ++
          (childPath split.right split.right_rank).tail) ++
          [datum.s parent.cell]) := by
  have hleft :
      needle <:+:
        datum.s split.left.cell ::
          ((childPath split.left split.left_rank).tail ++
            ((childPath split.right split.right_rank).tail ++
              [datum.s parent.cell])) :=
    List.infix_append_right
      (n := (childPath split.right split.right_rank).tail ++
        [datum.s parent.cell])
      hinfix
  simpa [split.head_start, List.append_assoc] using hleft

/-- If the mark occurs on the right child open path, it occurs on the parent append path. -/
theorem parentAppendOfRightOpenInfix
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, PositiveCell.faceRank P y < PositiveCell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y.cell) (datum.t y.cell))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s split.right.cell :: (childPath split.right split.right_rank).tail) :
    needle <:+:
      datum.s parent.cell ::
        (((childPath split.left split.left_rank).tail ++
          (childPath split.right split.right_rank).tail) ++
          [datum.s parent.cell]) := by
  have hright :
      needle <:+:
        datum.s split.right.cell ::
          ((childPath split.right split.right_rank).tail ++
            [datum.s parent.cell]) :=
    List.infix_append_right (n := [datum.s parent.cell]) hinfix
  have hend :
      endVertex (datum.s parent.cell)
          (childPath split.left split.left_rank).tail =
        datum.s split.right.cell := by
    calc
      endVertex (datum.s parent.cell)
          (childPath split.left split.left_rank).tail
          = endVertex (datum.s split.left.cell)
              (childPath split.left split.left_rank).tail := by
              rw [← split.head_start]
      _ = datum.t split.left.cell :=
              (childPath split.left split.left_rank).ends_at
      _ = datum.s split.right.cell := split.linked
  simpa [List.append_assoc] using
    (List.infix_cons_append_of_endVertex
      (xs := (childPath split.left split.left_rank).tail)
      (ys := (childPath split.right split.right_rank).tail ++
        [datum.s parent.cell])
      hend hright)

/-- Open occurrence on either positive child gives the explicit parent append infix. -/
theorem parentAppendOfChildOpenInfix
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent)
    (childPath :
      ∀ y, PositiveCell.faceRank P y < PositiveCell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y.cell) (datum.t y.cell))
    {needle : List V}
    (hinfix :
      needle <:+:
        datum.s split.left.cell :: (childPath split.left split.left_rank).tail ∨
      needle <:+:
        datum.s split.right.cell :: (childPath split.right split.right_rank).tail) :
    needle <:+:
      datum.s parent.cell ::
        (((childPath split.left split.left_rank).tail ++
          (childPath split.right split.right_rank).tail) ++
          [datum.s parent.cell]) := by
  rcases hinfix with hleft | hright
  · exact split.parentAppendOfLeftOpenInfix childPath hleft
  · exact split.parentAppendOfRightOpenInfix childPath hright

/--
For the Barnette length-four mark, it is enough to choose an active child whose
start is one of the first three marked vertices.

The recursive hypothesis gives the mark cyclically on that active child. Since
`Path3Vertices` makes `d` distinct from every vertex in `[a, b, c]`, the cyclic
occurrence opens on the chosen child and then lifts to the parent append path.
-/
theorem parentAppendOfPath4PrefixActiveChildStart
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {parent : PositiveCell P}
    (split : PositiveFaceCoverTwoChildMoveGeometry P datum parent)
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (childPath :
      ∀ y, PositiveCell.faceRank P y < PositiveCell.faceRank P parent →
        ListSpanningPath G.Adj (y.support P) (datum.s y.cell) (datum.t y.cell))
    {active : PositiveCell P → Prop}
    (active_child_start :
      (active split.left ∧ datum.s split.left.cell ∈ [a, b, c]) ∨
      (active split.right ∧ datum.s split.right.cell ∈ [a, b, c]))
    (childInfix :
      ∀ y (hy : PositiveCell.faceRank P y < PositiveCell.faceRank P parent),
        active y →
        [a, b, c, d] <:+:
          datum.s y.cell :: ((childPath y hy).tail ++ [datum.s y.cell])) :
    [a, b, c, d] <:+:
      datum.s parent.cell ::
        (((childPath split.left split.left_rank).tail ++
          (childPath split.right split.right_rank).tail) ++
          [datum.s parent.cell]) := by
  have hchild_open :
      [a, b, c, d] <:+:
        datum.s split.left.cell ::
          (childPath split.left split.left_rank).tail ∨
      [a, b, c, d] <:+:
        datum.s split.right.cell ::
          (childPath split.right split.right_rank).tail := by
    rcases active_child_start with hleft | hright
    · rcases hleft with ⟨hleft_active, hleft_start⟩
      left
      exact
        List.path4_open_of_cyclic_append_of_last_ne_start
          (childInfix split.left split.left_rank hleft_active)
          (Path3Vertices.last_ne_of_mem_prefixList hpath hleft_start)
    · rcases hright with ⟨hright_active, hright_start⟩
      right
      exact
        List.path4_open_of_cyclic_append_of_last_ne_start
          (childInfix split.right split.right_rank hright_active)
          (Path3Vertices.last_ne_of_mem_prefixList hpath hright_start)
  exact split.parentAppendOfChildOpenInfix childPath hchild_open

end PositiveFaceCoverTwoChildMoveGeometry

namespace PositiveCell

/--
Active branch generated by a two-child split and a deterministic child choice.

The root is active. Each active nonterminal parent activates exactly the child
selected by `chooseLeft`.
-/
inductive SplitActiveBranch
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    (root : PositiveCell P)
    (split :
      ∀ x, ¬ IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P datum x)
    (chooseLeft : ∀ x, ¬ IsSingletonFace P x → Bool) :
    PositiveCell P → Prop
  | root :
      SplitActiveBranch root split chooseLeft root
  | left
      {x : PositiveCell P}
      (hactive : SplitActiveBranch root split chooseLeft x)
      {hnonterminal : ¬ IsSingletonFace P x}
      (hchoose : chooseLeft x hnonterminal = true) :
      SplitActiveBranch root split chooseLeft (split x hnonterminal).left
  | right
      {x : PositiveCell P}
      (hactive : SplitActiveBranch root split chooseLeft x)
      {hnonterminal : ¬ IsSingletonFace P x}
      (hchoose : chooseLeft x hnonterminal = false) :
      SplitActiveBranch root split chooseLeft (split x hnonterminal).right

/-- The active predicate generated by a split tree and a child selector. -/
def splitActive
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    (root : PositiveCell P)
    (split :
      ∀ x, ¬ IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P datum x)
    (chooseLeft : ∀ x, ¬ IsSingletonFace P x → Bool) :
    PositiveCell P → Prop :=
  SplitActiveBranch root split chooseLeft

/-- The chosen root is active in the generated active branch. -/
theorem splitActive_root
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    (root : PositiveCell P)
    (split :
      ∀ x, ¬ IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P datum x)
    (chooseLeft : ∀ x, ¬ IsSingletonFace P x → Bool) :
    splitActive root split chooseLeft root :=
  SplitActiveBranch.root

/--
If the selected child of every active nonterminal parent starts at one of the
first three marked vertices, the generated active branch supplies the
active-child-start field required by the positive certificate constructor.
-/
theorem splitActive_child_start
    {P : PolyhedralEmbedding G}
    {datum : CellPathDatum P}
    {a b c : V}
    {root : PositiveCell P}
    {split :
      ∀ x, ¬ IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P datum x}
    {chooseLeft : ∀ x, ¬ IsSingletonFace P x → Bool}
    (selected_child_start :
      ∀ x, splitActive root split chooseLeft x →
        (hnonterminal : ¬ IsSingletonFace P x) →
        if chooseLeft x hnonterminal then
          datum.s (split x hnonterminal).left.cell ∈ [a, b, c]
        else
          datum.s (split x hnonterminal).right.cell ∈ [a, b, c]) :
    ∀ x, splitActive root split chooseLeft x →
      (hnonterminal : ¬ IsSingletonFace P x) →
        (splitActive root split chooseLeft (split x hnonterminal).left ∧
          datum.s (split x hnonterminal).left.cell ∈ [a, b, c]) ∨
        (splitActive root split chooseLeft (split x hnonterminal).right ∧
          datum.s (split x hnonterminal).right.cell ∈ [a, b, c]) := by
  intro x hactive hnonterminal
  cases hchoose : chooseLeft x hnonterminal
  · right
    exact
      ⟨SplitActiveBranch.right hactive hchoose,
        by
          simpa [hchoose] using selected_child_start x hactive hnonterminal⟩
  · left
    exact
      ⟨SplitActiveBranch.left hactive hchoose,
        by
          simpa [hchoose] using selected_child_start x hactive hnonterminal⟩

end PositiveCell

/--
Recursive marked split certificate over nonempty face-cells.

This is the repaired final-route certificate: the recursive universe excludes
the empty face-set cell, while the root and all children still use concrete
polyhedral face-support geometry.
-/
structure PositiveMarkedFaceSplitCertificate
    (P : PolyhedralEmbedding G)
    (needle : List V) where
  datum : CellPathDatum P
  faceDatum : FacePathDatum P
  hs_singleton :
    ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f
  ht_singleton :
    ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f
  root : PositiveCell P
  root_support : root.support P = (Finset.univ : Finset V)
  root_closing : G.Adj (datum.t root.cell) (datum.s root.cell)
  split :
    ∀ x, ¬ PositiveCell.IsSingletonFace P x →
      PositiveFaceCoverTwoChildMoveGeometry P datum x
  active : PositiveCell P → Prop
  root_active : active root
  terminal_boundary :
    ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
      needle <:+:
        faceDatum.s (PositiveCell.singletonFace P x hx) ::
          ((faceDatum.witness (PositiveCell.singletonFace P x hx)).middle ++
            [faceDatum.t (PositiveCell.singletonFace P x hx),
              faceDatum.s (PositiveCell.singletonFace P x hx)])
  move_preservation :
    ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
      (childPath :
        ∀ y, PositiveCell.faceRank P y < PositiveCell.faceRank P x →
          ListSpanningPath G.Adj (y.support P) (datum.s y.cell) (datum.t y.cell)) →
      (∀ y (hy : PositiveCell.faceRank P y < PositiveCell.faceRank P x), active y →
        needle <:+:
          datum.s y.cell :: ((childPath y hy).tail ++ [datum.s y.cell])) →
      needle <:+:
        datum.s x.cell ::
          (((childPath
            (split x hnonterminal).left
            (split x hnonterminal).left_rank).tail ++
            (childPath
              (split x hnonterminal).right
              (split x hnonterminal).right_rank).tail) ++
            [datum.s x.cell])

namespace PositiveMarkedFaceSplitCertificate

/-- Convert a positive split certificate to a generic concrete cell system. -/
noncomputable def toConcreteCellSystem
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (cert : PositiveMarkedFaceSplitCertificate P needle) :
    ConcreteCellSystem (Cell := PositiveCell P) (V := V) (Adj := G.Adj) where
  support := fun x => x.support P
  datum := { s := fun x => cert.datum.s x.cell, t := fun x => cert.datum.t x.cell }
  rank := PositiveCell.faceRank P
  terminal := PositiveCell.IsSingletonFace P
  terminal_witness := by
    intro x hx
    let f := PositiveCell.singletonFace P x hx
    have hcell : x.cell = Cell.singleton P f :=
      PositiveCell.eq_singleton_singletonFace P x hx
    have hs : cert.datum.s x.cell = cert.faceDatum.s f :=
      (congrArg cert.datum.s hcell).trans (cert.hs_singleton f)
    have ht : cert.datum.t x.cell = cert.faceDatum.t f :=
      (congrArg cert.datum.t hcell).trans (cert.ht_singleton f)
    simpa [PositiveCell.support, f] using
      cert.datum.terminalWitnessOfSingletonFace cert.faceDatum f hcell hs ht
  move_witness := by
    intro x hnonterminal childPath
    exact (cert.split x hnonterminal).toMoveStepData childPath

/-- Terminal-boundary data for the concrete system converted from a positive certificate. -/
theorem terminalBoundary
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (cert : PositiveMarkedFaceSplitCertificate P needle) :
    ∀ x, cert.active x →
      (hx : cert.toConcreteCellSystem.terminal x) →
        needle <:+:
          cert.toConcreteCellSystem.datum.s x ::
            ((cert.toConcreteCellSystem.terminal_witness x hx).middle ++
              [cert.toConcreteCellSystem.datum.t x,
                cert.toConcreteCellSystem.datum.s x]) := by
  intro x hactive hx
  let f := PositiveCell.singletonFace P x hx
  have hcell : x.cell = Cell.singleton P f :=
    PositiveCell.eq_singleton_singletonFace P x hx
  have hs : cert.datum.s x.cell = cert.faceDatum.s f :=
    (congrArg cert.datum.s hcell).trans (cert.hs_singleton f)
  have ht : cert.datum.t x.cell = cert.faceDatum.t f :=
    (congrArg cert.datum.t hcell).trans (cert.ht_singleton f)
  simpa [toConcreteCellSystem, PositiveCell.support, f] using
    cert.datum.terminalBoundaryInfixOfSingletonFace
      cert.faceDatum f hcell hs ht
      (cert.terminal_boundary x hactive hx)

/-- Recursive marked-move preservation for the concrete system from a positive certificate. -/
theorem moveCyclicMarkPreservation
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (cert : PositiveMarkedFaceSplitCertificate P needle) :
    cert.toConcreteCellSystem.LocalizedMoveCyclicMarkPreservation
      cert.active needle := by
  intro x hactive hnonterminal childPath childInfix
  simpa [toConcreteCellSystem] using
    (cert.split x hnonterminal).parentOpenOfInfixAppend childPath
      (cert.move_preservation x hactive hnonterminal childPath childInfix)

/-- Localized marked induction data produced by a positive split certificate. -/
noncomputable def markedInductionData
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (cert : PositiveMarkedFaceSplitCertificate P needle) :
    cert.toConcreteCellSystem.LocalizedCyclicMarkedInductionData
      cert.active needle :=
  ConcreteCellSystem.LocalizedCyclicMarkedInductionData.ofTerminalAndMovePreservation
    (ConcreteCellSystem.LocalizedTerminalCyclicMarkData.of_boundaryCycleInfix
      (by
        intro x hactive hx
        exact cert.terminalBoundary x hactive hx))
    cert.moveCyclicMarkPreservation

/-- Extract the Hamiltonian-cycle witness supplied by the positive root certificate. -/
noncomputable def existsHamiltonianCycleWitness
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (cert : PositiveMarkedFaceSplitCertificate P needle) :
    ∃ w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V),
      needle <:+: w.start :: (w.tail ++ [w.start]) := by
  classical
  let sys := cert.toConcreteCellSystem
  let marked := cert.markedInductionData
  let p :
      ListSpanningPath G.Adj
        (sys.support cert.root)
        (sys.datum.s cert.root)
        (sys.datum.t cert.root) :=
    sys.buildCellwiseLocalizedCyclicMarkedSpanningPath
      marked cert.root cert.root_active
  let wRoot : HamiltonianCycleWitness G.Adj (sys.support cert.root) :=
    hamiltonianCycleWitnessOfSpanningPath p cert.root_closing
  let w : HamiltonianCycleWitness G.Adj (Finset.univ : Finset V) :=
    wRoot.castSupport cert.root_support
  refine ⟨w, ?_⟩
  simpa [w, wRoot, p, sys, HamiltonianCycleWitness.castSupport,
    hamiltonianCycleWitnessOfSpanningPath] using
      sys.buildCellwiseLocalizedCyclicMarkedSpanningPath_infix
        marked cert.root cert.root_active

/--
The positive certificate's move-preservation field for `[a, b, c, d]` reduces
to choosing, at each active nonterminal parent, an active child whose start is
one of `a`, `b`, or `c`.
-/
theorem movePreservation_of_path4PrefixActiveChildStart
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    {datum : CellPathDatum P}
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P datum x)
    (active : PositiveCell P → Prop)
    (active_child_start :
      ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          datum.s (split x hnonterminal).left.cell ∈ [a, b, c]) ∨
        (active (split x hnonterminal).right ∧
          datum.s (split x hnonterminal).right.cell ∈ [a, b, c])) :
    ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
      (childPath :
        ∀ y, PositiveCell.faceRank P y < PositiveCell.faceRank P x →
          ListSpanningPath G.Adj (y.support P) (datum.s y.cell) (datum.t y.cell)) →
      (∀ y (hy : PositiveCell.faceRank P y < PositiveCell.faceRank P x), active y →
        [a, b, c, d] <:+:
          datum.s y.cell :: ((childPath y hy).tail ++ [datum.s y.cell])) →
      [a, b, c, d] <:+:
        datum.s x.cell ::
          (((childPath
            (split x hnonterminal).left
            (split x hnonterminal).left_rank).tail ++
            (childPath
              (split x hnonterminal).right
              (split x hnonterminal).right_rank).tail) ++
            [datum.s x.cell]) := by
  intro x hactive hnonterminal childPath childInfix
  exact
    (split x hnonterminal).parentAppendOfPath4PrefixActiveChildStart
      hpath childPath (active_child_start x hactive hnonterminal) childInfix

/--
Path-specific positive certificate constructor where the active child starts at
one of the first three vertices of the marked path.
-/
noncomputable def ofPath4PrefixActiveChildPreservation
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (hs_singleton :
      ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f)
    (ht_singleton :
      ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f)
    (root : PositiveCell P)
    (root_support : root.support P = (Finset.univ : Finset V))
    (root_closing : G.Adj (datum.t root.cell) (datum.s root.cell))
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P datum x)
    (active : PositiveCell P → Prop)
    (root_active : active root)
    (terminal_boundary :
      ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
        [a, b, c, d] <:+:
          faceDatum.s (PositiveCell.singletonFace P x hx) ::
            ((faceDatum.witness (PositiveCell.singletonFace P x hx)).middle ++
              [faceDatum.t (PositiveCell.singletonFace P x hx),
                faceDatum.s (PositiveCell.singletonFace P x hx)]))
    (active_child_start :
      ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          datum.s (split x hnonterminal).left.cell ∈ [a, b, c]) ∨
        (active (split x hnonterminal).right ∧
          datum.s (split x hnonterminal).right.cell ∈ [a, b, c])) :
    PositiveMarkedFaceSplitCertificate P [a, b, c, d] where
  datum := datum
  faceDatum := faceDatum
  hs_singleton := hs_singleton
  ht_singleton := ht_singleton
  root := root
  root_support := root_support
  root_closing := root_closing
  split := split
  active := active
  root_active := root_active
  terminal_boundary := terminal_boundary
  move_preservation :=
    movePreservation_of_path4PrefixActiveChildStart
      hpath split active active_child_start

/--
Path-specific positive certificate constructor with the root fixed to the
all-faces positive cell generated from the first marked vertex.

This removes the explicit root/support fields from the remaining full-class
target. The remaining root obligation is the closing edge for `Cell.full P`.
-/
noncomputable def ofFullRootPath4PrefixActiveChildPreservation
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (hs_singleton :
      ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f)
    (ht_singleton :
      ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f)
    (root_closing : G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P datum x)
    (active : PositiveCell P → Prop)
    (root_active : active (PositiveCell.fullOfVertex P a))
    (terminal_boundary :
      ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
        [a, b, c, d] <:+:
          faceDatum.s (PositiveCell.singletonFace P x hx) ::
            ((faceDatum.witness (PositiveCell.singletonFace P x hx)).middle ++
              [faceDatum.t (PositiveCell.singletonFace P x hx),
                faceDatum.s (PositiveCell.singletonFace P x hx)]))
    (active_child_start :
      ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          datum.s (split x hnonterminal).left.cell ∈ [a, b, c]) ∨
        (active (split x hnonterminal).right ∧
          datum.s (split x hnonterminal).right.cell ∈ [a, b, c])) :
    PositiveMarkedFaceSplitCertificate P [a, b, c, d] :=
  ofPath4PrefixActiveChildPreservation hpath datum faceDatum
    hs_singleton ht_singleton
    (PositiveCell.fullOfVertex P a)
    (PositiveCell.support_fullOfVertex P a)
    (by
      simpa using root_closing)
    split active root_active terminal_boundary active_child_start

/--
Full-root positive certificate constructor that takes the terminal face-boundary
presentations directly.

This is the constructor for the boundary-presentation step: the supplied
`FaceBoundaryPresentations` object is converted to `FacePathDatum`, so the
remaining proof does not need to rebuild terminal witnesses face by face.
-/
noncomputable def ofFullRootBoundaryPresentationsPath4PrefixActiveChildPreservation
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (datum : CellPathDatum P)
    (presentations : FaceBoundaryPresentations P)
    (hs_singleton :
      ∀ f, datum.s (Cell.singleton P f) = presentations.s f)
    (ht_singleton :
      ∀ f, datum.t (Cell.singleton P f) = presentations.t f)
    (root_closing : G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P datum x)
    (active : PositiveCell P → Prop)
    (root_active : active (PositiveCell.fullOfVertex P a))
    (terminal_boundary :
      ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
        [a, b, c, d] <:+:
          presentations.s (PositiveCell.singletonFace P x hx) ::
            (presentations.middle (PositiveCell.singletonFace P x hx) ++
              [presentations.t (PositiveCell.singletonFace P x hx),
                presentations.s (PositiveCell.singletonFace P x hx)]))
    (active_child_start :
      ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          datum.s (split x hnonterminal).left.cell ∈ [a, b, c]) ∨
        (active (split x hnonterminal).right ∧
          datum.s (split x hnonterminal).right.cell ∈ [a, b, c])) :
    PositiveMarkedFaceSplitCertificate P [a, b, c, d] :=
  ofFullRootPath4PrefixActiveChildPreservation hpath datum
    presentations.toFacePathDatum
    (by
      intro f
      simpa using hs_singleton f)
    (by
      intro f
      simpa using ht_singleton f)
    root_closing split active root_active
    (by
      intro x hactive hx
      simpa using terminal_boundary x hactive hx)
    active_child_start

/--
Full-root positive certificate constructor using singleton-compatible cell
endpoint data.

This removes the separate singleton endpoint proof fields from the caller: the
agreement with the chosen face-boundary endpoints is carried by
`CellPathDatum.SingletonCompatible`.
-/
noncomputable def ofCompatibleFullRootBoundaryPresentationsPath4PrefixActiveChildPreservation
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (presentations : FaceBoundaryPresentations P)
    (compatible : CellPathDatum.SingletonCompatible presentations)
    (root_closing :
      G.Adj (compatible.datum.t (Cell.full P))
        (compatible.datum.s (Cell.full P)))
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P compatible.datum x)
    (active : PositiveCell P → Prop)
    (root_active : active (PositiveCell.fullOfVertex P a))
    (terminal_boundary :
      ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
        [a, b, c, d] <:+:
          presentations.s (PositiveCell.singletonFace P x hx) ::
            (presentations.middle (PositiveCell.singletonFace P x hx) ++
              [presentations.t (PositiveCell.singletonFace P x hx),
                presentations.s (PositiveCell.singletonFace P x hx)]))
    (active_child_start :
      ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          compatible.datum.s (split x hnonterminal).left.cell ∈ [a, b, c]) ∨
        (active (split x hnonterminal).right ∧
          compatible.datum.s (split x hnonterminal).right.cell ∈ [a, b, c])) :
    PositiveMarkedFaceSplitCertificate P [a, b, c, d] :=
  ofFullRootBoundaryPresentationsPath4PrefixActiveChildPreservation hpath
    compatible.datum presentations compatible.s_singleton
    compatible.t_singleton root_closing split active root_active
    terminal_boundary active_child_start

/--
Full-root positive certificate constructor using endpoint data that already
chooses the all-faces positive root, proves root support, and closes the root
cycle along the first edge of `[a,b,c,d]`.
-/
noncomputable def ofFullRootCompatibleBoundaryPresentationsPath4PrefixActiveChildPreservation
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (presentations : FaceBoundaryPresentations P)
    (compatible :
      CellPathDatum.FullRootSingletonCompatible presentations hpath)
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P compatible.datum x)
    (active : PositiveCell P → Prop)
    (root_active : active (PositiveCell.fullOfVertex P a))
    (terminal_boundary :
      ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
        [a, b, c, d] <:+:
          presentations.s (PositiveCell.singletonFace P x hx) ::
            (presentations.middle (PositiveCell.singletonFace P x hx) ++
              [presentations.t (PositiveCell.singletonFace P x hx),
                presentations.s (PositiveCell.singletonFace P x hx)]))
    (active_child_start :
      ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          compatible.datum.s (split x hnonterminal).left.cell ∈ [a, b, c]) ∨
        (active (split x hnonterminal).right ∧
          compatible.datum.s (split x hnonterminal).right.cell ∈ [a, b, c])) :
    PositiveMarkedFaceSplitCertificate P [a, b, c, d] :=
  ofPath4PrefixActiveChildPreservation hpath compatible.datum
    presentations.toFacePathDatum compatible.s_singleton
    compatible.t_singleton (PositiveCell.fullOfVertex P a)
    compatible.root_support compatible.root_closing split active root_active
    (by
      intro x hactive hx
      simpa using terminal_boundary x hactive hx)
    active_child_start

/--
Full-root positive certificate constructor using a generated active branch.

The active predicate is `PositiveCell.splitActive` for the supplied child
selector, so root activity is automatic. The caller only proves that the
selected child of each active nonterminal parent starts at one of `a`, `b`, or
`c`.
-/
noncomputable def ofFullRootCompatibleBoundaryPresentationsBranchChoicePath4Prefix
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (presentations : FaceBoundaryPresentations P)
    (compatible :
      CellPathDatum.FullRootSingletonCompatible presentations hpath)
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P compatible.datum x)
    (chooseLeft :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x → Bool)
    (terminal_boundary :
      ∀ x,
        PositiveCell.splitActive
          (PositiveCell.fullOfVertex P a) split chooseLeft x →
        (hx : PositiveCell.IsSingletonFace P x) →
          [a, b, c, d] <:+:
            presentations.s (PositiveCell.singletonFace P x hx) ::
              (presentations.middle (PositiveCell.singletonFace P x hx) ++
                [presentations.t (PositiveCell.singletonFace P x hx),
                  presentations.s (PositiveCell.singletonFace P x hx)]))
    (selected_child_start :
      ∀ x,
        PositiveCell.splitActive
          (PositiveCell.fullOfVertex P a) split chooseLeft x →
        (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        if chooseLeft x hnonterminal then
          compatible.datum.s (split x hnonterminal).left.cell ∈ [a, b, c]
        else
          compatible.datum.s (split x hnonterminal).right.cell ∈ [a, b, c]) :
    PositiveMarkedFaceSplitCertificate P [a, b, c, d] :=
  ofFullRootCompatibleBoundaryPresentationsPath4PrefixActiveChildPreservation
    hpath presentations compatible split
    (PositiveCell.splitActive
      (PositiveCell.fullOfVertex P a) split chooseLeft)
    (PositiveCell.splitActive_root
      (PositiveCell.fullOfVertex P a) split chooseLeft)
    terminal_boundary
    (PositiveCell.splitActive_child_start selected_child_start)

/--
Generated-branch constructor whose terminal singleton obligation is stated on
the recorded face-boundary vertices.

The boundary-presentation equality then converts those proofs to the chosen
cyclic boundary lists required by the certificate.
-/
noncomputable def ofFullRootCompatibleBoundaryPresentationsBranchChoicePath4PrefixOfBoundaryVertices
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (presentations : FaceBoundaryPresentations P)
    (compatible :
      CellPathDatum.FullRootSingletonCompatible presentations hpath)
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P compatible.datum x)
    (chooseLeft :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x → Bool)
    (terminal_boundary_vertices :
      ∀ x,
        PositiveCell.splitActive
          (PositiveCell.fullOfVertex P a) split chooseLeft x →
        (hx : PositiveCell.IsSingletonFace P x) →
          [a, b, c, d] <:+:
            (P.boundary (PositiveCell.singletonFace P x hx)).vertices)
    (selected_child_start :
      ∀ x,
        PositiveCell.splitActive
          (PositiveCell.fullOfVertex P a) split chooseLeft x →
        (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        if chooseLeft x hnonterminal then
          compatible.datum.s (split x hnonterminal).left.cell ∈ [a, b, c]
        else
          compatible.datum.s (split x hnonterminal).right.cell ∈ [a, b, c]) :
    PositiveMarkedFaceSplitCertificate P [a, b, c, d] :=
  ofFullRootCompatibleBoundaryPresentationsBranchChoicePath4Prefix
    hpath presentations compatible split chooseLeft
    (presentations.activeSingletonBoundaryInfix_of_boundary_vertices
      terminal_boundary_vertices)
    selected_child_start

/--
Full-root positive certificate constructor that starts from arbitrary cell
endpoint data and forces singleton compatibility before using it.
-/
noncomputable def ofBaseDatumFullRootBoundaryPresentationsPath4PrefixActiveChildPreservation
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (presentations : FaceBoundaryPresentations P)
    (baseDatum : CellPathDatum P)
    (root_closing :
      G.Adj
        ((CellPathDatum.withSingletonFaceEndpoints presentations baseDatum).t
          (Cell.full P))
        ((CellPathDatum.withSingletonFaceEndpoints presentations baseDatum).s
          (Cell.full P)))
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P
          (CellPathDatum.withSingletonFaceEndpoints presentations baseDatum) x)
    (active : PositiveCell P → Prop)
    (root_active : active (PositiveCell.fullOfVertex P a))
    (terminal_boundary :
      ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
        [a, b, c, d] <:+:
          presentations.s (PositiveCell.singletonFace P x hx) ::
            (presentations.middle (PositiveCell.singletonFace P x hx) ++
              [presentations.t (PositiveCell.singletonFace P x hx),
                presentations.s (PositiveCell.singletonFace P x hx)]))
    (active_child_start :
      ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          (CellPathDatum.withSingletonFaceEndpoints presentations baseDatum).s
            (split x hnonterminal).left.cell ∈ [a, b, c]) ∨
        (active (split x hnonterminal).right ∧
          (CellPathDatum.withSingletonFaceEndpoints presentations baseDatum).s
            (split x hnonterminal).right.cell ∈ [a, b, c])) :
    PositiveMarkedFaceSplitCertificate P [a, b, c, d] :=
  ofCompatibleFullRootBoundaryPresentationsPath4PrefixActiveChildPreservation
    hpath presentations
    (CellPathDatum.SingletonCompatible.ofBase presentations baseDatum)
    root_closing split active root_active terminal_boundary active_child_start

/--
Full-root positive certificate constructor that starts from arbitrary endpoint
data and forces both singleton compatibility and the all-faces root closing edge.
-/
noncomputable def ofBaseDatumFullRootCompatibleBoundaryPresentationsPath4PrefixActiveChildPreservation
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (presentations : FaceBoundaryPresentations P)
    (baseDatum : CellPathDatum P)
    (split :
      ∀ x, ¬ PositiveCell.IsSingletonFace P x →
        PositiveFaceCoverTwoChildMoveGeometry P
          (CellPathDatum.FullRootSingletonCompatible.ofBase
            presentations hpath baseDatum).datum x)
    (active : PositiveCell P → Prop)
    (root_active : active (PositiveCell.fullOfVertex P a))
    (terminal_boundary :
      ∀ x, active x → (hx : PositiveCell.IsSingletonFace P x) →
        [a, b, c, d] <:+:
          presentations.s (PositiveCell.singletonFace P x hx) ::
            (presentations.middle (PositiveCell.singletonFace P x hx) ++
              [presentations.t (PositiveCell.singletonFace P x hx),
                presentations.s (PositiveCell.singletonFace P x hx)]))
    (active_child_start :
      ∀ x, active x → (hnonterminal : ¬ PositiveCell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          (CellPathDatum.FullRootSingletonCompatible.ofBase
            presentations hpath baseDatum).datum.s
              (split x hnonterminal).left.cell ∈ [a, b, c]) ∨
        (active (split x hnonterminal).right ∧
          (CellPathDatum.FullRootSingletonCompatible.ofBase
            presentations hpath baseDatum).datum.s
              (split x hnonterminal).right.cell ∈ [a, b, c])) :
    PositiveMarkedFaceSplitCertificate P [a, b, c, d] :=
  ofFullRootCompatibleBoundaryPresentationsPath4PrefixActiveChildPreservation
    hpath presentations
    (CellPathDatum.FullRootSingletonCompatible.ofBase
      presentations hpath baseDatum)
    split active root_active terminal_boundary active_child_start

end PositiveMarkedFaceSplitCertificate

/-- Build a nonterminal move field from rank-decreasing two-child splits. -/
def CellMoveData.ofTwoChildSplits
    {P : PolyhedralEmbedding G}
    (datum : CellPathDatum P)
    (rank : Cell P → Nat)
    {terminal : Cell P → Prop}
    (split : ∀ x, ¬ terminal x → TwoChildMoveGeometry P datum rank x) :
    ∀ x, ¬ terminal x →
      (∀ y, rank y < rank x →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      CellMoveData P datum x :=
  fun x hnonterminal childPath =>
    (split x hnonterminal).toCellMoveData childPath

/--
Direct Hamiltonicity theorem for the two-child target-side move.
-/
theorem hamiltonianOfTwoChildMove
    (P : PolyhedralEmbedding G)
    (datum : CellPathDatum P)
    (parent : Cell P)
    (left right : CellSegmentDatum P datum)
    (hstart : datum.s left.cell = datum.s parent)
    (hsupport :
      PathSegment.supportUnion
        [left.toPathSegment P datum, right.toPathSegment P datum] =
          parent.support P)
    (hlink : datum.t left.cell = datum.s right.cell)
    (hoverlap :
      ∀ v, v ∈ left.cell.support P → v ∈ right.cell.support P → v = datum.t left.cell)
    (hfinish : datum.t right.cell = datum.t parent)
    (hclose : G.Adj (datum.t parent) (datum.s parent)) :
    HamiltonianOn (parent.support P) G.Adj := by
  have step : CellMoveData P datum parent :=
    CellMoveData.ofTwoChildren P datum parent left right hstart hsupport hlink hoverlap hfinish
  exact CellMoveData.hamiltonianOfClosingEdge P datum step hclose

/--
Target-side localized open-boundary cell-system data.

This is the graph-generic form of the direct Barnette provider: moves are stated
using `CellMoveData` on actual polyhedral cells, while the conversion to the
generic `ConcreteCellSystem` is handled once below.
-/
structure LocalizedOpenBoundaryCellSystem
    (P : PolyhedralEmbedding G)
    (needle : List V) where
  datum : CellPathDatum P
  rank : Cell P → Nat
  terminal : Cell P → Prop
  terminal_witness :
    ∀ x, terminal x →
      OrderedSegmentFamily.BoundaryCycleWitness G.Adj
        (x.support P) (datum.s x) (datum.t x)
  move_data :
    ∀ x, ¬ terminal x →
      (∀ y, rank y < rank x →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      CellMoveData P datum x
  root : Cell P
  root_support : root.support P = (Finset.univ : Finset V)
  root_closing : G.Adj (datum.t root) (datum.s root)
  active : Cell P → Prop
  root_active : active root
  terminal_boundary :
    ∀ x, active x → (hx : terminal x) →
      needle <:+:
        datum.s x ::
          ((terminal_witness x hx).middle ++
            [datum.t x, datum.s x])
  parent_open :
    ∀ x, active x → (hnonterminal : ¬ terminal x) →
      (childPath :
        ∀ y, rank y < rank x →
          ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      needle <:+:
        datum.s x ::
          (((move_data x hnonterminal childPath).spanningPath P datum).tail ++
            [datum.s x])

/--
Localized open-boundary cell-system data with the root fixed to the all-faces
cell.

Compared with `LocalizedOpenBoundaryCellSystem`, this removes the root-cell and
root-support fields: the support proof follows from `Cell.support_full`.
-/
structure AllFacesRootLocalizedOpenBoundaryCellSystem
    (P : PolyhedralEmbedding G)
    (needle : List V) where
  datum : CellPathDatum P
  rank : Cell P → Nat
  terminal : Cell P → Prop
  terminal_witness :
    ∀ x, terminal x →
      OrderedSegmentFamily.BoundaryCycleWitness G.Adj
        (x.support P) (datum.s x) (datum.t x)
  move_data :
    ∀ x, ¬ terminal x →
      (∀ y, rank y < rank x →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      CellMoveData P datum x
  root_closing :
    G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P))
  active : Cell P → Prop
  root_active : active (Cell.full P)
  terminal_boundary :
    ∀ x, active x → (hx : terminal x) →
      needle <:+:
        datum.s x ::
          ((terminal_witness x hx).middle ++
            [datum.t x, datum.s x])
  parent_open :
    ∀ x, active x → (hnonterminal : ¬ terminal x) →
      (childPath :
        ∀ y, rank y < rank x →
          ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      needle <:+:
        datum.s x ::
          (((move_data x hnonterminal childPath).spanningPath P datum).tail ++
            [datum.s x])

/--
Target-side localized marked cell-system data.

Unlike `LocalizedOpenBoundaryCellSystem`, the nonterminal marked proof receives
the recursive marked-path hypotheses for active lower-rank children. This is the
direct shape of the ranked cell-system recursion.
-/
structure LocalizedMarkedBoundaryCellSystem
    (P : PolyhedralEmbedding G)
    (needle : List V) where
  datum : CellPathDatum P
  rank : Cell P → Nat
  terminal : Cell P → Prop
  terminal_witness :
    ∀ x, terminal x →
      OrderedSegmentFamily.BoundaryCycleWitness G.Adj
        (x.support P) (datum.s x) (datum.t x)
  move_data :
    ∀ x, ¬ terminal x →
      (∀ y, rank y < rank x →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      CellMoveData P datum x
  root : Cell P
  root_support : root.support P = (Finset.univ : Finset V)
  root_closing : G.Adj (datum.t root) (datum.s root)
  active : Cell P → Prop
  root_active : active root
  terminal_boundary :
    ∀ x, active x → (hx : terminal x) →
      needle <:+:
        datum.s x ::
          ((terminal_witness x hx).middle ++
            [datum.t x, datum.s x])
  move_preservation :
    ∀ x, active x → (hnonterminal : ¬ terminal x) →
      (childPath :
        ∀ y, rank y < rank x →
          ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      (∀ y (hy : rank y < rank x), active y →
        needle <:+:
          datum.s y :: ((childPath y hy).tail ++ [datum.s y])) →
      needle <:+:
        datum.s x ::
          (((move_data x hnonterminal childPath).spanningPath P datum).tail ++
            [datum.s x])

/--
Localized marked cell-system data with the root fixed to the all-faces cell.

This is the recursive sibling of
`AllFacesRootLocalizedOpenBoundaryCellSystem`: nonterminal marked preservation
may use active child marked-path hypotheses.
-/
structure AllFacesRootLocalizedMarkedBoundaryCellSystem
    (P : PolyhedralEmbedding G)
    (needle : List V) where
  datum : CellPathDatum P
  rank : Cell P → Nat
  terminal : Cell P → Prop
  terminal_witness :
    ∀ x, terminal x →
      OrderedSegmentFamily.BoundaryCycleWitness G.Adj
        (x.support P) (datum.s x) (datum.t x)
  move_data :
    ∀ x, ¬ terminal x →
      (∀ y, rank y < rank x →
        ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      CellMoveData P datum x
  root_closing :
    G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P))
  active : Cell P → Prop
  root_active : active (Cell.full P)
  terminal_boundary :
    ∀ x, active x → (hx : terminal x) →
      needle <:+:
        datum.s x ::
          ((terminal_witness x hx).middle ++
            [datum.t x, datum.s x])
  move_preservation :
    ∀ x, active x → (hnonterminal : ¬ terminal x) →
      (childPath :
        ∀ y, rank y < rank x →
          ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      (∀ y (hy : rank y < rank x), active y →
        needle <:+:
          datum.s y :: ((childPath y hy).tail ++ [datum.s y])) →
      needle <:+:
        datum.s x ::
          (((move_data x hnonterminal childPath).spanningPath P datum).tail ++
            [datum.s x])

namespace AllFacesRootLocalizedMarkedBoundaryCellSystem

/-- Reinsert the standard all-faces root fields. -/
def toLocalizedMarkedBoundaryCellSystem
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (inputs : AllFacesRootLocalizedMarkedBoundaryCellSystem P needle) :
    LocalizedMarkedBoundaryCellSystem P needle where
  datum := inputs.datum
  rank := inputs.rank
  terminal := inputs.terminal
  terminal_witness := inputs.terminal_witness
  move_data := inputs.move_data
  root := Cell.full P
  root_support := Cell.support_full P
  root_closing := inputs.root_closing
  active := inputs.active
  root_active := inputs.root_active
  terminal_boundary := inputs.terminal_boundary
  move_preservation := inputs.move_preservation

end AllFacesRootLocalizedMarkedBoundaryCellSystem

namespace LocalizedMarkedBoundaryCellSystem

/-- Convert target-side recursive marked data into the generic concrete cell system. -/
def toConcreteCellSystem
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (inputs : LocalizedMarkedBoundaryCellSystem P needle) :
    ConcreteCellSystem (Cell := Cell P) (V := V) (Adj := G.Adj) where
  support := fun x => x.support P
  datum := { s := inputs.datum.s, t := inputs.datum.t }
  rank := inputs.rank
  terminal := inputs.terminal
  terminal_witness := by
    intro x hx
    exact inputs.terminal_witness x hx
  move_witness := by
    intro x hnonterminal childPath
    exact (inputs.move_data x hnonterminal childPath).toMoveStepData P inputs.datum

/-- Terminal-boundary data for the converted concrete system. -/
theorem terminalBoundary
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (inputs : LocalizedMarkedBoundaryCellSystem P needle) :
    ∀ x, inputs.active x →
      (hx : inputs.toConcreteCellSystem.terminal x) →
        needle <:+:
          inputs.toConcreteCellSystem.datum.s x ::
            ((inputs.toConcreteCellSystem.terminal_witness x hx).middle ++
              [inputs.toConcreteCellSystem.datum.t x,
                inputs.toConcreteCellSystem.datum.s x]) := by
  intro x hactive hx
  simpa [toConcreteCellSystem] using
    inputs.terminal_boundary x hactive hx

/-- Recursive marked-move preservation for the converted concrete system. -/
theorem moveCyclicMarkPreservation
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (inputs : LocalizedMarkedBoundaryCellSystem P needle) :
    inputs.toConcreteCellSystem.LocalizedMoveCyclicMarkPreservation
      inputs.active needle := by
  intro x hactive hnonterminal childPath childInfix
  simpa [toConcreteCellSystem, CellMoveData.spanningPath] using
    inputs.move_preservation x hactive hnonterminal childPath childInfix

end LocalizedMarkedBoundaryCellSystem

namespace AllFacesRootLocalizedMarkedBoundaryCellSystem

/--
Default-rank recursive constructor where support coverage is supplied as a
face-set cover.

This is the genuinely recursive all-faces-root surface: the nonterminal move
proof receives active child marked-path hypotheses, instead of proving the mark
for arbitrary child paths.
-/
noncomputable def ofFaceCountRankedFaceCoverTwoChildDecomposition
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (hs_singleton :
      ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f)
    (ht_singleton :
      ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f)
    (split :
      ∀ x, ¬ Cell.IsSingletonFace P x →
        FaceCoverTwoChildMoveGeometry P datum x)
    (root_closing :
      G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (active : Cell P → Prop)
    (root_active : active (Cell.full P))
    (terminal_boundary :
      ∀ x, active x → (hx : Cell.IsSingletonFace P x) →
        needle <:+:
          faceDatum.s (Cell.singletonFace P x hx) ::
            ((faceDatum.witness (Cell.singletonFace P x hx)).middle ++
              [faceDatum.t (Cell.singletonFace P x hx),
                faceDatum.s (Cell.singletonFace P x hx)]))
    (move_preservation :
      ∀ x, active x → (hnonterminal : ¬ Cell.IsSingletonFace P x) →
        (childPath :
          ∀ y, Cell.faceRank P y < Cell.faceRank P x →
            ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
        (∀ y (hy : Cell.faceRank P y < Cell.faceRank P x), active y →
          needle <:+:
            datum.s y :: ((childPath y hy).tail ++ [datum.s y])) →
        needle <:+:
          datum.s x ::
            (((childPath
              (split x hnonterminal).left
              (Cell.faceRank_lt_of_faces_ssubset P
                (split x hnonterminal).left_faces)).tail ++
              (childPath
                (split x hnonterminal).right
                (Cell.faceRank_lt_of_faces_ssubset P
                  (split x hnonterminal).right_faces)).tail) ++
              [datum.s x])) :
    AllFacesRootLocalizedMarkedBoundaryCellSystem P needle where
  datum := datum
  rank := Cell.faceRank P
  terminal := Cell.IsSingletonFace P
  terminal_witness :=
    CellPathDatum.terminalWitnessesOfSingletonFaces
      datum faceDatum (Cell.singletonFace P)
      (Cell.eq_singleton_singletonFace P)
      (by
        intro x hx
        exact
          (congrArg datum.s (Cell.eq_singleton_singletonFace P x hx)).trans
            (hs_singleton (Cell.singletonFace P x hx)))
      (by
        intro x hx
        exact
          (congrArg datum.t (Cell.eq_singleton_singletonFace P x hx)).trans
            (ht_singleton (Cell.singletonFace P x hx)))
  move_data := by
    intro x hnonterminal childPath
    exact (split x hnonterminal).toTwoChildMoveGeometry.toCellMoveData childPath
  root_closing := root_closing
  active := active
  root_active := root_active
  terminal_boundary :=
    CellPathDatum.terminalBoundaryInfixOfSingletonFaces
      datum faceDatum (Cell.singletonFace P)
      (Cell.eq_singleton_singletonFace P)
      (by
        intro x hx
        exact
          (congrArg datum.s (Cell.eq_singleton_singletonFace P x hx)).trans
            (hs_singleton (Cell.singletonFace P x hx)))
      (by
        intro x hx
        exact
          (congrArg datum.t (Cell.eq_singleton_singletonFace P x hx)).trans
            (ht_singleton (Cell.singletonFace P x hx)))
      terminal_boundary
  move_preservation := by
    intro x hactive hnonterminal childPath childInfix
    exact
      (split x hnonterminal).parentOpenOfInfixAppend childPath
        (move_preservation x hactive hnonterminal childPath childInfix)

end AllFacesRootLocalizedMarkedBoundaryCellSystem

/--
Named certificate for the remaining planar geometry in the recursive all-faces
route.

The fields are the concrete choices consumed by
`AllFacesRootLocalizedMarkedBoundaryCellSystem.ofFaceCountRankedFaceCoverTwoChildDecomposition`:
singleton face terminals, face-cover two-child splits, root closing data, and
recursive marked preservation for active children.
-/
structure MarkedFaceSplitCertificate
    (P : PolyhedralEmbedding G)
    (needle : List V) where
  datum : CellPathDatum P
  faceDatum : FacePathDatum P
  hs_singleton :
    ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f
  ht_singleton :
    ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f
  split :
    ∀ x, ¬ Cell.IsSingletonFace P x →
      FaceCoverTwoChildMoveGeometry P datum x
  root_closing :
    G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P))
  active : Cell P → Prop
  root_active : active (Cell.full P)
  terminal_boundary :
    ∀ x, active x → (hx : Cell.IsSingletonFace P x) →
      needle <:+:
        faceDatum.s (Cell.singletonFace P x hx) ::
          ((faceDatum.witness (Cell.singletonFace P x hx)).middle ++
            [faceDatum.t (Cell.singletonFace P x hx),
              faceDatum.s (Cell.singletonFace P x hx)])
  move_preservation :
    ∀ x, active x → (hnonterminal : ¬ Cell.IsSingletonFace P x) →
      (childPath :
        ∀ y, Cell.faceRank P y < Cell.faceRank P x →
          ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
      (∀ y (hy : Cell.faceRank P y < Cell.faceRank P x), active y →
        needle <:+:
          datum.s y :: ((childPath y hy).tail ++ [datum.s y])) →
      needle <:+:
        datum.s x ::
          (((childPath
            (split x hnonterminal).left
            (Cell.faceRank_lt_of_faces_ssubset P
              (split x hnonterminal).left_faces)).tail ++
            (childPath
              (split x hnonterminal).right
              (Cell.faceRank_lt_of_faces_ssubset P
                (split x hnonterminal).right_faces)).tail) ++
            [datum.s x])

namespace MarkedFaceSplitCertificate

/--
Build the recursive split certificate when nonterminal marked preservation is
proved by showing that the marked word lies on one of the two child open paths.

This factors the pure list transport out of the remaining planar work. The
geometric obligation is to choose splits and active children so that the mark
does not use the child closing edge at each recursive step.
-/
noncomputable def ofChildOpenPreservation
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (hs_singleton :
      ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f)
    (ht_singleton :
      ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f)
    (split :
      ∀ x, ¬ Cell.IsSingletonFace P x →
        FaceCoverTwoChildMoveGeometry P datum x)
    (root_closing :
      G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (active : Cell P → Prop)
    (root_active : active (Cell.full P))
    (terminal_boundary :
      ∀ x, active x → (hx : Cell.IsSingletonFace P x) →
        needle <:+:
          faceDatum.s (Cell.singletonFace P x hx) ::
            ((faceDatum.witness (Cell.singletonFace P x hx)).middle ++
              [faceDatum.t (Cell.singletonFace P x hx),
                faceDatum.s (Cell.singletonFace P x hx)]))
    (move_child_open :
      ∀ x, active x → (hnonterminal : ¬ Cell.IsSingletonFace P x) →
        (childPath :
          ∀ y, Cell.faceRank P y < Cell.faceRank P x →
            ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
        (∀ y (hy : Cell.faceRank P y < Cell.faceRank P x), active y →
          needle <:+:
            datum.s y :: ((childPath y hy).tail ++ [datum.s y])) →
        needle <:+:
          datum.s (split x hnonterminal).left ::
            (childPath
              (split x hnonterminal).left
              (Cell.faceRank_lt_of_faces_ssubset P
                (split x hnonterminal).left_faces)).tail ∨
        needle <:+:
          datum.s (split x hnonterminal).right ::
            (childPath
              (split x hnonterminal).right
              (Cell.faceRank_lt_of_faces_ssubset P
                (split x hnonterminal).right_faces)).tail) :
    MarkedFaceSplitCertificate P needle where
  datum := datum
  faceDatum := faceDatum
  hs_singleton := hs_singleton
  ht_singleton := ht_singleton
  split := split
  root_closing := root_closing
  active := active
  root_active := root_active
  terminal_boundary := terminal_boundary
  move_preservation := by
    intro x hactive hnonterminal childPath childInfix
    exact
      (split x hnonterminal).parentAppendOfChildOpenInfix childPath
        (move_child_open x hactive hnonterminal childPath childInfix)

/--
Specialized constructor for the Barnette path mark `[a, b, c, d]`.

At a nonterminal active cell it is enough to pick an active child whose start is
not `d`: the recursive cyclic marked-path hypothesis for that child is then an
open occurrence, and the two-child append lemmas lift it to the parent.
-/
noncomputable def ofPath4ActiveChildPreservation
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (hs_singleton :
      ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f)
    (ht_singleton :
      ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f)
    (split :
      ∀ x, ¬ Cell.IsSingletonFace P x →
        FaceCoverTwoChildMoveGeometry P datum x)
    (root_closing :
      G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (active : Cell P → Prop)
    (root_active : active (Cell.full P))
    (terminal_boundary :
      ∀ x, active x → (hx : Cell.IsSingletonFace P x) →
        [a, b, c, d] <:+:
          faceDatum.s (Cell.singletonFace P x hx) ::
            ((faceDatum.witness (Cell.singletonFace P x hx)).middle ++
              [faceDatum.t (Cell.singletonFace P x hx),
                faceDatum.s (Cell.singletonFace P x hx)]))
    (active_child :
      ∀ x, active x → (hnonterminal : ¬ Cell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          d ≠ datum.s (split x hnonterminal).left) ∨
        (active (split x hnonterminal).right ∧
          d ≠ datum.s (split x hnonterminal).right)) :
    MarkedFaceSplitCertificate P [a, b, c, d] :=
  ofChildOpenPreservation datum faceDatum hs_singleton ht_singleton split
    root_closing active root_active terminal_boundary
    (by
      intro x hactive hnonterminal childPath childInfix
      rcases active_child x hactive hnonterminal with hleft | hright
      · rcases hleft with ⟨hleft_active, hleft_start⟩
        left
        exact
          List.path4_open_of_cyclic_append_of_last_ne_start
            (childInfix (split x hnonterminal).left
              (Cell.faceRank_lt_of_faces_ssubset P
                (split x hnonterminal).left_faces)
              hleft_active)
            hleft_start
      · rcases hright with ⟨hright_active, hright_start⟩
        right
        exact
          List.path4_open_of_cyclic_append_of_last_ne_start
            (childInfix (split x hnonterminal).right
              (Cell.faceRank_lt_of_faces_ssubset P
                (split x hnonterminal).right_faces)
              hright_active)
            hright_start)

/--
Path-specific constructor where the active child is required to start at one of
the first three vertices of the marked path. Distinctness in `Path3Vertices`
then proves the child-start avoidance condition needed by
`ofPath4ActiveChildPreservation`.
-/
noncomputable def ofPath4PrefixActiveChildPreservation
    {P : PolyhedralEmbedding G}
    {a b c d : V}
    (hpath : Path3Vertices G a b c d)
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (hs_singleton :
      ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f)
    (ht_singleton :
      ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f)
    (split :
      ∀ x, ¬ Cell.IsSingletonFace P x →
        FaceCoverTwoChildMoveGeometry P datum x)
    (root_closing :
      G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (active : Cell P → Prop)
    (root_active : active (Cell.full P))
    (terminal_boundary :
      ∀ x, active x → (hx : Cell.IsSingletonFace P x) →
        [a, b, c, d] <:+:
          faceDatum.s (Cell.singletonFace P x hx) ::
            ((faceDatum.witness (Cell.singletonFace P x hx)).middle ++
              [faceDatum.t (Cell.singletonFace P x hx),
                faceDatum.s (Cell.singletonFace P x hx)]))
    (active_child_start :
      ∀ x, active x → (hnonterminal : ¬ Cell.IsSingletonFace P x) →
        (active (split x hnonterminal).left ∧
          datum.s (split x hnonterminal).left ∈ [a, b, c]) ∨
        (active (split x hnonterminal).right ∧
          datum.s (split x hnonterminal).right ∈ [a, b, c])) :
    MarkedFaceSplitCertificate P [a, b, c, d] :=
  ofPath4ActiveChildPreservation datum faceDatum hs_singleton ht_singleton
    split root_closing active root_active terminal_boundary
    (by
      intro x hactive hnonterminal
      rcases active_child_start x hactive hnonterminal with hleft | hright
      · rcases hleft with ⟨hleft_active, hleft_start⟩
        exact Or.inl
          ⟨hleft_active,
            Path3Vertices.last_ne_of_mem_prefixList hpath hleft_start⟩
      · rcases hright with ⟨hright_active, hright_start⟩
        exact Or.inr
          ⟨hright_active,
            Path3Vertices.last_ne_of_mem_prefixList hpath hright_start⟩)

/-- Convert the named split certificate into the recursive all-faces cell-system input. -/
noncomputable def toAllFacesRootLocalizedMarkedBoundaryCellSystem
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (cert : MarkedFaceSplitCertificate P needle) :
    AllFacesRootLocalizedMarkedBoundaryCellSystem P needle :=
  AllFacesRootLocalizedMarkedBoundaryCellSystem.ofFaceCountRankedFaceCoverTwoChildDecomposition
    cert.datum cert.faceDatum cert.hs_singleton cert.ht_singleton cert.split
    cert.root_closing cert.active cert.root_active cert.terminal_boundary
    cert.move_preservation

/-- Convert the named split certificate into the general localized marked input. -/
noncomputable def toLocalizedMarkedBoundaryCellSystem
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (cert : MarkedFaceSplitCertificate P needle) :
    LocalizedMarkedBoundaryCellSystem P needle :=
  cert.toAllFacesRootLocalizedMarkedBoundaryCellSystem.toLocalizedMarkedBoundaryCellSystem

end MarkedFaceSplitCertificate

namespace AllFacesRootLocalizedOpenBoundaryCellSystem

/--
Build all-faces-root localized open-boundary data when terminal cells are
singleton faces.

This removes two fields from the concrete recursive construction: the terminal
boundary witnesses and the active-terminal boundary infix obligations are both
derived from the chosen face-boundary presentations.
-/
def ofSingletonTerminalFaces
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (rank : Cell P → Nat)
    (terminal : Cell P → Prop)
    (faceOf : ∀ x, terminal x → P.Face)
    (hcell : ∀ x hx, x = Cell.singleton P (faceOf x hx))
    (hs : ∀ x hx, datum.s x = faceDatum.s (faceOf x hx))
    (ht : ∀ x hx, datum.t x = faceDatum.t (faceOf x hx))
    (move_data :
      ∀ x, ¬ terminal x →
        (∀ y, rank y < rank x →
          ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
        CellMoveData P datum x)
    (root_closing :
      G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (active : Cell P → Prop)
    (root_active : active (Cell.full P))
    (terminal_boundary :
      ∀ x, active x → (hx : terminal x) →
        needle <:+:
          faceDatum.s (faceOf x hx) ::
            ((faceDatum.witness (faceOf x hx)).middle ++
              [faceDatum.t (faceOf x hx), faceDatum.s (faceOf x hx)]))
    (parent_open :
      ∀ x, active x → (hnonterminal : ¬ terminal x) →
        (childPath :
          ∀ y, rank y < rank x →
            ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
        needle <:+:
          datum.s x ::
            (((move_data x hnonterminal childPath).spanningPath P datum).tail ++
              [datum.s x])) :
    AllFacesRootLocalizedOpenBoundaryCellSystem P needle where
  datum := datum
  rank := rank
  terminal := terminal
  terminal_witness :=
    CellPathDatum.terminalWitnessesOfSingletonFaces
      datum faceDatum faceOf hcell hs ht
  move_data := move_data
  root_closing := root_closing
  active := active
  root_active := root_active
  terminal_boundary :=
    CellPathDatum.terminalBoundaryInfixOfSingletonFaces
      datum faceDatum faceOf hcell hs ht terminal_boundary
  parent_open := parent_open

/--
Build all-faces-root localized open-boundary data from singleton terminal faces
and rank-decreasing two-child nonterminal splits.

This is the next construction surface for the recursive proof: terminal fields
come from face boundaries, and `move_data` comes from concrete two-child split
geometry.
-/
def ofSingletonTerminalFacesAndTwoChildMoves
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (rank : Cell P → Nat)
    (terminal : Cell P → Prop)
    (faceOf : ∀ x, terminal x → P.Face)
    (hcell : ∀ x hx, x = Cell.singleton P (faceOf x hx))
    (hs : ∀ x hx, datum.s x = faceDatum.s (faceOf x hx))
    (ht : ∀ x hx, datum.t x = faceDatum.t (faceOf x hx))
    (split :
      ∀ x, ¬ terminal x → TwoChildMoveGeometry P datum rank x)
    (root_closing :
      G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (active : Cell P → Prop)
    (root_active : active (Cell.full P))
    (terminal_boundary :
      ∀ x, active x → (hx : terminal x) →
        needle <:+:
          faceDatum.s (faceOf x hx) ::
            ((faceDatum.witness (faceOf x hx)).middle ++
              [faceDatum.t (faceOf x hx), faceDatum.s (faceOf x hx)]))
    (parent_open :
      ∀ x, active x → (hnonterminal : ¬ terminal x) →
        (childPath :
          ∀ y, rank y < rank x →
            ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
        needle <:+:
          datum.s x ::
            ((((split x hnonterminal).toCellMoveData childPath).spanningPath
              P datum).tail ++ [datum.s x])) :
    AllFacesRootLocalizedOpenBoundaryCellSystem P needle :=
  ofSingletonTerminalFaces
    datum faceDatum rank terminal faceOf hcell hs ht
    (CellMoveData.ofTwoChildSplits datum rank split)
    root_closing active root_active terminal_boundary
    (by
      intro x hactive hnonterminal childPath
      simpa [CellMoveData.ofTwoChildSplits] using
        parent_open x hactive hnonterminal childPath)

/--
Variant of `ofSingletonTerminalFacesAndTwoChildMoves` where the active
parent-open proof is stated against the explicit concatenation of the two child
path tails.
-/
def ofSingletonTerminalFacesAndTwoChildMovesOfParentAppend
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (rank : Cell P → Nat)
    (terminal : Cell P → Prop)
    (faceOf : ∀ x, terminal x → P.Face)
    (hcell : ∀ x hx, x = Cell.singleton P (faceOf x hx))
    (hs : ∀ x hx, datum.s x = faceDatum.s (faceOf x hx))
    (ht : ∀ x hx, datum.t x = faceDatum.t (faceOf x hx))
    (split :
      ∀ x, ¬ terminal x → TwoChildMoveGeometry P datum rank x)
    (root_closing :
      G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (active : Cell P → Prop)
    (root_active : active (Cell.full P))
    (terminal_boundary :
      ∀ x, active x → (hx : terminal x) →
        needle <:+:
          faceDatum.s (faceOf x hx) ::
            ((faceDatum.witness (faceOf x hx)).middle ++
              [faceDatum.t (faceOf x hx), faceDatum.s (faceOf x hx)]))
    (parent_open :
      ∀ x, active x → (hnonterminal : ¬ terminal x) →
        (childPath :
          ∀ y, rank y < rank x →
            ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
        needle <:+:
          datum.s x ::
            ((((childPath
              (split x hnonterminal).left
              (split x hnonterminal).left_rank).tail) ++
              ((childPath
                (split x hnonterminal).right
                (split x hnonterminal).right_rank).tail)) ++
              [datum.s x])) :
    AllFacesRootLocalizedOpenBoundaryCellSystem P needle :=
  ofSingletonTerminalFacesAndTwoChildMoves
    datum faceDatum rank terminal faceOf hcell hs ht split
    root_closing active root_active terminal_boundary
    (by
      intro x hactive hnonterminal childPath
      exact
        (split x hnonterminal).parentOpenOfInfixAppend childPath
          (parent_open x hactive hnonterminal childPath))

/--
Concrete default-rank constructor for the recursive proof surface.

This fixes the rank to face-count and terminal cells to singleton faces. A
caller must supply proper face-subset two-child splits for nonterminal cells,
plus the remaining root and active-branch facts.
-/
noncomputable def ofFaceCountRankedTwoChildDecomposition
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (hs_singleton :
      ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f)
    (ht_singleton :
      ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f)
    (split :
      ∀ x, ¬ Cell.IsSingletonFace P x →
        FaceSubsetTwoChildMoveGeometry P datum x)
    (root_closing :
      G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (active : Cell P → Prop)
    (root_active : active (Cell.full P))
    (terminal_boundary :
      ∀ x, active x → (hx : Cell.IsSingletonFace P x) →
        needle <:+:
          faceDatum.s (Cell.singletonFace P x hx) ::
            ((faceDatum.witness (Cell.singletonFace P x hx)).middle ++
              [faceDatum.t (Cell.singletonFace P x hx),
                faceDatum.s (Cell.singletonFace P x hx)]))
    (parent_open :
      ∀ x, active x → (hnonterminal : ¬ Cell.IsSingletonFace P x) →
        (childPath :
          ∀ y, Cell.faceRank P y < Cell.faceRank P x →
            ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
        needle <:+:
          datum.s x ::
            (((childPath
              (split x hnonterminal).left
              (Cell.faceRank_lt_of_faces_ssubset P
                (split x hnonterminal).left_faces)).tail ++
              (childPath
                (split x hnonterminal).right
                (Cell.faceRank_lt_of_faces_ssubset P
                  (split x hnonterminal).right_faces)).tail) ++
              [datum.s x])) :
    AllFacesRootLocalizedOpenBoundaryCellSystem P needle :=
  ofSingletonTerminalFacesAndTwoChildMovesOfParentAppend
    datum faceDatum (Cell.faceRank P) (Cell.IsSingletonFace P)
    (Cell.singletonFace P)
    (Cell.eq_singleton_singletonFace P)
    (by
      intro x hx
      exact
        (congrArg datum.s (Cell.eq_singleton_singletonFace P x hx)).trans
          (hs_singleton (Cell.singletonFace P x hx)))
    (by
      intro x hx
      exact
        (congrArg datum.t (Cell.eq_singleton_singletonFace P x hx)).trans
          (ht_singleton (Cell.singletonFace P x hx)))
    (fun x hnonterminal =>
      (split x hnonterminal).toTwoChildMoveGeometry)
    root_closing active root_active terminal_boundary
    (by
      intro x hactive hnonterminal childPath
      simpa [FaceSubsetTwoChildMoveGeometry.toTwoChildMoveGeometry] using
        parent_open x hactive hnonterminal childPath)

/--
Default-rank constructor where support coverage is supplied as a face-set cover.

This is the preferred next surface for the planar split theorem: the recursive
split must produce proper face-subset children covering the parent faces. The
vertex-support cover is then derived automatically.
-/
noncomputable def ofFaceCountRankedFaceCoverTwoChildDecomposition
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (datum : CellPathDatum P)
    (faceDatum : FacePathDatum P)
    (hs_singleton :
      ∀ f, datum.s (Cell.singleton P f) = faceDatum.s f)
    (ht_singleton :
      ∀ f, datum.t (Cell.singleton P f) = faceDatum.t f)
    (split :
      ∀ x, ¬ Cell.IsSingletonFace P x →
        FaceCoverTwoChildMoveGeometry P datum x)
    (root_closing :
      G.Adj (datum.t (Cell.full P)) (datum.s (Cell.full P)))
    (active : Cell P → Prop)
    (root_active : active (Cell.full P))
    (terminal_boundary :
      ∀ x, active x → (hx : Cell.IsSingletonFace P x) →
        needle <:+:
          faceDatum.s (Cell.singletonFace P x hx) ::
            ((faceDatum.witness (Cell.singletonFace P x hx)).middle ++
              [faceDatum.t (Cell.singletonFace P x hx),
                faceDatum.s (Cell.singletonFace P x hx)]))
    (parent_open :
      ∀ x, active x → (hnonterminal : ¬ Cell.IsSingletonFace P x) →
        (childPath :
          ∀ y, Cell.faceRank P y < Cell.faceRank P x →
            ListSpanningPath G.Adj (y.support P) (datum.s y) (datum.t y)) →
        needle <:+:
          datum.s x ::
            (((childPath
              (split x hnonterminal).left
              (Cell.faceRank_lt_of_faces_ssubset P
                (split x hnonterminal).left_faces)).tail ++
              (childPath
                (split x hnonterminal).right
                (Cell.faceRank_lt_of_faces_ssubset P
                  (split x hnonterminal).right_faces)).tail) ++
              [datum.s x])) :
    AllFacesRootLocalizedOpenBoundaryCellSystem P needle :=
  ofFaceCountRankedTwoChildDecomposition
    datum faceDatum hs_singleton ht_singleton
    (fun x hnonterminal =>
      (split x hnonterminal).toFaceSubsetTwoChildMoveGeometry)
    root_closing active root_active terminal_boundary
    (by
      intro x hactive hnonterminal childPath
      simpa [FaceCoverTwoChildMoveGeometry.toFaceSubsetTwoChildMoveGeometry]
        using parent_open x hactive hnonterminal childPath)

/-- Reinsert the standard all-faces root fields. -/
def toLocalizedOpenBoundaryCellSystem
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (inputs : AllFacesRootLocalizedOpenBoundaryCellSystem P needle) :
    LocalizedOpenBoundaryCellSystem P needle where
  datum := inputs.datum
  rank := inputs.rank
  terminal := inputs.terminal
  terminal_witness := inputs.terminal_witness
  move_data := inputs.move_data
  root := Cell.full P
  root_support := Cell.support_full P
  root_closing := inputs.root_closing
  active := inputs.active
  root_active := inputs.root_active
  terminal_boundary := inputs.terminal_boundary
  parent_open := inputs.parent_open

end AllFacesRootLocalizedOpenBoundaryCellSystem

namespace LocalizedOpenBoundaryCellSystem

/-- Convert target-side cell-system data into the generic concrete cell system. -/
def toConcreteCellSystem
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (inputs : LocalizedOpenBoundaryCellSystem P needle) :
    ConcreteCellSystem (Cell := Cell P) (V := V) (Adj := G.Adj) where
  support := fun x => x.support P
  datum := { s := inputs.datum.s, t := inputs.datum.t }
  rank := inputs.rank
  terminal := inputs.terminal
  terminal_witness := by
    intro x hx
    exact inputs.terminal_witness x hx
  move_witness := by
    intro x hnonterminal childPath
    exact (inputs.move_data x hnonterminal childPath).toMoveStepData P inputs.datum

/--
The target-side terminal-boundary field is exactly the terminal-boundary field
expected by the concrete localized marked API.
-/
theorem terminalBoundary
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (inputs : LocalizedOpenBoundaryCellSystem P needle) :
    ∀ x, inputs.active x →
      (hx : inputs.toConcreteCellSystem.terminal x) →
        needle <:+:
          inputs.toConcreteCellSystem.datum.s x ::
            ((inputs.toConcreteCellSystem.terminal_witness x hx).middle ++
              [inputs.toConcreteCellSystem.datum.t x,
                inputs.toConcreteCellSystem.datum.s x]) := by
  intro x hactive hx
  simpa [toConcreteCellSystem] using
    inputs.terminal_boundary x hactive hx

/--
The target-side open-parent field is exactly localized open-parent marked data
for the converted concrete cell system.
-/
theorem parentOpenCyclicMarkData
    {P : PolyhedralEmbedding G}
    {needle : List V}
    (inputs : LocalizedOpenBoundaryCellSystem P needle) :
    inputs.toConcreteCellSystem.LocalizedParentOpenCyclicMarkData
      inputs.active needle := by
  intro x hactive hnonterminal childPath
  simpa [toConcreteCellSystem, CellMoveData.spanningPath] using
    inputs.parent_open x hactive hnonterminal childPath

end LocalizedOpenBoundaryCellSystem

end PolyhedralEmbedding

end PolyhedralFaceCells

end SpanningCycle
