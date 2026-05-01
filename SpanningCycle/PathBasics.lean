import SpanningCycleCore
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.List.Rotate

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Spanning-cycle path basics

Destination module for list-based path/cycle witnesses, elementary list
infix/rotation lemmas, and the bridge from list Hamiltonian witnesses to
mathlib Hamiltonian cycles.
-/

namespace SpanningCycle

universe u v

/-- Entry and exit vertices attached to each cell. -/
structure PathDatum (Cell : Type u) (V : Type v) where
  s : Cell → V
  t : Cell → V

section ConcreteSpanningPaths

variable {V : Type v} [DecidableEq V]

/--
A concrete list-based witness for a spanning path in a finite vertex set.

The path starts at `s`, follows the vertices in `tail`, uses only `Adj`-edges,
has no repeated vertices, and visits exactly the vertices of `support`.
-/
structure ListSpanningPath
    (Adj : V → V → Prop)
    (support : Finset V)
    (s t : V) where
  tail : List V
  ends_at : endVertex s tail = t
  adj : ∀ ⦃a b⦄, (a, b) ∈ edgePairs (s :: tail) → Adj a b
  nodup : List.Nodup (s :: tail)
  spans : ∀ v, v ∈ support ↔ v ∈ s :: tail

namespace ListSpanningPath

variable {Adj : V → V → Prop}
variable {S₁ S₂ : Finset V}
variable {s a t : V}

theorem endVertex_map
    {W : Type w} (f : V → W) (u : V) :
    ∀ vs, endVertex (f u) (vs.map f) = f (endVertex u vs)
  | [] => rfl
  | v :: vs => by
      simpa [endVertex] using endVertex_map f v vs

theorem edgePairs_map
    {W : Type w} (f : V → W) :
    ∀ l : List V,
      edgePairs (l.map f) = (edgePairs l).map (fun e => (f e.1, f e.2))
  | [] => rfl
  | [_] => rfl
  | u :: v :: vs => by
      simpa [edgePairs] using edgePairs_map f (v :: vs)

/-- The underlying vertex list of the path. -/
def vertices (p : ListSpanningPath Adj S₁ s t) : List V :=
  s :: p.tail

@[simp] theorem vertices_def (p : ListSpanningPath Adj S₁ s t) :
    p.vertices = s :: p.tail := rfl

@[simp] theorem mem_support_iff (p : ListSpanningPath Adj S₁ s t) (v : V) :
    v ∈ S₁ ↔ v ∈ p.vertices := by
  simpa [vertices] using p.spans v

@[simp] theorem start_mem_vertices (p : ListSpanningPath Adj S₁ s t) :
    s ∈ p.vertices := by
  simp [vertices]

@[simp] theorem end_mem_vertices (p : ListSpanningPath Adj S₁ s t) :
    t ∈ p.vertices := by
  simpa [vertices, p.ends_at] using (endVertex_mem_cons s p.tail)

/--
Reindex a spanning path across equal support and endpoint data while preserving
the underlying vertex list definitionally.
-/
def reindex
    {S' : Finset V} {s' t' : V}
    (p : ListSpanningPath Adj S₁ s t)
    (hS : S₁ = S')
    (hs : s = s')
    (ht : t = t') :
    ListSpanningPath Adj S' s' t' where
  tail := p.tail
  ends_at := by
    subst s'
    subst t'
    exact p.ends_at
  adj := by
    subst s'
    exact p.adj
  nodup := by
    subst s'
    exact p.nodup
  spans := by
    intro v
    subst S'
    subst s'
    exact p.spans v

@[simp] theorem reindex_tail
    {S' : Finset V} {s' t' : V}
    (p : ListSpanningPath Adj S₁ s t)
    (hS : S₁ = S')
    (hs : s = s')
    (ht : t = t') :
    (p.reindex hS hs ht).tail = p.tail := rfl

/--
Keep the initial segment of a spanning path up to a chosen tail vertex.
-/
def takePrefix
    (p : ListSpanningPath Adj S₁ s t)
    (xs : List V) (u : V) (ys : List V)
    (htail : p.tail = xs ++ u :: ys) :
    ListSpanningPath Adj ((s :: (xs ++ [u])).toFinset) s u where
  tail := xs ++ [u]
  ends_at := by
    rw [endVertex_append]
    simp [endVertex]
  adj := by
    intro a b hab
    have hab' : (a, b) ∈ edgePairs (s :: ((xs ++ [u]) ++ ys)) := by
      rw [edgePairs_append]
      exact List.mem_append.2 (Or.inl hab)
    have hab'' : (a, b) ∈ edgePairs (s :: p.tail) := by
      simpa [htail, List.append_assoc] using hab'
    exact p.adj hab''
  nodup := by
    have hpref : s :: (xs ++ [u]) <+: s :: p.tail := by
      use ys
      simp [htail, List.append_assoc]
    exact hpref.nodup p.nodup
  spans := by
    intro v
    simp [List.mem_toFinset, or_assoc, or_left_comm, or_comm]

/--
Drop an initial segment of a spanning path and restart it at a chosen tail vertex.
-/
def dropPrefix
    (p : ListSpanningPath Adj S₁ s t)
    (xs : List V) (u : V) (ys : List V)
    (htail : p.tail = xs ++ u :: ys) :
    ListSpanningPath Adj ((u :: ys).toFinset) u t where
  tail := ys
  ends_at := by
    have hEnd :
        endVertex s (xs ++ u :: ys) = endVertex u ys := by
      rw [endVertex_append]
      simp [endVertex]
    rw [← hEnd, ← htail]
    exact p.ends_at
  adj := by
    intro a b hab
    have hab' : (a, b) ∈ edgePairs (s :: p.tail) := by
      have htail' : (a, b) ∈ edgePairs (endVertex s xs :: (u :: ys)) := by
        exact List.mem_cons_of_mem _ hab
      rw [htail, edgePairs_append]
      exact List.mem_append.2 (Or.inr (by simpa [endVertex_append, endVertex] using htail'))
    exact p.adj hab'
  nodup := by
    have hsuf : u :: ys <:+ s :: p.tail := by
      use s :: xs
      simp [htail, List.append_assoc]
    exact hsuf.nodup p.nodup
  spans := by
    intro v
    simp

/--
Low-level gluing lemma: concatenate two spanning paths when the second tail is
disjoint from the first vertex list.
-/
def append
    (p₁ : ListSpanningPath Adj S₁ s a)
    (p₂ : ListSpanningPath Adj S₂ a t)
    (hdisj : List.Disjoint p₁.vertices p₂.tail) :
    ListSpanningPath Adj (S₁ ∪ S₂) s t where
  tail := p₁.tail ++ p₂.tail
  ends_at := by
    rw [endVertex_append, p₁.ends_at, p₂.ends_at]
  adj := by
    intro x y hxy
    change (x, y) ∈ edgePairs (s :: (p₁.tail ++ p₂.tail)) at hxy
    rw [edgePairs_append] at hxy
    rcases List.mem_append.1 hxy with hxy | hxy
    · exact p₁.adj hxy
    · have hxy' : (x, y) ∈ edgePairs (a :: p₂.tail) := by
        simpa [p₁.ends_at] using hxy
      exact p₂.adj hxy'
  nodup := by
    have htail : List.Nodup p₂.tail := List.Nodup.of_cons p₂.nodup
    simpa [vertices] using p₁.nodup.append htail hdisj
  spans := by
    intro v
    constructor
    · intro hv
      rw [Finset.mem_union] at hv
      change v ∈ (s :: p₁.tail) ++ p₂.tail
      rcases hv with hv | hv
      · exact List.mem_append.2 <| Or.inl ((p₁.mem_support_iff v).1 hv)
      · have hv' : v ∈ a :: p₂.tail := (p₂.mem_support_iff v).1 hv
        rcases List.mem_cons.1 hv' with rfl | hvtail
        · exact List.mem_append.2 <| Or.inl p₁.end_mem_vertices
        · exact List.mem_append.2 <| Or.inr hvtail
    · intro hv
      rw [show v ∈ s :: (p₁.tail ++ p₂.tail) ↔ v ∈ (s :: p₁.tail) ++ p₂.tail by rfl] at hv
      rw [List.mem_append] at hv
      rw [Finset.mem_union]
      rcases hv with hv | hv
      · exact Or.inl ((p₁.mem_support_iff v).2 hv)
      · exact Or.inr ((p₂.mem_support_iff v).2 (by simp [hv]))

/--
If the child supports only meet at the attachment vertex, then the second tail is
automatically disjoint from the first child path.
-/
theorem disjoint_tail_of_support_inter
    (p₁ : ListSpanningPath Adj S₁ s a)
    (p₂ : ListSpanningPath Adj S₂ a t)
    (hinter : ∀ v, v ∈ S₁ → v ∈ S₂ → v = a) :
    List.Disjoint p₁.vertices p₂.tail := by
  intro v hv₁ hv₂
  have hvS₁ : v ∈ S₁ := (p₁.mem_support_iff v).2 hv₁
  have hvS₂ : v ∈ S₂ := (p₂.mem_support_iff v).2 (by simp [hv₂])
  have hEq : v = a := hinter v hvS₁ hvS₂
  subst hEq
  exact (List.nodup_cons.1 p₂.nodup).1 hv₂

/--
Path gluing in the form used by the manuscript: if two child paths meet only at
their attachment vertex, they concatenate to a parent spanning path.
-/
def append_of_support_inter
    (p₁ : ListSpanningPath Adj S₁ s a)
    (p₂ : ListSpanningPath Adj S₂ a t)
    (hinter : ∀ v, v ∈ S₁ → v ∈ S₂ → v = a) :
    ListSpanningPath Adj (S₁ ∪ S₂) s t :=
  append p₁ p₂ (disjoint_tail_of_support_inter p₁ p₂ hinter)

/--
If a spanning path list ends with `u, t`, then the final edge `u - t` is
present in the adjacency relation.
-/
theorem finalEdge_of_split
    (p : ListSpanningPath Adj S₁ s t)
    (middle : List V) (u : V)
    (htail : p.tail = middle ++ [u, t]) :
    Adj u t := by
  have hmem : (u, t) ∈ edgePairs (s :: p.tail) := by
    have hend : endVertex s (middle ++ [u]) = u := by
      rw [endVertex_append]
      simp [endVertex]
    rw [htail, edgePairs_append]
    exact List.mem_append.2 (Or.inr (by simpa [hend, edgePairs]))
  exact p.adj hmem

/--
Delete the terminal vertex `t` from a spanning path that ends with `u, t` and
keep `u` as the new endpoint.
-/
def truncateFinish
    (p : ListSpanningPath Adj S₁ s t)
    (middle : List V) (u : V)
    (htail : p.tail = middle ++ [u, t]) :
    ListSpanningPath Adj (S₁.erase t) s u where
  tail := middle ++ [u]
  ends_at := by
    rw [endVertex_append]
    simp [endVertex]
  adj := by
    intro a b hab
    have hab' : (a, b) ∈ edgePairs (s :: ((middle ++ [u]) ++ [t])) := by
      rw [edgePairs_append]
      exact List.mem_append.2 (Or.inl hab)
    exact p.adj (by simpa [htail, List.append_assoc] using hab')
  nodup := by
    have hpref : s :: (middle ++ [u]) <+: s :: p.tail := by
      use [t]
      simp [htail, List.append_assoc]
    exact hpref.nodup p.nodup
  spans := by
    intro v
    constructor
    · intro hv
      rw [Finset.mem_erase] at hv
      rcases hv with ⟨hvt, hv⟩
      have hv' : v ∈ s :: (middle ++ [u, t]) := by
        simpa [htail, List.append_assoc] using (p.spans v).1 hv
      simpa [List.append_assoc, hvt] using hv'
    · intro hv
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hvt
        have hnodup : List.Nodup ((s :: (middle ++ [u])) ++ [t]) := by
          simpa [htail, List.append_assoc] using p.nodup
        rw [List.nodup_append] at hnodup
        have hdisj := hnodup.2.2
        exact hdisj v (by simpa using hv) t (by simp) hvt
      · exact (p.spans v).2 (by
          have hv' : v ∈ s :: (middle ++ [u, t]) := by
            simpa [List.append_assoc] using
              (List.mem_append.2 (Or.inl hv) : v ∈ (s :: (middle ++ [u])) ++ [t])
          simpa [htail, List.append_assoc] using hv')

/--
Transport a spanning-path witness across an implication on the edges actually
used by its vertex list.
-/
def transportAdj
    {Adj' : V → V → Prop}
    (p : ListSpanningPath Adj S₁ s t)
    (htransport :
      ∀ ⦃u v⦄, (u, v) ∈ edgePairs (s :: p.tail) → Adj u v → Adj' u v) :
    ListSpanningPath Adj' S₁ s t where
  tail := p.tail
  ends_at := p.ends_at
  adj := by
    intro u v huv
    exact htransport huv (p.adj huv)
  nodup := p.nodup
  spans := p.spans

/-- Transport a list-based spanning path across a vertex equivalence. -/
def mapEquiv
    {W : Type w} [DecidableEq W]
    {Adj' : W → W → Prop}
    {S : Finset V} {s t : V}
    (p : ListSpanningPath Adj S s t)
    (e : V ≃ W)
    (hAdj : ∀ ⦃u v⦄, Adj u v → Adj' (e u) (e v)) :
    ListSpanningPath Adj' (S.map e.toEmbedding) (e s) (e t) where
  tail := p.tail.map e
  ends_at := by
    simpa [endVertex_map] using congrArg e p.ends_at
  adj := by
    intro a b hab
    have habMap :
        (a, b) ∈ (edgePairs (s :: p.tail)).map (fun q => (e q.1, e q.2)) := by
      have hab' : (a, b) ∈ edgePairs ((s :: p.tail).map e) := by
        simpa using hab
      rwa [edgePairs_map] at hab'
    rcases List.mem_map.1 habMap with ⟨q, hq, hqeq⟩
    rcases q with ⟨u, v⟩
    simp at hqeq
    rcases hqeq with ⟨rfl, rfl⟩
    exact hAdj (p.adj hq)
  nodup := by
    simpa using p.nodup.map e.injective
  spans := by
    intro w
    constructor
    · intro hw
      rcases Finset.mem_map.1 hw with ⟨v, hvS, rfl⟩
      exact List.mem_map.2 ⟨v, (p.spans v).1 hvS, rfl⟩
    · intro hw
      have hw' : w ∈ (s :: p.tail).map e := by
        simpa using hw
      rcases List.mem_map.1 hw' with ⟨v, hv, hvw⟩
      exact Finset.mem_map.2 ⟨v, (p.spans v).2 hv, hvw⟩

/-- Transport a list-based spanning path across a graph isomorphism. -/
def mapIso
    {W : Type w} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {S : Finset V} {s t : V}
    (p : ListSpanningPath G.Adj S s t)
    (e : G ≃g H) :
    ListSpanningPath H.Adj (S.map e.toEquiv.toEmbedding) (e s) (e t) :=
  p.mapEquiv e.toEquiv (by
    intro u v huv
    exact e.toHom.map_adj huv)

/--
Transport a list-based spanning path across a graph isomorphism while naming
the transported endpoints explicitly.
-/
def mapIsoTo
    {W : Type w} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {S : Finset V} {s t : V}
    (p : ListSpanningPath G.Adj S s t)
    (e : G ≃g H)
    (s' t' : W)
    (hs : e s = s')
    (ht : e t = t') :
    ListSpanningPath H.Adj (S.map e.toEquiv.toEmbedding) s' t' where
  tail := p.tail.map e
  ends_at := by
    subst s'
    subst t'
    simpa [endVertex_map] using congrArg e p.ends_at
  adj := by
    subst s'
    intro a b hab
    have habMap :
        (a, b) ∈ (edgePairs (s :: p.tail)).map (fun q => (e q.1, e q.2)) := by
      have hab' : (a, b) ∈ edgePairs ((s :: p.tail).map e) := by
        simpa using hab
      rwa [edgePairs_map] at hab'
    rcases List.mem_map.1 habMap with ⟨q, hq, hqeq⟩
    rcases q with ⟨u, v⟩
    simp at hqeq
    rcases hqeq with ⟨rfl, rfl⟩
    exact e.toHom.map_adj (p.adj hq)
  nodup := by
    subst s'
    simpa using p.nodup.map e.injective
  spans := by
    subst s'
    intro w
    constructor
    · intro hw
      rcases Finset.mem_map.1 hw with ⟨v, hvS, rfl⟩
      exact List.mem_map.2 ⟨v, (p.spans v).1 hvS, rfl⟩
    · intro hw
      have hw' : w ∈ (s :: p.tail).map e := by
        simpa using hw
      rcases List.mem_map.1 hw' with ⟨v, hv, hvw⟩
      exact Finset.mem_map.2 ⟨v, (p.spans v).2 hv, hvw⟩

@[simp] theorem mapIso_tail
    {W : Type w} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {S : Finset V} {s t : V}
    (p : ListSpanningPath G.Adj S s t)
    (e : G ≃g H) :
    (p.mapIso e).tail = p.tail.map e := rfl

@[simp] theorem mapIsoTo_tail
    {W : Type w} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {S : Finset V} {s t : V}
    (p : ListSpanningPath G.Adj S s t)
    (e : G ≃g H)
    (s' t' : W)
    (hs : e s = s')
    (ht : e t = t') :
    (p.mapIsoTo e s' t' hs ht).tail = p.tail.map e := rfl

theorem mapIso_tail_ne_singleton
    {W : Type w} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {S : Finset V} {s t : V}
    (p : ListSpanningPath G.Adj S s t)
    (e : G ≃g H)
    (hnot : p.tail ≠ [t]) :
    (p.mapIso e).tail ≠ [e t] := by
  intro htail
  apply hnot
  have hpre := congrArg (List.map e.symm) htail
  simpa [mapIso_tail, List.map_map, Function.comp_def] using hpre

theorem mapIsoTo_tail_ne_singleton
    {W : Type w} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {S : Finset V} {s t : V}
    (p : ListSpanningPath G.Adj S s t)
    (e : G ≃g H)
    (s' t' : W)
    (hs : e s = s')
    (ht : e t = t')
    (hnot : p.tail ≠ [t]) :
    (p.mapIsoTo e s' t' hs ht).tail ≠ [t'] := by
  intro htail
  apply hnot
  have hpre := congrArg (List.map e.symm) htail
  have ht' : e.symm t' = t := by
    simpa [← ht]
  simpa [mapIsoTo_tail, List.map_map, Function.comp_def, ht'] using hpre

end ListSpanningPath

end ConcreteSpanningPaths


end SpanningCycle
