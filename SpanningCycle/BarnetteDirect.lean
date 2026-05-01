import SpanningCycle.PolyhedralFaceCells

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# Direct Barnette endpoint

P4-free endpoint for the positive recursive face-split route.
-/

namespace SpanningCycle

universe u

section BarnetteDirect

open SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace SimpleGraph

/-- Every finite cubic connected graph contains four vertices forming an ordered length-3 path. -/
theorem exists_path3Vertices_of_cubic_connected
    (G : SimpleGraph V)
    (hcubic : IsCubicGraph G)
    (hconn : G.Connected) :
    ∃ a b c d : V, Path3Vertices G a b c d := by
  classical
  let u : V := Classical.choice hconn.nonempty
  have hNu3 : (G.neighborFinset u).card = 3 := hcubic u
  have hNu_nonempty : (G.neighborFinset u).Nonempty := by
    have hpos : 0 < (G.neighborFinset u).card := by omega
    exact Finset.card_pos.mp hpos
  obtain ⟨x, hxmem⟩ := hNu_nonempty
  have hNux_card : ((G.neighborFinset u).erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hxmem, hNu3]
  have hNux_nonempty : ((G.neighborFinset u).erase x).Nonempty := by
    have hpos : 0 < ((G.neighborFinset u).erase x).card := by
      rw [hNux_card]
      omega
    exact Finset.card_pos.mp hpos
  obtain ⟨y, hymem⟩ := hNux_nonempty
  have hy_ne_x : y ≠ x := (Finset.mem_erase.mp hymem).1
  have hy_mem : y ∈ G.neighborFinset u := (Finset.mem_erase.mp hymem).2
  have hux : G.Adj u x := by simpa using hxmem
  have huy : G.Adj u y := by simpa using hy_mem
  have hxu_ne : x ≠ u := by
    intro hxu
    exact G.loopless.irrefl u (hxu ▸ hux)
  have huy_ne : u ≠ y := by
    intro huy'
    exact G.loopless.irrefl u (huy' ▸ huy)
  have hNy3 : (G.neighborFinset y).card = 3 := hcubic y
  have hu_mem_y : u ∈ G.neighborFinset y := by
    simpa [G.adj_comm] using huy
  have hNyu_card : ((G.neighborFinset y).erase u).card = 2 := by
    rw [Finset.card_erase_of_mem hu_mem_y, hNy3]
  have hNyu_x_nonempty : (((G.neighborFinset y).erase u).erase x).Nonempty := by
    by_cases hx_mem : x ∈ (G.neighborFinset y).erase u
    · have hcard : (((G.neighborFinset y).erase u).erase x).card = 1 := by
        rw [Finset.card_erase_of_mem hx_mem, hNyu_card]
      have hpos : 0 < (((G.neighborFinset y).erase u).erase x).card := by
        rw [hcard]
        omega
      exact Finset.card_pos.mp hpos
    · have hcard : (((G.neighborFinset y).erase u).erase x).card = 2 := by
        simpa [Finset.erase_eq_self.2 hx_mem] using hNyu_card
      have hpos : 0 < (((G.neighborFinset y).erase u).erase x).card := by
        rw [hcard]
        omega
      exact Finset.card_pos.mp hpos
  obtain ⟨z, hzmem⟩ := hNyu_x_nonempty
  have hz_ne_x : z ≠ x := (Finset.mem_erase.mp hzmem).1
  have hzmem' : z ∈ (G.neighborFinset y).erase u := (Finset.mem_erase.mp hzmem).2
  have hz_ne_u : z ≠ u := (Finset.mem_erase.mp hzmem').1
  have hz_mem : z ∈ G.neighborFinset y := (Finset.mem_erase.mp hzmem').2
  have hyz : G.Adj y z := by simpa using hz_mem
  have hxu : G.Adj x u := G.symm hux
  have hxy_ne : x ≠ y := by
    intro hxy
    exact hy_ne_x hxy.symm
  have hxz_ne : x ≠ z := by
    intro hxz
    exact hz_ne_x hxz.symm
  have huz_ne : u ≠ z := by
    intro huz
    exact hz_ne_u huz.symm
  have hyz_ne : y ≠ z := by
    intro hyz'
    exact G.loopless.irrefl y (hyz' ▸ hyz)
  exact
    ⟨x, u, y, z,
      ⟨hxu, huy, hyz, hxu_ne, hxy_ne, hxz_ne,
        huy_ne, huz_ne, hyz_ne⟩⟩

end SimpleGraph

namespace BarnetteGraph

/-- Barnette-facing certificate for repaired nonempty recursive face-split data. -/
abbrev PositiveRecursiveFaceSplitCertificate
    (B : BarnetteGraph (V := V)) (a b c d : V) : Type u :=
  PolyhedralEmbedding.PositiveMarkedFaceSplitCertificate
    B.embedding [a, b, c, d]

/-- A finite cubic connected Barnette graph has at least three vertices. -/
theorem vertex_card_at_least_three
    (B : BarnetteGraph (V := V)) :
    3 ≤ Fintype.card V := by
  classical
  have hnonempty : Nonempty V := B.connected.nonempty
  have hmin : 3 ≤ B.G.minDegree := by
    letI : Nonempty V := hnonempty
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [← B.G.card_neighborFinset_eq_degree, B.cubic v]
  have hlt : B.G.minDegree < Fintype.card V := by
    letI : Nonempty V := hnonempty
    exact SimpleGraph.minDegree_lt_card (G := B.G)
  omega

/-- An explicit Hamiltonian-cycle witness on all vertices proves Hamiltonicity of a Barnette graph. -/
theorem isHamiltonian_of_hamiltonianCycleWitness
    (B : BarnetteGraph (V := V))
    (w : HamiltonianCycleWitness B.G.Adj (Finset.univ : Finset V)) :
    B.IsHamiltonian := by
  have hham : HamiltonianOn (Finset.univ : Finset V) B.G.Adj := ⟨w⟩
  simpa [BarnetteGraph.IsHamiltonian] using
    isHamiltonian_of_hamiltonianOn_univ
      (G := B.G) (vertex_card_at_least_three B) hham

/--
The positive recursive face-split certificate already contains enough data to
produce Hamiltonicity; no P4 route is needed for this conclusion.
-/
theorem isHamiltonian_of_positiveRecursiveFaceSplitCertificate
    (B : BarnetteGraph (V := V))
    {a b c d : V}
    (cert : PositiveRecursiveFaceSplitCertificate B a b c d) :
    B.IsHamiltonian := by
  classical
  rcases cert.existsHamiltonianCycleWitness with ⟨w, _hinfix⟩
  exact B.isHamiltonian_of_hamiltonianCycleWitness w

end BarnetteGraph

/--
Universe-polymorphic Barnette conjecture target.

This is the theorem statement we ultimately want with no graph-specific
parameters left outside the quantifier.
-/
abbrev BarnetteConjecture : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W],
    ∀ B : BarnetteGraph (V := W), B.IsHamiltonian

/--
Uniform provider for the repaired nonempty-cell recursive face-split
certificate.

This is the P4-free direct geometry target.
-/
abbrev FullClassPositiveRecursiveFaceSplitCertificateProvider :
    Type (u + 1) :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W],
    ∀ B : BarnetteGraph (V := W),
      ∀ {a b c d : W}, Path3Vertices B.G a b c d →
        BarnetteGraph.PositiveRecursiveFaceSplitCertificate B a b c d

/--
Direct Barnette bridge from the repaired nonempty-cell recursive face-split
certificate.

Choose one length-3 path in each cubic connected Barnette graph, extract the Hamiltonian
cycle supplied by the corresponding positive certificate, and close the graph
Hamiltonicity conclusion directly.
-/
theorem barnetteConjecture_of_fullClassPositiveRecursiveFaceSplitCertificateProvider
    (hcerts : FullClassPositiveRecursiveFaceSplitCertificateProvider.{u}) :
    BarnetteConjecture.{u} := by
  classical
  intro W _ _ B
  rcases SimpleGraph.exists_path3Vertices_of_cubic_connected
      B.G B.cubic B.connected with
    ⟨a, b, c, d, hpath⟩
  exact
    B.isHamiltonian_of_positiveRecursiveFaceSplitCertificate
      (hcerts (W := W) B hpath)

end BarnetteDirect

end SpanningCycle
