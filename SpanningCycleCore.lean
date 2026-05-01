import Mathlib

/-!
# SpanningCycleCore

This file formalizes the most Lean-friendly part of the note:
section 4 (balanced edge functionals), together with a generic rank-induction
lemma that matches the proof pattern of Theorem 6.2.

The graph-theoretic part is intentionally stated for arbitrary lists of vertices,
so it does not depend on any specific `SimpleGraph` API.
-/

namespace SpanningCycle

universe u

section BalancedEdge

variable {V : Type u}

/-- The exact edge functional attached to a coloring `χ : V → ℚ`. -/
def epsilon (χ : V → ℚ) (u v : V) : ℚ :=
  (χ v - χ u) / 2

/-- The terminal vertex of a walk that starts at `u` and then follows the list `vs`. -/
def endVertex (u : V) : List V → V
  | [] => u
  | v :: vs => endVertex v vs

/-- Consecutive oriented edges of a vertex list. -/
def edgePairs : List V → List (V × V)
  | [] => []
  | _ :: [] => []
  | u :: v :: vs => (u, v) :: edgePairs (v :: vs)

/-- The value of `εχ` on the walk `u = x₀, x₁, ..., x_m`. -/
def epsilonChain (χ : V → ℚ) (u : V) : List V → ℚ
  | [] => 0
  | v :: vs => epsilon χ u v + epsilonChain χ v vs

/-- Exactness: the value on a walk depends only on its endpoints. -/
theorem epsilonChain_eq (χ : V → ℚ) (u : V) :
    ∀ vs, epsilonChain χ u vs = epsilon χ u (endVertex u vs) := by
  intro vs
  induction vs generalizing u with
  | nil =>
      simp [epsilonChain, endVertex, epsilon]
  | cons v vs ih =>
      simp [epsilonChain, endVertex, ih, epsilon]
      ring

/-- Terminal vertices behave well under concatenation of tails. -/
theorem endVertex_append (u : V) :
    ∀ xs ys, endVertex u (xs ++ ys) = endVertex (endVertex u xs) ys := by
  intro xs ys
  induction xs generalizing u with
  | nil =>
      simp [endVertex]
  | cons v xs ih =>
      simp [endVertex, ih]

/-- The terminal vertex of a nonempty walk appears in its vertex list. -/
theorem endVertex_mem_cons (u : V) :
    ∀ vs, endVertex u vs ∈ u :: vs := by
  intro vs
  induction vs generalizing u with
  | nil =>
      simp [endVertex]
  | cons v vs ih =>
      dsimp [endVertex]
      exact List.mem_cons_of_mem _ (ih (u := v))

/-- Edge pairs split over concatenation of tails. -/
theorem edgePairs_append (u : V) :
    ∀ xs ys,
      edgePairs (u :: (xs ++ ys)) =
        edgePairs (u :: xs) ++ edgePairs (endVertex u xs :: ys) := by
  intro xs ys
  induction xs generalizing u with
  | nil =>
      simp [edgePairs, endVertex]
  | cons v xs ih =>
      simp [edgePairs, endVertex, ih]

/-- Values of `εχ` split over concatenation of tails. -/
theorem epsilonChain_append (χ : V → ℚ) (u : V) :
    ∀ xs ys,
      epsilonChain χ u (xs ++ ys) =
        epsilonChain χ u xs + epsilonChain χ (endVertex u xs) ys := by
  intro xs ys
  induction xs generalizing u with
  | nil =>
      simp [epsilonChain, endVertex]
  | cons v xs ih =>
      simp [epsilonChain, endVertex, ih]
      ring

/-- The note's exactness identity, written with an explicit starting vertex and tail. -/
theorem exactness (χ : V → ℚ) (u : V) :
    ∀ vs, epsilonChain χ u vs = (χ (endVertex u vs) - χ u) / 2 := by
  intro vs
  simpa [epsilon] using epsilonChain_eq χ u vs

/-- Replacing an edge by a path does not change the total `εχ`-value. -/
theorem pathSubstitution (χ : V → ℚ) (u v : V) (vs : List V)
    (hend : endVertex u vs = v) :
    epsilonChain χ u vs = epsilon χ u v := by
  rw [epsilonChain_eq, hend]

/-- A closed walk is balanced. -/
def BalancedWalk (χ : V → ℚ) (u : V) (vs : List V) : Prop :=
  epsilonChain χ u vs = 0

/-- The edge values along the walk are not all zero. -/
def EdgeValuesNotAllZero (χ : V → ℚ) (u : V) (vs : List V) : Prop :=
  ∃ a b, (a, b) ∈ edgePairs (u :: vs) ∧ epsilon χ a b ≠ 0

/-- A closed walk is nontrivially balanced if it is balanced and some edge has nonzero value. -/
def NontriviallyBalancedWalk (χ : V → ℚ) (u : V) (vs : List V) : Prop :=
  BalancedWalk χ u vs ∧ EdgeValuesNotAllZero χ u vs

/-- Closed walks are balanced by exactness. -/
theorem balanced_of_closed (χ : V → ℚ) (u : V) (vs : List V)
    (hclosed : endVertex u vs = u) :
    BalancedWalk χ u vs := by
  unfold BalancedWalk
  rw [epsilonChain_eq, hclosed, epsilon]
  ring

/-- The coloring only takes the values `±1`. -/
abbrev PmOne (χ : V → ℚ) : Prop :=
  ∀ v, χ v = -1 ∨ χ v = 1

/-- Endpoints of an oriented edge have opposite colors. -/
def Bichromatic (χ : V → ℚ) (u v : V) : Prop :=
  χ v = -χ u

/-- A walk is properly bicolored if every edge is bichromatic and the coloring is `±1`-valued. -/
def ProperlyBicoloredAlong (χ : V → ℚ) (w : List V) : Prop :=
  PmOne χ ∧ ∀ ⦃a b⦄, (a, b) ∈ edgePairs w → Bichromatic χ a b

/-- On a bichromatic edge, `εχ(u,v) = -χ(u)`. -/
theorem epsilon_eq_neg_color_of_bichromatic (χ : V → ℚ) {u v : V}
    (hbi : Bichromatic χ u v) :
    epsilon χ u v = -χ u := by
  unfold epsilon Bichromatic at *
  rw [hbi]
  ring

/-- On a properly colored edge, the `εχ`-value is `±1`. -/
theorem epsilon_eq_pmOne_of_bichromatic (χ : V → ℚ) {u v : V}
    (hpm : PmOne χ) (hbi : Bichromatic χ u v) :
    epsilon χ u v = -1 ∨ epsilon χ u v = 1 := by
  rw [epsilon_eq_neg_color_of_bichromatic χ hbi]
  rcases hpm u with hu | hu
  · right
    simp [hu]
  · left
    simp [hu]

/-- In particular, the `εχ`-value on each such edge is nonzero. -/
theorem epsilon_ne_zero_of_bichromatic (χ : V → ℚ) {u v : V}
    (hpm : PmOne χ) (hbi : Bichromatic χ u v) :
    epsilon χ u v ≠ 0 := by
  rcases epsilon_eq_pmOne_of_bichromatic χ hpm hbi with h | h <;> simp [h]

/-- Every edge in a properly bicolored walk has nonzero `εχ`-value. -/
theorem every_edge_nonzero_of_properlyBicolored
    (χ : V → ℚ) (w : List V)
    (hproper : ProperlyBicoloredAlong χ w) :
    ∀ ⦃a b⦄, (a, b) ∈ edgePairs w → epsilon χ a b ≠ 0 := by
  intro a b hab
  rcases hproper with ⟨hpm, hbip⟩
  exact epsilon_ne_zero_of_bichromatic χ hpm (hbip hab)

/-- Version of Corollary 4.4 for a nonempty closed walk. -/
theorem nontriviallyBalanced_of_closed_of_properlyBicolored
    (χ : V → ℚ) (u : V) (vs : List V)
    (hclosed : endVertex u vs = u)
    (hproper : ProperlyBicoloredAlong χ (u :: vs))
    (hne : vs ≠ []) :
    NontriviallyBalancedWalk χ u vs := by
  refine ⟨balanced_of_closed χ u vs hclosed, ?_⟩
  cases vs with
  | nil =>
      contradiction
  | cons v vs' =>
      refine ⟨u, v, ?_, ?_⟩
      · simp [edgePairs]
      · rcases hproper with ⟨hpm, hbip⟩
        exact epsilon_ne_zero_of_bichromatic χ hpm (hbip (by simp [edgePairs]))

end BalancedEdge

section RankInduction

variable {α : Type u}

/--
A generic induction principle on a natural-valued rank.

This mirrors the shape of the induction in Theorem 6.2: terminal cells are handled
by a base case, and every nonterminal cell is obtained from strictly smaller cells.
-/
theorem ranked_induction
    (rank : α → Nat) (terminal : α → Prop) {P : α → Prop}
    (base : ∀ x, terminal x → P x)
    (step : ∀ x, ¬ terminal x → (∀ y, rank y < rank x → P y) → P x) :
    ∀ x, P x := by
  let Q : Nat → Prop := fun n => ∀ x, rank x ≤ n → P x
  have hQ : ∀ n, Q n := by
    intro n
    induction n with
    | zero =>
        intro x hx
        have hr : rank x = 0 := Nat.le_zero.mp hx
        by_cases ht : terminal x
        · exact base x ht
        · exact step x ht (by
            intro y hy
            have : ¬ rank y < 0 := Nat.not_lt_zero _
            simp [hr] at hy)
    | succ n ih =>
        intro x hx
        by_cases ht : terminal x
        · exact base x ht
        · exact step x ht (by
            intro y hy
            exact ih y (Nat.le_of_lt_succ (lt_of_lt_of_le hy hx)))
  intro x
  exact hQ (rank x) x le_rfl

end RankInduction

end SpanningCycle
