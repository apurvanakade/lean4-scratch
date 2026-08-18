import Mathlib.Tactic

/-!
# The Directed Handshake Lemma

For a **directed** graph the out-degrees sum to the number of edges, with no
factor of two:

  `∑ v, outdeg v = |E|`

## Why this is easier than the undirected case

In the undirected setting (see `Scratch.handshake_lemma`) an edge is an
*unordered* pair, so one has to count ordered pairs — edges with a chosen
source — and
observe that each edge carries two of them. That is where the factor `2` comes
from.

Here a directed edge simply *is* an ordered pair `(v, w)`. So there is only one
count to do: group the edges by their source vertex `v`, and observe that the
edges with source `v` are exactly the out-neighbours of `v`, of which there are
`outdeg v`. No orientation bookkeeping is needed, and looplessness is not
required either — a loop `(v, v)` is a perfectly good directed edge and is
counted once on each side.

## Notes for readers new to Lean

* `Finset V` is the type of **finite subsets** of `V`, and `#s` is the
  cardinality of `s`.
* `∑ v, f v` sums `f` over all of `V`, and `∑ x ∈ s, f x` sums over a finset `s`.
* `{x ∈ s | p x}` is the sub-finset of `s` where `p` holds.
* The square-bracket arguments `[Fintype V]` and `[DecidableRel G.Adj]` are
  *typeclass* hypotheses ("`V` is finite", "adjacency is decidable") that let us
  treat sets of vertices as finsets and count them. They hold automatically for
  any concrete finite graph and can be ignored on a first reading.
-/

open Finset

variable {V : Type*} [Fintype V]

/-- A directed graph on `V`. Unlike `Graph`, the adjacency relation need not be
symmetric, and loops are permitted: `Adj v w` means "there is an edge *from* `v`
*to* `w`". -/
structure Digraph (V : Type*) where
  /-- The adjacency relation: `Adj v w` means "there is an edge from `v` to `w`". -/
  Adj : V → V → Prop

namespace Digraph

variable (G : Digraph V) [DecidableRel G.Adj]

/-- The out-neighbours of a vertex `v`: the vertices `w` with an edge `v → w`. -/
def outNeighborFinset (v : V) : Finset V :=
  {w | G.Adj v w}.toFinset

theorem mem_outNeighborFinset (v w : V) : w ∈ G.outNeighborFinset v ↔ G.Adj v w := by
  simp [outNeighborFinset]

/-- The out-degree of a vertex is its number of out-neighbours. -/
def outDegree (v : V) : ℕ :=
  #(G.outNeighborFinset v)

/-- The edges of `G`: ordered pairs `(v, w)` with an edge from `v` to `w`. -/
def edgeFinset : Finset (V × V) :=
  {p : V × V | G.Adj p.1 p.2}.toFinset

theorem mem_edgeFinset (p : V × V) : p ∈ G.edgeFinset ↔ G.Adj p.1 p.2 := by
  simp [edgeFinset]

/-- **Directed handshake lemma.** The out-degrees of a finite directed graph sum
to its number of edges: grouping the edges by their source vertex `v` recovers
exactly the out-degree of `v`. -/
theorem sum_outDegree_eq_card_edges : ∑ v, G.outDegree v = #G.edgeFinset := by
  classical
  -- Every edge has *some* source vertex, so we may split the edges into fibres
  -- indexed by all of `V`.
  have hsource : ∀ p ∈ G.edgeFinset, p.1 ∈ (univ : Finset V) := by
    intro p _
    exact mem_univ p.1
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) hsource]
  -- It remains to check, for each vertex `v`, that the fibre over `v` has
  -- exactly `outDegree v` elements.
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [outDegree]
  -- The bijection {out-neighbours of v} → {edges with source v} sends `w ↦ (v, w)`.
  refine Finset.card_bij (fun w _ => (v, w)) ?_ ?_ ?_
  · -- Well defined: if `w` is an out-neighbour of `v`, then `(v, w)` is an edge
    -- and its source is `v`.
    intro w hw
    simp only [mem_outNeighborFinset] at hw
    simp only [mem_filter, mem_edgeFinset]
    exact ⟨hw, trivial⟩
  · -- Injective: `(v, w) = (v, w')` forces `w = w'`.
    intro w _ w' _ h
    exact congrArg Prod.snd h
  · -- Surjective: an edge `p` with source `v` is `(v, p.2)`, coming from the
    -- out-neighbour `p.2`.
    intro p hp
    simp only [mem_filter, mem_edgeFinset] at hp
    obtain ⟨hadj, hsrc⟩ := hp
    refine ⟨p.2, ?_, ?_⟩
    · simp only [mem_outNeighborFinset]
      rwa [hsrc] at hadj
    · exact Prod.ext hsrc.symm rfl

end Digraph
