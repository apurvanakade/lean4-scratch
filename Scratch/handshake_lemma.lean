import Mathlib.Tactic

/-!
# The Handshake Lemma

The **handshake lemma** says that in a finite simple graph the degrees sum to
twice the number of edges:

  `∑ v, deg v = 2 * |E|`

Equivalently: at a party, the total number of hands shaken is twice the number
of handshakes.

## The proof in one paragraph

We count one set in two different ways, namely the set of **ordered pairs**
`(v, w)` with `v` adjacent to `w` — that is, an edge together with a choice of
one of its two endpoints as the *source*. (In the literature these are often
called *darts* or *half-edges*.) Then:

* grouping the ordered pairs by their **source vertex** gives `∑ v, deg v`,
  because the pairs with source `v` are exactly the neighbours of `v`;
* grouping the ordered pairs by their **underlying edge** gives `2 * |E|`,
  because each edge `{v, w}` carries exactly the two pairs `(v, w)` and `(w, v)`.

Comparing the two counts proves the lemma. This is the standard *double
counting* argument; everything below is bookkeeping for those two counts.

Note where looplessness is used: if `v = w` were allowed, the loop `{v, v}`
would carry only *one* ordered pair, not two, and the factor of `2` would fail.

## Notes for readers new to Lean

We do not use Mathlib's `SimpleGraph` API; we define our own minimal notion of
a graph and prove only what is needed. A few Lean-isms to know:

* `Finset V` is the type of **finite subsets** of `V`, and `#s` is the
  cardinality of `s`. (This differs from `Set V`, an arbitrary subset, which
  has no cardinality in `ℕ`.)
* `Sym2 V` is the type of **unordered pairs** from `V`. We write `s(v, w)` for
  the unordered pair `{v, w}`, so that `s(v, w) = s(w, v)` holds definitionally.
* `∑ v, f v` sums `f` over all of `V`, and `∑ x ∈ s, f x` sums over a finset `s`.
* `{x ∈ s | p x}` is the sub-finset of `s` where `p` holds.
* The square-bracket arguments `[Fintype V]`, `[DecidableRel G.Adj]`,
  `[DecidableEq V]` are *typeclass* hypotheses: "`V` is finite", "adjacency is
  decidable", "equality of vertices is decidable". They are what let us treat
  sets of vertices as finsets and count them. They hold automatically for any
  concrete finite graph and can safely be ignored on a first reading.
-/

open Finset

variable {V : Type*} [Fintype V]

/-- A simple graph on `V`: a symmetric, irreflexive adjacency relation. -/
structure Graph (V : Type*) where
  /-- The adjacency relation: `Adj v w` means "`v` and `w` are joined by an edge". -/
  Adj : V → V → Prop
  /-- Edges are undirected: if `v` is adjacent to `w` then `w` is adjacent to `v`. -/
  symm : ∀ {v w}, Adj v w → Adj w v
  /-- There are no loops: no vertex is adjacent to itself. -/
  loopless : ∀ v, ¬ Adj v v

namespace Graph

variable (G : Graph V) [DecidableRel G.Adj]

/-! ### Degrees -/

/-- The neighbours of a vertex `v`, as a finite set. -/
def neighborFinset (v : V) : Finset V :=
  {w | G.Adj v w}.toFinset

theorem mem_neighborFinset (v w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w := by
  simp [neighborFinset]

/-- The degree of a vertex is its number of neighbours. -/
def degree (v : V) : ℕ :=
  #(G.neighborFinset v)

/-! ### Ordered pairs

An ordered pair of adjacent vertices is an edge together with a choice of source
endpoint. These form the set we will count in two different ways.
-/

/-- The ordered pairs of `G`: pairs `(v, w)` of adjacent vertices. Each edge
`{v, w}` gives rise to two of them, namely `(v, w)` and `(w, v)`. -/
def orderedPairs : Finset (V × V) :=
  {p : V × V | G.Adj p.1 p.2}.toFinset

theorem mem_orderedPairs (p : V × V) : p ∈ G.orderedPairs ↔ G.Adj p.1 p.2 := by
  simp [orderedPairs]

/-- **First count.** Grouping the ordered pairs by their source vertex gives the
sum of the degrees: the pairs with source `v` correspond bijectively to the
neighbours of `v`, via `(v, w) ↦ w`. -/
theorem card_orderedPairs_eq_sum_degrees : #G.orderedPairs = ∑ v, G.degree v := by
  classical
  -- Every ordered pair has *some* source vertex, so we may split them into
  -- fibres indexed by all of `V`.
  have hsource : ∀ p ∈ G.orderedPairs, p.1 ∈ (univ : Finset V) := by
    intro p _
    exact mem_univ p.1
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) hsource]
  -- It remains to check, for each vertex `v`, that the fibre over `v` has
  -- exactly `degree v` elements.
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [degree]
  -- The bijection {pairs with source v} → {neighbours of v} sends `(v, w) ↦ w`.
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · -- Well defined: if `(v, w)` is a pair with source `v`, then `w` neighbours `v`.
    intro p hp
    simp only [mem_filter, mem_orderedPairs] at hp
    simpa [hp.2, mem_neighborFinset] using hp.1
  · -- Injective: two pairs in the same fibre agree on their source, so if they
    -- also agree on their target they are equal.
    intro p hp q hq h
    simp only [mem_filter, mem_orderedPairs] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) h
  · -- Surjective: every neighbour `w` of `v` arises from the pair `(v, w)`.
    intro w hw
    refine ⟨(v, w), ?_, rfl⟩
    simp only [mem_filter, mem_orderedPairs]
    simpa [mem_neighborFinset] using hw

/-! ### Edges -/

/-- The unordered pair underlying an ordered pair: `(v, w) ↦ {v, w}`. -/
def toEdge (p : V × V) : Sym2 V := s(p.1, p.2)

variable [DecidableEq V]

/-- The edges of `G`, as unordered pairs of adjacent vertices: the image of the
ordered pairs under `toEdge`. -/
def edgeFinset : Finset (Sym2 V) :=
  G.orderedPairs.image toEdge

theorem mk_mem_edgeFinset (v w : V) : s(v, w) ∈ G.edgeFinset ↔ G.Adj v w := by
  simp only [edgeFinset, mem_image, mem_orderedPairs, toEdge, Sym2.eq_iff]
  constructor
  · -- If `{v, w}` is the edge underlying some pair `(a, b)`, then `(a, b)` is
    -- either `(v, w)` or `(w, v)`; adjacency follows, using symmetry.
    rintro ⟨⟨a, b⟩, hab, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact hab
    · exact G.symm hab
  · -- Conversely, if `v` and `w` are adjacent then `(v, w)` is such a pair.
    intro h
    exact ⟨(v, w), h, Or.inl ⟨rfl, rfl⟩⟩

/-- Every edge carries exactly two ordered pairs. This is the step that uses
looplessness: `v ≠ w`, so `(v, w)` and `(w, v)` really are distinct. -/
theorem card_orderedPairs_fiber_eq_two (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    #{p ∈ G.orderedPairs | toEdge p = e} = 2 := by
  -- Every unordered pair is of the form `s(v, w)`, so we may assume `e = s(v, w)`.
  induction e using Sym2.ind with
  | _ v w =>
    rw [mk_mem_edgeFinset] at he
    -- Looplessness: an edge joins two *distinct* vertices.
    have hvw : v ≠ w := fun h => G.loopless v (h ▸ he)
    -- The pairs lying over `{v, w}` are precisely `(v, w)` and `(w, v)`.
    have hfiber : {p ∈ G.orderedPairs | toEdge p = s(v, w)} = {(v, w), (w, v)} := by
      ext p
      simp only [mem_filter, mem_orderedPairs, mem_insert, mem_singleton, toEdge, Sym2.eq_iff]
      constructor
      · rintro ⟨-, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨he, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨G.symm he, Or.inr ⟨rfl, rfl⟩⟩
    rw [hfiber]
    -- That two-element listing really has two elements, since `v ≠ w`.
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton]
    exact fun h => hvw (congrArg Prod.fst h)

/-- **Second count.** Grouping the ordered pairs by their underlying edge gives
twice the number of edges, since each edge contributes exactly two pairs. -/
theorem card_orderedPairs_eq_twice_card_edges : #G.orderedPairs = 2 * #G.edgeFinset := by
  -- Every ordered pair lies over one of the edges, so we may split them into
  -- fibres indexed by `edgeFinset`.
  have hlies : ∀ p ∈ G.orderedPairs, toEdge p ∈ G.edgeFinset :=
    fun p hp => Finset.mem_image_of_mem toEdge hp
  calc #G.orderedPairs
      = ∑ e ∈ G.edgeFinset, #{p ∈ G.orderedPairs | toEdge p = e} :=
        Finset.card_eq_sum_card_fiberwise hlies
    _ = ∑ _e ∈ G.edgeFinset, 2 := Finset.sum_congr rfl G.card_orderedPairs_fiber_eq_two
    _ = #G.edgeFinset * 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * #G.edgeFinset := mul_comm _ _

/-- **The handshake lemma.** The degrees of a finite simple graph sum to twice
its number of edges — because both quantities count the ordered pairs. -/
theorem sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * #G.edgeFinset :=
  calc ∑ v, G.degree v
      = #G.orderedPairs := G.card_orderedPairs_eq_sum_degrees.symm
    _ = 2 * #G.edgeFinset := G.card_orderedPairs_eq_twice_card_edges

end Graph
