module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The birthday paradox for non-backtracking walks

This file formalizes the statement of Theorem 1.1 in
`human_proof_nonbacktracking_walks.tex`.

A walk of length `k` is represented by the `k + 1` vertices it visits.  Its
first oriented edge is fixed, and the probability in the theorem is written
explicitly as a ratio of finite cardinalities.
-/


@[expose] public section

variable {V : Type*} [Fintype V]

universe u

/-- An edge of `G` together with an orientation from `tail` to `head`. -/
structure OrientedEdge (G : SimpleGraph V) where
  tail : V
  head : V
  adjacent : G.Adj tail head

/-- Every vertex of `G` has exactly `d` neighbors. -/
def IsRegularOfDegree (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, Nat.card (G.neighborSet v) = d

/--
A length-`k` non-backtracking walk in `G` whose first oriented edge is `start`.

The walk visits `vertices 0, ..., vertices k`.  The last field says that a
vertex can never be revisited exactly two steps later; because consecutive
vertices are adjacent, this is precisely the non-backtracking condition.
-/
structure NonbacktrackingWalk (G : SimpleGraph V) (start : OrientedEdge G) (k : ℕ) where
  vertices : Fin (k + 1) → V
  length_pos : 0 < k
  startsAtTail : vertices 0 = start.tail
  startsAtHead : vertices ⟨1, Nat.succ_lt_succ length_pos⟩ = start.head
  adjacent : ∀ i : Fin k, G.Adj (vertices i.castSucc) (vertices i.succ)
  noBacktrack :
    ∀ (i : Fin (k + 1)) (hi : (i : ℕ) + 2 < k + 1),
      vertices i ≠ vertices ⟨(i : ℕ) + 2, hi⟩

/-- A non-backtracking walk that visits no vertex more than once. -/
def SimpleNonbacktrackingWalk (G : SimpleGraph V) (start : OrientedEdge G) (k : ℕ) :=
  {w : NonbacktrackingWalk G start k // Function.Injective w.vertices}

/-- The number of length-`k` non-backtracking walks starting with `start`. -/
noncomputable def walkCount (G : SimpleGraph V) (start : OrientedEdge G) (k : ℕ) : ℕ :=
  Nat.card (NonbacktrackingWalk G start k)

/-- The number of those walks that are simple. -/
noncomputable def simpleWalkCount
    (G : SimpleGraph V) (start : OrientedEdge G) (k : ℕ) : ℕ :=
  Nat.card (SimpleNonbacktrackingWalk G start k)

/--
The probability that a uniformly random length-`k` non-backtracking walk
starting with `start` is simple.
-/
noncomputable def simpleProbability
    (G : SimpleGraph V) (start : OrientedEdge G) (k : ℕ) : ℝ :=
  (simpleWalkCount G start k : ℝ) / (walkCount G start k : ℝ)

/--
Theorem 1.1: on every finite simple `d`-regular graph with `d ≥ 3`, a
non-backtracking walk of length more than a constant times the square root of
the number of vertices is unlikely to be simple.  The quantifier order makes
the constant depend only on `d` and `ε`.
-/
theorem birthday_paradox
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G),
          C * Real.sqrt (Fintype.card V : ℝ) < (k : ℝ) →
            simpleProbability G start k < ε := by
  sorry
