import Mathlib

/-!
# The birthday paradox for non-backtracking walks

This file repeats the formal statement of Theorem 0.1 from
`human_proof_nonbacktracking_walks.tex` and proves it.

A walk of length `k` has `k` oriented edges and `k + 1` visited vertices.
The probability is the ratio of the finite number of vertex-simple walks to
all non-backtracking walks with the prescribed first oriented edge.

The proof follows the paper's local-plan and excursion-reversal argument.  At
each vertex we label the `d` incident half-edges by `Fin d` and use the
nonzero cyclic translations as local plans.  This inverse-closed family acts
sharply transitively on the `d - 1` legal continuations, so averaging over it
has exactly the same fixed-start walk distribution used in the paper.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false



set_option linter.unusedSectionVars false

namespace NonbacktrackingWalks

noncomputable section

variable {V : Type*} [Fintype V]

def IsRegularOfDegree (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∀ v : V, Nat.card (G.neighborSet v) = d

variable (d : ℕ) [NeZero d]

/-- A nonzero translation in the cyclic group `Fin d`. -/
abbrev Offset := {a : Fin d // a ≠ 0}

theorem card_offset : Fintype.card (Offset d) = d - 1 := by
  classical
  rw [Fintype.card_subtype_compl (fun a : Fin d ↦ a = 0)]
  simp

theorem natCard_offset : Nat.card (Offset d) = d - 1 := by
  rw [Nat.card_eq_fintype_card, card_offset]

def negOffset (a : Offset d) : Offset d :=
  ⟨-a.1, neg_ne_zero.mpr a.2⟩

@[simp] theorem negOffset_val (a : Offset d) : (negOffset d a).1 = -a.1 := rfl

@[simp] theorem negOffset_negOffset (a : Offset d) :
    negOffset d (negOffset d a) = a := by
  apply Subtype.ext
  simp

section Graph

variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)

local instance graphAdjDecidable : DecidableRel G.Adj := Classical.decRel _
local instance vertexDecidableEq : DecidableEq V := Classical.decEq _

/-- A fixed cyclic label for the `d` neighbors of each vertex. -/
def neighborPorts (v : V) : G.neighborSet v ≃ Fin d :=
  Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card]
    exact hG v)

/-- Translation by a nonzero cyclic offset, transported to a neighbor set. -/
def localRotation (a : Offset d) (v : V) :
    G.neighborSet v ≃ G.neighborSet v :=
  (neighborPorts d G hG v).trans <|
    (Equiv.addRight a.1).trans (neighborPorts d G hG v).symm

@[simp] theorem neighborPorts_localRotation (a : Offset d) (v : V)
    (x : G.neighborSet v) :
    neighborPorts d G hG v (localRotation d G hG a v x) =
      neighborPorts d G hG v x + a.1 := by
  simp [localRotation]

theorem localRotation_ne (a : Offset d) (v : V) (x : G.neighborSet v) :
    localRotation d G hG a v x ≠ x := by
  intro h
  have hp := congrArg (neighborPorts d G hG v) h
  simp only [neighborPorts_localRotation] at hp
  apply a.2
  apply add_left_cancel (a := neighborPorts d G hG v x)
  simpa using hp

theorem localRotation_injective_offset (v : V) (x : G.neighborSet v) :
    Function.Injective (fun a : Offset d ↦ localRotation d G hG a v x) := by
  intro a b hab
  apply Subtype.ext
  have hp := congrArg (neighborPorts d G hG v) hab
  simp only [neighborPorts_localRotation] at hp
  exact add_left_cancel hp

/-- Every legal non-backtracking successor is selected by one unique offset. -/
theorem existsUnique_localRotation {v : V} {x y : G.neighborSet v} (hxy : y ≠ x) :
    ∃! a : Offset d, localRotation d G hG a v x = y := by
  let a0 : Fin d := neighborPorts d G hG v y - neighborPorts d G hG v x
  have ha0 : a0 ≠ 0 := by
    intro ha
    have heq : neighborPorts d G hG v y = neighborPorts d G hG v x := by
      exact sub_eq_zero.mp ha
    exact hxy ((neighborPorts d G hG v).injective heq)
  let chosen : Offset d := ⟨a0, ha0⟩
  have hchosen : localRotation d G hG chosen v x = y := by
    apply (neighborPorts d G hG v).injective
    simp only [neighborPorts_localRotation]
    dsimp [chosen, a0]
    abel
  refine ⟨chosen, hchosen, ?_⟩
  intro a ha
  exact localRotation_injective_offset d G hG v x (ha.trans hchosen.symm)

theorem localRotation_neg (a : Offset d) (v : V) :
    (localRotation d G hG a v).symm =
      localRotation d G hG (negOffset d a) v := by
  apply Equiv.ext
  intro x
  apply (neighborPorts d G hG v).injective
  have h := congrArg (neighborPorts d G hG v)
    ((localRotation d G hG a v).apply_symm_apply x)
  simp only [neighborPorts_localRotation] at h ⊢
  rw [← h]
  simp

/-- Translation data at every vertex. -/
abbrev RotationSystem (V : Type*) := V → Offset d

/-- Oriented edges, in a representation convenient for the permutation proof. -/
abbrev Dart := Σ v : V, G.neighborSet v

namespace Dart

def tail (e : Dart G) : V := e.1
def head (e : Dart G) : V := e.2.1
theorem adjacent (e : Dart G) : G.Adj e.tail e.head := e.2.2

@[ext] theorem ext {e f : Dart G} (ht : e.tail = f.tail) (hh : e.head = f.head) :
    e = f := by
  rcases e with ⟨et, eh, he⟩
  rcases f with ⟨ft, fh, hf⟩
  simp only [tail] at ht
  subst ft
  simp only [head] at hh
  subst fh
  rfl

def reverse : Dart G ≃ Dart G where
  toFun e := ⟨e.head, ⟨e.tail, e.adjacent.symm⟩⟩
  invFun e := ⟨e.head, ⟨e.tail, e.adjacent.symm⟩⟩
  left_inv e := by rcases e with ⟨u,v,h⟩; rfl
  right_inv e := by rcases e with ⟨u,v,h⟩; rfl

@[simp] theorem tail_reverse (e : Dart G) : (reverse G e).tail = e.head := rfl
@[simp] theorem head_reverse (e : Dart G) : (reverse G e).head = e.tail := rfl
@[simp] theorem reverse_reverse (e : Dart G) : reverse G (reverse G e) = e := by
  rcases e with ⟨u,v,h⟩
  rfl

end Dart

def rotate (rho : RotationSystem d V) : Dart G ≃ Dart G :=
  Equiv.sigmaCongrRight fun v ↦ localRotation d G hG (rho v) v

/-- The plan permutation: reverse a dart, then translate at its new tail. -/
def phi (rho : RotationSystem d V) : Dart G ≃ Dart G :=
  (Dart.reverse G).trans (rotate d G hG rho)

@[simp] theorem Dart.tail_phi (rho : RotationSystem d V) (e : Dart G) :
    (phi d G hG rho e).tail = e.head := rfl

@[simp] theorem Dart.head_phi (rho : RotationSystem d V) (e : Dart G) :
    (phi d G hG rho e).head =
      (localRotation d G hG (rho e.head) e.head
        ⟨e.tail, e.adjacent.symm⟩).1 := rfl

theorem Dart.head_phi_ne_tail (rho : RotationSystem d V) (e : Dart G) :
    (phi d G hG rho e).head ≠ e.tail := by
  intro heq
  apply localRotation_ne d G hG (rho e.head) e.head
    ⟨e.tail, e.adjacent.symm⟩
  apply Subtype.ext
  exact heq

/-- Negating every local offset inverts the rotation part. -/
def inverseRotationSystem (rho : RotationSystem d V) : RotationSystem d V :=
  fun v ↦ negOffset d (rho v)

theorem rotate_inverse (rho : RotationSystem d V) :
    (rotate d G hG rho).symm = rotate d G hG (inverseRotationSystem d rho) := by
  apply Equiv.ext
  rintro ⟨v,x⟩
  apply Dart.ext
  · rfl
  · change ((localRotation d G hG (rho v) v).symm x).1 =
      (localRotation d G hG (negOffset d (rho v)) v x).1
    rw [localRotation_neg]

/-! ### Fixed-start walks and their exact plan encoding -/

structure OrientedEdge where
  tail : V
  head : V
  adjacent : G.Adj tail head

structure NonbacktrackingWalk (start : OrientedEdge G) (k : ℕ) where
  vertices : Fin (k + 1) → V
  length_pos : 0 < k
  startsAtTail : vertices 0 = start.tail
  startsAtHead : vertices ⟨1, Nat.succ_lt_succ length_pos⟩ = start.head
  adjacent : ∀ i : Fin k, G.Adj (vertices i.castSucc) (vertices i.succ)
  noBacktrack :
    ∀ (i : Fin (k + 1)) (hi : (i : ℕ) + 2 < k + 1),
      vertices i ≠ vertices ⟨(i : ℕ) + 2, hi⟩

def SimpleNonbacktrackingWalk (start : OrientedEdge G) (k : ℕ) :=
  {w : NonbacktrackingWalk G start k // Function.Injective w.vertices}

@[ext] theorem NonbacktrackingWalk.ext {start : OrientedEdge G} {k : ℕ}
    {w w' : NonbacktrackingWalk G start k} (h : w.vertices = w'.vertices) : w = w' := by
  cases w
  cases w'
  cases h
  rfl

instance nonbacktrackingWalkFinite (start : OrientedEdge G) (k : ℕ) :
    Finite (NonbacktrackingWalk G start k) :=
  Finite.of_injective (fun w ↦ w.vertices) fun _ _ h ↦
    NonbacktrackingWalk.ext (G := G) h

instance simpleNonbacktrackingWalkFinite (start : OrientedEdge G) (k : ℕ) :
    Finite (SimpleNonbacktrackingWalk G start k) :=
  Finite.of_injective Subtype.val Subtype.val_injective

def startDart (start : OrientedEdge G) : Dart G :=
  ⟨start.tail, ⟨start.head, start.adjacent⟩⟩

def orbitDart (start : OrientedEdge G) (rho : RotationSystem d V) (t : ℕ) : Dart G :=
  (phi d G hG rho)^[t] (startDart G start)

def orbitVertex (start : OrientedEdge G) (rho : RotationSystem d V) (t : ℕ) : V :=
  (orbitDart d G hG start rho t).tail

@[simp] theorem orbitDart_zero (start : OrientedEdge G) (rho : RotationSystem d V) :
    orbitDart d G hG start rho 0 = startDart G start := rfl

theorem orbitDart_succ (start : OrientedEdge G) (rho : RotationSystem d V) (t : ℕ) :
    orbitDart d G hG start rho (t + 1) =
      phi d G hG rho (orbitDart d G hG start rho t) := by
  simp only [orbitDart, Function.iterate_succ_apply']

theorem orbitVertex_succ (start : OrientedEdge G) (rho : RotationSystem d V) (t : ℕ) :
    orbitVertex d G hG start rho (t + 1) =
      (orbitDart d G hG start rho t).head := by
  rw [orbitVertex, orbitDart_succ]
  exact Dart.tail_phi d G hG _ _

def encodedWalk (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (hk : 0 < k) : NonbacktrackingWalk G start k where
  vertices i := orbitVertex d G hG start rho i
  length_pos := hk
  startsAtTail := rfl
  startsAtHead := by
    change orbitVertex d G hG start rho 1 = start.head
    rw [show (1 : ℕ) = 0 + 1 by omega, orbitVertex_succ, orbitDart_zero]
    rfl
  adjacent i := by
    rw [show (i.succ : ℕ) = (i.castSucc : ℕ) + 1 by rfl,
      orbitVertex_succ]
    exact (orbitDart d G hG start rho i).adjacent
  noBacktrack i hi := by
    intro heq
    have hne := Dart.head_phi_ne_tail d G hG rho
      (orbitDart d G hG start rho i)
    change (orbitDart d G hG start rho i).tail =
      (orbitDart d G hG start rho (i + 2)).tail at heq
    rw [show (i : ℕ) + 2 = ((i : ℕ) + 1) + 1 by omega,
      orbitDart_succ, Dart.tail_phi, orbitDart_succ] at heq
    exact hne heq.symm

def IsGood (start : OrientedEdge G) (rho : RotationSystem d V) (k : ℕ) : Prop :=
  Function.Injective (fun i : Fin (k + 1) ↦ orbitVertex d G hG start rho i)

def GoodOmega (start : OrientedEdge G) (k : ℕ) :=
  {rho : RotationSystem d V // IsGood d G hG start rho k}

instance rotationSystemFinite : Finite (RotationSystem d V) := inferInstance

instance goodOmegaFinite (start : OrientedEdge G) (k : ℕ) :
    Finite (GoodOmega d G hG start k) :=
  Finite.of_injective Subtype.val Subtype.val_injective

def decodeGood (start : OrientedEdge G) {k : ℕ} (hk : 0 < k)
    (rho : GoodOmega d G hG start k) : SimpleNonbacktrackingWalk G start k :=
  ⟨encodedWalk d G hG start rho.1 k hk, rho.2⟩

section Encoding

variable {m : ℕ} (start : OrientedEdge G)

def internalVertex (w : NonbacktrackingWalk G start (m + 1)) (i : Fin m) : V :=
  w.vertices ⟨i + 1, by omega⟩

theorem internalVertex_injective (w : SimpleNonbacktrackingWalk G start (m + 1)) :
    Function.Injective (internalVertex G start w.1) := by
  intro i j hij
  have hfin := w.2 hij
  apply Fin.ext
  simpa [internalVertex] using congrArg Fin.val hfin

def incomingNeighbor (w : NonbacktrackingWalk G start (m + 1)) (i : Fin m) :
    G.neighborSet (internalVertex G start w i) :=
  ⟨w.vertices ⟨i, by omega⟩, (w.adjacent ⟨i, by omega⟩).symm⟩

def outgoingNeighbor (w : NonbacktrackingWalk G start (m + 1)) (i : Fin m) :
    G.neighborSet (internalVertex G start w i) :=
  ⟨w.vertices ⟨i + 2, by omega⟩,
    w.adjacent ⟨i + 1, Nat.succ_lt_succ i.isLt⟩⟩

theorem outgoing_ne_incoming (w : NonbacktrackingWalk G start (m + 1)) (i : Fin m) :
    outgoingNeighbor G start w i ≠ incomingNeighbor G start w i := by
  intro heq
  have hval := congrArg Subtype.val heq
  let ii : Fin (m + 1 + 1) :=
    ⟨i, lt_trans i.isLt (by omega)⟩
  have hi2 : (ii : ℕ) + 2 < (m + 1) + 1 := by
    change (i : ℕ) + 2 < m + 2
    exact Nat.add_lt_add_right i.isLt 2
  exact w.noBacktrack ii hi2 hval.symm

noncomputable def requiredOffset (w : NonbacktrackingWalk G start (m + 1))
    (i : Fin m) : Offset d :=
  Classical.choose (existsUnique_localRotation d G hG (outgoing_ne_incoming G start w i))

theorem requiredOffset_spec (w : NonbacktrackingWalk G start (m + 1)) (i : Fin m) :
    localRotation d G hG (requiredOffset d G hG start w i)
      (internalVertex G start w i) (incomingNeighbor G start w i) =
        outgoingNeighbor G start w i :=
  (Classical.choose_spec
    (existsUnique_localRotation d G hG (outgoing_ne_incoming G start w i))).1

theorem requiredOffset_unique (w : NonbacktrackingWalk G start (m + 1))
    (i : Fin m) (a : Offset d)
    (ha : localRotation d G hG a (internalVertex G start w i)
      (incomingNeighbor G start w i) = outgoingNeighbor G start w i) :
    a = requiredOffset d G hG start w i :=
  (Classical.choose_spec
    (existsUnique_localRotation d G hG (outgoing_ne_incoming G start w i))).2 a ha

def HasForcedOffsets (w : NonbacktrackingWalk G start (m + 1))
    (rho : RotationSystem d V) : Prop :=
  ∀ i : Fin m, rho (internalVertex G start w i) = requiredOffset d G hG start w i

def walkDartAt (w : NonbacktrackingWalk G start (m + 1))
    (i : ℕ) (hi : i < m + 1) : Dart G :=
  ⟨w.vertices ⟨i, by omega⟩,
    ⟨w.vertices ⟨i + 1, by omega⟩, w.adjacent ⟨i, hi⟩⟩⟩

@[simp] theorem walkDartAt_tail (w : NonbacktrackingWalk G start (m + 1))
    (i : ℕ) (hi : i < m + 1) :
    (walkDartAt G start w i hi).tail = w.vertices ⟨i, by omega⟩ := rfl

@[simp] theorem walkDartAt_head (w : NonbacktrackingWalk G start (m + 1))
    (i : ℕ) (hi : i < m + 1) :
    (walkDartAt G start w i hi).head = w.vertices ⟨i + 1, by omega⟩ := rfl

theorem orbitDart_eq_walkDartAt_of_forced
    (w : NonbacktrackingWalk G start (m + 1)) (rho : RotationSystem d V)
    (hR : HasForcedOffsets d G hG start w rho) (i : ℕ) (hi : i < m + 1) :
    orbitDart d G hG start rho i = walkDartAt G start w i hi := by
  induction i with
  | zero =>
      apply Dart.ext
      · exact w.startsAtTail.symm
      · exact w.startsAtHead.symm
  | succ i ih =>
      have him : i < m := by omega
      rw [orbitDart_succ]
      rw [ih (by omega)]
      apply Dart.ext
      · rfl
      · change
          (localRotation d G hG
            (rho (internalVertex G start w ⟨i, him⟩))
            (internalVertex G start w ⟨i, him⟩)
            (incomingNeighbor G start w ⟨i, him⟩) : V) =
              (outgoingNeighbor G start w ⟨i, him⟩ : V)
        rw [hR ⟨i, him⟩]
        exact congrArg Subtype.val (requiredOffset_spec d G hG start w ⟨i, him⟩)

theorem encodedWalk_eq_of_forced
    (w : NonbacktrackingWalk G start (m + 1)) (rho : RotationSystem d V)
    (hR : HasForcedOffsets d G hG start w rho) :
    encodedWalk d G hG start rho (m + 1) (by omega) = w := by
  apply NonbacktrackingWalk.ext
  funext i
  change orbitVertex d G hG start rho i = w.vertices i
  by_cases hi : i.val < m + 1
  · rw [orbitVertex, orbitDart_eq_walkDartAt_of_forced d G hG start w rho hR i hi]
    rfl
  · have hieq : i.val = m + 1 := by omega
    change (orbitDart d G hG start rho i).tail = w.vertices i
    rw [show (i : ℕ) = m + 1 by omega, orbitDart_succ,
      orbitDart_eq_walkDartAt_of_forced d G hG start w rho hR m (by omega)]
    rw [Dart.tail_phi]
    exact congrArg w.vertices (Fin.ext hieq).symm

def IsInternal (w : NonbacktrackingWalk G start (m + 1)) (v : V) : Prop :=
  ∃ i : Fin m, internalVertex G start w i = v

noncomputable def internalIndexOf (w : NonbacktrackingWalk G start (m + 1))
    (v : V) (hv : IsInternal G start w v) : Fin m := Classical.choose hv

theorem internalIndexOf_spec (w : NonbacktrackingWalk G start (m + 1))
    (v : V) (hv : IsInternal G start w v) :
    internalVertex G start w (internalIndexOf G start w v hv) = v :=
  Classical.choose_spec hv

abbrev ForcedRotations (w : SimpleNonbacktrackingWalk G start (m + 1)) :=
  {rho : RotationSystem d V // HasForcedOffsets d G hG start w.1 rho}

abbrev FreeOffsets (w : SimpleNonbacktrackingWalk G start (m + 1)) :=
  ({v : V // ¬ IsInternal G start w.1 v} → Offset d)

noncomputable def completeRotation (w : SimpleNonbacktrackingWalk G start (m + 1))
    (f : FreeOffsets d G start w) : RotationSystem d V := by
  classical
  exact fun v ↦ if hv : IsInternal G start w.1 v then
    requiredOffset d G hG start w.1 (internalIndexOf G start w.1 v hv)
  else f ⟨v, hv⟩

theorem completeRotation_forced (w : SimpleNonbacktrackingWalk G start (m + 1))
    (f : FreeOffsets d G start w) :
    HasForcedOffsets d G hG start w.1 (completeRotation d G hG start w f) := by
  intro i
  rw [completeRotation, dif_pos ⟨i, rfl⟩]
  have hidx : internalIndexOf G start w.1 (internalVertex G start w.1 i) ⟨i, rfl⟩ = i := by
    apply internalVertex_injective G start w
    exact internalIndexOf_spec G start w.1 _ _
  rw [hidx]

def restrictRotation (w : SimpleNonbacktrackingWalk G start (m + 1))
    (rho : ForcedRotations d G hG start w) : FreeOffsets d G start w :=
  fun v ↦ rho.1 v

noncomputable def forcedRotationsEquivFreeOffsets
    (w : SimpleNonbacktrackingWalk G start (m + 1)) :
    ForcedRotations d G hG start w ≃ FreeOffsets d G start w where
  toFun := restrictRotation d G hG start w
  invFun f := ⟨completeRotation d G hG start w f,
    completeRotation_forced d G hG start w f⟩
  left_inv rho := by
    classical
    apply Subtype.ext
    funext v
    change (if hv : IsInternal G start w.1 v then
      requiredOffset d G hG start w.1 (internalIndexOf G start w.1 v hv)
      else rho.1 v) = rho.1 v
    by_cases hv : IsInternal G start w.1 v
    · rw [dif_pos hv]
      have hf := rho.2 (internalIndexOf G start w.1 v hv)
      rw [internalIndexOf_spec G start w.1 v hv] at hf
      exact hf.symm
    · rw [dif_neg hv]
  right_inv f := by
    classical
    funext v
    change (if hv : IsInternal G start w.1 v then
      requiredOffset d G hG start w.1 (internalIndexOf G start w.1 v hv)
      else f ⟨v, hv⟩) = f v
    rw [dif_neg v.2]

noncomputable def internalVerticesEquiv
    (w : SimpleNonbacktrackingWalk G start (m + 1)) :
    Fin m ≃ {v : V // IsInternal G start w.1 v} :=
  Equiv.ofBijective
    (fun i ↦ ⟨internalVertex G start w.1 i, ⟨i, rfl⟩⟩)
    ⟨by
      intro i j hij
      apply internalVertex_injective G start w
      exact congrArg Subtype.val hij,
    by
      rintro ⟨v, i, hi⟩
      exact ⟨i, Subtype.ext hi⟩⟩

theorem card_internalVertices (w : SimpleNonbacktrackingWalk G start (m + 1)) :
    Nat.card {v : V // IsInternal G start w.1 v} = m := by
  rw [Nat.card_congr (internalVerticesEquiv G start w).symm]
  simp

theorem card_freeOffsets (w : SimpleNonbacktrackingWalk G start (m + 1)) :
    Nat.card (FreeOffsets d G start w) =
      (d - 1) ^ (Fintype.card V - m) := by
  rw [Nat.card_fun, natCard_offset]
  congr 1
  classical
  letI : Fintype {v : V // IsInternal G start w.1 v} := Fintype.ofFinite _
  letI : Fintype {v : V // ¬ IsInternal G start w.1 v} := Fintype.ofFinite _
  have hc : Fintype.card {v : V // IsInternal G start w.1 v} = m := by
    rw [← Nat.card_eq_fintype_card]
    exact card_internalVertices G start w
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hc]

theorem card_forcedRotations (w : SimpleNonbacktrackingWalk G start (m + 1)) :
    Nat.card (ForcedRotations d G hG start w) =
      (d - 1) ^ (Fintype.card V - m) := by
  rw [Nat.card_congr (forcedRotationsEquivFreeOffsets d G hG start w)]
  exact card_freeOffsets d G start w

theorem orbitDart_eq_encodedWalkDartAt (rho : RotationSystem d V)
    (i : ℕ) (hi : i < m + 1) :
    orbitDart d G hG start rho i =
      walkDartAt G start (encodedWalk d G hG start rho (m + 1) (by omega)) i hi := by
  apply Dart.ext
  · rfl
  · change (orbitDart d G hG start rho i).head =
      orbitVertex d G hG start rho (i + 1)
    exact (orbitVertex_succ d G hG start rho i).symm

theorem encodedWalk_hasForcedOffsets (rho : RotationSystem d V) :
    HasForcedOffsets d G hG start
      (encodedWalk d G hG start rho (m + 1) (by omega)) rho := by
  intro i
  apply requiredOffset_unique d G hG start _ i
  apply Subtype.ext
  have hi0 : (i : ℕ) < m + 1 := by omega
  have hi1 : (i : ℕ) + 1 < m + 1 := by omega
  have hstep :
      phi d G hG rho
          (walkDartAt G start
            (encodedWalk d G hG start rho (m + 1) (by omega)) i hi0) =
        walkDartAt G start
          (encodedWalk d G hG start rho (m + 1) (by omega)) (i + 1) hi1 := by
    rw [← orbitDart_eq_encodedWalkDartAt d G hG start rho i hi0]
    rw [← orbitDart_eq_encodedWalkDartAt d G hG start rho (i + 1) hi1]
    exact (orbitDart_succ d G hG start rho i).symm
  have hhead := congrArg (Dart.head G) hstep
  simp only [Dart.head_phi, walkDartAt_head, walkDartAt_tail, internalVertex,
    incomingNeighbor, outgoingNeighbor, show (i : ℕ) + 1 + 1 = i + 2 by omega]
    at hhead
  exact hhead

noncomputable def goodToWalkForced (rho : GoodOmega d G hG start (m + 1)) :
    Σ w : SimpleNonbacktrackingWalk G start (m + 1), ForcedRotations d G hG start w :=
  ⟨decodeGood d G hG start (by omega) rho,
    ⟨rho.1, encodedWalk_hasForcedOffsets d G hG start rho.1⟩⟩

noncomputable def walkForcedToGood
    (x : Σ w : SimpleNonbacktrackingWalk G start (m + 1),
      ForcedRotations d G hG start w) : GoodOmega d G hG start (m + 1) := by
  refine ⟨x.2.1, ?_⟩
  change Function.Injective
    (encodedWalk d G hG start x.2.1 (m + 1) (by omega)).vertices
  rw [encodedWalk_eq_of_forced d G hG start x.1.1 x.2.1 x.2.2]
  exact x.1.2

noncomputable def goodOmegaEquivWalkForced :
    GoodOmega d G hG start (m + 1) ≃
      (Σ w : SimpleNonbacktrackingWalk G start (m + 1),
        ForcedRotations d G hG start w) where
  toFun := goodToWalkForced d G hG start
  invFun := walkForcedToGood d G hG start
  left_inv rho := by
    apply Subtype.ext
    rfl
  right_inv x := by
    rcases x with ⟨w, rho⟩
    have hw : encodedWalk d G hG start rho.1 (m + 1) (by omega) = w.1 :=
      encodedWalk_eq_of_forced d G hG start w.1 rho.1 rho.2
    have hws : decodeGood d G hG start (by omega)
        (walkForcedToGood d G hG start ⟨w, rho⟩) = w := by
      apply Subtype.ext
      exact hw
    apply Sigma.ext hws
    apply (Subtype.heq_iff_coe_eq (fun S ↦ by
      change HasForcedOffsets d G hG start
        (decodeGood d G hG start (by omega)
          (walkForcedToGood d G hG start ⟨w, rho⟩)).1 S ↔
        HasForcedOffsets d G hG start w.1 S
      rw [hws])).2
    rfl

theorem card_goodOmega_succ :
    Nat.card (GoodOmega d G hG start (m + 1)) =
      Nat.card (SimpleNonbacktrackingWalk G start (m + 1)) *
        (d - 1) ^ (Fintype.card V - m) := by
  let : Fintype (GoodOmega d G hG start (m + 1)) := Fintype.ofFinite _
  let : Fintype (SimpleNonbacktrackingWalk G start (m + 1)) := Fintype.ofFinite _
  rw [Nat.card_congr (goodOmegaEquivWalkForced d G hG start), Nat.card_sigma]
  simp_rw [card_forcedRotations d G hG start]
  simp

end Encoding

/-! ### Deviation indices and first-return bases -/

def internalTime {k : ℕ} (i : Fin (k - 1)) : ℕ := i + 1

theorem internalTime_lt {k : ℕ} (i : Fin (k - 1)) : internalTime i < k := by
  simp only [internalTime]
  omega

/-- A raw deviation chooses an internal path time and a replacement nonzero offset. -/
abbrev DeviationIndex (k : ℕ) := Fin (k - 1) × Offset d

def currentOffset (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (i : Fin (k - 1)) : Offset d :=
  rho (orbitVertex d G hG start rho (internalTime i))

def IsValidDeviation (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (q : DeviationIndex d k) : Prop :=
  q.2 ≠ currentOffset d G hG start rho q.1

def ValidDeviation (start : OrientedEdge G) (rho : RotationSystem d V) (k : ℕ) :=
  {q : DeviationIndex d k // IsValidDeviation d G hG start rho q}

noncomputable instance validDeviationFintype (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ) :
    Fintype (ValidDeviation d G hG start rho k) := by
  classical
  unfold ValidDeviation
  infer_instance

def validDeviationEquivSigma (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) :
    ValidDeviation d G hG start rho k ≃
      Σ i : Fin (k - 1), {a : Offset d // a ≠ currentOffset d G hG start rho i} where
  toFun q := ⟨q.1.1, ⟨q.1.2, q.2⟩⟩
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv q := by rcases q with ⟨⟨i,a⟩,h⟩; rfl
  right_inv q := by rcases q with ⟨i,a,h⟩; rfl

theorem natCard_offset_ne (a : Offset d) :
    Nat.card {b : Offset d // b ≠ a} = d - 2 := by
  classical
  letI : Fintype {b : Offset d // b ≠ a} := Fintype.ofFinite _
  letI : Fintype {b : Offset d // b = a} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun b : Offset d ↦ b = a)]
  rw [card_offset]
  simp only [Fintype.card_subtype_eq]
  have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  omega

theorem natCard_validDeviation (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) :
    Nat.card (ValidDeviation d G hG start rho k) = (k - 1) * (d - 2) := by
  classical
  rw [Nat.card_congr (validDeviationEquivSigma d G hG start rho k), Nat.card_sigma]
  simp_rw [natCard_offset_ne]
  simp

def setOffsetAt (rho : RotationSystem d V) (v₀ : V) (a : Offset d) :
    RotationSystem d V :=
  fun v ↦ if v = v₀ then a else rho v

@[simp] theorem setOffsetAt_eq (rho : RotationSystem d V) (v : V) (a : Offset d) :
    setOffsetAt d rho v a v = a := by simp [setOffsetAt]

theorem setOffsetAt_ne (rho : RotationSystem d V) {v v₀ : V} (a : Offset d)
    (h : v ≠ v₀) : setOffsetAt d rho v₀ a v = rho v := by
  simp [setOffsetAt, h]

def deviationRotation (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (q : DeviationIndex d k) : RotationSystem d V :=
  setOffsetAt d rho (orbitVertex d G hG start rho (internalTime q.1)) q.2

/-- The first dart taken after replacing the offset at the selected path vertex. -/
def sideDart (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (q : DeviationIndex d k) : Dart G :=
  phi d G hG (deviationRotation d G hG start rho q)
    (orbitDart d G hG start rho q.1)

@[simp] theorem sideDart_tail (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (q : DeviationIndex d k) :
    (sideDart d G hG start rho q).tail =
      orbitVertex d G hG start rho (internalTime q.1) := by
  rw [sideDart, Dart.tail_phi]
  change (orbitDart d G hG start rho q.1).head = _
  exact (orbitVertex_succ d G hG start rho q.1).symm

/-- The neighbor from which the original path enters an internal path vertex. -/
def orbitIncomingNeighbor (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (i : Fin (k - 1)) :
    G.neighborSet (orbitDart d G hG start rho i).head :=
  ⟨(orbitDart d G hG start rho i).tail,
    (orbitDart d G hG start rho i).adjacent.symm⟩

@[simp] theorem sideDart_head (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (i : Fin (k - 1)) (a : Offset d) :
    (sideDart d G hG start rho (i, a)).head =
      (localRotation d G hG a
        (orbitDart d G hG start rho i).head
        (orbitIncomingNeighbor d G hG start rho i)).1 := by
  change
    (localRotation d G hG
      (setOffsetAt d rho
        (orbitVertex d G hG start rho (internalTime i)) a
        (orbitDart d G hG start rho i).head)
      (orbitDart d G hG start rho i).head
      ⟨(orbitDart d G hG start rho i).tail,
        (orbitDart d G hG start rho i).adjacent.symm⟩).1 = _
  have hv : (orbitDart d G hG start rho i).head =
      orbitVertex d G hG start rho (internalTime i) :=
    (orbitVertex_succ d G hG start rho i).symm
  rw [show orbitVertex d G hG start rho (internalTime i) =
      (orbitDart d G hG start rho i).head from hv.symm]
  simp only [setOffsetAt_eq]
  rfl

theorem sideDart_injective_offset (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (i : Fin (k - 1)) :
    Function.Injective (fun a : Offset d ↦
      sideDart d G hG start rho (i, a)) := by
  intro a b hab
  apply localRotation_injective_offset d G hG
    (orbitDart d G hG start rho i).head
    ⟨(orbitDart d G hG start rho i).tail,
      (orbitDart d G hG start rho i).adjacent.symm⟩
  apply Subtype.ext
  have hh := congrArg (Dart.head G) hab
  change
    (localRotation d G hG
      (setOffsetAt d rho
        (orbitVertex d G hG start rho (internalTime i)) a
        (orbitDart d G hG start rho i).head)
      (orbitDart d G hG start rho i).head
      ⟨(orbitDart d G hG start rho i).tail,
        (orbitDart d G hG start rho i).adjacent.symm⟩).1 =
    (localRotation d G hG
      (setOffsetAt d rho
        (orbitVertex d G hG start rho (internalTime i)) b
        (orbitDart d G hG start rho i).head)
      (orbitDart d G hG start rho i).head
      ⟨(orbitDart d G hG start rho i).tail,
        (orbitDart d G hG start rho i).adjacent.symm⟩).1 at hh
  have hv : (orbitDart d G hG start rho i).head =
      orbitVertex d G hG start rho (internalTime i) := by
    exact (orbitVertex_succ d G hG start rho i).symm
  simpa [hv] using hh

/-- The old-plan preimage of the first deviating dart. -/
def returnBase (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (q : DeviationIndex d k) : Dart G :=
  (phi d G hG rho).symm (sideDart d G hG start rho q)

@[simp] theorem phi_returnBase (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (q : DeviationIndex d k) :
    phi d G hG rho (returnBase d G hG start rho q) =
      sideDart d G hG start rho q :=
  (phi d G hG rho).apply_symm_apply _

@[simp] theorem returnBase_head (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (q : DeviationIndex d k) :
    (returnBase d G hG start rho q).head =
      orbitVertex d G hG start rho (internalTime q.1) := by
  calc
    (returnBase d G hG start rho q).head =
        (phi d G hG rho (returnBase d G hG start rho q)).tail := by
      rw [Dart.tail_phi]
    _ = (sideDart d G hG start rho q).tail :=
      congrArg (Dart.tail G) (phi_returnBase d G hG start rho q)
    _ = orbitVertex d G hG start rho (internalTime q.1) :=
      sideDart_tail d G hG start rho q

def pathVertices (start : OrientedEdge G) (rho : RotationSystem d V) (k : ℕ) :
    Finset V :=
  Finset.univ.image fun i : Fin (k + 1) ↦ orbitVertex d G hG start rho i

theorem mem_pathVertices (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (i : Fin (k + 1)) :
    orbitVertex d G hG start rho i ∈ pathVertices d G hG start rho k :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

def pathIncomingDarts (start : OrientedEdge G) (rho : RotationSystem d V) (k : ℕ) :
    Finset (Dart G) :=
  Finset.univ.filter fun e ↦ e.head ∈ pathVertices d G hG start rho k

theorem mem_pathIncomingDarts_iff (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (e : Dart G) :
    e ∈ pathIncomingDarts d G hG start rho k ↔
      e.head ∈ pathVertices d G hG start rho k := by
  simp [pathIncomingDarts]

include hG in
theorem natCard_dart : Nat.card (Dart G) = d * Fintype.card V := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [show ∀ v : V, Fintype.card (G.neighborSet v) = d by
    intro v
    rw [← Nat.card_eq_fintype_card]
    exact hG v]
  simp [mul_comm]

theorem returnBase_mem (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (q : DeviationIndex d k) :
    returnBase d G hG start rho q ∈ pathIncomingDarts d G hG start rho k := by
  rw [mem_pathIncomingDarts_iff, returnBase_head]
  exact mem_pathVertices d G hG start rho k
    ⟨internalTime q.1, lt_trans (internalTime_lt q.1) (Nat.lt_succ_self k)⟩

def validReturnBases (start : OrientedEdge G) (rho : RotationSystem d V) (k : ℕ) :
    ValidDeviation d G hG start rho k → pathIncomingDarts d G hG start rho k :=
  fun q ↦ ⟨returnBase d G hG start rho q.1, returnBase_mem d G hG start rho q.1⟩

theorem validReturnBases_injective (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Function.Injective (validReturnBases d G hG start rho.1 k) := by
  rintro ⟨⟨i,a⟩, ha⟩ ⟨⟨j,b⟩, hbvalid⟩ hqq
  have hb : returnBase d G hG start rho.1 (i,a) =
      returnBase d G hG start rho.1 (j,b) := congrArg Subtype.val hqq
  have hv : orbitVertex d G hG start rho.1 (internalTime i) =
      orbitVertex d G hG start rho.1 (internalTime j) := by
    simpa using congrArg (Dart.head G) hb
  have hiFin :
      (⟨internalTime i,
        lt_trans (internalTime_lt i) (Nat.lt_succ_self k)⟩ : Fin (k + 1)) =
      ⟨internalTime j,
        lt_trans (internalTime_lt j) (Nat.lt_succ_self k)⟩ := rho.2 hv
  have hi : i = j := by
    apply Fin.ext
    simpa [internalTime] using congrArg Fin.val hiFin
  subst j
  have hs : sideDart d G hG start rho.1 (i,a) =
      sideDart d G hG start rho.1 (i,b) := by
    exact (phi d G hG rho.1).symm.injective hb
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact sideDart_injective_offset d G hG start rho.1 i hs

namespace MiniFirstReturn

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
theorem exists_pos_pow_mem (p : Equiv.Perm X) (B : Finset X) (b : X) (hb : b ∈ B) :
    ∃ n : ℕ, 0 < n ∧ (p ^ n) b ∈ B := by
  refine ⟨orderOf p, orderOf_pos p, ?_⟩
  simpa using hb

noncomputable def time (p : Equiv.Perm X) (B : Finset X) (b : B) : ℕ :=
  Nat.find (exists_pos_pow_mem p B b b.property)

theorem time_pos (p : Equiv.Perm X) (B : Finset X) (b : B) :
    0 < time p B b :=
  (Nat.find_spec (exists_pos_pow_mem p B b b.property)).1

theorem pow_time_mem (p : Equiv.Perm X) (B : Finset X) (b : B) :
    (p ^ time p B b) (b : X) ∈ B :=
  (Nat.find_spec (exists_pos_pow_mem p B b b.property)).2

theorem pow_not_mem_of_lt_time (p : Equiv.Perm X) (B : Finset X) (b : B)
    {n : ℕ} (hn : 0 < n) (hnc : n < time p B b) :
    (p ^ n) (b : X) ∉ B := by
  intro hmem
  exact Nat.find_min (exists_pos_pow_mem p B b b.property) hnc ⟨hn, hmem⟩

noncomputable def endpoint (p : Equiv.Perm X) (B : Finset X) (b : B) : B :=
  ⟨(p ^ time p B b) (b : X), pow_time_mem p B b⟩

theorem endpoint_injective (p : Equiv.Perm X) (B : Finset X) :
    Function.Injective (endpoint p B) := by
  intro b b' hend
  have hend' :
      (p ^ time p B b) (b : X) = (p ^ time p B b') (b' : X) :=
    congrArg Subtype.val hend
  rcases le_total (time p B b) (time p B b') with hle | hle
  · obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hle
    have hbase : (b : X) = (p ^ q) (b' : X) := by
      apply (p ^ time p B b).injective
      simpa [hq, pow_add] using hend'
    have hqzero : q = 0 := by
      by_contra hne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hne
      have hqlt : q < time p B b' := by
        rw [hq]
        exact Nat.lt_add_of_pos_left (time_pos p B b)
      exact pow_not_mem_of_lt_time p B b' hqpos hqlt (hbase ▸ b.property)
    apply Subtype.ext
    simpa [hqzero] using hbase
  · obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hle
    have hbase : (b' : X) = (p ^ q) (b : X) := by
      apply (p ^ time p B b').injective
      simpa [hq, pow_add] using hend'.symm
    have hqzero : q = 0 := by
      by_contra hne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hne
      have hqlt : q < time p B b := by
        rw [hq]
        exact Nat.lt_add_of_pos_left (time_pos p B b')
      exact pow_not_mem_of_lt_time p B b hqpos hqlt (hbase ▸ b'.property)
    apply Subtype.ext
    simpa [hqzero] using hbase.symm

abbrev IntervalIndex {I : Type*} [Fintype I] (p : Equiv.Perm X) (B : Finset X)
    (bases : I → B) :=
  Σ i : I, Fin (time p B (bases i))

noncomputable def intervalPoint {I : Type*} [Fintype I]
    (p : Equiv.Perm X) (B : Finset X) (bases : I → B) :
    IntervalIndex p B bases → X :=
  fun q ↦ (p ^ (q.2 : ℕ)) (bases q.1 : X)

theorem intervalPoint_injective {I : Type*} [Fintype I]
    (p : Equiv.Perm X) (B : Finset X) (bases : I → B)
    (hbases : Function.Injective bases) :
    Function.Injective (intervalPoint p B bases) := by
  rintro ⟨i,t⟩ ⟨j,u⟩ heq
  rcases le_total (t : ℕ) (u : ℕ) with hle | hle
  · obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hle
    have hbase : (bases i : X) = (p ^ q) (bases j : X) := by
      apply (p ^ (t : ℕ)).injective
      simpa [intervalPoint, hq, pow_add] using heq
    have hqzero : q = 0 := by
      by_contra hne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hne
      have hqlt : q < time p B (bases j) := by
        have hqu : q ≤ (u : ℕ) := by omega
        exact lt_of_le_of_lt hqu u.isLt
      exact pow_not_mem_of_lt_time p B (bases j) hqpos hqlt (hbase ▸ (bases i).property)
    have hij : i = j := hbases <| by
      apply Subtype.ext
      simpa [hqzero] using hbase
    subst j
    have htu : (t : ℕ) = (u : ℕ) := by omega
    cases Fin.ext htu
    rfl
  · obtain ⟨q,hq⟩ := Nat.exists_eq_add_of_le hle
    have hbase : (bases j : X) = (p ^ q) (bases i : X) := by
      apply (p ^ (u : ℕ)).injective
      simpa [intervalPoint, hq, pow_add] using heq.symm
    have hqzero : q = 0 := by
      by_contra hne
      have hqpos : 0 < q := Nat.pos_of_ne_zero hne
      have hqlt : q < time p B (bases i) := by
        have hqt : q ≤ (t : ℕ) := by omega
        exact lt_of_le_of_lt hqt t.isLt
      exact pow_not_mem_of_lt_time p B (bases i) hqpos hqlt (hbase ▸ (bases j).property)
    have hji : j = i := hbases <| by
      apply Subtype.ext
      simpa [hqzero] using hbase
    subst j
    have htu : (t : ℕ) = (u : ℕ) := by omega
    cases Fin.ext htu
    rfl

theorem sum_time_le_card {I : Type*} [Fintype I]
    (p : Equiv.Perm X) (B : Finset X) (bases : I → B)
    (hbases : Function.Injective bases) :
    ∑ i : I, time p B (bases i) ≤ Fintype.card X := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Fintype.card_le_of_injective (intervalPoint p B bases)
      (intervalPoint_injective p B bases hbases)

end MiniFirstReturn

noncomputable def returnLength (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (q : ValidDeviation d G hG start rho k) : ℕ :=
  MiniFirstReturn.time (phi d G hG rho)
    (pathIncomingDarts d G hG start rho k)
    (validReturnBases d G hG start rho k q)

theorem returnLength_pos (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (q : ValidDeviation d G hG start rho k) :
    0 < returnLength d G hG start rho k q :=
  MiniFirstReturn.time_pos _ _ _

noncomputable def returnEndpoint (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (q : ValidDeviation d G hG start rho k) : Dart G :=
  (MiniFirstReturn.endpoint (phi d G hG rho)
    (pathIncomingDarts d G hG start rho k)
    (validReturnBases d G hG start rho k q) : Dart G)

theorem returnEndpoint_eq_pow (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (q : ValidDeviation d G hG start rho k) :
    returnEndpoint d G hG start rho k q =
      (phi d G hG rho ^ returnLength d G hG start rho k q)
        (returnBase d G hG start rho q.1) := rfl

theorem returnEndpoint_mem (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (q : ValidDeviation d G hG start rho k) :
    returnEndpoint d G hG start rho k q ∈
      pathIncomingDarts d G hG start rho k :=
  (MiniFirstReturn.endpoint _ _ _).property

theorem return_no_earlier (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (q : ValidDeviation d G hG start rho k)
    {t : ℕ} (ht : 0 < t) (hlt : t < returnLength d G hG start rho k q) :
    (phi d G hG rho ^ t) (returnBase d G hG start rho q.1) ∉
      pathIncomingDarts d G hG start rho k :=
  MiniFirstReturn.pow_not_mem_of_lt_time _ _ _ ht hlt

theorem returnEndpoint_injective (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Function.Injective (returnEndpoint d G hG start rho.1 k) := by
  intro q q' hqq
  apply validReturnBases_injective d G hG start rho
  apply MiniFirstReturn.endpoint_injective
  exact Subtype.ext hqq

def boundaryVertices (start : OrientedEdge G) (rho : RotationSystem d V) (k : ℕ) :
    Finset V :=
  {orbitVertex d G hG start rho 0,
    orbitVertex d G hG start rho 1,
    orbitVertex d G hG start rho (k - 1),
    orbitVertex d G hG start rho k}

theorem card_boundaryVertices_le_four (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ) :
    (boundaryVertices d G hG start rho k).card ≤ 4 := by
  exact Finset.card_insert_le _ _ |>.trans <| by
    have h₁ := Finset.card_insert_le
      (orbitVertex d G hG start rho 1)
      ({orbitVertex d G hG start rho (k-1), orbitVertex d G hG start rho k} : Finset V)
    have h₂ := Finset.card_insert_le
      (orbitVertex d G hG start rho (k-1))
      ({orbitVertex d G hG start rho k} : Finset V)
    simp only [Finset.card_singleton] at h₂
    omega

def exceptionalDarts (start : OrientedEdge G) (rho : RotationSystem d V) (k : ℕ) :
    Finset (Dart G) :=
  Finset.univ.filter fun e ↦ e.head ∈ boundaryVertices d G hG start rho k

theorem mem_exceptionalDarts_iff (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (e : Dart G) :
    e ∈ exceptionalDarts d G hG start rho k ↔
      e.head ∈ boundaryVertices d G hG start rho k := by
  simp [exceptionalDarts]

def ExceptionalDart (start : OrientedEdge G) (rho : RotationSystem d V) (k : ℕ) :=
  {e : Dart G // e ∈ exceptionalDarts d G hG start rho k}

instance exceptionalDartFinite (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) : Finite (ExceptionalDart d G hG start rho k) :=
  Finite.of_injective Subtype.val Subtype.val_injective

def exceptionalDartCode (start : OrientedEdge G) (rho : RotationSystem d V) (k : ℕ) :
    ExceptionalDart d G hG start rho k →
      ({v : V // v ∈ boundaryVertices d G hG start rho k} × Fin d) :=
  fun e ↦
    (⟨e.1.head, (mem_exceptionalDarts_iff d G hG start rho k e.1).mp e.2⟩,
      neighborPorts d G hG e.1.head ⟨e.1.tail, e.1.adjacent.symm⟩)

theorem exceptionalDartCode_injective (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ) :
    Function.Injective (exceptionalDartCode d G hG start rho k) := by
  rintro ⟨⟨et,⟨eh,he⟩⟩,hem⟩ ⟨⟨ft,⟨fh,hf⟩⟩,hfm⟩ hcode
  apply Subtype.ext
  have hhead : eh = fh := congrArg (fun q ↦ (q.1 : V)) hcode
  subst fh
  have hport := congrArg Prod.snd hcode
  change neighborPorts d G hG eh ⟨et,he.symm⟩ =
    neighborPorts d G hG eh ⟨ft,hf.symm⟩ at hport
  have htail : et = ft := congrArg Subtype.val
    ((neighborPorts d G hG eh).injective hport)
  subst ft
  rfl

theorem natCard_exceptionalDart_le (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ) :
    Nat.card (ExceptionalDart d G hG start rho k) ≤ 4 * d := by
  calc
    Nat.card (ExceptionalDart d G hG start rho k) ≤
        Nat.card ({v : V // v ∈ boundaryVertices d G hG start rho k} × Fin d) :=
      Nat.card_le_card_of_injective _
        (exceptionalDartCode_injective d G hG start rho k)
    _ = (boundaryVertices d G hG start rho k).card * d := by simp
    _ ≤ 4 * d := Nat.mul_le_mul_right d
      (card_boundaryVertices_le_four d G hG start rho k)

def ExceptionalDeviation (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :=
  {q : ValidDeviation d G hG start rho.1 k //
    returnEndpoint d G hG start rho.1 k q ∈
      exceptionalDarts d G hG start rho.1 k}

def exceptionalDeviationToDart (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    ExceptionalDeviation d G hG start rho →
      ExceptionalDart d G hG start rho.1 k :=
  fun q ↦ ⟨returnEndpoint d G hG start rho.1 k q.1, q.2⟩

theorem exceptionalDeviationToDart_injective (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Function.Injective (exceptionalDeviationToDart d G hG start rho) := by
  intro q q' h
  apply Subtype.ext
  apply returnEndpoint_injective d G hG start rho
  exact congrArg
    (fun e : ExceptionalDart d G hG start rho.1 k ↦ (e.1 : Dart G)) h

theorem natCard_exceptionalDeviation_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Nat.card (ExceptionalDeviation d G hG start rho) ≤ 4 * d :=
  (Nat.card_le_card_of_injective _
    (exceptionalDeviationToDart_injective d G hG start rho)).trans
      (natCard_exceptionalDart_le d G hG start rho.1 k)

theorem sideDart_currentOffset (start : OrientedEdge G) (rho : RotationSystem d V)
    {k : ℕ} (i : Fin (k - 1)) :
    sideDart d G hG start rho (i, currentOffset d G hG start rho i) =
      orbitDart d G hG start rho (i + 1) := by
  rw [orbitDart_succ]
  apply Dart.ext
  · rfl
  · change
      (localRotation d G hG
        (setOffsetAt d rho
          (orbitVertex d G hG start rho (internalTime i))
          (currentOffset d G hG start rho i)
          (orbitDart d G hG start rho i).head)
        (orbitDart d G hG start rho i).head
        ⟨(orbitDart d G hG start rho i).tail,
          (orbitDart d G hG start rho i).adjacent.symm⟩).1 =
      (localRotation d G hG (rho (orbitDart d G hG start rho i).head)
        (orbitDart d G hG start rho i).head
        ⟨(orbitDart d G hG start rho i).tail,
          (orbitDart d G hG start rho i).adjacent.symm⟩).1
    have hv : (orbitDart d G hG start rho i).head =
        orbitVertex d G hG start rho (internalTime i) :=
      (orbitVertex_succ d G hG start rho i).symm
    simp [hv, currentOffset]

theorem sideDart_ne_orbitDart_succ (start : OrientedEdge G)
    (rho : RotationSystem d V) {k : ℕ}
    (q : ValidDeviation d G hG start rho k) :
    sideDart d G hG start rho q.1 ≠
      orbitDart d G hG start rho (q.1.1 + 1) := by
  intro h
  apply q.2
  apply sideDart_injective_offset d G hG start rho q.1.1
  exact h.trans (sideDart_currentOffset d G hG start rho q.1.1).symm

theorem sideDart_ne_reverse_incoming (start : OrientedEdge G)
    (rho : RotationSystem d V) {k : ℕ} (q : DeviationIndex d k) :
    sideDart d G hG start rho q ≠ Dart.reverse G (orbitDart d G hG start rho q.1) := by
  intro h
  apply Dart.head_phi_ne_tail d G hG
    (deviationRotation d G hG start rho q)
    (orbitDart d G hG start rho q.1)
  have hh := congrArg (Dart.head G) h
  simpa only [sideDart, Dart.head_reverse] using hh

theorem returnEndpoint_has_deep_internal_head (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k)
    (hnexc : returnEndpoint d G hG start rho.1 k q ∉
      exceptionalDarts d G hG start rho.1 k) :
    ∃ j : Fin (k - 1),
      (returnEndpoint d G hG start rho.1 k q).head =
          orbitVertex d G hG start rho.1 (internalTime j) ∧
        2 ≤ internalTime j ∧ internalTime j + 1 < k := by
  have hpath : (returnEndpoint d G hG start rho.1 k q).head ∈
      pathVertices d G hG start rho.1 k :=
    (mem_pathIncomingDarts_iff d G hG start rho.1 k _).mp
      (returnEndpoint_mem d G hG start rho.1 k q)
  rw [pathVertices] at hpath
  obtain ⟨t,-,ht⟩ := Finset.mem_image.mp hpath
  have hnhead : (returnEndpoint d G hG start rho.1 k q).head ∉
      boundaryVertices d G hG start rho.1 k := by
    intro hm
    exact hnexc ((mem_exceptionalDarts_iff d G hG start rho.1 k _).mpr hm)
  have htpos : 0 < (t : ℕ) := by
    by_contra h
    have ht0 : (t : ℕ) = 0 := by omega
    apply hnhead
    rw [← ht]
    simp [boundaryVertices, ht0]
  have htlt : (t : ℕ) < k := by
    by_contra h
    have htk : (t : ℕ) = k := by omega
    apply hnhead
    rw [← ht]
    simp [boundaryVertices, htk]
  let j : Fin (k - 1) := ⟨(t : ℕ) - 1, by omega⟩
  have hj : internalTime j = (t : ℕ) := by
    simp [j, internalTime]
    omega
  refine ⟨j, hj ▸ ht.symm, ?_, ?_⟩
  · have hne : internalTime j ≠ 1 := by
      intro h1
      apply hnhead
      rw [ht.symm, ← hj, h1]
      simp [boundaryVertices]
    omega
  · have hne : internalTime j ≠ k - 1 := by
      intro hk1
      apply hnhead
      rw [ht.symm, ← hj, hk1]
      simp [boundaryVertices]
    have := internalTime_lt j
    omega

theorem orbitDart_mem_pathIncomingDarts (start : OrientedEdge G)
    (rho : RotationSystem d V) (k t : ℕ) (ht : t < k) :
    orbitDart d G hG start rho t ∈ pathIncomingDarts d G hG start rho k := by
  rw [mem_pathIncomingDarts_iff, ← orbitVertex_succ]
  exact mem_pathVertices d G hG start rho k ⟨t + 1, by omega⟩

theorem phi_pow_pred (rho : RotationSystem d V) (b : Dart G) (c : ℕ)
    (hc : 0 < c) :
    phi d G hG rho ((phi d G hG rho ^ (c - 1)) b) =
      (phi d G hG rho ^ c) b := by
  conv_rhs => rw [← Nat.sub_add_cancel hc]
  simp [pow_succ']

theorem no_mem_predecessor_of_returnEndpoint (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k)
    (hc : 1 < returnLength d G hG start rho k q)
    (e : Dart G)
    (hstep : phi d G hG rho e = returnEndpoint d G hG start rho k q)
    (hemem : e ∈ pathIncomingDarts d G hG start rho k) : False := by
  let c := returnLength d G hG start rho k q
  let b := returnBase d G hG start rho q.1
  have hs : phi d G hG rho ((phi d G hG rho ^ (c - 1)) b) =
      returnEndpoint d G hG start rho k q := by
    rw [phi_pow_pred d G hG rho b c (by omega), returnEndpoint_eq_pow]
  have hbefore : (phi d G hG rho ^ (c - 1)) b = e :=
    (phi d G hG rho).injective (hs.trans hstep.symm)
  apply return_no_earlier d G hG start rho k q (t := c - 1) (by omega) (by omega)
  rwa [hbefore]

theorem returnEndpoint_ne_pathIncoming (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) (j : Fin (k - 1))
    (hjlow : 2 ≤ internalTime j) :
    returnEndpoint d G hG start rho.1 k q ≠
      orbitDart d G hG start rho.1 j := by
  intro heq
  rcases (show returnLength d G hG start rho.1 k q = 1 ∨
      1 < returnLength d G hG start rho.1 k q by
    have := returnLength_pos d G hG start rho.1 k q
    omega) with hc | hc
  · have hside : returnEndpoint d G hG start rho.1 k q =
        sideDart d G hG start rho.1 q.1 := by
      rw [returnEndpoint_eq_pow, hc, pow_one]
      exact phi_returnBase d G hG start rho.1 q.1
    have hs : sideDart d G hG start rho.1 q.1 =
        orbitDart d G hG start rho.1 j := hside.symm.trans heq
    have hv : orbitVertex d G hG start rho.1 (internalTime q.1.1) =
        orbitVertex d G hG start rho.1 j := by
      calc
        _ = (sideDart d G hG start rho.1 q.1).tail :=
          (sideDart_tail d G hG start rho.1 q.1).symm
        _ = (orbitDart d G hG start rho.1 j).tail := congrArg (Dart.tail G) hs
        _ = _ := rfl
    have hfin :
        (⟨internalTime q.1.1,
          lt_trans (internalTime_lt q.1.1) (Nat.lt_succ_self k)⟩ : Fin (k + 1)) =
        ⟨(j : ℕ), by omega⟩ := rho.2 hv
    have ht : internalTime q.1.1 = (j : ℕ) := congrArg Fin.val hfin
    apply sideDart_ne_orbitDart_succ d G hG start rho.1 q
    simpa [internalTime] using hs.trans
      (congrArg (orbitDart d G hG start rho.1) ht.symm)
  · let e := orbitDart d G hG start rho.1 ((j : ℕ) - 1)
    have hjpos : 0 < (j : ℕ) := by
      simp [internalTime] at hjlow
      omega
    have hstep : phi d G hG rho.1 e =
        returnEndpoint d G hG start rho.1 k q := by
      rw [heq]
      simpa [e, Nat.sub_add_cancel hjpos] using
        (orbitDart_succ d G hG start rho.1 ((j : ℕ) - 1)).symm
    have hemem : e ∈ pathIncomingDarts d G hG start rho.1 k := by
      apply orbitDart_mem_pathIncomingDarts d G hG start rho.1 k
      have := j.isLt
      omega
    exact no_mem_predecessor_of_returnEndpoint d G hG start rho.1 k q hc e hstep hemem

theorem returnEndpoint_ne_reverse_pathOutgoing (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) (j : Fin (k - 1))
    (hjhigh : internalTime j + 1 < k) :
    returnEndpoint d G hG start rho.1 k q ≠
      Dart.reverse G (orbitDart d G hG start rho.1 (internalTime j)) := by
  intro heq
  rcases (show returnLength d G hG start rho.1 k q = 1 ∨
      1 < returnLength d G hG start rho.1 k q by
    have := returnLength_pos d G hG start rho.1 k q
    omega) with hc | hc
  · have hside : returnEndpoint d G hG start rho.1 k q =
        sideDart d G hG start rho.1 q.1 := by
      rw [returnEndpoint_eq_pow, hc, pow_one]
      exact phi_returnBase d G hG start rho.1 q.1
    have hs : sideDart d G hG start rho.1 q.1 =
        Dart.reverse G (orbitDart d G hG start rho.1 (internalTime j)) :=
      hside.symm.trans heq
    have hv : orbitVertex d G hG start rho.1 (internalTime q.1.1) =
        orbitVertex d G hG start rho.1 (internalTime j + 1) := by
      calc
        _ = (sideDart d G hG start rho.1 q.1).tail :=
          (sideDart_tail d G hG start rho.1 q.1).symm
        _ = (Dart.reverse G
            (orbitDart d G hG start rho.1 (internalTime j))).tail :=
          congrArg (Dart.tail G) hs
        _ = (orbitDart d G hG start rho.1 (internalTime j)).head := rfl
        _ = _ := (orbitVertex_succ d G hG start rho.1 (internalTime j)).symm
    have hfin :
        (⟨internalTime q.1.1,
          lt_trans (internalTime_lt q.1.1) (Nat.lt_succ_self k)⟩ : Fin (k + 1)) =
        ⟨internalTime j + 1, by omega⟩ := rho.2 hv
    have ht : internalTime q.1.1 = internalTime j + 1 := congrArg Fin.val hfin
    have hji : internalTime j = (q.1.1 : ℕ) := by
      simp only [internalTime] at ht ⊢
      omega
    exact sideDart_ne_reverse_incoming d G hG start rho.1 q.1 <|
      hs.trans (congrArg
        (fun t ↦ Dart.reverse G (orbitDart d G hG start rho.1 t)) hji)
  · let e := (phi d G hG rho.1).symm
        (returnEndpoint d G hG start rho.1 k q)
    have hstep : phi d G hG rho.1 e =
        returnEndpoint d G hG start rho.1 k q :=
      (phi d G hG rho.1).apply_symm_apply _
    have hehead : e.head =
        (returnEndpoint d G hG start rho.1 k q).tail := by
      calc
        e.head = (phi d G hG rho.1 e).tail := by rw [Dart.tail_phi]
        _ = _ := congrArg (Dart.tail G) hstep
    have hemem : e ∈ pathIncomingDarts d G hG start rho.1 k := by
      rw [mem_pathIncomingDarts_iff, hehead, heq]
      change (orbitDart d G hG start rho.1 (internalTime j)).head ∈ _
      rw [← orbitVertex_succ]
      exact mem_pathVertices d G hG start rho.1 k
        ⟨internalTime j + 1, by omega⟩
    exact no_mem_predecessor_of_returnEndpoint d G hG start rho.1 k q hc e hstep hemem

theorem validSideDart_injective (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Function.Injective
      (fun q : ValidDeviation d G hG start rho.1 k ↦
        sideDart d G hG start rho.1 q.1) := by
  rintro ⟨⟨i, a⟩, ha⟩ ⟨⟨j, b⟩, hb⟩ hside
  have hv : orbitVertex d G hG start rho.1 (internalTime i) =
      orbitVertex d G hG start rho.1 (internalTime j) := by
    simpa only [sideDart_tail] using congrArg (Dart.tail G) hside
  have hfin :
      (⟨internalTime i,
        lt_trans (internalTime_lt i) (Nat.lt_succ_self k)⟩ : Fin (k + 1)) =
      ⟨internalTime j,
        lt_trans (internalTime_lt j) (Nat.lt_succ_self k)⟩ := rho.2 hv
  have hij : i = j := by
    apply Fin.ext
    have hval := congrArg Fin.val hfin
    simp only [internalTime] at hval
    omega
  subst j
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact sideDart_injective_offset d G hG start rho.1 i hside

/-- Every nonexceptional return endpoint is the reverse of one unique valid
side dart.  This identifies the finish deviation of the excursion. -/
theorem existsUnique_finishDeviation (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k)
    (hnexc : returnEndpoint d G hG start rho.1 k q ∉
      exceptionalDarts d G hG start rho.1 k) :
    ∃! q' : ValidDeviation d G hG start rho.1 k,
      returnEndpoint d G hG start rho.1 k q =
        Dart.reverse G (sideDart d G hG start rho.1 q'.1) := by
  obtain ⟨j, hhead, hjlow, hjhigh⟩ :=
    returnEndpoint_has_deep_internal_head d G hG start rho q hnexc
  let e := returnEndpoint d G hG start rho.1 k q
  let x := orbitIncomingNeighbor d G hG start rho.1 j
  have hjvertex : (orbitDart d G hG start rho.1 j).head =
      orbitVertex d G hG start rho.1 (internalTime j) :=
    (orbitVertex_succ d G hG start rho.1 j).symm
  have hehead : e.head = (orbitDart d G hG start rho.1 j).head :=
    hhead.trans hjvertex.symm
  let z : G.neighborSet (orbitDart d G hG start rho.1 j).head :=
    ⟨e.tail, by
      rw [← hehead]
      exact e.adjacent.symm⟩
  have hzx : z ≠ x := by
    intro hzx'
    apply returnEndpoint_ne_pathIncoming d G hG start rho q j hjlow
    apply Dart.ext
    · exact congrArg Subtype.val hzx'
    · exact hehead
  obtain ⟨a, ha, -⟩ := existsUnique_localRotation d G hG hzx
  have hside : sideDart d G hG start rho.1 (j, a) = Dart.reverse G e := by
    apply Dart.ext
    · rw [sideDart_tail, Dart.tail_reverse]
      exact hhead.symm
    · rw [sideDart_head, Dart.head_reverse]
      simpa only [x, z] using congrArg Subtype.val ha
  have havalid : a ≠ currentOffset d G hG start rho.1 j := by
    intro hac
    apply returnEndpoint_ne_reverse_pathOutgoing d G hG start rho q j hjhigh
    apply (Dart.reverse G).injective
    simp only [Dart.reverse_reverse]
    exact hside.symm.trans <| by
      rw [hac]
      simpa only [internalTime] using
        sideDart_currentOffset d G hG start rho.1 j
  let q' : ValidDeviation d G hG start rho.1 k := ⟨(j, a), havalid⟩
  have hq' : e = Dart.reverse G (sideDart d G hG start rho.1 q'.1) := by
    apply (Dart.reverse G).injective
    simpa only [Dart.reverse_reverse] using hside.symm
  refine ⟨q', hq', ?_⟩
  intro r hr
  apply validSideDart_injective d G hG start rho
  apply (Dart.reverse G).injective
  exact hr.symm.trans hq'

/-- The exceptional deviations as a finset, for use in the counting argument. -/
def exceptionalDeviations (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Finset (ValidDeviation d G hG start rho.1 k) :=
  Finset.univ.filter fun q ↦
    returnEndpoint d G hG start rho.1 k q ∈
      exceptionalDarts d G hG start rho.1 k

theorem mem_exceptionalDeviations_iff (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) :
    q ∈ exceptionalDeviations d G hG start rho ↔
      returnEndpoint d G hG start rho.1 k q ∈
        exceptionalDarts d G hG start rho.1 k := by
  simp [exceptionalDeviations]

theorem card_exceptionalDeviations_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    (exceptionalDeviations d G hG start rho).card ≤ 4 * d := by
  letI : Finite (ExceptionalDeviation d G hG start rho) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let f : {q // q ∈ exceptionalDeviations d G hG start rho} →
      ExceptionalDeviation d G hG start rho :=
    fun q ↦ ⟨q.1,
      (mem_exceptionalDeviations_iff d G hG start rho q.1).mp q.2⟩
  have hf : Function.Injective f := by
    intro q r hqr
    apply Subtype.ext
    exact congrArg (fun z : ExceptionalDeviation d G hG start rho ↦ z.1) hqr
  calc
    (exceptionalDeviations d G hG start rho).card =
        Nat.card {q // q ∈ exceptionalDeviations d G hG start rho} := by simp
    _ ≤ Nat.card (ExceptionalDeviation d G hG start rho) :=
      Nat.card_le_card_of_injective f hf
    _ ≤ 4 * d := natCard_exceptionalDeviation_le d G hG start rho

/-- The classified finish deviation; exceptional inputs receive a harmless
default value because they are discarded before this function is used. -/
noncomputable def finishDeviation (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) :
    ValidDeviation d G hG start rho.1 k :=
  if hq : q ∈ exceptionalDeviations d G hG start rho then q
  else Classical.choose <| existsUnique_finishDeviation d G hG start rho q <|
    by simpa [mem_exceptionalDeviations_iff] using hq

theorem finishDeviation_spec (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k)
    (hq : q ∉ exceptionalDeviations d G hG start rho) :
    returnEndpoint d G hG start rho.1 k q =
      Dart.reverse G
        (sideDart d G hG start rho.1 (finishDeviation d G hG start rho q).1) := by
  rw [finishDeviation, dif_neg hq]
  exact (Classical.choose_spec <|
    existsUnique_finishDeviation d G hG start rho q <|
      by simpa [mem_exceptionalDeviations_iff] using hq).1

theorem finishDeviation_injective_off_exceptional (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Set.InjOn (finishDeviation d G hG start rho)
      ((Finset.univ \ exceptionalDeviations d G hG start rho :
        Finset (ValidDeviation d G hG start rho.1 k)) :
          Set (ValidDeviation d G hG start rho.1 k)) := by
  intro q hq r hr hfinish
  have hq' : q ∉ exceptionalDeviations d G hG start rho :=
    (Finset.mem_sdiff.mp hq).2
  have hr' : r ∉ exceptionalDeviations d G hG start rho :=
    (Finset.mem_sdiff.mp hr).2
  apply returnEndpoint_injective d G hG start rho
  rw [finishDeviation_spec d G hG start rho q hq',
    finishDeviation_spec d G hG start rho r hr', hfinish]

namespace DegreeEligibleArithmetic

variable {ι : Type*} [DecidableEq ι]

def longBad (I : Finset ι) (c : ι → ℕ) (L : ℕ) : Finset ι :=
  I.filter fun i ↦ L < c i

def boundaryBad (I : Finset ι) (f : ι → ℕ) (k L : ℕ) : Finset ι :=
  I.filter fun i ↦ k < f i + L

def eligible (I X : Finset ι) (c r j : ι → ℕ) (k L : ℕ) : Finset ι :=
  I.filter fun i ↦ c i ≤ L ∧ r i + L ≤ k ∧ j i + L ≤ k ∧ i ∉ X

theorem card_longBad_mul_le_sum (I : Finset ι) (c : ι → ℕ) (L : ℕ) :
    (longBad I c L).card * (L + 1) ≤ ∑ i ∈ I, c i := by
  classical
  calc
    (longBad I c L).card * (L + 1) =
        ∑ _i ∈ longBad I c L, (L + 1) := by simp
    _ ≤ ∑ i ∈ longBad I c L, c i := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      omega
    _ ≤ ∑ i ∈ I, c i :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- A degree-uniform arithmetic core.  The hypotheses isolate the three
simple estimates used later: Markov for long excursions, a degree-`d` bound
for each endpoint strip, and the `4d` exceptional endpoints. -/
theorem four_mul_card_eligible_ge
    (n k d L : ℕ) (I X : Finset ι) (c r j : ι → ℕ)
    (hk : 2 ≤ k)
    (hcardI : k - 1 ≤ I.card)
    (hsum : ∑ i ∈ I, c i ≤ d * n)
    (hX : X.card ≤ 4 * d)
    (hstart : (boundaryBad I r k L).card ≤ L * d)
    (hfinish : (boundaryBad (I \ X) j k L).card ≤ L * d)
    (hlongScale : 16 * (d * n) ≤ k * (L + 1))
    (hboundaryScale : 16 * (L * d) ≤ k)
    (hexceptionScale : 64 * d ≤ k) :
    k ≤ 4 * (eligible I X c r j k L).card := by
  classical
  let Long := longBad I c L
  let Start := boundaryBad I r k L
  let Finish := boundaryBad (I \ X) j k L
  let P : ι → Prop := fun i ↦
    c i ≤ L ∧ r i + L ≤ k ∧ j i + L ≤ k ∧ i ∉ X
  let Good := I.filter P
  let Bad := I.filter fun i ↦ ¬ P i
  let U := ((Long ∪ Start) ∪ Finish) ∪ X
  have hpack0 := card_longBad_mul_le_sum I c L
  have hpack : Long.card * (L + 1) ≤ d * n := by
    have hpackI : Long.card * (L + 1) ≤ ∑ i ∈ I, c i := by
      simpa only [Long] using hpack0
    exact hpackI.trans hsum
  have hlong : 16 * Long.card ≤ k := by
    have hmul : (16 * Long.card) * (L + 1) ≤ k * (L + 1) := by
      calc
        (16 * Long.card) * (L + 1) =
            16 * (Long.card * (L + 1)) := by ring
        _ ≤ 16 * (d * n) := Nat.mul_le_mul_left 16 hpack
        _ ≤ k * (L + 1) := hlongScale
    exact Nat.le_of_mul_le_mul_right hmul (by omega)
  have hstart' : 16 * Start.card ≤ k := by
    calc
      16 * Start.card ≤ 16 * (L * d) :=
        Nat.mul_le_mul_left 16 (by simpa only [Start] using hstart)
      _ ≤ k := hboundaryScale
  have hfinish' : 16 * Finish.card ≤ k := by
    calc
      16 * Finish.card ≤ 16 * (L * d) :=
        Nat.mul_le_mul_left 16 (by simpa only [Finish] using hfinish)
      _ ≤ k := hboundaryScale
  have hX' : 16 * X.card ≤ k := by
    calc
      16 * X.card ≤ 16 * (4 * d) := Nat.mul_le_mul_left 16 hX
      _ = 64 * d := by ring
      _ ≤ k := hexceptionScale
  have hBadSub : Bad ⊆ U := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hiI := hi'.1
    have hnot := hi'.2
    by_cases hx : i ∈ X
    · simp [U, hx]
    · have hiClassified : i ∈ I \ X := Finset.mem_sdiff.mpr ⟨hiI, hx⟩
      by_cases hc : c i ≤ L
      · by_cases hr : r i + L ≤ k
        · by_cases hj : j i + L ≤ k
          · exact (hnot ⟨hc, hr, hj, hx⟩).elim
          · have hj' : k < j i + L := Nat.lt_of_not_ge hj
            simp [U, Finish, boundaryBad, hiClassified, hj']
        · have hr' : k < r i + L := Nat.lt_of_not_ge hr
          simp [U, Start, boundaryBad, hiI, hr']
      · have hc' : L < c i := Nat.lt_of_not_ge hc
        simp [U, Long, longBad, hiI, hc']
  have hU : U.card ≤ Long.card + Start.card + Finish.card + X.card := by
    have h1 := Finset.card_union_le ((Long ∪ Start) ∪ Finish) X
    have h2 := Finset.card_union_le (Long ∪ Start) Finish
    have h3 := Finset.card_union_le Long Start
    dsimp [U]
    omega
  have hbad : 16 * Bad.card ≤ 4 * k := by
    have hsub := Finset.card_le_card hBadSub
    omega
  have hpartition : Good.card + Bad.card = I.card := by
    simpa [Good, Bad] using Finset.card_filter_add_card_filter_not (s := I) P
  have hgood : k ≤ 4 * Good.card := by omega
  simpa [Good, P, eligible] using hgood

end DegreeEligibleArithmetic

def deviationStartTime (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) : ℕ :=
  internalTime q.1.1

def deviationFinishTime (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) : ℕ :=
  internalTime (finishDeviation d G hG start rho q).1.1

/-- A boundary strip has at most `L` possible path indices and at most
`d-1` possible offset labels. -/
theorem card_boundaryDeviation_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (J : Finset (ValidDeviation d G hG start rho.1 k))
    (f : ValidDeviation d G hG start rho.1 k →
      ValidDeviation d G hG start rho.1 k)
    (hf : Set.InjOn f (J : Set (ValidDeviation d G hG start rho.1 k)))
    (L : ℕ) :
    (DegreeEligibleArithmetic.boundaryBad J
      (fun q ↦ internalTime (f q).1.1) k L).card ≤ L * d := by
  classical
  let B := DegreeEligibleArithmetic.boundaryBad J
    (fun q ↦ internalTime (f q).1.1) k L
  let code : B → Fin L × Offset d := fun q ↦
    (⟨k - 1 - internalTime (f q.1).1.1, by
      have hmem : k < internalTime (f q.1).1.1 + L := by
        have hqmem : q.1 ∈ DegreeEligibleArithmetic.boundaryBad J
            (fun z ↦ internalTime (f z).1.1) k L := q.2
        exact (Finset.mem_filter.mp hqmem).2
      have hlt := internalTime_lt (f q.1).1.1
      omega⟩,
    (f q.1).1.2)
  have hcode : Function.Injective code := by
    intro q r hqr
    have hfirst := congrArg (fun z : Fin L × Offset d ↦ (z.1 : ℕ)) hqr
    have hqtime := internalTime_lt (f q.1).1.1
    have hrtime := internalTime_lt (f r.1).1.1
    have htime : internalTime (f q.1).1.1 = internalTime (f r.1).1.1 := by
      dsimp only [code] at hfirst
      omega
    have hindex : (f q.1).1.1 = (f r.1).1.1 := by
      apply Fin.ext
      simp only [internalTime] at htime
      omega
    have hoffset : (f q.1).1.2 = (f r.1).1.2 :=
      congrArg (fun z : Fin L × Offset d ↦ z.2) hqr
    have hfr : f q.1 = f r.1 := by
      apply Subtype.ext
      exact Prod.ext hindex hoffset
    apply Subtype.ext
    apply hf
    · have hqmem : q.1 ∈ DegreeEligibleArithmetic.boundaryBad J
          (fun z ↦ internalTime (f z).1.1) k L := q.2
      exact (Finset.mem_filter.mp hqmem).1
    · have hrmem : r.1 ∈ DegreeEligibleArithmetic.boundaryBad J
          (fun z ↦ internalTime (f z).1.1) k L := r.2
      exact (Finset.mem_filter.mp hrmem).1
    · exact hfr
  calc
    B.card = Fintype.card B := by simp
    _ ≤ Fintype.card (Fin L × Offset d) :=
      Fintype.card_le_of_injective code hcode
    _ = L * (d - 1) := by simp [card_offset]
    _ ≤ L * d := Nat.mul_le_mul_left L (Nat.sub_le d 1)

theorem card_startBoundary_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) (L : ℕ) :
    (DegreeEligibleArithmetic.boundaryBad Finset.univ
      (deviationStartTime d G hG start rho) k L).card ≤ L * d := by
  change (DegreeEligibleArithmetic.boundaryBad Finset.univ
    (fun q : ValidDeviation d G hG start rho.1 k ↦ internalTime q.1.1)
    k L).card ≤ L * d
  exact card_boundaryDeviation_le d G hG start rho Finset.univ id
    (fun _ _ _ _ h ↦ h) L

theorem card_finishBoundary_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) (L : ℕ) :
    (DegreeEligibleArithmetic.boundaryBad
      (Finset.univ \ exceptionalDeviations d G hG start rho)
      (deviationFinishTime d G hG start rho) k L).card ≤ L * d := by
  change (DegreeEligibleArithmetic.boundaryBad
    (Finset.univ \ exceptionalDeviations d G hG start rho)
    (fun q ↦ internalTime (finishDeviation d G hG start rho q).1.1)
    k L).card ≤ L * d
  exact card_boundaryDeviation_le d G hG start rho
    (Finset.univ \ exceptionalDeviations d G hG start rho)
    (finishDeviation d G hG start rho)
    (finishDeviation_injective_off_exceptional d G hG start rho) L

theorem sum_returnLength_le_d_mul_card (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    ∑ q : ValidDeviation d G hG start rho.1 k,
      returnLength d G hG start rho.1 k q ≤ d * Fintype.card V := by
  calc
    ∑ q : ValidDeviation d G hG start rho.1 k,
        returnLength d G hG start rho.1 k q ≤ Fintype.card (Dart G) :=
      (by
        simpa only [returnLength] using
          (MiniFirstReturn.sum_time_le_card
            (phi d G hG rho.1)
            (pathIncomingDarts d G hG start rho.1 k)
            (validReturnBases d G hG start rho.1 k)
            (validReturnBases_injective d G hG start rho)))
    _ = d * Fintype.card V := by
      rw [← Nat.card_eq_fintype_card, natCard_dart d G hG]

/-- A deliberately generous cutoff.  Its large slack keeps all subsequent
integer estimates monotone and transparent. -/
def degreeCutoff (d n k : ℕ) : ℕ := 64 * d * n / k + 1

def eligibleDeviations (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k) :
    Finset (ValidDeviation d G hG start rho.1 k) :=
  DegreeEligibleArithmetic.eligible Finset.univ
    (exceptionalDeviations d G hG start rho)
    (returnLength d G hG start rho.1 k)
    (deviationStartTime d G hG start rho)
    (deviationFinishTime d G hG start rho)
    k (degreeCutoff d (Fintype.card V) k)

/-- In the high regime, every good plan has linearly many classified short
returns, even though we only retain a degree-independent `k/4` lower bound. -/
theorem many_eligibleDeviations (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k ≤ 4 * (eligibleDeviations d G hG start rho).card := by
  let n := Fintype.card V
  let L := degreeCutoff d n k
  have hnpos : 0 < n := by omega
  have hkpos : 0 < k := by
    have hdpos : 0 < d := by omega
    have hcoef : 0 < 1048576 * d ^ 2 * n := by positivity
    nlinarith [hhigh]
  have hk : 2 ≤ k := by
    have hbase : 4 ≤ 1048576 * d ^ 2 * n := by
      have : 1 ≤ n := hnpos
      nlinarith
    nlinarith [hhigh]
  have hcardI : k - 1 ≤
      (Finset.univ : Finset (ValidDeviation d G hG start rho.1 k)).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      natCard_validDeviation d G hG start rho.1 k]
    have : 1 ≤ d - 2 := by omega
    nlinarith
  have hsum :
      ∑ q ∈ (Finset.univ : Finset (ValidDeviation d G hG start rho.1 k)),
          returnLength d G hG start rho.1 k q ≤ d * n := by
    simpa [n] using sum_returnLength_le_d_mul_card d G hG start rho
  have hlongScale : 16 * (d * n) ≤ k * (L + 1) := by
    have hlt : 64 * d * n < k * L := by
      simpa [L, degreeCutoff] using Nat.lt_mul_div_succ (64 * d * n) hkpos
    nlinarith
  have hdiv : (64 * d * n / k) * k ≤ 64 * d * n :=
    Nat.div_mul_le_self _ _
  have hboundaryMul : (16 * (L * d)) * k ≤ k * k := by
    calc
      (16 * (L * d)) * k =
          16 * d * ((64 * d * n / k) * k + k) := by
            dsimp [L, degreeCutoff]
            ring
      _ ≤ 16 * d * (64 * d * n + n) := by
        gcongr
      _ ≤ 1048576 * d ^ 2 * n := by
        calc
          16 * d * (64 * d * n + n) =
              1024 * d ^ 2 * n + 16 * d * n := by ring
          _ ≤ 1024 * d ^ 2 * n + 16 * d ^ 2 * n := by
            gcongr
            nlinarith
          _ = 1040 * (d ^ 2 * n) := by ring
          _ ≤ 1048576 * (d ^ 2 * n) := by gcongr <;> omega
          _ = 1048576 * d ^ 2 * n := by ring
      _ ≤ k ^ 2 := hhigh
      _ = k * k := by ring
  have hboundaryScale : 16 * (L * d) ≤ k :=
    Nat.le_of_mul_le_mul_right hboundaryMul hkpos
  have hexceptionScale : 64 * d ≤ k := by
    have hsmall : (64 * d) ^ 2 ≤ 1048576 * d ^ 2 * n := by
      have hc : 4096 ≤ 1048576 * n := by nlinarith
      calc
        (64 * d) ^ 2 = 4096 * d ^ 2 := by ring
        _ ≤ (1048576 * n) * d ^ 2 := Nat.mul_le_mul_right (d ^ 2) hc
        _ = 1048576 * d ^ 2 * n := by ring
    nlinarith [hsmall, hhigh]
  apply DegreeEligibleArithmetic.four_mul_card_eligible_ge
    (n := n) (k := k) (d := d) (L := L)
    (I := Finset.univ)
    (X := exceptionalDeviations d G hG start rho)
    (c := returnLength d G hG start rho.1 k)
    (r := deviationStartTime d G hG start rho)
    (j := deviationFinishTime d G hG start rho)
  · exact hk
  · exact hcardI
  · exact hsum
  · exact card_exceptionalDeviations_le d G hG start rho
  · exact card_startBoundary_le d G hG start rho L
  · exact card_finishBoundary_le d G hG start rho L
  · exact hlongScale
  · exact hboundaryScale
  · exact hexceptionScale

end Graph

end

end NonbacktrackingWalks



set_option linter.unusedSectionVars false

namespace TranslationReversal

open NonbacktrackingWalks

noncomputable section

variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)

local instance graphAdjDecidable : DecidableRel G.Adj := Classical.decRel _
local instance vertexDecidableEq : DecidableEq V := Classical.decEq _

def negateVertices (rho : RotationSystem d V) (S : Finset V) :
    RotationSystem d V :=
  fun v ↦ if v ∈ S then negOffset d (rho v) else rho v

@[simp] theorem negateVertices_of_mem (rho : RotationSystem d V)
    (S : Finset V) {v : V} (hv : v ∈ S) :
    negateVertices (d := d) rho S v = negOffset d (rho v) := by
  simp [negateVertices, hv]

@[simp] theorem negateVertices_of_not_mem (rho : RotationSystem d V)
    (S : Finset V) {v : V} (hv : v ∉ S) :
    negateVertices (d := d) rho S v = rho v := by
  simp [negateVertices, hv]

@[simp] theorem negateVertices_twice (rho : RotationSystem d V)
    (S : Finset V) :
    negateVertices (d := d) (negateVertices (d := d) rho S) S = rho := by
  funext v
  by_cases hv : v ∈ S <;> simp [negateVertices, hv]

def interiorRouteVertices (x : ℕ → Dart G) (c : ℕ) : Finset V :=
  (Finset.Ico 1 c).image fun t ↦ (x t).head

theorem mem_interiorRouteVertices (x : ℕ → Dart G) (c t : ℕ)
    (ht0 : 0 < t) (htc : t < c) :
    (x t).head ∈ interiorRouteVertices G x c := by
  exact Finset.mem_image.mpr
    ⟨t, Finset.mem_Ico.mpr ⟨ht0, htc⟩, rfl⟩

theorem phi_negate_reverse_step (rho : RotationSystem d V) (S : Finset V)
    (x y : Dart G) (hxy : phi d G hG rho x = y) (hxS : x.head ∈ S) :
    phi d G hG (negateVertices (d := d) rho S) (Dart.reverse G y) =
      Dart.reverse G x := by
  subst y
  apply Dart.ext
  · simp
  · change
      (localRotation d G hG
        (negateVertices (d := d) rho S x.head) x.head
        (localRotation d G hG (rho x.head) x.head
          ⟨x.tail, x.adjacent.symm⟩)).1 = x.tail
    rw [negateVertices_of_mem (d := d) rho S hxS]
    rw [← localRotation_neg]
    exact congrArg Subtype.val
      ((localRotation d G hG (rho x.head) x.head).symm_apply_apply
        ⟨x.tail, x.adjacent.symm⟩)

def reverseRouteRotation (rho : RotationSystem d V) (x : ℕ → Dart G)
    (c : ℕ) : RotationSystem d V :=
  negateVertices (d := d) rho (interiorRouteVertices G x c)

theorem iterate_reverse_route (rho : RotationSystem d V) (x : ℕ → Dart G)
    (c q : ℕ)
    (hx : ∀ t < c, x (t + 1) = phi d G hG rho (x t))
    (hq : q < c) :
    (phi d G hG (reverseRouteRotation (d := d) G rho x c))^[q]
        (Dart.reverse G (x c)) =
      Dart.reverse G (x (c - q)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hq' : q < c := by omega
      have hpos : 0 < c - (q + 1) := by omega
      have hlt : c - (q + 1) < c := by omega
      have hstep : phi d G hG rho (x (c - (q + 1))) = x (c - q) := by
        have hs := hx (c - (q + 1)) hlt
        rw [show c - q = (c - (q + 1)) + 1 by omega]
        exact hs.symm
      rw [Function.iterate_succ_apply', ih hq']
      exact phi_negate_reverse_step (d := d) G hG rho
        (interiorRouteVertices G x c)
        (x (c - (q + 1))) (x (c - q)) hstep
        (mem_interiorRouteVertices G x c (c - (q + 1)) hpos hlt)

theorem phi_eq_of_eq_at_head (rho rho' : RotationSystem d V) (e : Dart G)
    (hhead : rho' e.head = rho e.head) :
    phi d G hG rho' e = phi d G hG rho e := by
  apply Dart.ext
  · simp
  · change
      (localRotation d G hG (rho' e.head) e.head
        ⟨e.tail, e.adjacent.symm⟩).1 =
      (localRotation d G hG (rho e.head) e.head
        ⟨e.tail, e.adjacent.symm⟩).1
    rw [hhead]

theorem orbitDart_eq_of_eq_on_path (start : OrientedEdge G)
    (rho rho' : RotationSystem d V) (k : ℕ)
    (hrho : ∀ v ∈ pathVertices d G hG start rho k, rho' v = rho v) :
    ∀ t ≤ k,
      orbitDart d G hG start rho' t = orbitDart d G hG start rho t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show t + 1 = Nat.succ t by omega, orbitDart_succ,
        orbitDart_succ, ih (by omega)]
      apply phi_eq_of_eq_at_head (d := d) G hG
      apply hrho
      have hv := mem_pathVertices d G hG start rho k
        ⟨t + 1, by omega⟩
      rwa [orbitVertex_succ] at hv

def returnRoute (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (q : ValidDeviation d G hG start rho k) (t : ℕ) : Dart G :=
  (phi d G hG rho)^[t] (returnBase d G hG start rho q.1)

@[simp] theorem returnRoute_zero (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) :
    returnRoute (d := d) G hG start rho k q 0 =
      returnBase d G hG start rho q.1 := rfl

theorem returnRoute_succ (start : OrientedEdge G) (rho : RotationSystem d V)
    (k : ℕ) (q : ValidDeviation d G hG start rho k) (t : ℕ) :
    returnRoute (d := d) G hG start rho k q (t + 1) =
      phi d G hG rho (returnRoute (d := d) G hG start rho k q t) := by
  simp only [returnRoute, Function.iterate_succ_apply']

@[simp] theorem returnRoute_one (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) :
    returnRoute (d := d) G hG start rho k q 1 =
      sideDart d G hG start rho q.1 := by
  rw [show 1 = 0 + 1 by omega, returnRoute_succ]
  exact phi_returnBase d G hG start rho q.1

theorem returnRoute_at_length (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) :
    returnRoute (d := d) G hG start rho k q
        (returnLength d G hG start rho k q) =
      returnEndpoint d G hG start rho k q := by
  exact (returnEndpoint_eq_pow d G hG start rho k q).symm

theorem firstReturn_head_outside (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) (t : ℕ)
    (ht0 : 0 < t) (htc : t < returnLength d G hG start rho k q) :
    (returnRoute (d := d) G hG start rho k q t).head ∉
      pathVertices d G hG start rho k := by
  intro hhead
  apply return_no_earlier d G hG start rho k q ht0 htc
  exact (mem_pathIncomingDarts_iff d G hG start rho k _).mpr hhead

def exteriorReturnVertices (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) : Finset V :=
  interiorRouteVertices G (returnRoute (d := d) G hG start rho k q)
    (returnLength d G hG start rho k q)

def reversedReturnRotation (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) : RotationSystem d V :=
  negateVertices (d := d) rho (exteriorReturnVertices (d := d) G hG start rho k q)

theorem reversedReturnRotation_eq_on_path (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) :
    ∀ v ∈ pathVertices d G hG start rho k,
      reversedReturnRotation (d := d) G hG start rho k q v = rho v := by
  intro v hv
  apply negateVertices_of_not_mem
  intro hext
  obtain ⟨t, ht, htv⟩ := Finset.mem_image.mp hext
  have hout := firstReturn_head_outside (d := d) G hG start rho k q t
    (Finset.mem_Ico.mp ht).1 (Finset.mem_Ico.mp ht).2
  exact hout (htv ▸ hv)

theorem reversedReturn_path_orbit (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) :
    ∀ t ≤ k,
      orbitDart d G hG start
          (reversedReturnRotation (d := d) G hG start rho k q) t =
        orbitDart d G hG start rho t := by
  exact orbitDart_eq_of_eq_on_path (d := d) G hG start rho _ k
    (reversedReturnRotation_eq_on_path (d := d) G hG start rho k q)

theorem reversedReturn_isGood (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) :
    IsGood d G hG start
      (reversedReturnRotation (d := d) G hG start rho.1 k q) k := by
  intro a b hab
  apply rho.2
  change
    (orbitDart d G hG start rho.1 a).tail =
      (orbitDart d G hG start rho.1 b).tail
  change
    (orbitDart d G hG start
      (reversedReturnRotation (d := d) G hG start rho.1 k q) a).tail =
    (orbitDart d G hG start
      (reversedReturnRotation (d := d) G hG start rho.1 k q) b).tail at hab
  simpa only [reversedReturn_path_orbit (d := d) G hG start rho.1 k q _
      (Nat.le_of_lt_succ a.isLt),
    reversedReturn_path_orbit (d := d) G hG start rho.1 k q _
      (Nat.le_of_lt_succ b.isLt)] using hab

def reversedReturnGood (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) :
    GoodOmega d G hG start k :=
  ⟨reversedReturnRotation (d := d) G hG start rho.1 k q,
    reversedReturn_isGood (d := d) G hG start rho q⟩

theorem reversedReturn_pathVertices (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) :
    pathVertices d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k =
      pathVertices d G hG start rho k := by
  classical
  apply Finset.ext
  intro v
  simp only [pathVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    unfold orbitVertex
    rw [reversedReturn_path_orbit (d := d) G hG start rho k q t
      (Nat.le_of_lt_succ t.isLt)]
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    unfold orbitVertex
    rw [reversedReturn_path_orbit (d := d) G hG start rho k q t
      (Nat.le_of_lt_succ t.isLt)]

theorem reversedReturn_pathIncomingDarts (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) :
    pathIncomingDarts d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k =
      pathIncomingDarts d G hG start rho k := by
  classical
  apply Finset.ext
  intro e
  simp only [mem_pathIncomingDarts_iff]
  rw [reversedReturn_pathVertices (d := d) G hG start rho k q]

theorem reversedReturn_currentOffset (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) (i : Fin (k - 1)) :
    currentOffset d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) i =
      currentOffset d G hG start rho i := by
  unfold currentOffset
  have hd := reversedReturn_path_orbit (d := d) G hG start rho k q
    (internalTime i) (Nat.le_of_lt (internalTime_lt i))
  have hv := congrArg (Dart.tail G) hd
  change orbitVertex d G hG start
      (reversedReturnRotation (d := d) G hG start rho k q) (internalTime i) =
    orbitVertex d G hG start rho (internalTime i) at hv
  rw [hv]
  apply reversedReturnRotation_eq_on_path (d := d) G hG start rho k q
  exact mem_pathVertices d G hG start rho k
    ⟨internalTime i,
      lt_trans (internalTime_lt i) (Nat.lt_succ_self k)⟩

/-- A deviation valid for the original path is valid, with the same raw data,
after reversing an exterior return interval. -/
def transportDeviation (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k)
    (a : ValidDeviation d G hG start rho k) :
    ValidDeviation d G hG start
      (reversedReturnRotation (d := d) G hG start rho k q) k :=
  ⟨a.1, by
    change a.1.2 ≠ currentOffset d G hG start
      (reversedReturnRotation (d := d) G hG start rho k q) a.1.1
    rw [reversedReturn_currentOffset (d := d) G hG start rho k q a.1.1]
    exact a.2⟩

@[simp] theorem transportDeviation_val (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q a : ValidDeviation d G hG start rho k) :
    (transportDeviation (d := d) G hG start rho k q a).1 = a.1 := rfl

theorem reversedReturn_sideDart (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k)
    (a : DeviationIndex d k) :
    sideDart d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) a =
      sideDart d G hG start rho a := by
  rcases a with ⟨i, a⟩
  unfold sideDart
  have hd := reversedReturn_path_orbit (d := d) G hG start rho k q i
    (by have := i.isLt; omega)
  rw [hd]
  apply phi_eq_of_eq_at_head (d := d) G hG
  unfold deviationRotation
  have hdInternal := reversedReturn_path_orbit (d := d) G hG start rho k q
    (internalTime i) (Nat.le_of_lt (internalTime_lt i))
  have hv := congrArg (Dart.tail G) hdInternal
  change orbitVertex d G hG start
      (reversedReturnRotation (d := d) G hG start rho k q) (internalTime i) =
    orbitVertex d G hG start rho (internalTime i) at hv
  have hhead : (orbitDart d G hG start rho i).head =
      orbitVertex d G hG start rho (internalTime i) :=
    (orbitVertex_succ d G hG start rho i).symm
  simp [hv, hhead]

theorem reversedReturn_returnBase (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k)
    (a : DeviationIndex d k) :
    returnBase d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) a =
      returnBase d G hG start rho a := by
  apply (phi d G hG
    (reversedReturnRotation (d := d) G hG start rho k q)).injective
  rw [phi_returnBase, reversedReturn_sideDart (d := d) G hG start rho k q a]
  symm
  calc
    phi d G hG
        (reversedReturnRotation (d := d) G hG start rho k q)
        (returnBase d G hG start rho a) =
      phi d G hG rho (returnBase d G hG start rho a) := by
        apply phi_eq_of_eq_at_head (d := d) G hG
        apply reversedReturnRotation_eq_on_path (d := d) G hG start rho k q
        rw [returnBase_head]
        exact mem_pathVertices d G hG start rho k
          ⟨internalTime a.1,
            lt_trans (internalTime_lt a.1) (Nat.lt_succ_self k)⟩
    _ = sideDart d G hG start rho a :=
      phi_returnBase d G hG start rho a

theorem firstReturnTime_eq_of_mem_of_no_earlier
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : Equiv.Perm X) (B : Finset X) (b : B) (c : ℕ)
    (hc : 0 < c) (hmem : (p ^ c) (b : X) ∈ B)
    (hno : ∀ t, 0 < t → t < c → (p ^ t) (b : X) ∉ B) :
    MiniFirstReturn.time p B b = c := by
  apply Nat.le_antisymm
  · exact Nat.find_min'
      (MiniFirstReturn.exists_pos_pow_mem p B b b.property) ⟨hc, hmem⟩
  · by_contra hnot
    have hlt : MiniFirstReturn.time p B b < c := by omega
    exact hno _ (MiniFirstReturn.time_pos p B b) hlt
      (MiniFirstReturn.pow_time_mem p B b)

/-- If the old classified interval runs from `q` to `q'`, then the interval
from `q'` under the reversed rotation traverses it dart-for-dart backward.
The `+1` is essential because route time `1`, not `0`, is the first side dart. -/
theorem classified_reverse_route (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1))
    (t : ℕ) (ht0 : 0 < t)
    (htc : t ≤ returnLength d G hG start rho k q) :
    returnRoute (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') t =
      Dart.reverse G
        (returnRoute (d := d) G hG start rho k q
          (returnLength d G hG start rho k q + 1 - t)) := by
  let c := returnLength d G hG start rho k q
  let x := returnRoute (d := d) G hG start rho k q
  have hc : 0 < c := returnLength_pos d G hG start rho k q
  have hxstep : ∀ s < c, x (s + 1) = phi d G hG rho (x s) := by
    intro s hs
    exact returnRoute_succ (d := d) G hG start rho k q s
  have hxc : x c = Dart.reverse G (sideDart d G hG start rho q'.1) := by
    calc
      x c = returnEndpoint d G hG start rho k q :=
        returnRoute_at_length (d := d) G hG start rho k q
      _ = Dart.reverse G (sideDart d G hG start rho q'.1) := hend
  have hfirst :
      phi d G hG
          (reversedReturnRotation (d := d) G hG start rho k q)
          (returnBase d G hG start
            (reversedReturnRotation (d := d) G hG start rho k q) q'.1) =
        Dart.reverse G (x c) := by
    rw [phi_returnBase,
      reversedReturn_sideDart (d := d) G hG start rho k q q'.1,
      hxc, Dart.reverse_reverse]
  have hq : t - 1 < c := by omega
  change
    (phi d G hG
      (reversedReturnRotation (d := d) G hG start rho k q))^[t]
      (returnBase d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) q'.1) =
      Dart.reverse G (x (c + 1 - t))
  rw [show t = (t - 1).succ by omega, Function.iterate_succ_apply, hfirst]
  have hreverse := iterate_reverse_route (d := d) G hG rho x c (t - 1)
    hxstep hq
  have hrot : reverseRouteRotation (d := d) G rho x c =
      reversedReturnRotation (d := d) G hG start rho k q := rfl
  rw [hrot] at hreverse
  rw [hreverse]
  congr 2
  omega

theorem classified_reverse_returnLength (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1)) :
    returnLength d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') =
      returnLength d G hG start rho k q := by
  let c := returnLength d G hG start rho k q
  have hc : 0 < c := returnLength_pos d G hG start rho k q
  unfold returnLength
  apply firstReturnTime_eq_of_mem_of_no_earlier
    (p := phi d G hG
      (reversedReturnRotation (d := d) G hG start rho k q))
    (B := pathIncomingDarts d G hG start
      (reversedReturnRotation (d := d) G hG start rho k q) k)
    (b := validReturnBases d G hG start
      (reversedReturnRotation (d := d) G hG start rho k q) k
      (transportDeviation (d := d) G hG start rho k q q'))
    c hc
  · change returnRoute (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') c ∈ _
    rw [classified_reverse_route (d := d) G hG start rho k q q' hend c hc
      (by rfl)]
    rw [show c + 1 - c = 1 by omega, returnRoute_one,
      mem_pathIncomingDarts_iff,
      reversedReturn_pathVertices (d := d) G hG start rho k q]
    simp only [Dart.head_reverse, sideDart_tail]
    exact mem_pathVertices d G hG start rho k
      ⟨internalTime q.1.1,
        lt_trans (internalTime_lt q.1.1) (Nat.lt_succ_self k)⟩
  · intro t ht0 htc
    change returnRoute (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') t ∉ _
    rw [classified_reverse_route (d := d) G hG start rho k q q' hend t ht0
      htc.le]
    rw [mem_pathIncomingDarts_iff,
      reversedReturn_pathVertices (d := d) G hG start rho k q]
    simp only [Dart.head_reverse]
    have hspos : 0 < c - t := by omega
    have hslt : c - t < c := by omega
    have hstep := returnRoute_succ (d := d) G hG start rho k q (c - t)
    have htail :
        (returnRoute (d := d) G hG start rho k q (c + 1 - t)).tail =
          (returnRoute (d := d) G hG start rho k q (c - t)).head := by
      rw [show c + 1 - t = (c - t) + 1 by omega, hstep]
      simp
    rw [htail]
    exact firstReturn_head_outside (d := d) G hG start rho k q
      (c - t) hspos hslt

theorem classified_reverse_endpoint (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1)) :
    returnEndpoint d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') =
      Dart.reverse G
        (sideDart d G hG start
          (reversedReturnRotation (d := d) G hG start rho k q) q.1) := by
  let c := returnLength d G hG start rho k q
  have hc : 0 < c := returnLength_pos d G hG start rho k q
  calc
    returnEndpoint d G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') =
      returnRoute (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q')
        (returnLength d G hG start
          (reversedReturnRotation (d := d) G hG start rho k q) k
          (transportDeviation (d := d) G hG start rho k q q')) :=
      (returnRoute_at_length (d := d) G hG start _ k _).symm
    _ = returnRoute (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') c := by
      rw [classified_reverse_returnLength (d := d) G hG start rho k q q' hend]
    _ = Dart.reverse G
        (returnRoute (d := d) G hG start rho k q (c + 1 - c)) :=
      classified_reverse_route (d := d) G hG start rho k q q' hend c hc
        (by rfl)
    _ = Dart.reverse G (sideDart d G hG start rho q.1) := by
      rw [show c + 1 - c = 1 by omega, returnRoute_one]
    _ = Dart.reverse G
        (sideDart d G hG start
          (reversedReturnRotation (d := d) G hG start rho k q) q.1) := by
      rw [reversedReturn_sideDart (d := d) G hG start rho k q q.1]

def ReturnRouteSimple (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q : ValidDeviation d G hG start rho k) : Prop :=
  ∀ a b : ℕ,
    0 < a → a < returnLength d G hG start rho k q →
    0 < b → b < returnLength d G hG start rho k q →
    (returnRoute (d := d) G hG start rho k q a).head =
      (returnRoute (d := d) G hG start rho k q b).head →
    a = b

theorem classified_reverse_simple (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1))
    (hsimple : ReturnRouteSimple (d := d) G hG start rho k q) :
    ReturnRouteSimple (d := d) G hG start
      (reversedReturnRotation (d := d) G hG start rho k q) k
      (transportDeviation (d := d) G hG start rho k q q') := by
  intro a b ha0 haLen hb0 hbLen hab
  let c := returnLength d G hG start rho k q
  have hlength := classified_reverse_returnLength (d := d) G hG start rho k
    q q' hend
  have hac : a < c := by simpa [c, hlength] using haLen
  have hbc : b < c := by simpa [c, hlength] using hbLen
  have hra := classified_reverse_route (d := d) G hG start rho k q q' hend
    a ha0 hac.le
  have hrb := classified_reverse_route (d := d) G hG start rho k q q' hend
    b hb0 hbc.le
  rw [hra, hrb] at hab
  simp only [Dart.head_reverse] at hab
  have hatail :
      (returnRoute (d := d) G hG start rho k q (c + 1 - a)).tail =
        (returnRoute (d := d) G hG start rho k q (c - a)).head := by
    rw [show c + 1 - a = (c - a) + 1 by omega, returnRoute_succ]
    simp
  have hbtail :
      (returnRoute (d := d) G hG start rho k q (c + 1 - b)).tail =
        (returnRoute (d := d) G hG start rho k q (c - b)).head := by
    rw [show c + 1 - b = (c - b) + 1 by omega, returnRoute_succ]
    simp
  rw [hatail, hbtail] at hab
  have hindex := hsimple (c - a) (c - b) (by omega) (by omega)
    (by omega) (by omega) hab
  omega

theorem classified_reverse_interior_head (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1))
    (t : ℕ) (ht0 : 0 < t)
    (htc : t < returnLength d G hG start rho k q) :
    (returnRoute (d := d) G hG start
      (reversedReturnRotation (d := d) G hG start rho k q) k
      (transportDeviation (d := d) G hG start rho k q q') t).head =
    (returnRoute (d := d) G hG start rho k q
      (returnLength d G hG start rho k q - t)).head := by
  let c := returnLength d G hG start rho k q
  rw [classified_reverse_route (d := d) G hG start rho k q q' hend t ht0
    htc.le]
  simp only [Dart.head_reverse]
  rw [show c + 1 - t = (c - t) + 1 by omega, returnRoute_succ]
  simp
  rfl

theorem classified_reverse_exteriorReturnVertices (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1)) :
    exteriorReturnVertices (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') =
      exteriorReturnVertices (d := d) G hG start rho k q := by
  classical
  let c := returnLength d G hG start rho k q
  unfold exteriorReturnVertices interiorRouteVertices
  rw [classified_reverse_returnLength (d := d) G hG start rho k q q' hend]
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨t, ht, htv⟩ := Finset.mem_image.mp hv
    have ht0 : 0 < t := (Finset.mem_Ico.mp ht).1
    have htc : t < c := (Finset.mem_Ico.mp ht).2
    apply Finset.mem_image.mpr
    refine ⟨c - t, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [← htv]
    exact (classified_reverse_interior_head (d := d) G hG start rho k q q'
      hend t ht0 htc).symm
  · intro v hv
    obtain ⟨s, hs, hsv⟩ := Finset.mem_image.mp hv
    have hs0 : 0 < s := (Finset.mem_Ico.mp hs).1
    have hsc : s < c := (Finset.mem_Ico.mp hs).2
    apply Finset.mem_image.mpr
    refine ⟨c - s, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    have hhead := classified_reverse_interior_head (d := d) G hG start rho k q
      q' hend (c - s) (by omega) (by omega)
    rw [show c - (c - s) = s by omega] at hhead
    exact hhead.trans hsv

theorem reversedReturnRotation_twice (start : OrientedEdge G)
    (rho : RotationSystem d V) (k : ℕ)
    (q q' : ValidDeviation d G hG start rho k)
    (hend : returnEndpoint d G hG start rho k q =
      Dart.reverse G (sideDart d G hG start rho q'.1)) :
    reversedReturnRotation (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q') = rho := by
  change negateVertices (d := d)
      (negateVertices (d := d) rho
        (exteriorReturnVertices (d := d) G hG start rho k q))
      (exteriorReturnVertices (d := d) G hG start
        (reversedReturnRotation (d := d) G hG start rho k q) k
        (transportDeviation (d := d) G hG start rho k q q')) = rho
  rw [classified_reverse_exteriorReturnVertices (d := d) G hG start rho k q q'
    hend]
  exact negateVertices_twice (d := d) rho
    (exteriorReturnVertices (d := d) G hG start rho k q)

/-- A good rotation together with a vertex-simple classified return.  Raw
deviations are stored separately from their validity proofs so the type is
well behaved under reversal. -/
@[ext] structure SimpleClassifiedReturn (start : OrientedEdge G) (k : ℕ) where
  sample : GoodOmega d G hG start k
  source : DeviationIndex d k
  finish : DeviationIndex d k
  source_valid : IsValidDeviation d G hG start sample.1 source
  finish_valid : IsValidDeviation d G hG start sample.1 finish
  endpoint_eq :
    returnEndpoint d G hG start sample.1 k ⟨source, source_valid⟩ =
      Dart.reverse G (sideDart d G hG start sample.1 finish)
  route_simple :
    ReturnRouteSimple (d := d) G hG start sample.1 k ⟨source, source_valid⟩

def SimpleClassifiedReturn.sourceDeviation {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) :
    ValidDeviation d G hG start q.sample.1 k :=
  ⟨q.source, q.source_valid⟩

def SimpleClassifiedReturn.finishDeviation {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) :
    ValidDeviation d G hG start q.sample.1 k :=
  ⟨q.finish, q.finish_valid⟩

/-- Reverse a simple classified return, swapping its two raw deviations. -/
def reverseSimpleClassifiedReturn {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) :
    SimpleClassifiedReturn (d := d) G hG start k where
  sample := reversedReturnGood (d := d) G hG start q.sample
    q.sourceDeviation
  source := q.finish
  finish := q.source
  source_valid :=
    (transportDeviation (d := d) G hG start q.sample.1 k
      q.sourceDeviation q.finishDeviation).2
  finish_valid :=
    (transportDeviation (d := d) G hG start q.sample.1 k
      q.sourceDeviation q.sourceDeviation).2
  endpoint_eq :=
    classified_reverse_endpoint (d := d) G hG start q.sample.1 k
      q.sourceDeviation q.finishDeviation q.endpoint_eq
  route_simple :=
    classified_reverse_simple (d := d) G hG start q.sample.1 k
      q.sourceDeviation q.finishDeviation q.endpoint_eq q.route_simple

theorem reverseSimpleClassifiedReturn_involutive
    {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) :
    reverseSimpleClassifiedReturn (d := d) G hG
        (reverseSimpleClassifiedReturn (d := d) G hG q) = q := by
  apply SimpleClassifiedReturn.ext
  · apply Subtype.ext
    exact reversedReturnRotation_twice (d := d) G hG start q.sample.1 k
      q.sourceDeviation q.finishDeviation q.endpoint_eq
  · rfl
  · rfl

theorem reverseSimpleClassifiedReturn_injective
    {start : OrientedEdge G} {k : ℕ} :
    Function.Injective
      (reverseSimpleClassifiedReturn (d := d) G hG :
        SimpleClassifiedReturn (d := d) G hG start k →
          SimpleClassifiedReturn (d := d) G hG start k) :=
  Function.Involutive.injective
    (reverseSimpleClassifiedReturn_involutive (d := d) G hG)

def SimpleReturnEligible {start : OrientedEdge G} {k : ℕ} (L : ℕ)
    (q : SimpleClassifiedReturn (d := d) G hG start k) : Prop :=
  returnLength d G hG start q.sample.1 k q.sourceDeviation ≤ L ∧
    internalTime q.source.1 + L ≤ k ∧
    internalTime q.finish.1 + L ≤ k

theorem reverseSimpleClassifiedReturn_eligible
    {start : OrientedEdge G} {k L : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k)
    (hq : SimpleReturnEligible (d := d) G hG L q) :
    SimpleReturnEligible (d := d) G hG L
      (reverseSimpleClassifiedReturn (d := d) G hG q) := by
  rcases hq with ⟨hlen, hsource, hfinish⟩
  refine ⟨?_, hfinish, hsource⟩
  change returnLength d G hG start
      (reversedReturnRotation (d := d) G hG start q.sample.1 k
        q.sourceDeviation) k
      (transportDeviation (d := d) G hG start q.sample.1 k
        q.sourceDeviation q.finishDeviation) ≤ L
  rw [classified_reverse_returnLength (d := d) G hG start q.sample.1 k
    q.sourceDeviation q.finishDeviation q.endpoint_eq]
  exact hlen

def SimpleReturnCertified {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) : Prop :=
  (q.finish.1 : ℕ) ≤ (q.source.1 : ℕ)

theorem certified_or_reverse_certified
    {start : OrientedEdge G} {k : ℕ}
    (q : SimpleClassifiedReturn (d := d) G hG start k) :
    SimpleReturnCertified (d := d) G hG q ∨
      SimpleReturnCertified (d := d) G hG
        (reverseSimpleClassifiedReturn (d := d) G hG q) := by
  exact le_total (q.finish.1 : ℕ) (q.source.1 : ℕ)

def EligibleSimpleClassifiedReturn (start : OrientedEdge G) (k L : ℕ) :=
  {q : SimpleClassifiedReturn (d := d) G hG start k //
    SimpleReturnEligible (d := d) G hG L q}

def CertifiedEligibleSimpleReturn (start : OrientedEdge G) (k L : ℕ) :=
  {q : EligibleSimpleClassifiedReturn (d := d) G hG start k L //
    SimpleReturnCertified (d := d) G hG q.1}

def UncertifiedEligibleSimpleReturn (start : OrientedEdge G) (k L : ℕ) :=
  {q : EligibleSimpleClassifiedReturn (d := d) G hG start k L //
    ¬ SimpleReturnCertified (d := d) G hG q.1}

def reverseEligibleSimpleReturn {start : OrientedEdge G} {k L : ℕ}
    (q : EligibleSimpleClassifiedReturn (d := d) G hG start k L) :
    EligibleSimpleClassifiedReturn (d := d) G hG start k L :=
  ⟨reverseSimpleClassifiedReturn (d := d) G hG q.1,
    reverseSimpleClassifiedReturn_eligible (d := d) G hG q.1 q.2⟩

def uncertifiedToCertified {start : OrientedEdge G} {k L : ℕ}
    (q : UncertifiedEligibleSimpleReturn (d := d) G hG start k L) :
    CertifiedEligibleSimpleReturn (d := d) G hG start k L :=
  ⟨reverseEligibleSimpleReturn (d := d) G hG q.1, by
    have hnot := q.2
    change ¬ ((q.1.1.finish.1 : ℕ) ≤ (q.1.1.source.1 : ℕ)) at hnot
    change (q.1.1.source.1 : ℕ) ≤ (q.1.1.finish.1 : ℕ)
    omega⟩

theorem uncertifiedToCertified_injective
    {start : OrientedEdge G} {k L : ℕ} :
    Function.Injective
      (uncertifiedToCertified (d := d) G hG :
        UncertifiedEligibleSimpleReturn (d := d) G hG start k L →
          CertifiedEligibleSimpleReturn (d := d) G hG start k L) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply reverseSimpleClassifiedReturn_injective (d := d) G hG
  exact congrArg (fun z ↦ z.1.1) hab

instance simpleClassifiedReturnFinite
    {start : OrientedEdge G} {k : ℕ} :
    Finite (SimpleClassifiedReturn (d := d) G hG start k) :=
  Finite.of_injective
    (fun q : SimpleClassifiedReturn (d := d) G hG start k ↦
      (q.sample, q.source, q.finish)) (by
        intro a b hab
        apply SimpleClassifiedReturn.ext
        · exact congrArg (fun z ↦ z.1) hab
        · exact congrArg (fun z ↦ z.2.1) hab
        · exact congrArg (fun z ↦ z.2.2) hab)

instance eligibleSimpleClassifiedReturnFinite
    {start : OrientedEdge G} {k L : ℕ} :
    Finite (EligibleSimpleClassifiedReturn (d := d) G hG start k L) :=
  Finite.of_injective Subtype.val Subtype.val_injective

instance certifiedEligibleSimpleReturnFinite
    {start : OrientedEdge G} {k L : ℕ} :
    Finite (CertifiedEligibleSimpleReturn (d := d) G hG start k L) :=
  Finite.of_injective Subtype.val Subtype.val_injective

instance uncertifiedEligibleSimpleReturnFinite
    {start : OrientedEdge G} {k L : ℕ} :
    Finite (UncertifiedEligibleSimpleReturn (d := d) G hG start k L) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable def eligibleCertifiedSumEquiv
    {start : OrientedEdge G} {k L : ℕ} :
    EligibleSimpleClassifiedReturn (d := d) G hG start k L ≃
      CertifiedEligibleSimpleReturn (d := d) G hG start k L ⊕
        UncertifiedEligibleSimpleReturn (d := d) G hG start k L := by
  classical
  exact
    { toFun := fun q ↦
        if h : SimpleReturnCertified (d := d) G hG q.1 then
          Sum.inl ⟨q, h⟩
        else Sum.inr ⟨q, h⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := by
        intro q
        by_cases h : SimpleReturnCertified (d := d) G hG q.1
        · simp [h]
        · simp [h]
      right_inv := by
        intro q
        rcases q with q | q
        · simp [q.2]
        · simp [q.2] }

/-- At least half of all eligible simple classified returns are certified. -/
theorem card_eligibleSimpleClassifiedReturn_le_two_mul_certified
    {start : OrientedEdge G} {k L : ℕ} :
    Nat.card (EligibleSimpleClassifiedReturn (d := d) G hG start k L) ≤
      2 * Nat.card
        (CertifiedEligibleSimpleReturn (d := d) G hG start k L) := by
  rw [Nat.card_congr (eligibleCertifiedSumEquiv (d := d) G hG), Nat.card_sum]
  have hle :
      Nat.card (UncertifiedEligibleSimpleReturn (d := d) G hG start k L) ≤
        Nat.card (CertifiedEligibleSimpleReturn (d := d) G hG start k L) :=
    Nat.card_le_card_of_injective _
      (uncertifiedToCertified_injective (d := d) G hG)
  omega

end

end TranslationReversal



set_option linter.unusedSectionVars false

namespace TranslationIntegration

open NonbacktrackingWalks TranslationReversal

noncomputable section

variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)

local instance graphAdjDecidable : DecidableRel G.Adj := Classical.decRel _
local instance vertexDecidableEq : DecidableEq V := Classical.decEq _

/-- A classified eligible return without a route-simplicity assumption. -/
@[ext] structure ClassifiedEligibleReturn (start : OrientedEdge G) (k L : ℕ) where
  sample : GoodOmega d G hG start k
  source : DeviationIndex d k
  finish : DeviationIndex d k
  source_valid : IsValidDeviation d G hG start sample.1 source
  finish_valid : IsValidDeviation d G hG start sample.1 finish
  endpoint_eq :
    returnEndpoint d G hG start sample.1 k ⟨source, source_valid⟩ =
      Dart.reverse G (sideDart d G hG start sample.1 finish)
  length_le : returnLength d G hG start sample.1 k ⟨source, source_valid⟩ ≤ L
  source_le : internalTime source.1 + L ≤ k
  finish_le : internalTime finish.1 + L ≤ k

def CountedEligibleReturn (start : OrientedEdge G) (k : ℕ) :=
  Σ rho : GoodOmega d G hG start k,
    {q : ValidDeviation d G hG start rho.1 k //
      q ∈ eligibleDeviations d G hG start rho}

instance countedEligibleReturnFinite (start : OrientedEdge G) (k : ℕ) :
    Finite (CountedEligibleReturn (d := d) G hG start k) := by
  unfold CountedEligibleReturn
  infer_instance

instance classifiedEligibleReturnFinite (start : OrientedEdge G) (k L : ℕ) :
    Finite (ClassifiedEligibleReturn (d := d) G hG start k L) :=
  Finite.of_injective
    (fun q : ClassifiedEligibleReturn (d := d) G hG start k L ↦
      (q.sample, q.source, q.finish)) <| by
        intro q r hqr
        apply ClassifiedEligibleReturn.ext
        · exact congrArg (fun z ↦ z.1) hqr
        · exact congrArg (fun z ↦ z.2.1) hqr
        · exact congrArg (fun z ↦ z.2.2) hqr

/-- Each point counted by the arithmetic estimate has a unique classified
finish supplied by first return. -/
def countedEligibleToClassified (start : OrientedEdge G) (k : ℕ) :
    CountedEligibleReturn (d := d) G hG start k →
      ClassifiedEligibleReturn (d := d) G hG start k
        (degreeCutoff d (Fintype.card V) k) :=
  fun q ↦ by
    have hm := q.2.2
    simp only [eligibleDeviations, DegreeEligibleArithmetic.eligible,
      Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact
      { sample := q.1
        source := q.2.1.1
        finish := (finishDeviation d G hG start q.1 q.2.1).1
        source_valid := q.2.1.2
        finish_valid := (finishDeviation d G hG start q.1 q.2.1).2
        endpoint_eq := finishDeviation_spec d G hG start q.1 q.2.1 hm.2.2.2
        length_le := hm.1
        source_le := hm.2.1
        finish_le := hm.2.2.1 }

theorem countedEligibleToClassified_injective (start : OrientedEdge G) (k : ℕ) :
    Function.Injective (countedEligibleToClassified (d := d) G hG start k) := by
  rintro ⟨rho, q⟩ ⟨rho', r⟩ hqr
  have hsample : rho = rho' := congrArg ClassifiedEligibleReturn.sample hqr
  subst rho'
  have hsource : q.1.1 = r.1.1 :=
    congrArg ClassifiedEligibleReturn.source hqr
  have hq : q = r := by
    apply Subtype.ext
    apply Subtype.ext
    exact hsource
  subst r
  rfl

/-- Sum the pointwise `k/4` estimate over all good plans. -/
theorem countedEligible_lower (start : OrientedEdge G) (k : ℕ)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k * Nat.card (GoodOmega d G hG start k) ≤
      4 * Nat.card (CountedEligibleReturn (d := d) G hG start k) := by
  letI : Fintype (GoodOmega d G hG start k) := Fintype.ofFinite _
  letI (rho : GoodOmega d G hG start k) :
      Fintype {q : ValidDeviation d G hG start rho.1 k //
        q ∈ eligibleDeviations d G hG start rho} := Fintype.ofFinite _
  have hsum : ∑ _rho : GoodOmega d G hG start k, k ≤
      ∑ rho : GoodOmega d G hG start k,
        4 * (eligibleDeviations d G hG start rho).card := by
    exact Finset.sum_le_sum fun rho _ ↦
      many_eligibleDeviations d G hG start rho hd hhigh hkn
  change k * Nat.card (GoodOmega d G hG start k) ≤
    4 * Nat.card (Σ rho : GoodOmega d G hG start k,
      {q : ValidDeviation d G hG start rho.1 k //
        q ∈ eligibleDeviations d G hG start rho})
  rw [Nat.card_sigma]
  simpa [Nat.card_eq_fintype_card, Finset.mul_sum, Nat.mul_comm] using hsum

theorem classifiedEligible_lower (start : OrientedEdge G) (k : ℕ)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k * Nat.card (GoodOmega d G hG start k) ≤
      4 * Nat.card (ClassifiedEligibleReturn (d := d) G hG start k
        (degreeCutoff d (Fintype.card V) k)) := by
  calc
    k * Nat.card (GoodOmega d G hG start k) ≤
        4 * Nat.card (CountedEligibleReturn (d := d) G hG start k) :=
      countedEligible_lower (d := d) G hG start k hd hhigh hkn
    _ ≤ 4 * Nat.card (ClassifiedEligibleReturn (d := d) G hG start k
        (degreeCutoff d (Fintype.card V) k)) :=
      Nat.mul_le_mul_left 4 <| Nat.card_le_card_of_injective _
        (countedEligibleToClassified_injective (d := d) G hG start k)

/-- The paper's collision certification predicate. -/
def ClassifiedReturnCertified {start : OrientedEdge G} {k L : ℕ}
    (q : ClassifiedEligibleReturn (d := d) G hG start k L) : Prop :=
  ¬ ReturnRouteSimple (d := d) G hG start q.sample.1 k
      ⟨q.source, q.source_valid⟩ ∨
    (q.finish.1 : ℕ) ≤ (q.source.1 : ℕ)

def CertifiedClassifiedReturn (start : OrientedEdge G) (k L : ℕ) :=
  {q : ClassifiedEligibleReturn (d := d) G hG start k L //
    ClassifiedReturnCertified (d := d) G hG q}

def UncertifiedClassifiedReturn (start : OrientedEdge G) (k L : ℕ) :=
  {q : ClassifiedEligibleReturn (d := d) G hG start k L //
    ¬ ClassifiedReturnCertified (d := d) G hG q}

instance certifiedClassifiedReturnFinite (start : OrientedEdge G) (k L : ℕ) :
    Finite (CertifiedClassifiedReturn (d := d) G hG start k L) :=
  Finite.of_injective Subtype.val Subtype.val_injective

instance uncertifiedClassifiedReturnFinite (start : OrientedEdge G) (k L : ℕ) :
    Finite (UncertifiedClassifiedReturn (d := d) G hG start k L) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- An uncertified broad return is exactly an uncertified simple return. -/
def uncertifiedClassifiedToSimple {start : OrientedEdge G} {k L : ℕ}
    (q : UncertifiedClassifiedReturn (d := d) G hG start k L) :
    UncertifiedEligibleSimpleReturn (d := d) G hG start k L := by
  have hs : ReturnRouteSimple (d := d) G hG start q.1.sample.1 k
      ⟨q.1.source, q.1.source_valid⟩ := by
    by_contra hn
    exact q.2 (Or.inl hn)
  have hord : ¬ (q.1.finish.1 : ℕ) ≤ (q.1.source.1 : ℕ) := by
    intro h
    exact q.2 (Or.inr h)
  refine ⟨⟨{
      sample := q.1.sample
      source := q.1.source
      finish := q.1.finish
      source_valid := q.1.source_valid
      finish_valid := q.1.finish_valid
      endpoint_eq := q.1.endpoint_eq
      route_simple := hs }, ?_⟩, ?_⟩
  · exact ⟨q.1.length_le, q.1.source_le, q.1.finish_le⟩
  · exact hord

theorem uncertifiedClassifiedToSimple_injective
    {start : OrientedEdge G} {k L : ℕ} :
    Function.Injective
      (uncertifiedClassifiedToSimple (d := d) G hG :
        UncertifiedClassifiedReturn (d := d) G hG start k L →
          UncertifiedEligibleSimpleReturn (d := d) G hG start k L) := by
  intro q r hqr
  apply Subtype.ext
  apply ClassifiedEligibleReturn.ext
  · exact congrArg (fun z ↦ z.1.1.sample) hqr
  · exact congrArg (fun z ↦ z.1.1.source) hqr
  · exact congrArg (fun z ↦ z.1.1.finish) hqr

/-- Forget route simplicity after reversal; the result is broadly certified. -/
def certifiedSimpleToClassified {start : OrientedEdge G} {k L : ℕ}
    (q : CertifiedEligibleSimpleReturn (d := d) G hG start k L) :
    CertifiedClassifiedReturn (d := d) G hG start k L :=
  ⟨{
      sample := q.1.1.sample
      source := q.1.1.source
      finish := q.1.1.finish
      source_valid := q.1.1.source_valid
      finish_valid := q.1.1.finish_valid
      endpoint_eq := q.1.1.endpoint_eq
      length_le := q.1.2.1
      source_le := q.1.2.2.1
      finish_le := q.1.2.2.2 },
    Or.inr q.2⟩

theorem certifiedSimpleToClassified_injective
    {start : OrientedEdge G} {k L : ℕ} :
    Function.Injective
      (certifiedSimpleToClassified (d := d) G hG :
        CertifiedEligibleSimpleReturn (d := d) G hG start k L →
          CertifiedClassifiedReturn (d := d) G hG start k L) := by
  intro q r hqr
  apply Subtype.ext
  apply Subtype.ext
  apply SimpleClassifiedReturn.ext
  · exact congrArg (fun z ↦ z.1.sample) hqr
  · exact congrArg (fun z ↦ z.1.source) hqr
  · exact congrArg (fun z ↦ z.1.finish) hqr

def uncertifiedClassifiedToCertified {start : OrientedEdge G} {k L : ℕ}
    (q : UncertifiedClassifiedReturn (d := d) G hG start k L) :
    CertifiedClassifiedReturn (d := d) G hG start k L :=
  certifiedSimpleToClassified (d := d) G hG <|
    uncertifiedToCertified (d := d) G hG <|
      uncertifiedClassifiedToSimple (d := d) G hG q

theorem uncertifiedClassifiedToCertified_injective
    {start : OrientedEdge G} {k L : ℕ} :
    Function.Injective
      (uncertifiedClassifiedToCertified (d := d) G hG :
        UncertifiedClassifiedReturn (d := d) G hG start k L →
          CertifiedClassifiedReturn (d := d) G hG start k L) :=
  (certifiedSimpleToClassified_injective (d := d) G hG).comp <|
    (uncertifiedToCertified_injective (d := d) G hG).comp <|
      uncertifiedClassifiedToSimple_injective (d := d) G hG

def subtypeOrNotEquiv {X : Type*} (p : X → Prop) [DecidablePred p] :
    X ≃ {x : X // p x} ⊕ {x : X // ¬ p x} where
  toFun x := if hx : p x then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, hx⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv x := by by_cases hx : p x <;> simp [hx]
  right_inv q := by
    rcases q with q | q
    · simp [q.2]
    · simp [q.2]

/-- Excursion reversal certifies at least half of all classified returns. -/
theorem classified_le_two_mul_certified
    (start : OrientedEdge G) (k L : ℕ) :
    Nat.card (ClassifiedEligibleReturn (d := d) G hG start k L) ≤
      2 * Nat.card (CertifiedClassifiedReturn (d := d) G hG start k L) := by
  let E := ClassifiedEligibleReturn (d := d) G hG start k L
  let p : E → Prop := ClassifiedReturnCertified (d := d) G hG
  letI : DecidablePred p := Classical.decPred _
  change Nat.card E ≤ 2 * Nat.card {q : E // p q}
  have hUC : Nat.card {q : E // ¬ p q} ≤ Nat.card {q : E // p q} :=
    Nat.card_le_card_of_injective _ <|
      uncertifiedClassifiedToCertified_injective (d := d) G hG
  have hpartition : Nat.card E =
      Nat.card {q : E // p q} + Nat.card {q : E // ¬ p q} := by
    rw [Nat.card_congr (subtypeOrNotEquiv p), Nat.card_sum]
  omega

theorem certified_lower (start : OrientedEdge G) (k : ℕ)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k * Nat.card (GoodOmega d G hG start k) ≤
      8 * Nat.card (CertifiedClassifiedReturn (d := d) G hG start k
        (degreeCutoff d (Fintype.card V) k)) := by
  calc
    k * Nat.card (GoodOmega d G hG start k) ≤
        4 * Nat.card (ClassifiedEligibleReturn (d := d) G hG start k
          (degreeCutoff d (Fintype.card V) k)) :=
      classifiedEligible_lower (d := d) G hG start k hd hhigh hkn
    _ ≤ 8 * Nat.card (CertifiedClassifiedReturn (d := d) G hG start k
          (degreeCutoff d (Fintype.card V) k)) := by
      have hhalf := classified_le_two_mul_certified (d := d) G hG start k
        (degreeCutoff d (Fintype.card V) k)
      omega

end

end TranslationIntegration



set_option linter.unusedSectionVars false

namespace TranslationCollisionSwitching

open NonbacktrackingWalks TranslationReversal TranslationIntegration

noncomputable section

variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)

local instance graphAdjDecidable : DecidableRel G.Adj := Classical.decRel _
local instance vertexDecidableEq : DecidableEq V := Classical.decEq _

theorem phi_setOffsetAt_eq_of_head_ne (rho : RotationSystem d V) (v₀ : V)
    (a : Offset d) (e : Dart G) (h : e.head ≠ v₀) :
    phi d G hG (setOffsetAt d rho v₀ a) e = phi d G hG rho e := by
  apply Dart.ext
  · rfl
  · simp only [Dart.head_phi]
    rw [setOffsetAt_ne d rho a h]

/-- A one-vertex deviation agrees with its good source before the selected
internal time. -/
theorem deviation_orbitDart_eq_of_lt (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k)
    {t : ℕ} (ht : t < internalTime q.1.1) :
    orbitDart d G hG start (deviationRotation d G hG start rho.1 q.1) t =
      orbitDart d G hG start rho.1 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show t + 1 = Nat.succ t by omega, orbitDart_succ,
        orbitDart_succ, ih (by omega)]
      apply phi_setOffsetAt_eq_of_head_ne (d := d) G hG
      intro hhead
      have hvertices : orbitVertex d G hG start rho.1 (t + 1) =
          orbitVertex d G hG start rho.1 (internalTime q.1.1) := by
        rw [orbitVertex_succ]
        exact hhead
      have hfin :
          (⟨t + 1, by
              have := internalTime_lt q.1.1
              omega⟩ : Fin (k + 1)) =
            ⟨internalTime q.1.1,
              lt_trans (internalTime_lt q.1.1) (Nat.lt_succ_self k)⟩ :=
        rho.2 hvertices
      have hval : t + 1 = internalTime q.1.1 := congrArg Fin.val hfin
      omega

theorem deviation_orbitVertex_eq_of_le (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k)
    {t : ℕ} (ht : t ≤ internalTime q.1.1) :
    orbitVertex d G hG start (deviationRotation d G hG start rho.1 q.1) t =
      orbitVertex d G hG start rho.1 t := by
  rcases lt_or_eq_of_le ht with hlt | rfl
  · exact congrArg (Dart.tail G)
      (deviation_orbitDart_eq_of_lt (d := d) G hG start rho q hlt)
  · have hrpos : 0 < internalTime q.1.1 := by simp [internalTime]
    have hdart := deviation_orbitDart_eq_of_lt (d := d) G hG start rho q
      (t := internalTime q.1.1 - 1) (by omega)
    calc
      orbitVertex d G hG start
          (deviationRotation d G hG start rho.1 q.1) (internalTime q.1.1) =
          orbitVertex d G hG start
            (deviationRotation d G hG start rho.1 q.1)
            ((internalTime q.1.1 - 1) + 1) := by congr 1
      _ = (orbitDart d G hG start
            (deviationRotation d G hG start rho.1 q.1)
            (internalTime q.1.1 - 1)).head :=
        orbitVertex_succ d G hG start _ _
      _ = (orbitDart d G hG start rho.1
            (internalTime q.1.1 - 1)).head := congrArg (Dart.head G) hdart
      _ = orbitVertex d G hG start rho.1
            ((internalTime q.1.1 - 1) + 1) :=
        (orbitVertex_succ d G hG start _ _).symm
      _ = orbitVertex d G hG start rho.1 (internalTime q.1.1) := by congr 1

theorem deviation_orbitDart_internal (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) :
    orbitDart d G hG start (deviationRotation d G hG start rho.1 q.1)
        (internalTime q.1.1) =
      sideDart d G hG start rho.1 q.1 := by
  have hi : (q.1.1 : ℕ) < internalTime q.1.1 := by simp [internalTime]
  rw [show internalTime q.1.1 = (q.1.1 : ℕ) + 1 by rfl,
    orbitDart_succ,
    deviation_orbitDart_eq_of_lt (d := d) G hG start rho q hi]
  rfl

theorem deviation_follows_returnRoute (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k)
    (t : ℕ) (ht0 : 0 < t)
    (htc : t ≤ returnLength d G hG start rho.1 k q) :
    orbitDart d G hG start (deviationRotation d G hG start rho.1 q.1)
        (internalTime q.1.1 + t - 1) =
      returnRoute (d := d) G hG start rho.1 k q t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht : t = 0
      · subst t
        simpa using deviation_orbitDart_internal (d := d) G hG start rho q
      · have htpos : 0 < t := Nat.pos_of_ne_zero ht
        have htlt : t < returnLength d G hG start rho.1 k q := by omega
        have hiRoute := ih htpos htlt.le
        rw [show internalTime q.1.1 + (t + 1) - 1 =
            (internalTime q.1.1 + t - 1) + 1 by omega,
          orbitDart_succ, hiRoute, returnRoute_succ]
        apply phi_setOffsetAt_eq_of_head_ne (d := d) G hG
        intro heq
        apply firstReturn_head_outside (d := d) G hG start rho.1 k q t
          htpos htlt
        rw [heq]
        exact mem_pathVertices d G hG start rho.1 k
          ⟨internalTime q.1.1,
            lt_trans (internalTime_lt q.1.1) (Nat.lt_succ_self k)⟩

theorem deviation_orbitVertex_returnRoute_head (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k)
    (t : ℕ) (ht0 : 0 < t)
    (htc : t ≤ returnLength d G hG start rho.1 k q) :
    orbitVertex d G hG start (deviationRotation d G hG start rho.1 q.1)
        (internalTime q.1.1 + t) =
      (returnRoute (d := d) G hG start rho.1 k q t).head := by
  rw [show internalTime q.1.1 + t =
      (internalTime q.1.1 + t - 1) + 1 by omega,
    orbitVertex_succ,
    deviation_follows_returnRoute (d := d) G hG start rho q t ht0 htc]

def HasCollisionAt (start : OrientedEdge G)
    (rho : RotationSystem d V) (t : ℕ) : Prop :=
  ∃ s : Fin t,
    orbitVertex d G hG start rho s = orbitVertex d G hG start rho t

theorem exists_collision (start : OrientedEdge G) (rho : RotationSystem d V) :
    ∃ t : ℕ, HasCollisionAt (d := d) G hG start rho t := by
  let p := phi d G hG rho
  refine ⟨orderOf p, ⟨0, orderOf_pos p⟩, ?_⟩
  change (orbitDart d G hG start rho 0).tail =
    (orbitDart d G hG start rho (orderOf p)).tail
  apply congrArg (Dart.tail G)
  change startDart G start = ((p : Dart G → Dart G)^[orderOf p]) (startDart G start)
  rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
  rfl

include hG in
noncomputable def firstCollisionTime (start : OrientedEdge G)
    (rho : RotationSystem d V) : ℕ := by
  classical
  exact Nat.find (exists_collision (d := d) G hG start rho)

theorem firstCollision_spec (start : OrientedEdge G) (rho : RotationSystem d V) :
    HasCollisionAt (d := d) G hG start rho
      (firstCollisionTime (d := d) G hG start rho) :=
  by
    classical
    exact Nat.find_spec (exists_collision (d := d) G hG start rho)

theorem firstCollisionTime_pos (start : OrientedEdge G) (rho : RotationSystem d V) :
    0 < firstCollisionTime (d := d) G hG start rho := by
  obtain ⟨s, -⟩ := firstCollision_spec (d := d) G hG start rho
  exact Nat.zero_lt_of_lt s.isLt

theorem firstCollisionTime_le_of_collision (start : OrientedEdge G)
    (rho : RotationSystem d V) {t : ℕ}
    (ht : HasCollisionAt (d := d) G hG start rho t) :
    firstCollisionTime (d := d) G hG start rho ≤ t :=
  by
    classical
    exact Nat.find_min' (exists_collision (d := d) G hG start rho) ht

theorem deviation_lt_firstCollisionTime (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) :
    internalTime q.1.1 < firstCollisionTime (d := d) G hG start
      (deviationRotation d G hG start rho.1 q.1) := by
  let eta := deviationRotation d G hG start rho.1 q.1
  let T := firstCollisionTime (d := d) G hG start eta
  by_contra hnot
  change ¬ internalTime q.1.1 < T at hnot
  have hTr : T ≤ internalTime q.1.1 := by omega
  obtain ⟨s, hcollision⟩ := firstCollision_spec (d := d) G hG start eta
  have hsle : (s : ℕ) ≤ internalTime q.1.1 := by omega
  have hsource : orbitVertex d G hG start rho.1 s =
      orbitVertex d G hG start rho.1 T := by
    rw [← deviation_orbitVertex_eq_of_le (d := d) G hG start rho q hsle,
      ← deviation_orbitVertex_eq_of_le (d := d) G hG start rho q hTr]
    exact hcollision
  have hfin :
      (⟨(s : ℕ), by
          have := internalTime_lt q.1.1
          omega⟩ : Fin (k + 1)) =
        ⟨T, by
          have := internalTime_lt q.1.1
          omega⟩ := rho.2 hsource
  have hst : (s : ℕ) = T := congrArg Fin.val hfin
  omega

theorem not_good_of_collision_le (start : OrientedEdge G)
    (rho : RotationSystem d V) (k t : ℕ) (htk : t ≤ k)
    (hcollision : HasCollisionAt (d := d) G hG start rho t) :
    ¬ IsGood d G hG start rho k := by
  intro hgood
  obtain ⟨s, hvertices⟩ := hcollision
  have hfin :
      (⟨(s : ℕ), by omega⟩ : Fin (k + 1)) = ⟨t, by omega⟩ :=
    hgood hvertices
  have hst : (s : ℕ) = t := congrArg Fin.val hfin
  omega

/-- The broad certification predicate gives an explicit collision in the
deviated target by the end of its first-return route. -/
theorem deviation_exists_collision_of_detour (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q q' : ValidDeviation d G hG start rho.1 k)
    (hend : returnEndpoint d G hG start rho.1 k q =
      Dart.reverse G (sideDart d G hG start rho.1 q'.1))
    (hcert : ¬ ReturnRouteSimple (d := d) G hG start rho.1 k q ∨
      (q'.1.1 : ℕ) ≤ (q.1.1 : ℕ)) :
    ∃ t ≤ internalTime q.1.1 + returnLength d G hG start rho.1 k q,
      HasCollisionAt (d := d) G hG start
        (deviationRotation d G hG start rho.1 q.1) t := by
  rcases hcert with hnotSimple | hfinish
  · simp only [ReturnRouteSimple] at hnotSimple
    push Not at hnotSimple
    obtain ⟨a, b, ha0, hac, hb0, hbc, hab, hne⟩ := hnotSimple
    rcases lt_or_gt_of_ne hne with hablt | hbalt
    · refine ⟨internalTime q.1.1 + b, by omega, ?_⟩
      refine ⟨⟨internalTime q.1.1 + a, by omega⟩, ?_⟩
      calc
        orbitVertex d G hG start
            (deviationRotation d G hG start rho.1 q.1)
            (internalTime q.1.1 + a) =
            (returnRoute (d := d) G hG start rho.1 k q a).head :=
          deviation_orbitVertex_returnRoute_head (d := d) G hG start rho q a ha0 hac.le
        _ = (returnRoute (d := d) G hG start rho.1 k q b).head := hab
        _ = orbitVertex d G hG start
            (deviationRotation d G hG start rho.1 q.1)
            (internalTime q.1.1 + b) :=
          (deviation_orbitVertex_returnRoute_head (d := d) G hG start rho q b hb0 hbc.le).symm
    · refine ⟨internalTime q.1.1 + a, by omega, ?_⟩
      refine ⟨⟨internalTime q.1.1 + b, by omega⟩, ?_⟩
      calc
        orbitVertex d G hG start
            (deviationRotation d G hG start rho.1 q.1)
            (internalTime q.1.1 + b) =
            (returnRoute (d := d) G hG start rho.1 k q b).head :=
          deviation_orbitVertex_returnRoute_head (d := d) G hG start rho q b hb0 hbc.le
        _ = (returnRoute (d := d) G hG start rho.1 k q a).head := hab.symm
        _ = orbitVertex d G hG start
            (deviationRotation d G hG start rho.1 q.1)
            (internalTime q.1.1 + a) :=
          (deviation_orbitVertex_returnRoute_head (d := d) G hG start rho q a ha0 hac.le).symm
  · let c := returnLength d G hG start rho.1 k q
    have hc : 0 < c := returnLength_pos d G hG start rho.1 k q
    have hjle : internalTime q'.1.1 ≤ internalTime q.1.1 := by
      simp only [internalTime]
      omega
    refine ⟨internalTime q.1.1 + c, le_rfl, ?_⟩
    refine ⟨⟨internalTime q'.1.1, by omega⟩, ?_⟩
    calc
      orbitVertex d G hG start
          (deviationRotation d G hG start rho.1 q.1)
          (internalTime q'.1.1) =
          orbitVertex d G hG start rho.1 (internalTime q'.1.1) :=
        deviation_orbitVertex_eq_of_le (d := d) G hG start rho q hjle
      _ = (sideDart d G hG start rho.1 q'.1).tail :=
        (sideDart_tail d G hG start rho.1 q'.1).symm
      _ = (Dart.reverse G (sideDart d G hG start rho.1 q'.1)).head := by rfl
      _ = (returnEndpoint d G hG start rho.1 k q).head :=
        congrArg (Dart.head G) hend.symm
      _ = (returnRoute (d := d) G hG start rho.1 k q c).head := by
        rw [returnRoute_at_length]
      _ = orbitVertex d G hG start
          (deviationRotation d G hG start rho.1 q.1)
          (internalTime q.1.1 + c) :=
        (deviation_orbitVertex_returnRoute_head (d := d) G hG start rho q c hc le_rfl).symm

def certifiedTarget {start : OrientedEdge G} {k L : ℕ}
    (q : CertifiedClassifiedReturn (d := d) G hG start k L) :
    RotationSystem d V :=
  deviationRotation d G hG start q.1.sample.1 q.1.source

theorem certified_target_not_good {start : OrientedEdge G} {k L : ℕ}
    (q : CertifiedClassifiedReturn (d := d) G hG start k L) :
    ¬ IsGood d G hG start (certifiedTarget (d := d) G hG q) k := by
  let qs : ValidDeviation d G hG start q.1.sample.1 k :=
    ⟨q.1.source, q.1.source_valid⟩
  let qf : ValidDeviation d G hG start q.1.sample.1 k :=
    ⟨q.1.finish, q.1.finish_valid⟩
  obtain ⟨t, ht, hcollision⟩ :=
    deviation_exists_collision_of_detour (d := d) G hG start q.1.sample qs qf
      q.1.endpoint_eq q.2
  apply not_good_of_collision_le (d := d) G hG start _ k t
  · have hc := q.1.length_le
    have hs := q.1.source_le
    have ht' : t ≤ internalTime q.1.source.1 +
        returnLength d G hG start q.1.sample.1 k
          ⟨q.1.source, q.1.source_valid⟩ := by
      simpa only [qs] using ht
    change t ≤ k
    omega
  · exact hcollision

theorem certified_collision_window {start : OrientedEdge G} {k L : ℕ}
    (q : CertifiedClassifiedReturn (d := d) G hG start k L) :
    internalTime q.1.source.1 <
        firstCollisionTime (d := d) G hG start (certifiedTarget (d := d) G hG q) ∧
      firstCollisionTime (d := d) G hG start (certifiedTarget (d := d) G hG q) ≤
        internalTime q.1.source.1 + L := by
  let qs : ValidDeviation d G hG start q.1.sample.1 k :=
    ⟨q.1.source, q.1.source_valid⟩
  let qf : ValidDeviation d G hG start q.1.sample.1 k :=
    ⟨q.1.finish, q.1.finish_valid⟩
  constructor
  · exact deviation_lt_firstCollisionTime (d := d) G hG start q.1.sample qs
  · obtain ⟨t, ht, hcollision⟩ :=
      deviation_exists_collision_of_detour (d := d) G hG start q.1.sample qs qf
        q.1.endpoint_eq q.2
    have hTt := firstCollisionTime_le_of_collision (d := d) G hG start
      (certifiedTarget (d := d) G hG q) hcollision
    have hc := q.1.length_le
    have ht' : t ≤ internalTime q.1.source.1 +
        returnLength d G hG start q.1.sample.1 k
          ⟨q.1.source, q.1.source_valid⟩ := by
      simpa only [qs] using ht
    omega

def certifiedSlot {start : OrientedEdge G} {k L : ℕ}
    (q : CertifiedClassifiedReturn (d := d) G hG start k L) : Fin L :=
  ⟨firstCollisionTime (d := d) G hG start (certifiedTarget (d := d) G hG q) -
      (internalTime q.1.source.1 + 1), by
    have hw := certified_collision_window (d := d) G hG q
    omega⟩

def certifiedOldOffset {start : OrientedEdge G} {k L : ℕ}
    (q : CertifiedClassifiedReturn (d := d) G hG start k L) : Offset d :=
  currentOffset d G hG start q.1.sample.1 q.1.source.1

@[simp] theorem deviationRotation_apply_source (start : OrientedEdge G)
    (rho : RotationSystem d V) {k : ℕ} (q : DeviationIndex d k) :
    deviationRotation d G hG start rho q
        (orbitVertex d G hG start rho (internalTime q.1)) = q.2 := by
  simp [deviationRotation]

def recoverRotation (start : OrientedEdge G) (eta : RotationSystem d V)
    {k : ℕ} (i : Fin (k - 1)) (a : Offset d) : RotationSystem d V :=
  setOffsetAt d eta (orbitVertex d G hG start eta (internalTime i)) a

theorem recover_deviationRotation (start : OrientedEdge G)
    (rho : GoodOmega d G hG start k)
    (q : ValidDeviation d G hG start rho.1 k) :
    recoverRotation (d := d) G hG start
        (deviationRotation d G hG start rho.1 q.1) q.1.1
        (currentOffset d G hG start rho.1 q.1.1) = rho.1 := by
  have hv := deviation_orbitVertex_eq_of_le (d := d) G hG start rho q
    (le_refl (internalTime q.1.1))
  unfold recoverRotation
  rw [hv]
  funext v
  by_cases h : v = orbitVertex d G hG start rho.1 (internalTime q.1.1)
  · subst v
    simp [deviationRotation, currentOffset]
  · simp [deviationRotation, setOffsetAt, h]

def certifiedCode {start : OrientedEdge G} {k L : ℕ}
    (q : CertifiedClassifiedReturn (d := d) G hG start k L) :
    RotationSystem d V × (Fin L × Offset d) :=
  (certifiedTarget (d := d) G hG q,
    certifiedSlot (d := d) G hG q,
    certifiedOldOffset (d := d) G hG q)

theorem returnEndpoint_congr (start : OrientedEdge G)
    {rho sigma : RotationSystem d V} {k : ℕ}
    {q r : DeviationIndex d k}
    (hrho : rho = sigma) (hqr : q = r)
    (hq : IsValidDeviation d G hG start rho q)
    (hr : IsValidDeviation d G hG start sigma r) :
    returnEndpoint d G hG start rho k ⟨q, hq⟩ =
      returnEndpoint d G hG start sigma k ⟨r, hr⟩ := by
  subst sigma
  subst r
  rfl

theorem sideDart_rotation_congr (start : OrientedEdge G)
    {rho sigma : RotationSystem d V} {k : ℕ}
    (hrho : rho = sigma) (q : DeviationIndex d k) :
    sideDart d G hG start rho q = sideDart d G hG start sigma q := by
  subst sigma
  rfl

theorem certifiedCode_injective {start : OrientedEdge G} {k L : ℕ} :
    Function.Injective
      (certifiedCode (d := d) G hG :
        CertifiedClassifiedReturn (d := d) G hG start k L →
          RotationSystem d V × (Fin L × Offset d)) := by
  intro q r hcode
  have htarget : certifiedTarget (d := d) G hG q =
      certifiedTarget (d := d) G hG r := congrArg Prod.fst hcode
  have hslot : (certifiedSlot (d := d) G hG q : ℕ) =
      (certifiedSlot (d := d) G hG r : ℕ) :=
    congrArg (fun z : RotationSystem d V × (Fin L × Offset d) ↦
      (z.2.1 : ℕ)) hcode
  have hold : certifiedOldOffset (d := d) G hG q =
      certifiedOldOffset (d := d) G hG r :=
    congrArg (fun z : RotationSystem d V × (Fin L × Offset d) ↦ z.2.2) hcode
  have hT : firstCollisionTime (d := d) G hG start
      (certifiedTarget (d := d) G hG q) =
      firstCollisionTime (d := d) G hG start
        (certifiedTarget (d := d) G hG r) :=
    congrArg (firstCollisionTime (d := d) G hG start) htarget
  have hwq := certified_collision_window (d := d) G hG q
  have hwr := certified_collision_window (d := d) G hG r
  have htime : internalTime q.1.source.1 = internalTime r.1.source.1 := by
    change firstCollisionTime (d := d) G hG start
        (certifiedTarget (d := d) G hG q) -
          (internalTime q.1.source.1 + 1) =
      firstCollisionTime (d := d) G hG start
        (certifiedTarget (d := d) G hG r) -
          (internalTime r.1.source.1 + 1) at hslot
    omega
  have hindex : q.1.source.1 = r.1.source.1 := by
    apply Fin.ext
    simp only [internalTime] at htime
    omega
  let qs : ValidDeviation d G hG start q.1.sample.1 k :=
    ⟨q.1.source, q.1.source_valid⟩
  let rs : ValidDeviation d G hG start r.1.sample.1 k :=
    ⟨r.1.source, r.1.source_valid⟩
  have hvq := deviation_orbitVertex_eq_of_le (d := d) G hG start q.1.sample qs
    (le_refl (internalTime qs.1.1))
  have hvr := deviation_orbitVertex_eq_of_le (d := d) G hG start r.1.sample rs
    (le_refl (internalTime rs.1.1))
  have hoffset : q.1.source.2 = r.1.source.2 := by
    calc
      q.1.source.2 = certifiedTarget (d := d) G hG q
          (orbitVertex d G hG start q.1.sample.1 (internalTime q.1.source.1)) :=
        (deviationRotation_apply_source (d := d) G hG start q.1.sample.1 q.1.source).symm
      _ = certifiedTarget (d := d) G hG q
          (orbitVertex d G hG start (certifiedTarget (d := d) G hG q)
            (internalTime q.1.source.1)) :=
        congrArg (certifiedTarget (d := d) G hG q) hvq.symm
      _ = certifiedTarget (d := d) G hG r
          (orbitVertex d G hG start (certifiedTarget (d := d) G hG r)
            (internalTime r.1.source.1)) := by rw [htarget, htime]
      _ = certifiedTarget (d := d) G hG r
          (orbitVertex d G hG start r.1.sample.1 (internalTime r.1.source.1)) :=
        congrArg (certifiedTarget (d := d) G hG r) hvr
      _ = r.1.source.2 :=
        deviationRotation_apply_source (d := d) G hG start r.1.sample.1 r.1.source
  have hsource : q.1.source = r.1.source := Prod.ext hindex hoffset
  have hsampleVal : q.1.sample.1 = r.1.sample.1 := by
    calc
      q.1.sample.1 = recoverRotation (d := d) G hG start
          (certifiedTarget (d := d) G hG q) q.1.source.1
          (certifiedOldOffset (d := d) G hG q) :=
        (recover_deviationRotation (d := d) G hG start q.1.sample qs).symm
      _ = recoverRotation (d := d) G hG start
          (certifiedTarget (d := d) G hG r) r.1.source.1
          (certifiedOldOffset (d := d) G hG r) := by
        rw [htarget, hindex, hold]
      _ = r.1.sample.1 :=
        recover_deviationRotation (d := d) G hG start r.1.sample rs
  have hsample : q.1.sample = r.1.sample := Subtype.ext hsampleVal
  have hfinish : q.1.finish = r.1.finish := by
    have hendpoint :
        returnEndpoint d G hG start q.1.sample.1 k
            ⟨q.1.source, q.1.source_valid⟩ =
          returnEndpoint d G hG start r.1.sample.1 k
            ⟨r.1.source, r.1.source_valid⟩ :=
      returnEndpoint_congr (d := d) G hG start hsampleVal hsource
        q.1.source_valid r.1.source_valid
    have hsides : sideDart d G hG start q.1.sample.1 q.1.finish =
        sideDart d G hG start r.1.sample.1 r.1.finish := by
      apply (Dart.reverse G).injective
      exact q.1.endpoint_eq.symm.trans (hendpoint.trans r.1.endpoint_eq)
    have hsides' : sideDart d G hG start q.1.sample.1 q.1.finish =
        sideDart d G hG start q.1.sample.1 r.1.finish :=
      hsides.trans
        (sideDart_rotation_congr (d := d) G hG start hsampleVal r.1.finish).symm
    have hrvalid : IsValidDeviation d G hG start q.1.sample.1 r.1.finish := by
      simpa only [hsampleVal] using r.1.finish_valid
    have hvalid :
        (⟨q.1.finish, q.1.finish_valid⟩ :
          ValidDeviation d G hG start q.1.sample.1 k) =
        ⟨r.1.finish, hrvalid⟩ := by
      apply validSideDart_injective d G hG start q.1.sample
      exact hsides'
    exact congrArg Subtype.val hvalid
  apply Subtype.ext
  apply ClassifiedEligibleReturn.ext
  · exact hsample
  · exact hsource
  · exact hfinish

theorem card_certified_le_target_mul {start : OrientedEdge G} {k L : ℕ} :
    Nat.card (CertifiedClassifiedReturn (d := d) G hG start k L) ≤
      Nat.card (RotationSystem d V) * L * (d - 1) := by
  calc
    Nat.card (CertifiedClassifiedReturn (d := d) G hG start k L) ≤
        Nat.card (RotationSystem d V × (Fin L × Offset d)) :=
      Nat.card_le_card_of_injective _ (certifiedCode_injective (d := d) G hG)
    _ = Nat.card (RotationSystem d V) * L * (d - 1) := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_fin, natCard_offset]
      ring

theorem high_switching_card_bound (start : OrientedEdge G) (k : ℕ)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    k * Nat.card (GoodOmega d G hG start k) ≤
      8 * Nat.card (RotationSystem d V) *
        degreeCutoff d (Fintype.card V) k * (d - 1) := by
  calc
    k * Nat.card (GoodOmega d G hG start k) ≤
        8 * Nat.card (CertifiedClassifiedReturn (d := d) G hG start k
          (degreeCutoff d (Fintype.card V) k)) :=
      certified_lower (d := d) G hG start k hd hhigh hkn
    _ ≤ 8 * (Nat.card (RotationSystem d V) *
          degreeCutoff d (Fintype.card V) k * (d - 1)) :=
      Nat.mul_le_mul_left 8 <|
        card_certified_le_target_mul (d := d) G hG
    _ = 8 * Nat.card (RotationSystem d V) *
          degreeCutoff d (Fintype.card V) k * (d - 1) := by ring

theorem degreeCutoff_mul_k_bound {n k : ℕ} (hkn : k < n) :
    8 * degreeCutoff d n k * (d - 1) * k ≤ 1024 * d ^ 2 * n := by
  have hdiv : (64 * d * n / k) * k ≤ 64 * d * n :=
    Nat.div_mul_le_self _ _
  calc
    8 * degreeCutoff d n k * (d - 1) * k ≤
        8 * degreeCutoff d n k * d * k := by
      gcongr <;> omega
    _ = 8 * d * ((64 * d * n / k) * k + k) := by
      simp [degreeCutoff]
      ring
    _ ≤ 8 * d * (64 * d * n + n) := by
      gcongr
    _ ≤ 1024 * d ^ 2 * n := by
      calc
        8 * d * (64 * d * n + n) =
            512 * d ^ 2 * n + 8 * d * n := by ring
        _ ≤ 512 * d ^ 2 * n + 8 * d ^ 2 * n := by
          gcongr
          simpa [pow_two] using Nat.le_mul_of_pos_right d (NeZero.pos d)
        _ = 520 * (d ^ 2 * n) := by ring
        _ ≤ 1024 * (d ^ 2 * n) := by gcongr <;> omega
        _ = 1024 * d ^ 2 * n := by ring

/-- The complete integral high-regime estimate supplied by switching. -/
theorem high_good_plan_card_bound (start : OrientedEdge G) (k : ℕ)
    (hd : 3 ≤ d)
    (hhigh : 1048576 * d ^ 2 * Fintype.card V ≤ k ^ 2)
    (hkn : k < Fintype.card V) :
    Nat.card (GoodOmega d G hG start k) * k ^ 2 ≤
      1024 * d ^ 2 * Fintype.card V * Nat.card (RotationSystem d V) := by
  have hswitch := high_switching_card_bound (d := d) G hG start k hd hhigh hkn
  have hcut := degreeCutoff_mul_k_bound (d := d) hkn
  calc
    Nat.card (GoodOmega d G hG start k) * k ^ 2 =
        (k * Nat.card (GoodOmega d G hG start k)) * k := by ring
    _ ≤ (8 * Nat.card (RotationSystem d V) *
          degreeCutoff d (Fintype.card V) k * (d - 1)) * k :=
      Nat.mul_le_mul_right k hswitch
    _ = (8 * degreeCutoff d (Fintype.card V) k * (d - 1) * k) *
          Nat.card (RotationSystem d V) := by ring
    _ ≤ (1024 * d ^ 2 * Fintype.card V) *
          Nat.card (RotationSystem d V) :=
      Nat.mul_le_mul_right _ hcut
    _ = 1024 * d ^ 2 * Fintype.card V *
          Nat.card (RotationSystem d V) := by ring

end

end TranslationCollisionSwitching



namespace NonbacktrackingWalks

noncomputable section

variable {V : Type*} [Fintype V]

namespace NonbacktrackingWalk

variable {G : SimpleGraph V} {start : OrientedEdge G}

def dropLast {k : ℕ} (w : NonbacktrackingWalk G start (k + 2)) :
    NonbacktrackingWalk G start (k + 1) where
  vertices i := w.vertices i.castSucc
  length_pos := by omega
  startsAtTail := w.startsAtTail
  startsAtHead := w.startsAtHead
  adjacent i := w.adjacent i.castSucc
  noBacktrack i hi :=
    w.noBacktrack i.castSucc (by
      simpa only [Fin.val_castSucc] using Nat.lt_succ_of_lt hi)

@[simp] theorem dropLast_vertices {k : ℕ} (w : NonbacktrackingWalk G start (k + 2))
    (i : Fin (k + 2)) : w.dropLast.vertices i = w.vertices i.castSucc := rfl

def endVertex {k : ℕ} (w : NonbacktrackingWalk G start (k + 1)) : V :=
  w.vertices (Fin.last (k + 1))

def beforeEndVertex {k : ℕ} (w : NonbacktrackingWalk G start (k + 1)) : V :=
  w.vertices (Fin.last k).castSucc

def Extension {k : ℕ} (w : NonbacktrackingWalk G start (k + 1)) :=
  {x : V // G.Adj w.endVertex x ∧ x ≠ w.beforeEndVertex}

instance extensionFinite {k : ℕ} (w : NonbacktrackingWalk G start (k + 1)) :
    Finite (Extension w) :=
  Finite.of_injective Subtype.val Subtype.val_injective

def previousNeighbor {k : ℕ} (w : NonbacktrackingWalk G start (k + 1)) :
    G.neighborSet w.endVertex := by
  refine ⟨w.beforeEndVertex, ?_⟩
  apply (G.mem_neighborSet _ _).mpr
  simpa [endVertex, beforeEndVertex] using (w.adjacent (Fin.last k)).symm

def extensionEquivLegalNeighbor {k : ℕ} (w : NonbacktrackingWalk G start (k + 1)) :
    Extension w ≃ {x : G.neighborSet w.endVertex // x ≠ w.previousNeighbor} where
  toFun x := ⟨⟨x.1, (G.mem_neighborSet _ _).mpr x.2.1⟩, by
    intro h
    exact x.2.2 (congrArg Subtype.val h)⟩
  invFun x := ⟨x.1.1, (G.mem_neighborSet _ _).mp x.1.2, by
    intro h
    apply x.2
    apply Subtype.ext
    exact h⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; apply Subtype.ext; rfl

theorem card_extension {d : ℕ} (hG : IsRegularOfDegree G d) {k : ℕ}
    (w : NonbacktrackingWalk G start (k + 1)) : Nat.card (Extension w) = d - 1 := by
  classical
  rw [Nat.card_congr (extensionEquivLegalNeighbor w)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl
    (fun x : G.neighborSet w.endVertex ↦ x = w.previousNeighbor)]
  have hn : Fintype.card (G.neighborSet w.endVertex) = d := by
    simpa only [Nat.card_eq_fintype_card] using hG w.endVertex
  rw [hn]
  simp

def appendVertices {k : ℕ} (w : NonbacktrackingWalk G start (k + 1))
    (x : Extension w) : Fin (k + 3) → V :=
  Fin.lastCases x.1 w.vertices

@[simp] theorem appendVertices_last {k : ℕ} (w : NonbacktrackingWalk G start (k + 1))
    (x : Extension w) :
    appendVertices w x (Fin.last (k + 2)) = x.1 :=
  Fin.lastCases_last

@[simp] theorem appendVertices_castSucc {k : ℕ}
    (w : NonbacktrackingWalk G start (k + 1)) (x : Extension w) (i : Fin (k + 2)) :
    appendVertices w x i.castSucc = w.vertices i :=
  Fin.lastCases_castSucc i

@[simp] theorem appendVertices_castSucc_succ {k : ℕ}
    (w : NonbacktrackingWalk G start (k + 1)) (x : Extension w) (i : Fin (k + 1)) :
    appendVertices w x i.castSucc.succ = w.vertices i.succ := by
  rw [show i.castSucc.succ = i.succ.castSucc by ext; rfl]
  exact appendVertices_castSucc w x i.succ

@[simp] theorem appendVertices_last_succ {k : ℕ}
    (w : NonbacktrackingWalk G start (k + 1)) (x : Extension w) :
    appendVertices w x (Fin.last (k + 1)).succ = x.1 := by
  rw [show (Fin.last (k + 1)).succ = Fin.last (k + 2) by ext; rfl]
  exact appendVertices_last w x

def append {k : ℕ} (w : NonbacktrackingWalk G start (k + 1))
    (x : Extension w) : NonbacktrackingWalk G start (k + 2) where
  vertices := appendVertices w x
  length_pos := by omega
  startsAtTail := by
    change appendVertices w x (0 : Fin (k + 3)) = start.tail
    rw [show (0 : Fin (k + 3)) = (0 : Fin (k + 2)).castSucc by ext; rfl,
      appendVertices_castSucc]
    exact w.startsAtTail
  startsAtHead := by
    change appendVertices w x (1 : Fin (k + 3)) = start.head
    rw [show (1 : Fin (k + 3)) = (1 : Fin (k + 2)).castSucc by ext; rfl,
      appendVertices_castSucc]
    exact w.startsAtHead
  adjacent i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [appendVertices_castSucc, appendVertices_last_succ, endVertex] using x.2.1
    · simpa only [appendVertices_castSucc, appendVertices_castSucc_succ] using w.adjacent j
  noBacktrack := by
    intro i hi
    let j : Fin (k + 3) := ⟨(i : ℕ) + 2, hi⟩
    have haux : ∀ a b : Fin (k + 3), (b : ℕ) = (a : ℕ) + 2 →
        appendVertices w x a ≠ appendVertices w x b := by
      intro a
      refine Fin.lastCases ?_ (fun a' ↦ ?_) a
      · intro b hab
        change (b : ℕ) = k + 2 + 2 at hab
        omega
      · intro b
        refine Fin.lastCases ?_ (fun b' ↦ ?_) b
        · intro hab
          have ha : a' = (Fin.last k).castSucc := by
            apply Fin.ext
            simp only [Fin.val_castSucc, Fin.val_last] at hab ⊢
            omega
          subst a'
          simpa [beforeEndVertex] using x.2.2.symm
        · intro hab
          have hbound : (a' : ℕ) + 2 < k + 2 := by
            simp only [Fin.val_castSucc] at hab
            omega
          have hb : b' = (⟨(a' : ℕ) + 2, hbound⟩ : Fin (k + 2)) := by
            apply Fin.ext
            simp only [Fin.val_castSucc] at hab
            exact hab
          rw [hb]
          simpa only [appendVertices_castSucc] using w.noBacktrack a' hbound
    exact haux i j rfl

def lastExtension {k : ℕ} (w : NonbacktrackingWalk G start (k + 2)) :
    Extension (w.dropLast : NonbacktrackingWalk G start (k + 1)) := by
  refine ⟨w.vertices (Fin.last (k + 2)), ?_, ?_⟩
  · simpa [endVertex] using w.adjacent (Fin.last (k + 1))
  · have h : w.vertices (Fin.last k).castSucc.castSucc ≠
        w.vertices (Fin.last (k + 2)) := by
      let i : Fin (k + 3) := (Fin.last k).castSucc.castSucc
      have hi : (i : ℕ) + 2 < k + 3 := by simp [i]
      let j : Fin (k + 3) := ⟨(i : ℕ) + 2, hi⟩
      have h0 := w.noBacktrack i hi
      have hind : j = Fin.last (k + 2) := by
        apply Fin.ext
        simp [j, i]
      change w.vertices i ≠ w.vertices j at h0
      rw [hind] at h0
      change w.vertices (Fin.last k).castSucc.castSucc ≠
        w.vertices (Fin.last (k + 2)) at h0
      exact h0
    change w.vertices (Fin.last (k + 2)) ≠
      w.vertices (Fin.last k).castSucc.castSucc
    exact h.symm

def split {k : ℕ} (w : NonbacktrackingWalk G start (k + 2)) :
    Σ p : NonbacktrackingWalk G start (k + 1), Extension p :=
  ⟨w.dropLast, w.lastExtension⟩

def appendEquiv (k : ℕ) :
    NonbacktrackingWalk G start (k + 2) ≃
      Σ p : NonbacktrackingWalk G start (k + 1), Extension p where
  toFun := split
  invFun p := p.1.append p.2
  left_inv w := by
    apply ext
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · change appendVertices w.dropLast w.lastExtension (Fin.last (k + 2)) = _
      rw [appendVertices_last]
      rfl
    · simp [split, append]
  right_inv p := by
    rcases p with ⟨w, x⟩
    have hw : (w.append x).dropLast = w := by
      apply ext
      funext i
      simp [append]
    apply Sigma.ext hw
    apply (Subtype.heq_iff_coe_eq (fun y ↦ by
      change (G.Adj (w.append x).dropLast.endVertex y ∧
          y ≠ (w.append x).dropLast.beforeEndVertex) ↔
        (G.Adj w.endVertex y ∧ y ≠ w.beforeEndVertex)
      rw [hw])).2
    simp [split, lastExtension, append]

def oneEquivUnit : NonbacktrackingWalk G start 1 ≃ Unit where
  toFun _ := ()
  invFun _ :=
    { vertices := Fin.cases start.tail (fun _ ↦ start.head)
      length_pos := by omega
      startsAtTail := rfl
      startsAtHead := rfl
      adjacent := by
        intro i
        fin_cases i
        exact start.adjacent
      noBacktrack := by intro i hi; omega }
  left_inv w := by
    apply ext
    funext i
    fin_cases i
    · exact w.startsAtTail.symm
    · exact w.startsAtHead.symm
  right_inv u := by cases u; rfl

theorem card_one : Nat.card (NonbacktrackingWalk G start 1) = 1 := by
  rw [Nat.card_congr oneEquivUnit]
  simp

theorem card_step {d : ℕ} (hG : IsRegularOfDegree G d) (k : ℕ) :
    Nat.card (NonbacktrackingWalk G start (k + 2)) =
      (d - 1) * Nat.card (NonbacktrackingWalk G start (k + 1)) := by
  classical
  let : Fintype (NonbacktrackingWalk G start (k + 1)) := Fintype.ofFinite _
  let : ∀ w : NonbacktrackingWalk G start (k + 1), Fintype (Extension w) :=
    fun _ ↦ Fintype.ofFinite _
  rw [Nat.card_congr (appendEquiv k), Nat.card_sigma]
  simp_rw [card_extension hG]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp [mul_comm]

theorem card_walks {d : ℕ} (hG : IsRegularOfDegree G d) (k : ℕ) (hk : 1 ≤ k) :
    Nat.card (NonbacktrackingWalk G start k) = (d - 1) ^ (k - 1) := by
  have aux : ∀ m : ℕ, Nat.card (NonbacktrackingWalk G start (m + 1)) = (d - 1) ^ m := by
    intro m
    induction m with
    | zero => simpa using (card_one (G := G) (start := start))
    | succ m ih =>
        change Nat.card (NonbacktrackingWalk G start (m + 2)) = (d - 1) ^ (m + 1)
        rw [card_step hG m, ih, pow_succ]
        ac_rfl
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [← hk']
  simpa using aux (k - 1)


end NonbacktrackingWalk

end

end NonbacktrackingWalks



namespace NonbacktrackingWalks

noncomputable section

variable {V : Type*} [Fintype V]

def walkCount (G : SimpleGraph V) (start : OrientedEdge G) (k : ℕ) : ℕ :=
  Nat.card (NonbacktrackingWalk G start k)

def simpleWalkCount (G : SimpleGraph V) (start : OrientedEdge G) (k : ℕ) : ℕ :=
  Nat.card (SimpleNonbacktrackingWalk G start k)

def simpleProbability (G : SimpleGraph V) (start : OrientedEdge G) (k : ℕ) : ℝ :=
  (simpleWalkCount G start k : ℝ) / (walkCount G start k : ℝ)

theorem natCard_rotationSystem (d : ℕ) [NeZero d] :
  Nat.card (RotationSystem d V) = (d - 1) ^ Fintype.card V := by
  rw [Nat.card_fun, natCard_offset, Nat.card_eq_fintype_card]

theorem card_goodOmega (d : ℕ) [NeZero d] (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) :
    Nat.card (GoodOmega d G hG start k) =
      simpleWalkCount G start k *
        (d - 1) ^ (Fintype.card V - (k - 1)) := by
  have h := card_goodOmega_succ d G hG (m := k - 1) start
  rw [Nat.sub_add_cancel hk] at h
  exact h

theorem card_walkCount (d : ℕ) (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) :
    walkCount G start k = (d - 1) ^ (k - 1) := by
  exact NonbacktrackingWalk.card_walks hG k hk

theorem card_rotationSystem_eq_free_mul_walkCount
    (d : ℕ) [NeZero d] (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    Nat.card (RotationSystem d V) =
      (d - 1) ^ (Fintype.card V - (k - 1)) * walkCount G start k := by
  rw [natCard_rotationSystem, card_walkCount d G hG start k hk]
  rw [← pow_add]
  congr 1
  omega

theorem simpleProbability_eq_goodRatio
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) (G : SimpleGraph V)
    (hG : IsRegularOfDegree G d) (start : OrientedEdge G)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k < Fintype.card V) :
    simpleProbability G start k =
      (Nat.card (GoodOmega d G hG start k) : ℝ) /
        (Nat.card (RotationSystem d V) : ℝ) := by
  let free : ℕ := (d - 1) ^ (Fintype.card V - (k - 1))
  have hfree : 0 < free := by
    dsimp [free]
    exact pow_pos (by omega) _
  have hwalk : 0 < walkCount G start k := by
    rw [card_walkCount d G hG start k hk]
    exact pow_pos (by omega) _
  rw [simpleProbability, card_goodOmega d G hG start k hk,
    card_rotationSystem_eq_free_mul_walkCount d G hG start k hk hkn]
  change (simpleWalkCount G start k : ℝ) / (walkCount G start k : ℝ) =
    ((simpleWalkCount G start k * free : ℕ) : ℝ) /
      ((free * walkCount G start k : ℕ) : ℝ)
  push_cast
  field_simp [show (free : ℝ) ≠ 0 by exact_mod_cast hfree.ne',
    show (walkCount G start k : ℝ) ≠ 0 by exact_mod_cast hwalk.ne']

end

end NonbacktrackingWalks



namespace GeneralFinalRatio

def cutoff (d n k : ℕ) : ℕ := 64 * d * n / k + 1

def K (d : ℕ) : ℕ := 1048576 * d ^ 2

theorem cutoff_mul_k_le (d n k : ℕ) (hkn : k < n) :
    cutoff d n k * k ≤ (64 * d + 1) * n := by
  have hdiv : (64 * d * n / k) * k ≤ 64 * d * n := Nat.div_mul_le_self _ _
  calc
    cutoff d n k * k = (64 * d * n / k) * k + k := by
      simp [cutoff]
      ring
    _ ≤ 64 * d * n + n := Nat.add_le_add hdiv hkn.le
    _ = (64 * d + 1) * n := by ring

/-- Final integral consequence of the generalized switching double count. -/
theorem final_card_bound
    (d n k good plans : ℕ) (hd : 3 ≤ d) (hkn : k < n)
    (hinc : (d - 2) * k * good ≤
      8 * (d - 1) * cutoff d n k * plans) :
    good * k ^ 2 ≤ K d * n * plans := by
  have hq : 1 ≤ d - 2 := by omega
  have hdrop : k * good ≤ (d - 2) * k * good := by
    calc
      k * good = 1 * (k * good) := by ring
      _ ≤ (d - 2) * (k * good) := Nat.mul_le_mul_right (k * good) hq
      _ = (d - 2) * k * good := by ring
  have hswitch : k * good ≤ 8 * (d - 1) * cutoff d n k * plans :=
    hdrop.trans hinc
  have hcut := cutoff_mul_k_le d n k hkn
  have hcoef : 8 * (d - 1) * (64 * d + 1) ≤ K d := by
    calc
      8 * (d - 1) * (64 * d + 1) ≤ 8 * d * (65 * d) := by
        gcongr <;> omega
      _ = 520 * d ^ 2 := by ring
      _ ≤ 1048576 * d ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K d := by rfl
  calc
    good * k ^ 2 = (k * good) * k := by ring
    _ ≤ (8 * (d - 1) * cutoff d n k * plans) * k :=
      Nat.mul_le_mul_right k hswitch
    _ = 8 * (d - 1) * (cutoff d n k * k) * plans := by ring
    _ ≤ 8 * (d - 1) * ((64 * d + 1) * n) * plans := by
      gcongr
    _ = (8 * (d - 1) * (64 * d + 1)) * n * plans := by ring
    _ ≤ K d * n * plans := by
      gcongr

/-- Cast the integral bound to the probability ratio. -/
theorem ratio_bound
    (d n k good plans : ℕ) (hk : 0 < k) (hplans : 0 < plans)
    (hcard : good * k ^ 2 ≤ K d * n * plans) :
    (good : ℝ) / (plans : ℝ) ≤
      (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < plans := by exact_mod_cast hplans
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply (div_le_iff₀ hp).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hk')).2
  exact_mod_cast hcard

/-- Surround a high-regime switching proof by the trivial probability-at-most-one bound. -/
theorem ratio_bound_of_high
    (d n k : ℕ) (p : ℝ) (hk : 0 < k) (hp_one : p ≤ 1)
    (hhigh : K d * n ≤ k ^ 2 →
      p ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2) :
    p ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 := by
  by_cases h : K d * n ≤ k ^ 2
  · exact hhigh h
  · calc
      p ≤ 1 := hp_one
      _ ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 := by
        have hnat : k ^ 2 ≤ K d * n := by omega
        have hk' : (0 : ℝ) < k := by exact_mod_cast hk
        apply (le_div_iff₀ (sq_pos_of_pos hk')).2
        norm_num
        exact_mod_cast hnat

/-- A convenient purely real conversion from the quantitative `K(d)n/k²`
bound to the existential square-root threshold in the paper. -/
theorem quantitative_to_epsilon (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ) (p : ℝ),
        p ≤ (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 →
        C * Real.sqrt (n : ℝ) < (k : ℝ) → p < ε := by
  let a : ℝ := (K d : ℝ) / ε
  let C : ℝ := a + 1
  have hKpos : (0 : ℝ) < K d := by
    simp [K]
    positivity
  have ha : 0 < a := div_pos hKpos hε
  have hC : 0 < C := by simp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n k p hp hthreshold
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hleft : 0 ≤ C * Real.sqrt (n : ℝ) := mul_nonneg hC.le hsqrt
  have hkreal : (0 : ℝ) < k := lt_of_le_of_lt hleft hthreshold
  have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsq : C ^ 2 * (n : ℝ) < (k : ℝ) ^ 2 := by
    have : (C * Real.sqrt (n : ℝ)) ^ 2 < (k : ℝ) ^ 2 := by
      nlinarith
    nlinarith [hsqrt_sq]
  have haC : a ≤ C ^ 2 := by
    dsimp [C]
    nlinarith
  have han : a * (n : ℝ) ≤ C ^ 2 * (n : ℝ) := by
    gcongr
  have hnum : (K d : ℝ) * (n : ℝ) < ε * (k : ℝ) ^ 2 := by
    have hmain : a * (n : ℝ) < (k : ℝ) ^ 2 := han.trans_lt hsq
    have haeq : ε * a = (K d : ℝ) := by
      dsimp [a]
      field_simp
    nlinarith
  have hquant : (K d : ℝ) * (n : ℝ) / (k : ℝ) ^ 2 < ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hkreal)).2
    nlinarith
  exact hp.trans_lt hquant

end GeneralFinalRatio



namespace TranslationOuter

open NonbacktrackingWalks GeneralFinalRatio

noncomputable section

universe u

/-! ## Elementary endpoint cases -/

theorem simpleWalkCount_le_walkCount
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (start : OrientedEdge G) (k : ℕ) :
    simpleWalkCount G start k ≤ walkCount G start k := by
  exact Nat.card_le_card_of_injective
    (fun w : SimpleNonbacktrackingWalk G start k ↦ w.1) Subtype.val_injective

theorem simpleWalkCount_eq_zero_of_card_le
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (start : OrientedEdge G) (k : ℕ) (hk : Fintype.card V ≤ k) :
    simpleWalkCount G start k = 0 := by
  rw [simpleWalkCount, Finite.card_eq_zero_iff]
  refine ⟨fun w ↦ ?_⟩
  have hcard := Nat.card_le_card_of_injective w.1.vertices w.2
  have : k + 1 ≤ Fintype.card V := by simpa using hcard
  omega

theorem simpleProbability_le_one
    {V : Type u} [Fintype V]
    (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
    (start : OrientedEdge G) (k : ℕ) (hk : 0 < k) :
    simpleProbability G start k ≤ 1 := by
  have hk1 : 1 ≤ k := hk
  have hwalkNat : 0 < walkCount G start k := by
    rw [card_walkCount d G hG start k hk1]
    exact pow_pos (by omega) _
  have hwalkReal : (0 : ℝ) < walkCount G start k := by
    exact_mod_cast hwalkNat
  rw [simpleProbability]
  apply (div_le_iff₀ hwalkReal).2
  norm_num
  exact_mod_cast simpleWalkCount_le_walkCount G start k

/-- The final integral estimate when the double count directly controls
`k * good`; this is the form supplied by the generalized eligible-set bound. -/
theorem final_card_bound_from_k
    (d n k good plans : ℕ) (hd : 3 ≤ d) (hkn : k < n)
    (hinc : k * good ≤
      8 * (d - 1) * cutoff d n k * plans) :
    good * k ^ 2 ≤ K d * n * plans := by
  have hcut := cutoff_mul_k_le d n k hkn
  have hcoef : 8 * (d - 1) * (64 * d + 1) ≤ K d := by
    calc
      8 * (d - 1) * (64 * d + 1) ≤ 8 * d * (65 * d) := by
        gcongr <;> omega
      _ = 520 * d ^ 2 := by ring
      _ ≤ 1048576 * d ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K d := by rfl
  calc
    good * k ^ 2 = (k * good) * k := by ring
    _ ≤ (8 * (d - 1) * cutoff d n k * plans) * k :=
      Nat.mul_le_mul_right k hinc
    _ = 8 * (d - 1) * (cutoff d n k * k) * plans := by ring
    _ ≤ 8 * (d - 1) * ((64 * d + 1) * n) * plans := by
      gcongr
    _ = (8 * (d - 1) * (64 * d + 1)) * n * plans := by ring
    _ ≤ K d * n * plans := by
      gcongr

/-! ## Quantitative outer bound -/

/--
The sole graph-specific input still needed by the outer argument.  It is the
high-regime conclusion of the switching double count, in exactly the form
consumed by `GeneralFinalRatio.final_card_bound`.
-/
def HighGoodPlanCardBound (d : ℕ) (hd : 3 ≤ d) : Prop :=
  letI : NeZero d := ⟨by omega⟩
  ∀ {V : Type u} [Fintype V]
      (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
      (k : ℕ) (start : OrientedEdge G),
    0 < k →
    k < Fintype.card V →
    K d * Fintype.card V ≤ k ^ 2 →
    k * Nat.card (GoodOmega d G hG start k) ≤
      8 * (d - 1) * cutoff d (Fintype.card V) k *
        Nat.card (RotationSystem d V)

/--
The switching estimate implies the uniform quantitative probability bound.
This theorem includes the pigeonhole case `card V ≤ k` and the low/high
regime split.
-/
theorem quantitative_bound_of_high_good_plan_card_bound
    (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (hcard :
      ∀ {V : Type u} [Fintype V]
          (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
          (k : ℕ) (start : OrientedEdge G),
        0 < k →
        k < Fintype.card V →
        K d * Fintype.card V ≤ k ^ 2 →
        k * Nat.card (GoodOmega d G hG start k) ≤
          8 * (d - 1) * cutoff d (Fintype.card V) k *
            Nat.card (RotationSystem d V)) :
    ∀ {V : Type u} [Fintype V]
        (G : SimpleGraph V), IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G), 0 < k →
          simpleProbability G start k ≤
            (K d : ℝ) * (Fintype.card V : ℝ) / (k : ℝ) ^ 2 := by
  intro V instV G hG k start hk
  by_cases hnk : Fintype.card V ≤ k
  · have hsimple := simpleWalkCount_eq_zero_of_card_le G start k hnk
    rw [simpleProbability, hsimple]
    norm_num
    positivity
  · have hkn : k < Fintype.card V := Nat.lt_of_not_ge hnk
    rw [simpleProbability_eq_goodRatio d hd G hG start k hk hkn]
    apply ratio_bound_of_high d (Fintype.card V) k _ hk
    · rw [← simpleProbability_eq_goodRatio d hd G hG start k hk hkn]
      exact simpleProbability_le_one d hd G hG start k hk
    · intro hhigh
      have hplans : 0 < Nat.card (RotationSystem d V) := by
        rw [natCard_rotationSystem]
        exact pow_pos (by omega) _
      apply ratio_bound d (Fintype.card V) k
        (Nat.card (GoodOmega d G hG start k))
        (Nat.card (RotationSystem d V)) hk hplans
      apply final_card_bound_from_k d (Fintype.card V) k
        (Nat.card (GoodOmega d G hG start k))
        (Nat.card (RotationSystem d V)) hd hkn
      exact hcard G hG k start hk hkn hhigh

/-! ## Exact paper quantifiers -/

/--
The exact quantifier statement of `birthday_paradox`, conditional only on the
high-regime switching-cardinality lemma above.
-/
theorem birthday_paradox_of_high_good_plan_card_bound
    (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (hcard :
      ∀ {V : Type u} [Fintype V]
          (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
          (k : ℕ) (start : OrientedEdge G),
        0 < k →
        k < Fintype.card V →
        K d * Fintype.card V ≤ k ^ 2 →
        k * Nat.card (GoodOmega d G hG start k) ≤
          8 * (d - 1) * cutoff d (Fintype.card V) k *
            Nat.card (RotationSystem d V))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G),
          C * Real.sqrt (Fintype.card V : ℝ) < (k : ℝ) →
            simpleProbability G start k < ε := by
  have hquant :
      ∀ {V : Type u} [Fintype V]
          (G : SimpleGraph V), IsRegularOfDegree G d →
          ∀ (k : ℕ) (start : OrientedEdge G), 0 < k →
            simpleProbability G start k ≤
              (K d : ℝ) * (Fintype.card V : ℝ) / (k : ℝ) ^ 2 := by
    exact quantitative_bound_of_high_good_plan_card_bound d hd hcard
  obtain ⟨C, hC, hconvert⟩ := quantitative_to_epsilon d hd ε hε
  refine ⟨C, hC, ?_⟩
  intro V instV G hG k start hthreshold
  exact hconvert (Fintype.card V) k (simpleProbability G start k)
    (hquant G hG k start (by
      have hsqrt : 0 ≤ Real.sqrt (Fintype.card V : ℝ) := Real.sqrt_nonneg _
      have hkreal : (0 : ℝ) < k :=
        lt_of_le_of_lt (mul_nonneg hC.le hsqrt) hthreshold
      exact_mod_cast hkreal))
    hthreshold

end

end TranslationOuter



namespace NonbacktrackingWalks

theorem birthday_paradox
    (d : ℕ) (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
        IsRegularOfDegree G d →
        ∀ (k : ℕ) (start : OrientedEdge G),
          C * Real.sqrt (Fintype.card V : ℝ) < (k : ℝ) →
            simpleProbability G start k < ε := by
  letI : NeZero d := ⟨by omega⟩
  refine TranslationOuter.birthday_paradox_of_high_good_plan_card_bound d hd
    ?_ ε hε
  intro V instV G hG k start _hk hkn hhigh
  have hswitch := TranslationCollisionSwitching.high_switching_card_bound
    (d := d) G hG start k hd hhigh hkn
  simpa only [degreeCutoff, GeneralFinalRatio.cutoff, mul_comm, mul_left_comm,
    mul_assoc] using hswitch

end NonbacktrackingWalks


