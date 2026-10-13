import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.List.Rotate
import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.Basic

/-!
# Finite orientable triangulated surfaces: parameterized polygon normal form

Source: Gallier–Xu, *A Guide to the Classification Theorem for Compact Surfaces*,
author version 8 January 2025, Definitions 6.2–6.3, pp.81–86, Lemma 6.1, pp.92–95,
and Theorem 6.1, p.96; prescribed-boundary realization, Proposition 3.2, p.31,
and Note F.4, p.167. The source composite also uses Seifert–Threlfall (1980),
§§37–38, pp.138–140, and Lee (2011), Proposition 6.14, p.173, and p.175.

The words, incoming corners, elementary subdivisions, and interval-parameter disk
quotients below are concrete data. No classification, polygon-word oracle, or
surface homeomorphism is an input. Abstract simplicial complexes and standard
barycentric simplices are Mathlib's notions. All quotients carry quotient topology.
-/

noncomputable section

open Set Topology _root_.Topology
open scoped BigOperators Classical

namespace HolomorphicAnosov.Topology.GallierXu

/-- A signed occurrence of an unoriented edge label (GX Definition 6.1, pp.79–81). -/
abbrev Dart := ℕ × Bool

/-- Reverse the interval direction of an edge occurrence (GX Definition 6.1). -/
def inverse (a : Dart) : Dart := (a.1, !a.2)

/-- A face boundary retains every occurrence and its cyclic order (GX Definition 6.1). -/
abbrev Word := List Dart

/-- A finite family of face instances; equal boundary words still denote distinct faces. -/
abbrev Presentation := List Word

/-- All signed occurrences, including their multiplicities (GX Definition 6.1). -/
def occurrences (P : Presentation) : List Dart := P.flatten

/-- Labels actually used in a presentation (GX Definition 6.1). -/
def labels (P : Presentation) : Finset ℕ := ((occurrences P).map Prod.fst).toFinset

/-- Coherently oriented finite edge incidences: once unpaired, or twice with opposite signs. This is
the oriented part of GX Definition 6.1 and the invariant on pp.87–89. -/
def Oriented (P : Presentation) : Prop :=
  (∀ w ∈ P, w ≠ []) ∧ ∀ a ∈ labels P,
    ((occurrences P).count (a, true) = 1 ∧ (occurrences P).count (a, false) = 0) ∨
    ((occurrences P).count (a, true) = 0 ∧ (occurrences P).count (a, false) = 1) ∨
    ((occurrences P).count (a, true) = 1 ∧ (occurrences P).count (a, false) = 1)

/-- Incoming corner relation `u ~ inverse v` for consecutive boundary occurrences. GX Definition
6.2, pp.81–83; the wraparound corner is included. -/
def corner (P : Presentation) (a b : Dart) : Prop :=
  ∃ f : Fin P.length, ∃ i : Fin (P.get f).length,
    (P.get f).get i = a ∧
      inverse ((P.get f).get (finRotate (P.get f).length i)) = b

/-- The full incoming vertex class, not just the displayed pair (GX p.83). -/
def sameVertex (P : Presentation) : Dart → Dart → Prop := Relation.EqvGen (corner P)

/-- One edge subdivision applied to ALL paired occurrences with the reversed order on inverses. GX
Definition 6.3(P1), p.84, and ST §37, p.138. -/
def subdivideEdge (P : Presentation) (a b c : ℕ) : Presentation :=
  P.map fun w ↦ w.flatMap fun d ↦
    if d.1 = a then
      if d.2 then [(b, true), (c, true)] else [(c, false), (b, false)]
    else [d]

/-- Face enumerations and cyclic starting positions, with every edge name retained. These are
coordinate changes, not subdivisions (GX Definitions 6.1–6.3). -/
def Reindexed (P Q : Presentation) : Prop :=
  ∃ f : Fin P.length ≃ Fin Q.length, ∀ i, List.IsRotated (P.get i) (Q.get (f i))

/-- Genuine P1/P2 subdivisions and their inverses, with harmless face coordinate changes. The
inverse constructor remembers the ENTIRE forward presentation and its freshness guards. -/
inductive Elementary : Presentation → Presentation → Type
  | edge (P : Presentation) (a b c : ℕ)
      (ha : a ∈ labels P) (hb : b ∉ labels P) (hc : c ∉ labels P) (hbc : b ≠ c) :
      Elementary P (subdivideEdge P a b c)
  | face (L R : Presentation) (U V : Word) (d : ℕ)
      (hU : U ≠ []) (hV : V ≠ []) (hd : d ∉ labels (L ++ [U ++ V] ++ R)) :
      Elementary (L ++ [U ++ V] ++ R)
        (L ++ [U ++ [(d, true)], (d, false) :: V] ++ R)
  | inverse {P Q} (h : Elementary P Q) : Elementary Q P
  | reindex {P Q} (h : Reindexed P Q) : Elementary P Q
  | rename {P Q} (e : ℕ ≃ ℕ) (flip : ℕ → Bool) (f : Fin P.length ≃ Fin Q.length)
      (h : ∀ i, List.IsRotated
        ((P.get i).map fun a ↦ (e a.1, if flip a.1 then !a.2 else a.2)) (Q.get (f i))) :
      Elementary P Q

/-- Exact surviving interval parameters for elementary operations. P1 uses the two half intervals;
P2 and face coordinate changes retain every old parameter. ST §37 p.138 and GX Definition 6.3. -/
def Elementary.parameters {P Q} : Elementary P Q → ℕ → ℝ → ℕ → ℝ → Prop
  | .edge _ a b c _ _ _ _, e, t, f, s =>
      (e ≠ a ∧ f = e ∧ s = t) ∨
      (e = a ∧ f = b ∧ t ≤ 1 / 2 ∧ s = 2 * t) ∨
      (e = a ∧ f = c ∧ 1 / 2 ≤ t ∧ s = 2 * t - 1)
  | .face .., e, t, f, s => e = f ∧ t = s
  | .inverse h, e, t, f, s => h.parameters f s e t
  | .reindex _, e, t, f, s => e = f ∧ t = s
  | .rename e flip _ _, a, t, b, s => e a = b ∧ s = if flip a then 1 - t else t

/-- Round parameter disk, with its usual Euclidean subtype topology (GX p.31/F.4 p.167). -/
abbrev Disk := Metric.closedBall (0 : ℂ) 1

/-- Disjoint coproduct of the original face instances (GX pp.79–81; Lee p.173). -/
abbrev FaceDisks (P : Presentation) := Fin P.length × Disk

/-- Position on a face's circular boundary at the SAME normalized unoriented edge parameter.
Positive occurrences run forward and negative occurrences run backward. GX pp.79–81, ST §37. -/
def sidePoint (P : Presentation) (f : Fin P.length) (i : Fin (P.get f).length)
    (t : ℝ) : ℂ :=
  Circle.exp (2 * Real.pi *
    ((i.val : ℝ) + if ((P.get f).get i).2 then t else 1 - t) / (P.get f).length)

/-- Literal equal-label interval identifications, with endpoints INCLUDED. The orientation is
already carried by `sidePoint`; both occurrences use the same t. -/
def edgeIdentification (P : Presentation) (x y : FaceDisks P) : Prop :=
  ∃ i : Fin (P.get x.1).length, ∃ j : Fin (P.get y.1).length, ∃ t ∈ Icc (0 : ℝ) 1,
    ((P.get x.1).get i).1 = ((P.get y.1).get j).1 ∧
    (x.2 : ℂ) = sidePoint P x.1 i t ∧ (y.2 : ℂ) = sidePoint P y.1 j t

/-- Actual generated-edge disk quotient; no Hausdorffness or classification is built in. GX
Definition 6.1, Lee Proposition 6.14. -/
abbrev Realization (P : Presentation) := Quotient (Relation.EqvGen.setoid (edgeIdentification P))

/-- Quotient projection from the disjoint face disks (GX Definition 6.1). -/
def project (P : Presentation) : FaceDisks P → Realization P := Quotient.mk _

/-- Image of the SAME parameterized labeled edge in the quotient (GX Definition 6.1). -/
def edgeImage (P : Presentation) (a : ℕ) : Set (Realization P) :=
  {q | ∃ x : FaceDisks P, ∃ i : Fin (P.get x.1).length, ∃ t ∈ Icc (0 : ℝ) 1,
    ((P.get x.1).get i).1 = a ∧ (x.2 : ℂ) = sidePoint P x.1 i t ∧ project P x = q}

/-- The homeomorphism of an elementary operation respects its EXACT interval correspondence. This is
a conclusion witness, never an assumed input of the classification theorem. GX prescribed-boundary
realization p.31/F.4 p.167; ST §37. -/
def RespectsParameters {P Q} (h : Elementary P Q)
    (H : Realization P ≃ₜ Realization Q) : Prop :=
  ∀ (x : FaceDisks P) (y : FaceDisks Q)
    (i : Fin (P.get x.1).length) (j : Fin (Q.get y.1).length)
    (t s : ℝ), t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
    h.parameters ((P.get x.1).get i).1 t ((Q.get y.1).get j).1 s →
    (x.2 : ℂ) = sidePoint P x.1 i t → (y.2 : ℂ) = sidePoint Q y.1 j s →
    H (project P x) = project Q y

/-- A finite sequence of realized elementary subdivisions/inverses, with each parameter bound.
Harmless cyclic starting positions and face enumerations do not add geometric operations. -/
inductive RealizedSequence : Presentation → Presentation → Type
  | nil (P) : RealizedSequence P P
  | cons {P Q R} (h : Elementary P Q) (H : Realization P ≃ₜ Realization Q)
      (hH : RespectsParameters h H) (tail : RealizedSequence Q R) : RealizedSequence P R

/-- The homeomorphism INDUCED by composing the finite elementary sequence. -/
def RealizedSequence.homeomorph {P Q} : RealizedSequence P Q → Realization P ≃ₜ Realization Q
  | .nil _ => Homeomorph.refl _
  | .cons _ H _ tail => H.trans tail.homeomorph

/-- Nonnegative genus canonical word, with distinct handle, spoke and boundary labels. GX pp.88–90
and Lemma 6.1 Step 6, p.95. -/
def normalWord (g b : ℕ) : Word :=
  ((List.range g).flatMap fun i ↦
    [(2 * i, true), (2 * i + 1, true), (2 * i, false), (2 * i + 1, false)]) ++
  ((List.range b).flatMap fun j ↦
    [(2 * g + 2 * j, true), (2 * g + 2 * j + 1, true), (2 * g + 2 * j, false)])

/-- Cardinality-d simplices of the GIVEN finite abstract complex, including their instances. GX
finite polyhedra, Chapters 2 and 6; Mathlib's abstract complex notion is reused. -/
def simplices {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) (d : ℕ) :
    Finset (Finset (Fin N)) := Finset.univ.filter fun s ↦ s ∈ K.faces ∧ s.card = d + 1

/-- Standard finite-vertex barycentric realization, as in the source comparison with Lee p.173. The
standard simplex is Mathlib's; membership retains the support in an ORIGINAL face. -/
def carrier {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) : Set (Fin N → ℝ) :=
  {x | x ∈ {f : Fin N → ℝ | (∀ v, 0 ≤ f v) ∧ ∑ v, f v = 1} ∧ ∃ s ∈ K.faces, ∀ v ∉ s, x v = 0}

/-- Original finite triangles, before any quotient or subdivision (GX Chapter 6). -/
abbrev Triangle {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) :=
  {s : Finset (Fin N) // s ∈ K.faces ∧ s.card = 3}

/-- Literal unoriented edge label, using the two distinct original vertex indices. The natural
pairing is injective, so distinct original edges have distinct labels. -/
def edgeLabel {N : ℕ} (u v : Fin N) : ℕ := Nat.pair (min u.val v.val) (max u.val v.val)

/-- Directed original edge, relative to the increasing vertex orientation (GX p.84). -/
def edgeDart {N : ℕ} (u v : Fin N) : Dart := (edgeLabel u v, decide (u < v))

/-- Triangle boundary obtained from the GIVEN cyclic ordering of its three actual vertices. -/
def triangleWord {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) : Word :=
  (List.finRange 3).map fun i ↦ edgeDart (o i).val (o (finRotate 3 i)).val

/-- Original triangle cell complex, with every original triangle exactly once (GX p.84). An
orientation is a choice of cyclic ordering, not a polygon-word oracle. -/
def trianglePresentation {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val) : Presentation :=
  (simplices K 2).attach.toList.map fun s ↦
    let t : Triangle K := ⟨s.val, by simpa [simplices] using s.property⟩
    triangleWord t (o t)

/-- Every original face is contained in an original triangle: pure dimension two. GX compact
two-dimensional polyhedra; the empty-complex case is excluded by connectedness/b≥1. -/
def PureTwo {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) : Prop :=
  ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t

/-- Number of original triangles incident to the original edge e. -/
def incidence {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) (e : Finset (Fin N)) : ℕ :=
  ((simplices K 2).filter fun t ↦ e ⊆ t).card

/-- Original boundary edges: precisely the edges with one incident triangle. -/
def boundaryEdge {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) (u v : Fin N) : Prop :=
  u ≠ v ∧ ({u, v} : Finset (Fin N)) ∈ K.faces ∧ incidence K {u, v} = 1

/-- Original simplicial vertex-link adjacency, with no geometric link or manifold premise. -/
def linkEdge {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) (v a b : Fin N) : Prop :=
  a ≠ b ∧ a ≠ v ∧ b ≠ v ∧ ({v, a, b} : Finset (Fin N)) ∈ K.faces

/-- Edges in a finite simple cyclic vertex list; the last-first edge is retained. -/
def cycleEdge {N : ℕ} (l : List (Fin N)) (a b : Fin N) : Prop :=
  ∃ i : Fin l.length, (l.get i = a ∧ l.get (finRotate l.length i) = b) ∨
    (l.get i = b ∧ l.get (finRotate l.length i) = a)

/-- Edges in a finite simple interval vertex list, with no last-first edge. -/
def pathEdge {N : ℕ} (l : List (Fin N)) (a b : Fin N) : Prop :=
  ∃ i : ℕ, ∃ hi : i + 1 < l.length,
    (l.get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ = a ∧ l.get ⟨i + 1, hi⟩ = b) ∨
    (l.get ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩ = b ∧ l.get ⟨i + 1, hi⟩ = a)

/-- The GIVEN vertex link is an exact simplicial circle or interval, including all its vertices. GX
starting finite surface hypothesis; these finite fans are used in the Lee comparison. -/
def SurfaceLinks {N : ℕ} (K : AbstractSimplicialComplex (Fin N)) : Prop :=
  ∀ v : Fin N, ∃ l : List (Fin N), l.Nodup ∧
    (∀ a, a ∈ l ↔ a ≠ v ∧ ({v, a} : Finset (Fin N)) ∈ K.faces) ∧
    ((3 ≤ l.length ∧ ∀ a b, linkEdge K v a b ↔ cycleEdge l a b) ∨
      (2 ≤ l.length ∧ ∀ a b, linkEdge K v a b ↔ pathEdge l a b))

/-- The GIVEN b disjoint boundary cycles, with exactly all the one-triangle edges. They enumerate
boundary components rather than supplying a classification of the surface. -/
def BoundaryCycles {N b : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (B : Fin b → List (Fin N)) : Prop :=
  (∀ j, (B j).Nodup ∧ 3 ≤ (B j).length) ∧
  (∀ i j, i ≠ j → Disjoint (B i).toFinset (B j).toFinset) ∧
  (∀ u v, boundaryEdge K u v ↔ ∃ j, cycleEdge (B j) u v)

/-- Realization of an original boundary cycle inside the original barycentric realization. This is
the union of its actual straight edges, not an abstract substitute circle. -/
def cycleCarrier {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (l : List (Fin N)) : Set ↥(carrier K) :=
  {x | ∃ u v, cycleEdge l u v ∧
    (x : Fin N → ℝ) ∈ segment ℝ (Pi.single u 1) (Pi.single v 1)}

/-- The original edge parameter in standard vertex coordinates, always increasing in the original
vertex indices (GX p.84, Lee p.173, ST §37 p.138). -/
def originalEdgePoint {N : ℕ} (u v : Fin N) (t : ℝ) : Fin N → ℝ :=
  (1 - t) • Pi.single (min u v) 1 + t • Pi.single (max u v) 1

/-- The initial triangle-to-disk quotient comparison respects every original edge parameter. It is
constructed in the theorem's conclusion, not assumed as a surface-classification premise. -/
def OriginalParameters {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (H : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o)) : Prop :=
  ∀ (x : ↥(carrier K)) (y : FaceDisks (trianglePresentation K o))
    (i : Fin ((trianglePresentation K o).get y.1).length) (u v : Fin N) (t : ℝ),
    u ≠ v → t ∈ Icc (0 : ℝ) 1 →
    (x : Fin N → ℝ) = originalEdgePoint u v t →
    (((trianglePresentation K o).get y.1).get i).1 = edgeLabel u v →
    (y.2 : ℂ) = sidePoint (trianglePresentation K o) y.1 i t →
    H x = project (trianglePresentation K o) y

/-- Concatenate two finite realized move sequences, retaining each interval certificate.
Source: the finite sequences of Gallier–Xu Definition 6.3, pp.84–86. -/
def RealizedSequence.trans {P Q R : Presentation}
    (s : RealizedSequence P Q) (t : RealizedSequence Q R) : RealizedSequence P R :=
  match s with
  | .nil _ => t
  | .cons h H hH tail => .cons h H hH (tail.trans t)

/-- The homeomorphism of concatenated moves is the composite of their homeomorphisms.
This is the recursive definition of the realized sequence, GX Definition 6.3. -/
@[simp] theorem RealizedSequence.trans_homeomorph_apply {P Q R : Presentation}
    (s : RealizedSequence P Q) (t : RealizedSequence Q R) (x : Realization P) :
    (s.trans t).homeomorph x = t.homeomorph (s.homeomorph x) := by
  induction s with
  | nil P => rfl
  | cons h H hH tail ih => exact ih t (H x)

end HolomorphicAnosov.Topology.GallierXu
