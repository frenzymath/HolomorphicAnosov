import HolomorphicAnosov.Topology.ConnectedCWOneSkeletonFiniteWalk
import Mathlib.Topology.CWComplex.Classical.Graph
import Mathlib.Combinatorics.Graph.Delete

/-!
# Rooted spanning trees using original CW cell labels

DAG node: `topo.cw_realization_spanning_tree_g8`.
Source: Hatcher, *Algebraic Topology*, Proposition 1A.1, printed p. 84.
The connected-CW finite-walk prerequisite follows Appendix Propositions A.4
(pp. 522–523) and A.1 (p. 520), and relative Cellular Approximation Theorem 4.8
and Lemma 4.10 (pp. 349–351). Local source: `literature/hatcher-at.txt`.

The graph is Mathlib's actual CW one-skeleton multigraph. Vertices and edges
are the original zero- and one-cell indices, not adjacency classes. The finite
arrays below therefore retain loops and distinct parallel edge labels.
-/

namespace HolomorphicAnosov

open _root_.Topology

/-- A finite walk in the original edge-labelled multigraph, of a specified length
and with specified endpoints. Source: the finite walks in Hatcher's rooted
layer construction, Proposition 1A.1 p. 84, expanded in the present DAG node.
There is no simplicity requirement: repeated vertices, repeated edges, loops,
and parallel edges are allowed. At length zero the endpoint fields force u = v.
-/
structure CWEdgeWalk {V E : Type*} (G : Graph V E) (n : ℕ) (u v : V) where
  vertices : Fin (n + 1) → V
  edges : Fin n → E
  first : vertices 0 = u
  last : vertices (Fin.last n) = v
  isLink : ∀ i : Fin n, G.IsLink (edges i) (vertices i.castSucc) (vertices i.succ)

namespace CWEdgeWalk

variable {V E : Type*} {G : Graph V E} {n : ℕ} {u v w : V}

/-- The empty original-edge walk. -/
def nil (G : Graph V E) (u : V) : CWEdgeWalk G 0 u u where
  vertices := fun _ ↦ u
  edges := Fin.elim0
  first := rfl
  last := rfl
  isLink := fun i ↦ Fin.elim0 i

/-- Append one original edge, retaining all earlier array entries. -/
def snoc (p : CWEdgeWalk G n u v) (e : E) (h : G.IsLink e v w) :
    CWEdgeWalk G (n + 1) u w where
  vertices := Fin.snoc p.vertices w
  edges := Fin.snoc p.edges e
  first := by simpa using p.first
  last := by simp
  isLink := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [p.last] using h
    · rw [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact p.isLink j

/-- Prepend one original edge. -/
def cons (e : E) (h : G.IsLink e u v) (p : CWEdgeWalk G n v w) :
    CWEdgeWalk G (n + 1) u w where
  vertices := Fin.cons u p.vertices
  edges := Fin.cons e p.edges
  first := by simp
  last := by
    have hlast : Fin.last (n + 1) = (Fin.last n).succ := rfl
    rw [hlast, Fin.cons_succ]
    exact p.last
  isLink := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa [p.first] using h
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
      exact p.isLink j

/-- Drop the final edge of a nonempty walk. -/
def init (p : CWEdgeWalk G (n + 1) u v) :
    CWEdgeWalk G n u (p.vertices (Fin.last n).castSucc) where
  vertices := fun i ↦ p.vertices i.castSucc
  edges := fun i ↦ p.edges i.castSucc
  first := p.first
  last := rfl
  isLink := fun i ↦ by simpa only [Fin.castSucc_succ] using p.isLink i.castSucc

/-- Change only the length index, using a proved equality. -/
def cast {m : ℕ} (h : n = m) (p : CWEdgeWalk G n u v) : CWEdgeWalk G m u v :=
  h ▸ p

@[simp] theorem cast_rfl (p : CWEdgeWalk G n u v) : p.cast rfl = p := rfl

@[simp] theorem cast_vertices {m : ℕ} (h : n = m) (p : CWEdgeWalk G n u v)
    (i : Fin (n + 1)) :
    (p.cast h).vertices (Fin.cast (congrArg (· + 1) h) i) = p.vertices i := by
  subst m; rfl

@[simp] theorem cast_edges {m : ℕ} (h : n = m) (p : CWEdgeWalk G n u v)
    (i : Fin n) : (p.cast h).edges (Fin.cast h i) = p.edges i := by
  subst m; rfl

theorem cast_injective_vertices {m : ℕ} (p : CWEdgeWalk G n u v) (h : n = m)
    (hp : Function.Injective p.vertices) : Function.Injective (p.cast h).vertices := by
  subst m
  exact hp

/-- Restricting a walk's vertices does not change its original edge labels. -/
def mono {H : Graph V E} (h : G ≤ H) (p : CWEdgeWalk G n u v) :
    CWEdgeWalk H n u v where
  vertices := p.vertices
  edges := p.edges
  first := p.first
  last := p.last
  isLink := fun i ↦ h.isLink_mono (p.isLink i)

/-- Array equality gives equality of walks; all other fields are proofs. -/
@[ext] theorem ext {p q : CWEdgeWalk G n u v}
    (hv : p.vertices = q.vertices) (he : p.edges = q.edges) : p = q := by
  cases p; cases q; cases hv; cases he; rfl

/-- A walk of length zero has equal endpoints. -/
theorem eq_of_zero (p : CWEdgeWalk G 0 u v) : u = v := by
  have h : (Fin.last 0 : Fin 1) = 0 := rfl
  exact p.first.symm.trans (h ▸ p.last)

/-- Reverse a finite original-edge walk, using only link symmetry. -/
theorem exists_reverse (p : CWEdgeWalk G n u v) : ∃ m, Nonempty (CWEdgeWalk G m v u) := by
  induction n generalizing u v with
  | zero =>
    have h := p.eq_of_zero
    subst v
    exact ⟨0, ⟨nil G u⟩⟩
  | succ n ih =>
    obtain ⟨m, ⟨q⟩⟩ := ih p.init
    have hl := p.isLink (Fin.last n)
    rw [Fin.succ_last, p.last] at hl
    exact ⟨m + 1, ⟨cons _ hl.symm q⟩⟩

/-- Concatenate finite walks without changing any original edge label. -/
theorem exists_trans {m : ℕ} (p : CWEdgeWalk G n u v) (q : CWEdgeWalk G m v w) :
    ∃ k, Nonempty (CWEdgeWalk G k u w) := by
  induction m generalizing w with
  | zero =>
    have h := q.eq_of_zero
    subst w
    exact ⟨n, ⟨p⟩⟩
  | succ m ih =>
    obtain ⟨k, ⟨t⟩⟩ := ih q.init
    have hl := q.isLink (Fin.last m)
    rw [Fin.succ_last, q.last] at hl
    exact ⟨k + 1, ⟨t.snoc _ hl⟩⟩

end CWEdgeWalk

/-- Hatcher's rooted edge-layer construction, stated with minimal depths,
original edge arrays, loop/parallel-safe cycles, and the actual CW subcomplex.

Source: Hatcher, *Algebraic Topology*, Proposition 1A.1, printed p. 84.
Finite original-edge reachability uses the named connected-CW finite-walk
prerequisite and its published A.4 / relative 4.8 / A.1 source route.

A simple root path has an injective full vertex array. The cycle prohibition
uses distinct original edges and distinct vertices before the final return,
so it also excludes one-edge loops and two-edge parallel cycles. Equality of
root walks is expressed by `HEq` only to compare their length-indexed arrays;
the preceding length equality makes it ordinary equality after reindexing.
The recursive equations explicitly identify the full parent prefix and last
edge, using only `Fin.cast` for the proved parent-depth equality.

No finite, countable, locally finite, regular, or one-dimensional assumption
on the ambient CW complex is imposed. Higher cells remain in the ambient
complex and are not selected by the resulting subcomplex.

Source proof, expanded in the current DAG node:

1. Set G=CWComplex.OneSkeletonGraph Set.univ with the original vertex type V and edge type E. The
chosen root r supplies a point of K by the zero-cell singleton law, so the connected Hausdorff K
satisfies the finite-walk bridge’s nonemptiness hypothesis. For r and every v use
topo.connected_cw_one_skeleton_finite_walk_g8 to obtain actual finite arrays of original vertices
and edge indices, preserving loops and parallel edges. Its now-complete published source route
first makes K path connected by A.4 pp.522–523, cellularizes an interval path relative its zero-
cell endpoints by4.8 pp.349–351 into the original one-skeleton, puts that compact path image in a
finite original subcomplex by A.1 p.520, then uses1A.1 p.84 edge layers to extract finite labelled
walks. Finite edge support suffices; finite numbers of continuous edge crossings are not asserted.
The rooted shortest-layer construction in the remaining steps uses these exact walks.

2. For each v let L(v)⊆Nat be the set of lengths of explicit finite G-walks from r to v. L(v) is
nonempty by the finite-walk child. Well-ordering of Nat gives d(v)=min L(v), attained by a walk.
The empty root walk gives d(r)=0, and any length-zero walk has equal endpoints, so d(v)=0 iff v=r.
Appending any incident edge to an attained root walk proves d(v)≤d(u)+1 whenever G links u to v.
In Hatcher’s construction, the vertices reached after i adjoining-edge stages are exactly those
with d(v)≤i: induction on i gives both directions by appending or removing the final edge. No
finiteness of V or E is used.

3. For v≠r choose a shortest walk of length d(v). Its final edge has a penultimate vertex p and
links p to v. The prefix gives d(p)≤d(v)−1, while a strict inequality would yield a shorter walk
to v after appending the same final edge; hence d(p)+1=d(v). Classical choice selects parent(v)=p
and edge(v) equal to that original final edge. The root has no selected edge.

4. Let S=range edge and H=G.restrict S. Unfold the restriction to retain all original vertices,
selected original edge indices, and links e∈S∧G.IsLink e u v. Each selected edge joins a deeper
chosen child v to its parent at depth d(v)−1, so is not a loop. If edge(v)=edge(w), endpoint-pair
uniqueness gives either v=w with equal parents or v=parent(w) and w=parent(v); the swapped case
implies both d(v)=d(w)−1 and d(w)=d(v)−1, an impossibility. Thus edge is injective. Moreover any
selected edge linking x to a shallower y is edge(v) for some chosen v; endpoint-pair uniqueness
and the depth inequalities force v=x and parent(v)=y. Hence every nonroot x has exactly one
selected edge to lower depth, namely its own parent edge. Two selected parallel labels would have
the same deeper child and therefore both equal that edge; all other ambient labels are retained as
distinct elements of E.

5. By induction on d(v), construct R(v) as explicit arrays: for v=r use length0 and vertex r; for
v≠r append the original edge(v) and terminal vertex v to R(parent(v)). The parent-depth equation
makes the recursion decrease. The resulting successive vertex depths are 0,1,…,d(v), so R(v) is
vertex-simple and has length d(v), with every edge selected. Reverse R(u) using link symmetry and
concatenate it with R(v), identifying only the common root array position; this gives a finite
H-walk from u to v. Since H keeps V=univ and r∈V, every vertex is present and the graph is
nonempty.

6. To exclude a cycle in H, retain its explicit finite vertex and original-edge arrays. A selected
edge always changes depth by one. A positive closed walk of length one is therefore impossible.
For length at least two, a vertex of maximal depth on the cycle has both cyclic neighbours at one
lower depth; each incident cycle edge must consequently be that vertex’s unique selected parent
edge, contradicting the cycle’s pairwise edge distinctness. This argument includes two-edge cycles
formed by parallel ambient labels and does not assume a finite graph.

7. Any simple H-path from r to v is forced to increase depth at every step: a first decrease would
create a local maximum whose two selected incident edges are the same parent edge, repeating a
vertex. Hence its length is d(v), its final edge is edge(v), and induction on length identifies it
with the recursively defined root path. The same argument gives uniqueness of simple root paths.

8. Let I(0)=univ, I(1)=S, and I(n+2)=∅; let A be the union of precisely these original open cells.
A selected closed zero-cell is its zero-cell singleton, already in A. For a selected one-cell
e=edge(v), the defining G incidence identifies its frontier as
closedCell0(v)∪closedCell0(parent(v)), and the open/frontier decomposition therefore gives
closedCell1(e)⊆A. There is no higher selected cell. Apply CWComplex.Subcomplex.mk' to this exact
open-cell union and selected-closed-cell containment to obtain T with I and carrier A; this
constructor supplies genuine CW closedness, without treating an arbitrary infinite union of closed
sets as closed. The same incidence formula shows that adjoining the selected closed edges to all
zero-cells gives exactly A. At cutoffs1 and2, skeletonLT selects respectively all zero cells and
all zero/one cells, so the original skeleton formulas give skeleton univ0≤T≤skeleton univ1.

9. The carrier of T is equivalently the union of all vertices with the selected closed edges,
because every selected edge endpoint is already among the selected zero cells. All statements use
the original characteristic maps and cell indices; no replacement topology, orientation, local
finiteness, or contraction conclusion is introduced.

-/
theorem cw_realization_spanning_tree
    {K : Type*} [TopologicalSpace K] [T2Space K] [ConnectedSpace K]
    [CWComplex (Set.univ : Set K)]
    (r : RelCWComplex.cell (Set.univ : Set K) 0) :
    let V := RelCWComplex.cell (Set.univ : Set K) 0
    let E := RelCWComplex.cell (Set.univ : Set K) 1
    let G := CWComplex.OneSkeletonGraph (Set.univ : Set K)
    ∃ (d : V → ℕ) (parent : {v : V // v ≠ r} → V)
      (edge : {v : V // v ≠ r} → E) (T : CWComplex.Subcomplex (Set.univ : Set K)),
      let S := Set.range edge
      let H := G.restrict S
      (∀ v : V, Nonempty (CWEdgeWalk G (d v) r v) ∧
        ∀ n : ℕ, Nonempty (CWEdgeWalk G n r v) → d v ≤ n) ∧
      d r = 0 ∧
      (∀ v : {v : V // v ≠ r}, G.IsLink (edge v) v.val (parent v)) ∧
      (∀ v : {v : V // v ≠ r}, d (parent v) + 1 = d v.val) ∧
      Function.Injective edge ∧
      H.vertexSet = Set.univ ∧ H.edgeSet = S ∧
      (∀ u v : V, ∃ n : ℕ, Nonempty (CWEdgeWalk H n u v)) ∧
      (∀ (u : V) (n : ℕ), 0 < n → ∀ c : CWEdgeWalk H n u u,
        ¬(Function.Injective c.edges ∧
          Function.Injective (fun i : Fin n ↦ c.vertices i.castSucc))) ∧
      (∃ R : ∀ v : V, CWEdgeWalk H (d v) r v,
        (∀ v : V, Function.Injective (R v).vertices) ∧
        (∀ (v : V) (n : ℕ) (p : CWEdgeWalk H n r v),
          Function.Injective p.vertices → n = d v ∧ HEq p (R v)) ∧
        (∀ v : {v : V // v ≠ r}, ∃ hd : d (parent v) + 1 = d v.val,
          (∀ i : Fin (d (parent v) + 1),
            (R v.val).vertices (Fin.cast (congrArg (fun n : ℕ ↦ n + 1) hd) i.castSucc) =
              (R (parent v)).vertices i) ∧
          (∀ i : Fin (d (parent v)),
            (R v.val).edges (Fin.cast hd i.castSucc) = (R (parent v)).edges i) ∧
          (R v.val).edges (Fin.cast hd (Fin.last (d (parent v)))) = edge v)) ∧
      T.I 0 = Set.univ ∧ T.I 1 = S ∧
      (∀ n : ℕ, T.I (n + 2) = ∅) ∧
      (T : Set K) = Set.range (fun v : V ↦ RelCWComplex.map (C := Set.univ) 0 v 0) ∪
        ⋃ e ∈ S, RelCWComplex.openCell (C := Set.univ) 1 e ∧
      (T : Set K) = Set.range (fun v : V ↦ RelCWComplex.map (C := Set.univ) 0 v 0) ∪
        ⋃ e ∈ S, RelCWComplex.closedCell (C := Set.univ) 1 e ∧
      CWComplex.skeleton (Set.univ : Set K) 0 ≤ T ∧
      T ≤ CWComplex.skeleton (Set.univ : Set K) 1 := by
  classical
  dsimp only
  let V := RelCWComplex.cell (Set.univ : Set K) 0
  let E := RelCWComplex.cell (Set.univ : Set K) 1
  let G := CWComplex.OneSkeletonGraph (Set.univ : Set K)
  have reach : ∀ v : V, ∃ n : ℕ, Nonempty (CWEdgeWalk G n r v) := by
    intro v
    obtain ⟨n, a, b, ha, hb, hab⟩ := connected_cw_one_skeleton_finite_walk r v
    exact ⟨n, ⟨⟨a, b, ha, hb, hab⟩⟩⟩
  let d : V → ℕ := fun v ↦ Nat.find (reach v)
  have hmin : ∀ v : V, Nonempty (CWEdgeWalk G (d v) r v) ∧
      ∀ n, Nonempty (CWEdgeWalk G n r v) → d v ≤ n := by
    intro v
    exact ⟨Nat.find_spec (reach v), fun n h ↦ Nat.find_min' (reach v) h⟩
  have hdr : d r = 0 := Nat.eq_zero_of_le_zero ((hmin r).2 0 ⟨CWEdgeWalk.nil G r⟩)
  have hd0 : ∀ v : V, d v = 0 → v = r := by
    intro v hv
    obtain ⟨p⟩ := (hmin v).1
    exact ((p.cast hv).eq_of_zero).symm
  have pred : ∀ v : {v : V // v ≠ r}, ∃ (p : V) (e : E),
      G.IsLink e v.val p ∧ d p + 1 = d v.val := by
    intro v
    obtain ⟨p⟩ := (hmin v.val).1
    have hdpos : 0 < d v.val := Nat.pos_of_ne_zero (fun h ↦ v.property (hd0 v.val h))
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
    let q := p.cast hn
    let w := q.vertices (Fin.last n).castSucc
    let e := q.edges (Fin.last n)
    have hlink : G.IsLink e w v.val := by
      simpa only [Fin.succ_last, q.last] using q.isLink (Fin.last n)
    have hp : d w ≤ n := (hmin w).2 n ⟨q.init⟩
    obtain ⟨t⟩ := (hmin w).1
    have hv : d v.val ≤ d w + 1 := (hmin v.val).2 _ ⟨t.snoc e hlink⟩
    exact ⟨w, e, hlink.symm, by omega⟩
  choose parent edge hlink hdepth using pred
  have hedge : Function.Injective edge := by
    intro v w he
    have h := (hlink v).eq_and_eq_or_eq_and_eq (he ▸ hlink w)
    rcases h with h | h
    · exact Subtype.ext h.1
    · have hv := hdepth v
      have hw := hdepth w
      rw [h.1, h.2] at hv
      omega
  let S := Set.range edge
  let H := G.restrict S
  have hselected : ∀ v : {v : V // v ≠ r}, H.IsLink (edge v) v.val (parent v) := by
    intro v
    exact ⟨⟨v, rfl⟩, hlink v⟩
  have hlevels : ∀ {e : E} {x y : V}, H.IsLink e x y →
      (∃ hx : x ≠ r, d x = d y + 1 ∧ edge ⟨x, hx⟩ = e ∧ parent ⟨x, hx⟩ = y) ∨
      (∃ hy : y ≠ r, d y = d x + 1 ∧ edge ⟨y, hy⟩ = e ∧ parent ⟨y, hy⟩ = x) := by
    intro e x y he
    obtain ⟨v, hv⟩ := he.1
    have hh := (he.2).eq_and_eq_or_eq_and_eq (hv ▸ hlink v)
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨v.property, (hdepth v).symm, hv, rfl⟩
    · exact Or.inr ⟨v.property, (hdepth v).symm, hv, rfl⟩
  have hdown : ∀ {e : E} {x y : V}, H.IsLink e x y → d y < d x →
      ∃ hx : x ≠ r, edge ⟨x, hx⟩ = e ∧ parent ⟨x, hx⟩ = y := by
    intro e x y hl hd
    rcases hlevels hl with ⟨hx, hxy, he, hp⟩ | ⟨hy, hyx, he, hp⟩
    · exact ⟨hx, he, hp⟩
    · omega
  have rootlevels : ∀ (n : ℕ) (v : V) (p : CWEdgeWalk H n r v),
      Function.Injective p.vertices → ∀ i : Fin (n + 1), d (p.vertices i) = i.val := by
    intro n
    induction n with
    | zero =>
      intro v p _ i
      have hi : i = 0 := by apply Fin.ext; omega
      simpa only [hi, p.first, Fin.val_zero] using hdr
    | succ n ih =>
      intro v p hinj i
      let q := p.init
      have hqinj : Function.Injective q.vertices := by
        intro i j hij
        exact Fin.castSucc_injective _ (hinj hij)
      have hq := ih _ q hqinj
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · have hn : d (p.vertices (Fin.last n).castSucc) = n := hq (Fin.last n)
        have hl := p.isLink (Fin.last n)
        rw [Fin.succ_last, p.last] at hl
        rcases hlevels hl with ⟨hx, hxv, he, hp⟩ | ⟨hv, hvx, he, hp⟩
        · cases n with
          | zero => omega
          | succ m =>
            have hm : d (p.vertices (Fin.last m).castSucc.castSucc) = m :=
              hq (Fin.last m).castSucc
            have hl' := p.isLink (Fin.last m).castSucc
            have hsucc : (Fin.last m).castSucc.succ = (Fin.last (m + 1)).castSucc := by
              apply Fin.ext; simp
            rw [hsucc] at hl'
            obtain ⟨hx', he', hp'⟩ := hdown hl'.symm (by omega)
            have hvp : v = p.vertices (Fin.last m).castSucc.castSucc := by
              exact hp.symm.trans hp'
            have hindices := hinj (p.last.trans hvp)
            have hval := congrArg Fin.val hindices
            simp only [Fin.val_last, Fin.val_castSucc] at hval
            omega
        · simpa only [p.last, Fin.val_last] using (by omega : d v = n + 1)
      · exact hq j
  have paths : ∀ v : V, ∃ p : CWEdgeWalk H (d v) r v,
      ∀ i : Fin (d v + 1), d (p.vertices i) = i.val := by
    intro v
    generalize hv : d v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hr : v = r
      · subst v
        have hn : n = 0 := hv.symm.trans hdr
        rw [hn]
        refine ⟨CWEdgeWalk.nil H r, ?_⟩
        intro i
        simp only [CWEdgeWalk.nil, hdr, Fin.eq_zero i, Fin.val_zero]
      · let w : {v : V // v ≠ r} := ⟨v, hr⟩
        have hd : d (parent w) + 1 = d v := hdepth w
        have hlt : d (parent w) < n := by omega
        obtain ⟨q, hq⟩ := ih (d (parent w)) hlt (parent w) rfl
        have hpfull : ∃ p : CWEdgeWalk H (d (parent w) + 1) r v,
            ∀ i : Fin (d (parent w) + 1 + 1), d (p.vertices i) = i.val := by
          refine ⟨q.snoc (edge w) (hselected w).symm, ?_⟩
          intro i
          refine Fin.lastCases ?_ (fun j ↦ ?_) i
          · simpa only [CWEdgeWalk.snoc, Fin.snoc_last, Fin.val_last] using hd.symm
          · simpa only [CWEdgeWalk.snoc, Fin.snoc_castSucc, Fin.val_castSucc] using hq j
        have hn : d (parent w) + 1 = n := hd.trans hv
        exact hn ▸ hpfull
  choose R Rlevels using paths
  have Rinj : ∀ v : V, Function.Injective (R v).vertices := by
    intro v i j hij
    apply Fin.ext
    exact (Rlevels v i).symm.trans ((congrArg d hij).trans (Rlevels v j))
  have root_unique : ∀ (n : ℕ) (v : V) (p q : CWEdgeWalk H n r v),
      Function.Injective p.vertices → Function.Injective q.vertices → p = q := by
    intro n
    induction n with
    | zero =>
      intro v p q _ _
      apply CWEdgeWalk.ext
      · funext i
        have hi : i = 0 := by apply Fin.ext; omega
        exact (congrArg p.vertices hi).trans (p.first.trans
          (q.first.symm.trans (congrArg q.vertices hi).symm))
      · exact funext (fun i ↦ Fin.elim0 i)
    | succ n ih =>
      intro v p q hp hq
      have hpl := rootlevels _ _ p hp
      have hql := rootlevels _ _ q hq
      have hpd : d (p.vertices (Fin.last n).castSucc) = n := hpl (Fin.last n).castSucc
      have hqd : d (q.vertices (Fin.last n).castSucc) = n := hql (Fin.last n).castSucc
      have hvd : d v = n + 1 := by simpa only [p.last, Fin.val_last] using hpl (Fin.last (n + 1))
      have hpe := (p.isLink (Fin.last n)).symm
      have hqe := (q.isLink (Fin.last n)).symm
      rw [Fin.succ_last, p.last] at hpe
      rw [Fin.succ_last, q.last] at hqe
      obtain ⟨hv, he, hpar⟩ := hdown hpe (by omega)
      obtain ⟨hv', he', hpar'⟩ := hdown hqe (by omega)
      have hparent : q.vertices (Fin.last n).castSucc = p.vertices (Fin.last n).castSucc :=
        hpar'.symm.trans hpar
      let q' : CWEdgeWalk H n r (p.vertices (Fin.last n).castSucc) :=
        { vertices := fun i ↦ q.vertices i.castSucc
          edges := fun i ↦ q.edges i.castSucc
          first := q.first
          last := hparent
          isLink := fun i ↦ by simpa only [Fin.castSucc_succ] using q.isLink i.castSucc }
      have hpi : Function.Injective p.init.vertices := by
        intro i j hij
        exact Fin.castSucc_injective _ (hp hij)
      have hqi : Function.Injective q'.vertices := by
        intro i j hij
        exact Fin.castSucc_injective _ (hq hij)
      have hprefix := ih _ p.init q' hpi hqi
      apply CWEdgeWalk.ext
      · funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · exact p.last.trans q.last.symm
        · exact congrFun (congrArg CWEdgeWalk.vertices hprefix) j
      · funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · exact he.symm.trans he'
        · exact congrFun (congrArg CWEdgeWalk.edges hprefix) j
  have Runique : ∀ (v : V) (n : ℕ) (p : CWEdgeWalk H n r v),
      Function.Injective p.vertices → n = d v ∧ HEq p (R v) := by
    intro v n p hp
    have hn : n = d v := by
      simpa only [p.last, Fin.val_last] using (rootlevels n v p hp (Fin.last n)).symm
    refine ⟨hn, ?_⟩
    subst n
    exact heq_of_eq (root_unique _ _ p (R v) hp (Rinj v))
  have Rrec : ∀ v : {v : V // v ≠ r}, ∃ hd : d (parent v) + 1 = d v.val,
      (∀ i : Fin (d (parent v) + 1),
        (R v.val).vertices (Fin.cast (congrArg (· + 1) hd) i.castSucc) =
          (R (parent v)).vertices i) ∧
      (∀ i : Fin (d (parent v)),
        (R v.val).edges (Fin.cast hd i.castSucc) = (R (parent v)).edges i) ∧
      (R v.val).edges (Fin.cast hd (Fin.last (d (parent v)))) = edge v := by
    intro v
    let q := (R (parent v)).snoc (edge v) (hselected v).symm
    have hqlevels : ∀ i : Fin (d (parent v) + 1 + 1), d (q.vertices i) = i.val := by
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa only [q, CWEdgeWalk.snoc, Fin.snoc_last, Fin.val_last] using (hdepth v).symm
      · simpa only [q, CWEdgeWalk.snoc, Fin.snoc_castSucc, Fin.val_castSucc] using Rlevels (parent v) j
    have hqinj : Function.Injective q.vertices := by
      intro i j hij
      apply Fin.ext
      exact (hqlevels i).symm.trans ((congrArg d hij).trans (hqlevels j))
    have hc : Function.Injective (q.cast (hdepth v)).vertices :=
      q.cast_injective_vertices (hdepth v) hqinj
    have hqr : q.cast (hdepth v) = R v.val :=
      root_unique _ _ _ _ hc (Rinj v.val)
    refine ⟨hdepth v, ?_, ?_, ?_⟩
    · intro i
      rw [← hqr, CWEdgeWalk.cast_vertices]
      simp only [q, CWEdgeWalk.snoc, Fin.snoc_castSucc]
    · intro i
      rw [← hqr, CWEdgeWalk.cast_edges]
      simp only [q, CWEdgeWalk.snoc, Fin.snoc_castSucc]
    · rw [← hqr, CWEdgeWalk.cast_edges]
      simp only [q, CWEdgeWalk.snoc, Fin.snoc_last]
  have hconnected : ∀ u v : V, ∃ n : ℕ, Nonempty (CWEdgeWalk H n u v) := by
    intro u v
    obtain ⟨n, ⟨p⟩⟩ := (R u).exists_reverse
    exact p.exists_trans (R v)
  have hacyclic : ∀ (u : V) (n : ℕ), 0 < n → ∀ c : CWEdgeWalk H n u u,
      ¬(Function.Injective c.edges ∧
        Function.Injective (fun i : Fin n ↦ c.vertices i.castSucc)) := by
    intro u n hn c hc
    have heinj := hc.1
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero =>
        have hl := c.isLink 0
        have h0 : (0 : Fin 1).castSucc = 0 := rfl
        have h1 : (0 : Fin 1).succ = Fin.last 1 := rfl
        rw [h0, h1, c.first, c.last] at hl
        rcases hlevels hl with ⟨hx, h, _⟩ | ⟨hx, h, _⟩ <;> omega
      | succ k =>
        obtain ⟨i, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (k + 2)))
          (fun j ↦ d (c.vertices j.castSucc)) ⟨0, Finset.mem_univ _⟩
        have hmax' : ∀ j : Fin (k + 2),
            d (c.vertices j.castSucc) ≤ d (c.vertices i.castSucc) :=
          fun j ↦ hmax j (Finset.mem_univ _)
        let j : Fin (k + 2) := if hi : i.val = 0 then Fin.last (k + 1)
          else ⟨i.val - 1, by omega⟩
        have hji : c.vertices j.succ = c.vertices i.castSucc := by
          by_cases hi : i.val = 0
          · have hi0 : i = 0 := Fin.ext hi
            simp [j, hi0]
            exact c.last.trans c.first.symm
          · have hij : j.succ = i.castSucc := by
              apply Fin.ext
              simp [j, hi, Fin.val_castSucc]
              omega
            rw [hij]
        have hneq : j ≠ i := by
          intro h
          have he := congrArg Fin.val h
          by_cases hi : i.val = 0
          · simp [j, hi, Fin.val_last] at he
          · simp [j, hi] at he
            omega
        have hnext : d (c.vertices i.succ) ≤ d (c.vertices i.castSucc) := by
          by_cases hi : i.val + 1 < k + 2
          · let l : Fin (k + 2) := ⟨i.val + 1, hi⟩
            have hil : i.succ = l.castSucc := Fin.ext rfl
            rw [hil]
            exact hmax' l
          · have hil : i.succ = Fin.last (k + 2) := by
              apply Fin.ext
              simp only [Fin.val_succ, Fin.val_last]
              omega
            rw [hil, c.last]
            simpa only [Fin.castSucc_zero, c.first] using hmax' 0
        have hprev := hmax' j
        have hout := c.isLink i
        have hin := (c.isLink j).symm
        rw [hji] at hin
        have houtlt : d (c.vertices i.succ) < d (c.vertices i.castSucc) := by
          rcases hlevels hout with ⟨hx, h, _⟩ | ⟨hx, h, _⟩ <;> omega
        have hinlt : d (c.vertices j.castSucc) < d (c.vertices i.castSucc) := by
          rcases hlevels hin with ⟨hx, h, _⟩ | ⟨hx, h, _⟩ <;> omega
        obtain ⟨hi, hei, _⟩ := hdown hout houtlt
        obtain ⟨hi', hej, _⟩ := hdown hin hinlt
        exact hneq (heinj (hej.symm.trans hei))
  let I : ∀ n : ℕ, Set (RelCWComplex.cell (Set.univ : Set K) n)
    | 0 => Set.univ
    | 1 => S
    | _ + 2 => ∅
  let A : Set K := Set.range (fun v : V ↦ RelCWComplex.map (C := Set.univ) 0 v 0) ∪
    ⋃ e ∈ S, RelCWComplex.openCell (C := Set.univ) 1 e
  have hvertex : ∀ v : V, RelCWComplex.map (C := Set.univ) 0 v 0 ∈ A :=
    fun v ↦ Or.inl ⟨v, rfl⟩
  have hvertex' : ∀ v : V, RelCWComplex.map (C := Set.univ) 0 v ![] ∈ A := by
    intro v
    simpa only [Matrix.empty_eq] using hvertex v
  have hclosed : ∀ (n : ℕ) (i : I n),
      RelCWComplex.closedCell (C := Set.univ) n i.val ⊆ A := by
    intro n i
    cases n with
    | zero =>
      rw [RelCWComplex.closedCell_zero_eq_singleton]
      exact Set.singleton_subset_iff.mpr (hvertex' i.val)
    | succ n =>
      cases n with
      | zero =>
        obtain ⟨v, hv⟩ := i.property
        have hf := hlink v
        change RelCWComplex.cellFrontier (C := Set.univ) 1 (edge v) =
          RelCWComplex.closedCell (C := Set.univ) 0 v.val ∪
            RelCWComplex.closedCell (C := Set.univ) 0 (parent v) at hf
        rw [← hv, ← RelCWComplex.cellFrontier_union_openCell_eq_closedCell, hf,
          RelCWComplex.closedCell_zero_eq_singleton, RelCWComplex.closedCell_zero_eq_singleton]
        intro x hx
        rcases hx with (hx | hx) | hx
        · exact hx ▸ hvertex' v.val
        · exact hx ▸ hvertex' (parent v)
        · exact Or.inr (Set.mem_iUnion.mpr ⟨edge v,
            Set.mem_iUnion.mpr ⟨⟨v, rfl⟩, hx⟩⟩)
      | succ n => exact False.elim (Set.notMem_empty i.val i.property)
  have hunion : (⋃ (n : ℕ) (j : I n), RelCWComplex.openCell (C := Set.univ) n j.val) = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
      cases n with
      | zero =>
        rw [RelCWComplex.openCell_zero_eq_singleton] at hx
        exact hx ▸ hvertex' j.val
      | succ n =>
        cases n with
        | zero => exact Or.inr (Set.mem_iUnion.mpr ⟨j.val,
            Set.mem_iUnion.mpr ⟨j.property, hx⟩⟩)
        | succ n => exact False.elim (Set.notMem_empty j.val j.property)
    · rintro (⟨v, rfl⟩ | hx)
      · apply Set.mem_iUnion.mpr
        refine ⟨0, Set.mem_iUnion.mpr ⟨⟨v, Set.mem_univ _⟩, ?_⟩⟩
        simp only [RelCWComplex.openCell_zero_eq_singleton, Set.mem_singleton_iff, Matrix.empty_eq]
      · obtain ⟨e, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨he, hx⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩⟩
  let T := CWComplex.Subcomplex.mk' (Set.univ : Set K) A I hclosed hunion
  have hcarrier : (T : Set K) = A := rfl
  have hcarrier_closed : (T : Set K) =
      Set.range (fun v : V ↦ RelCWComplex.map (C := Set.univ) 0 v 0) ∪
        ⋃ e ∈ S, RelCWComplex.closedCell (C := Set.univ) 1 e := by
    rw [hcarrier]
    apply Set.Subset.antisymm
    · rintro x (hx | hx)
      · exact Or.inl hx
      · obtain ⟨e, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨he, hx⟩ := Set.mem_iUnion.mp hx
        exact Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he,
          RelCWComplex.openCell_subset_closedCell 1 e hx⟩⟩)
    · rintro x (hx | hx)
      · exact Or.inl hx
      · obtain ⟨e, hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨he, hx⟩ := Set.mem_iUnion.mp hx
        exact hclosed 1 ⟨e, he⟩ hx
  have hskeleton0 : CWComplex.skeleton (Set.univ : Set K) 0 ≤ T := by
    intro x hx
    obtain ⟨m, hm, j, hx⟩ := CWComplex.mem_skeleton_iff.mp hx
    have hm0 : m = 0 := by simpa using hm
    subst m
    rw [RelCWComplex.openCell_zero_eq_singleton] at hx
    exact hx ▸ hvertex' j
  have hskeleton1 : T ≤ CWComplex.skeleton (Set.univ : Set K) 1 := by
    rintro x (hx | hx)
    · obtain ⟨v, rfl⟩ := hx
      exact RelCWComplex.openCell_subset_skeleton 0 v
        (by simp [RelCWComplex.openCell_zero_eq_singleton]) |>
        (RelCWComplex.skeleton_mono (by simp))
    · obtain ⟨e, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨he, hx⟩ := Set.mem_iUnion.mp hx
      exact RelCWComplex.openCell_subset_skeleton 1 e hx
  refine ⟨d, parent, edge, T, hmin, hdr, hlink, hdepth, hedge,
    rfl, ?_, hconnected, hacyclic, ⟨R, Rinj, Runique, Rrec⟩, rfl, rfl,
    (fun n ↦ rfl), rfl, hcarrier_closed, hskeleton0, hskeleton1⟩
  change Set.univ ∩ S = S
  exact Set.univ_inter S

end HolomorphicAnosov
