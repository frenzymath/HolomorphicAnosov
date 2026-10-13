import HolomorphicAnosov.Topology.CWOneSkeletonPreconnected
import HolomorphicAnosov.Topology.ConnectedCWOneSkeletonFiniteWalkBase

/-!
# Finite original-edge walks in a connected CW complex

Source: Hatcher, *Algebraic Topology*, Proposition 1A.1, pp.83–84,
using the original one-skeleton connectedness consequence of Appendix A.4,
pp.522–523, and relative Cellular Approximation Theorem 4.8, pp.349–351.
DAG node: `topo.connected_cw_one_skeleton_finite_walk_g8`.
-/

namespace HolomorphicAnosov

open _root_.Topology

/-- Original zero cells in a connected Hausdorff CW complex are joined by a
finite walk labelled by original one cells, allowing a walk of length zero.

Proof: `cw_one_skeleton_preconnected` supplies preconnectedness in the original
subspace topology. Following Hatcher Proposition 1A.1's edge-layer argument
(pp.83–84), fix u and let P consist of the vertices reachable from u by finite
original-edge walks. Appending an edge shows that its endpoints have the same
membership in P. Select the zero cells in P and the one cells with an endpoint
in P; select no higher cells. Every selected closed cell is contained in the
union of selected open cells: the only issue is an edge's frontier, whose two
endpoints both belong to P. The CW subcomplex constructor therefore shows this
union R is closed. Apply the same construction to the complementary vertex
predicate to obtain another closed subcomplex Q.

The two subcomplexes cover the one-skeleton because every edge has endpoints.
They are disjoint: uniqueness of the open cell containing a point reduces
the question to vertices or edges; for an edge the graph endpoint-uniqueness
and append properties preclude simultaneous membership in both classes.
The point of u belongs to R, using the zero-length walk. If v were unreachable,
its point would belong to Q. These two nonempty disjoint closed parts contradict
preconnectedness. Thus the required finite arrays exist. No edge labels are
identified, so loops and parallel edges are retained. No finite-support or
finite-crossing assertion is needed.
-/
theorem connected_cw_one_skeleton_finite_walk
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)]
    (u v : RelCWComplex.cell (Set.univ : Set X) 0) :
    ∃ (n : ℕ) (a : Fin (n + 1) → RelCWComplex.cell (Set.univ : Set X) 0)
      (b : Fin n → RelCWComplex.cell (Set.univ : Set X) 1),
      a 0 = u ∧ a (Fin.last n) = v ∧
        ∀ i : Fin n,
          (CWComplex.OneSkeletonGraph (Set.univ : Set X)).IsLink
            (b i) (a i.castSucc) (a i.succ) := by
  classical
  let C : Set X := Set.univ
  let G := CWComplex.OneSkeletonGraph C
  let W (x y : RelCWComplex.cell C 0) : Prop :=
    ∃ (n : ℕ) (a : Fin (n + 1) → RelCWComplex.cell C 0)
      (b : Fin n → RelCWComplex.cell C 1),
      a 0 = x ∧ a (Fin.last n) = y ∧
        ∀ i : Fin n, G.IsLink (b i) (a i.castSucc) (a i.succ)
  have hrefl (x : RelCWComplex.cell C 0) : W x x :=
    connected_cw_one_skeleton_finite_walk_refl x x rfl
  have hstep {x y z : RelCWComplex.cell C 0} (h : W x y)
      (e : RelCWComplex.cell C 1) (he : G.IsLink e y z) : W x z := by
    obtain ⟨n, a, b, ha, hb, hab⟩ := h
    refine ⟨n + 1, Fin.snoc a z, Fin.snoc b e, ?_, by simp, ?_⟩
    · simpa using ha
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa [hb] using he
      · rw [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_castSucc,
          Fin.snoc_castSucc]
        exact hab j
  let P := W u
  have hP (e : RelCWComplex.cell C 1) (x y : RelCWComplex.cell C 0)
      (he : G.IsLink e x y) : P x ↔ P y :=
    ⟨fun h ↦ hstep h e he, fun h ↦ hstep h e he.symm⟩
  let I (Q : RelCWComplex.cell C 0 → Prop) : (n : ℕ) → Set (RelCWComplex.cell C n)
    | 0 => {x | Q x}
    | 1 => {e | ∃ x y, G.IsLink e x y ∧ Q x}
    | _ + 2 => ∅
  let R (Q : RelCWComplex.cell C 0 → Prop) : Set X :=
    ⋃ (n : ℕ) (j : I Q n), RelCWComplex.openCell (C := C) n j
  have hmem (Q : RelCWComplex.cell C 0 → Prop) (n : ℕ)
      (j : RelCWComplex.cell C n) {x : X} (hx : x ∈ RelCWComplex.openCell n j) :
      x ∈ R Q ↔ j ∈ I Q n := by
    constructor
    · intro h
      obtain ⟨m, k, hk⟩ := Set.mem_iUnion₂.mp h
      have heq := RelCWComplex.eq_of_not_disjoint_openCell
        (Set.not_disjoint_iff.mpr ⟨x, hk, hx⟩)
      cases heq
      exact k.property
    · intro hj
      exact Set.mem_iUnion₂.mpr ⟨n, ⟨j, hj⟩, hx⟩
  have hclosed (Q : RelCWComplex.cell C 0 → Prop)
      (hQ : ∀ e x y, G.IsLink e x y → (Q x ↔ Q y)) : IsClosed (R Q) := by
    apply (CWComplex.Subcomplex.mk' C (R Q) (I Q) ?_ rfl).closed
    intro n j x hx
    rcases n with _ | _ | n
    · apply (hmem Q 0 j.val ?_).mpr j.property
      simpa only [RelCWComplex.openCell_zero_eq_singleton, RelCWComplex.closedCell_zero_eq_singleton] using hx
    · obtain ⟨a, b, hab, ha⟩ := j.property
      rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell] at hx
      rcases hx with hx | hx
      · change RelCWComplex.cellFrontier 1 j.val =
          RelCWComplex.closedCell 0 a ∪ RelCWComplex.closedCell 0 b at hab
        rw [hab] at hx
        rcases hx with hx | hx
        · apply (hmem Q 0 a ?_).mpr ha
          simpa only [RelCWComplex.openCell_zero_eq_singleton, RelCWComplex.closedCell_zero_eq_singleton] using hx
        · apply (hmem Q 0 b ?_).mpr ((hQ _ _ _ hab).mp ha)
          simpa only [RelCWComplex.openCell_zero_eq_singleton, RelCWComplex.closedCell_zero_eq_singleton] using hx
      · exact (hmem Q 1 j.val hx).mpr j.property
    · exact (Set.notMem_empty _ j.property).elim
  have hconn : IsPreconnected
      (RelCWComplex.skeletonLT C 2 : Set X) := by
    exact cw_one_skeleton_preconnected
  by_contra hv
  let Q := fun x ↦ ¬ P x
  have hQ (e : RelCWComplex.cell C 1) (a b : RelCWComplex.cell C 0)
      (he : G.IsLink e a b) : Q a ↔ Q b := (hP e a b he).not
  have hcover : (RelCWComplex.skeletonLT C 2 : Set X) ⊆ R P ∪ R Q := by
    intro x hx
    obtain ⟨n, hn, j, hj⟩ := CWComplex.mem_skeletonLT_iff.mp hx
    have hn' : n < 2 := by exact_mod_cast hn
    rcases n with _ | _ | n
    · by_cases hp : P j
      · exact Or.inl ((hmem P 0 j hj).mpr hp)
      · exact Or.inr ((hmem Q 0 j hj).mpr hp)
    · obtain ⟨a, b, hab⟩ := CWComplex.exists_cellFrontier_one_eq j
      by_cases hp : P a
      · exact Or.inl ((hmem P 1 j hj).mpr ⟨a, b, hab, hp⟩)
      · exact Or.inr ((hmem Q 1 j hj).mpr ⟨a, b, hab, hp⟩)
    · omega
  have hvertex (x : RelCWComplex.cell C 0) :
      RelCWComplex.map 0 x 0 ∈ (RelCWComplex.skeletonLT C 2 : Set X) := by
    apply CWComplex.mem_skeletonLT_iff.mpr
    exact ⟨0, by norm_num, x, RelCWComplex.map_zero_mem_openCell 0 x⟩
  obtain ⟨x, hxS, hxP, hxQ⟩ := isPreconnected_closed_iff.mp hconn
    (R P) (R Q) (hclosed P hP) (hclosed Q hQ) hcover
    ⟨RelCWComplex.map 0 u 0, hvertex u,
      (hmem P 0 u (RelCWComplex.map_zero_mem_openCell 0 u)).mpr (hrefl u)⟩
    ⟨RelCWComplex.map 0 v 0, hvertex v,
      (hmem Q 0 v (RelCWComplex.map_zero_mem_openCell 0 v)).mpr hv⟩
  obtain ⟨n, hn, j, hj⟩ := CWComplex.mem_skeletonLT_iff.mp hxS
  have hn' : n < 2 := by exact_mod_cast hn
  have hp := (hmem P n j hj).mp hxP
  have hq := (hmem Q n j hj).mp hxQ
  rcases n with _ | _ | n
  · exact hq hp
  · obtain ⟨a, b, hab, ha⟩ := hp
    obtain ⟨c, d, hcd, hc⟩ := hq
    rcases hab.left_eq_or_eq hcd with h | h
    · exact hc (h ▸ ha)
    · exact hc ((hP j c d hcd).mpr (h ▸ ha))
  · omega

end HolomorphicAnosov
