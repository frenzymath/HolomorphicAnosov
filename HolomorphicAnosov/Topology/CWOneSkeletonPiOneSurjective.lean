import HolomorphicAnosov.Topology.CWOneSkeletonLoopApproximation
import HolomorphicAnosov.Topology.Pi1SurjectiveLoopCriterion
import HolomorphicAnosov.Topology.ContractibleOpenNeighborhoods
import Mathlib.Analysis.Convex.Topology

/-!
# Fundamental-group surjectivity of the original CW one-skeleton

Source: Hatcher, *Algebraic Topology*, Proposition 1.26(a)--(c), pp. 50--51,
and Appendix Proposition A.1, p. 520. The connected original-edge walk input
uses Appendix Proposition A.4, pp. 522--523, relative Cellular Approximation
Theorem 4.8 and Lemma 4.10, pp. 349--351, and Proposition 1A.1, pp. 83--84.
The finite-attachment argument uses the written strip construction in
Proposition 1.26 and Lemma 1.15, p. 35; its characteristic-disk coordinate
input is Bredon, *Topology and Geometry*, I.16.4, pp. 56--57.

This is the Stage2 statement of `topo.cw_one_skeleton_pi1_surjective`.
All skeletons have the original subspace topology, and all maps below are
literal subtype inclusions.
-/

namespace HolomorphicAnosov

open _root_.Topology

/-- The original one-skeleton of a connected Hausdorff CW complex is path
connected and its inclusion is surjective on the fundamental group at every
point of the zero-skeleton. Every original based loop is based homotopic to
the inclusion of a loop in that one-skeleton.

Proof (Hatcher, Proposition 1.26, pp. 50--51, and Appendix A.1, p. 520,
with the original-edge connectedness input cited in the module docstring):
Choose the original zero-cell label representing `k0`. A finite original
edge walk joins it to any other vertex. Realize each edge by its continuous
characteristic interval, reversing it when necessary, and concatenate the
finitely many paths. A loop edge may instead contribute a constant path.
Any interior point of a one-cell joins an endpoint along the same
characteristic interval. These paths lie in the original one-skeleton and
are continuous into its subtype topology, so that skeleton is path connected.

For a based loop `α`, compactness of its image and Appendix A.1 give a finite
original subcomplex `L` containing it. Choose finitely many original edge
walks from `k0` to all vertices of `L`. Let `P0` consist of their vertices
and `k0`, and `P1` of their edge labels. All endpoints of the selected edges
are in `P0`. The finite union `P` of their closed zero- and one-cells is
closed, since these cells are compact and the ambient space is Hausdorff.
It equals the union of the selected original open cells, because each edge
is its open cell together with its characteristic endpoints. The CW
subcomplex constructor therefore supplies the original subcomplex `P`
with precisely those indices and characteristic maps. Similarly `L ∪ P`
is an original subcomplex, using the unions of the selected index sets;
its total set of cells is finite and its topology is the inherited one.

The one-skeleton of `L ∪ P` is path connected to `k0`: its vertices lie
on the chosen walks, and each interior edge point joins an endpoint.
Each higher-dimensional selected cell attaches to the lower skeleton;
its boundary sphere is nonempty, and a characteristic radial segment joins
an interior point to a boundary point. Descending through the finitely many
dimensions shows that `L ∪ P` is connected and obtained from its connected
one-skeleton by finitely many attachments of cells of dimension at least two.

Restrict `α` to the subtype `L ∪ P` using its actual range inclusion.
The restriction is continuous and has both endpoints equal to the subtype
point represented by `k0`. The finite-attachment surjectivity theorem,
proved by Hatcher's auxiliary-strip construction and Lemma 1.15, gives a
loop in its one-skeleton whose inclusion is homotopic to this restricted
loop fixing both endpoints. Include that loop in the full original
one-skeleton, and include the homotopy in the ambient complex. These
inclusions compose literally to the original loop and preserve the
basepoint. `FundamentalGroup.map` is precisely this postcomposition on
path-homotopy classes; since every class has a loop representative, it is
surjective, and the same construction gives the stated based homotopy.

The basepoint excludes the empty complex. For a connected zero-dimensional
complex the inclusion is the identity on its single point. Zero-length
walks, loop edges and parallel edges are allowed. The finite enlarged
subcomplex depends on `α`; no global finiteness, dimensional bound, or local
finiteness is assumed.
-/
theorem cw_one_skeleton_pi1_surjective
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)]
    (k0 : X)
    (hk0 : k0 ∈ (CWComplex.skeletonLT (Set.univ : Set X) 1 : Set X)) :
    let K1 := ↥(CWComplex.skeletonLT (Set.univ : Set X) 2 : Set X)
    let k1 : K1 :=
      ⟨k0, CWComplex.skeletonLT_mono (show (1 : ℕ∞) ≤ 2 by decide) hk0⟩
    let inclusion : C(K1, X) := ⟨Subtype.val, continuous_subtype_val⟩
    PathConnectedSpace K1 ∧
      Function.Surjective (FundamentalGroup.map inclusion k1) ∧
      ∀ α : Path k0 k0, ∃ β : Path k1 k1,
        (β.map inclusion.continuous).Homotopic α := by
  dsimp only
  have hloops := cw_one_skeleton_loop_approximation k0 hk0
  refine ⟨?_, (pi1_surjective_iff_loop_homotopic _ _).mpr hloops, hloops⟩
  classical
  have : PathConnectedSpace X :=
    cw_contractible_open_neighborhoods.2.2.2 inferInstance
  let C : Set X := Set.univ
  let S : Set X := RelCWComplex.skeletonLT C 2
  obtain ⟨K, labels, hend, hprism, _, ⟨A, hA, _⟩, _⟩ :=
    Topology.cw_interval_product (X := Unit)
  let : CWComplex (Set.univ : Set (Unit × unitInterval)) := K
  let V := RelCWComplex.cell (Set.univ : Set Unit) 0
  let vertex : V := ⟨(), Set.mem_univ ()⟩
  have hv (i : V) : RelCWComplex.closedCell 0 i = (Set.univ : Set Unit) := by
    rw [RelCWComplex.closedCell_zero_eq_singleton]
    exact Set.eq_univ_of_forall fun x ↦ Subsingleton.elim x _
  have hfull (z : Unit × unitInterval) :
      z ∈ (RelCWComplex.skeleton (Set.univ : Set (Unit × unitInterval)) 1 : Set _) := by
    apply RelCWComplex.closedCell_subset_skeleton 1
      (labels 1 (Sum.inr ⟨0, ⟨vertex, rfl⟩⟩))
    rw [(hprism 0 vertex).2.1, hv]
    exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  have : PathConnectedSpace Unit :=
    ⟨inferInstance, fun x y ↦ by
      have hxy : x = y := Subsingleton.elim _ _
      subst y
      exact ⟨Path.refl x⟩⟩
  have : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  have hpath (u v : RelCWComplex.cell C 0) :
      ∃ T : Set X, T ⊆ S ∧ RelCWComplex.map 0 u 0 ∈ T ∧
        RelCWComplex.map 0 v 0 ∈ T ∧ IsPathConnected T := by
    let p := PathConnectedSpace.somePath (RelCWComplex.map 0 u 0)
      (RelCWComplex.map 0 v 0)
    let f : C(Unit × unitInterval, X) := ⟨fun z ↦ p z.2,
      p.continuous.comp continuous_snd⟩
    have hf : ∀ n : ℕ, Set.MapsTo f
        ((A : Set (Unit × unitInterval)) ∩
          (RelCWComplex.skeleton (Set.univ : Set (Unit × unitInterval)) n : Set _))
        (RelCWComplex.skeleton C n : Set X) := by
      intro n z hz
      have hz' := hz.1
      rw [hA] at hz'
      rcases hz'.2 with h | h
      · have hp : f z = RelCWComplex.map 0 u 0 := by
          change p z.2 = _
          rw [h, p.source]
        rw [hp]
        exact RelCWComplex.skeleton_mono (by simp) <|
          RelCWComplex.closedCell_subset_skeleton 0 u
            (RelCWComplex.map_zero_mem_closedCell 0 u)
      · have hp : f z = RelCWComplex.map 0 v 0 := by
          change p z.2 = _
          rw [Set.mem_singleton_iff.mp h, p.target]
        rw [hp]
        exact RelCWComplex.skeleton_mono (by simp) <|
          RelCWComplex.closedCell_subset_skeleton 0 v
            (RelCWComplex.map_zero_mem_closedCell 0 v)
    obtain ⟨c, hc, H⟩ := Topology.CWComplex.cellularApproximation A f hf
    refine ⟨Set.range c, ?_, ?_, ?_, isPathConnected_range c.continuous⟩
    · rintro x ⟨z, rfl⟩
      exact hc 1 (hfull z)
    · refine ⟨((), 0), ?_⟩
      have heq := ContinuousMap.HomotopicRel.fst_eq_snd H (x := ((), 0))
        (by rw [hA]; exact ⟨Set.mem_univ _, by simp⟩)
      exact heq.symm.trans p.source
    · refine ⟨((), 1), ?_⟩
      have heq := ContinuousMap.HomotopicRel.fst_eq_snd H (x := ((), 1))
        (by rw [hA]; exact ⟨Set.mem_univ _, by simp⟩)
      exact heq.symm.trans p.target
  have hlocal (x : X) (hx : x ∈ S) :
      ∃ (u : RelCWComplex.cell C 0) (T : Set X),
        T ⊆ S ∧ RelCWComplex.map 0 u 0 ∈ T ∧ x ∈ T ∧ IsPathConnected T := by
    obtain ⟨n, hn, j, hj⟩ := CWComplex.mem_skeletonLT_iff.mp hx
    have hn' : n < 2 := by exact_mod_cast hn
    rcases n with _ | _ | n
    · refine ⟨j, RelCWComplex.closedCell 0 j, ?_,
        RelCWComplex.map_zero_mem_closedCell 0 j,
        RelCWComplex.openCell_subset_closedCell _ _ hj, ?_⟩
      · exact fun y hy ↦ RelCWComplex.skeletonLT_mono (by norm_num)
          (RelCWComplex.closedCell_subset_skeletonLT 0 j hy)
      · rw [RelCWComplex.closedCell_zero_eq_singleton]
        exact isPathConnected_singleton _
    · obtain ⟨u, v, huv⟩ := CWComplex.exists_cellFrontier_one_eq j
      refine ⟨u, RelCWComplex.closedCell 1 j,
        RelCWComplex.closedCell_subset_skeletonLT 1 j, ?_,
        RelCWComplex.openCell_subset_closedCell _ _ hj, ?_⟩
      · apply RelCWComplex.cellFrontier_subset_closedCell
        rw [huv]
        exact Or.inl (RelCWComplex.map_zero_mem_closedCell 0 u)
      · exact ((convex_closedBall (0 : Fin 1 → ℝ) 1).isPathConnected
          ⟨0, by simp⟩).image' (RelCWComplex.continuousOn 1 j)
    · omega
  apply isPathConnected_iff_pathConnectedSpace.mp
  have hkS : k0 ∈ S := CWComplex.skeletonLT_mono (show (1 : ℕ∞) ≤ 2 by decide) hk0
  refine ⟨k0, hkS, ?_⟩
  intro x hx
  obtain ⟨u, U, hUS, huU, hkU, hU⟩ := hlocal k0 hkS
  obtain ⟨v, V, hVS, hvV, hxV, hV⟩ := hlocal x hx
  obtain ⟨T, hTS, huT, hvT, hT⟩ := hpath u v
  exact ((hU.joinedIn _ hkU _ huU).mono hUS).trans
    (((hT.joinedIn _ huT _ hvT).mono hTS).trans
      ((hV.joinedIn _ hvV _ hxV).mono hVS))

end HolomorphicAnosov
