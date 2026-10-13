import HolomorphicAnosov.Topology.CWComplex.CellularApproximation
import HolomorphicAnosov.Topology.ContractibleOpenNeighborhoods
import HolomorphicAnosov.Topology.CWIntervalProduct
import Mathlib.Analysis.Convex.Topology

namespace HolomorphicAnosov

open _root_.Topology

/-- The one-skeleton of a connected Hausdorff CW complex is preconnected.

Source: Hatcher, *Algebraic Topology*, Appendix Proposition A.4 and the
connected-if-and-only-if-path-connected consequence, pp.522–523; relative
Cellular Approximation Theorem 4.8 and Lemma 4.10, pp.349–351. Proof: A.4 gives contractible open neighborhoods in the original CW topology.
These are path connected; consequently path components are open. Connectedness
of X forces any two points of X to be joined by an interval path. In particular
there is such a path between the characteristic points of any two zero cells.

Apply the existing interval-product theorem to the discrete singleton CW
complex Unit. It supplies the ordinary product Unit × [0,1], its original
endpoint subcomplex, and a closed one-cell covering the entire product. This
is the interval CW presentation needed below; its source is Fritsch–Piccinini,
*Cellular Structures in Topology*, Theorem 2.2.2, p.58, with Hatcher A.6, p.524.
The singleton closed zero-cell is the whole Unit, so the product prism formula
places the whole product in its one-skeleton.

Compose a chosen path between original vertex points with the second
projection from this product. On the endpoint subcomplex it takes the two
original zero-cell values, hence it is cellular there. Apply relative Theorem
4.8. The resulting continuous cellular map still has these endpoint values;
its whole range lies in the original target one-skeleton. Its range is
preconnected as the continuous image of the preconnected interval product.
Thus any two original vertex points lie in a preconnected subset of the
original one-skeleton.

Every point of the target one-skeleton is in an original zero cell or open
one cell. For a zero cell take its singleton closed cell. For a one cell take
its entire closed cell: it is preconnected as the continuous characteristic
image of the convex closed native one-ball, contains the given point, and
contains the point of an original endpoint zero cell. All these closed cells
lie in the target one-skeleton. Given any two points, join their respective
closed cells by the preconnected range between these endpoint vertices. The
three sets have successive common vertex points, so their union is a
preconnected subset of the one-skeleton containing the given pair. Mathlib's
pairwise preconnected-subset criterion gives the conclusion, including the
empty-skeleton case without an extra nonemptiness assumption.
No finiteness, local finiteness, dimension bound, or regularity is imposed.
-/
theorem cw_one_skeleton_preconnected
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)] :
    IsPreconnected (RelCWComplex.skeletonLT (Set.univ : Set X) 2 : Set X) := by
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
  have hpath (u v : RelCWComplex.cell C 0) :
      ∃ T : Set X, T ⊆ S ∧ RelCWComplex.map 0 u 0 ∈ T ∧
        RelCWComplex.map 0 v 0 ∈ T ∧ IsPreconnected T := by
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
    refine ⟨Set.range c, ?_, ?_, ?_, isPreconnected_range c.continuous⟩
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
        T ⊆ S ∧ RelCWComplex.map 0 u 0 ∈ T ∧ x ∈ T ∧ IsPreconnected T := by
    obtain ⟨n, hn, j, hj⟩ := CWComplex.mem_skeletonLT_iff.mp hx
    have hn' : n < 2 := by exact_mod_cast hn
    rcases n with _ | _ | n
    · refine ⟨j, RelCWComplex.closedCell 0 j, ?_,
        RelCWComplex.map_zero_mem_closedCell 0 j,
        RelCWComplex.openCell_subset_closedCell _ _ hj, ?_⟩
      · exact fun y hy ↦ RelCWComplex.skeletonLT_mono (by norm_num)
          (RelCWComplex.closedCell_subset_skeletonLT 0 j hy)
      · rw [RelCWComplex.closedCell_zero_eq_singleton]
        exact isPreconnected_singleton
    · obtain ⟨u, v, huv⟩ := CWComplex.exists_cellFrontier_one_eq j
      refine ⟨u, RelCWComplex.closedCell 1 j,
        RelCWComplex.closedCell_subset_skeletonLT 1 j, ?_,
        RelCWComplex.openCell_subset_closedCell _ _ hj, ?_⟩
      · apply RelCWComplex.cellFrontier_subset_closedCell
        rw [huv]
        exact Or.inl (RelCWComplex.map_zero_mem_closedCell 0 u)
      · exact (convex_closedBall (0 : Fin 1 → ℝ) 1).isPreconnected.image
          (RelCWComplex.map 1 j) (RelCWComplex.continuousOn 1 j)
    · omega
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  obtain ⟨u, U, hUS, huU, hxU, hU⟩ := hlocal x hx
  obtain ⟨v, V, hVS, hvV, hyV, hV⟩ := hlocal y hy
  obtain ⟨T, hTS, huT, hvT, hT⟩ := hpath u v
  refine ⟨(U ∪ T) ∪ V, Set.union_subset (Set.union_subset hUS hTS) hVS,
    Or.inl (Or.inl hxU), Or.inr hyV, ?_⟩
  exact ((hU.union _ huU huT hT).union _ (Or.inr hvT) hvV hV)


end HolomorphicAnosov

