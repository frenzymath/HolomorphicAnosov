import HolomorphicAnosov.Topology.BasedHomotopyUniqueness
import HolomorphicAnosov.Topology.BarycentricCoverage
import HolomorphicAnosov.Topology.CWComplex.RealizationSpanningTree
import HolomorphicAnosov.Topology.CompactLocallyContractibleNeighborhoodRetract
import HolomorphicAnosov.Topology.ContractibleOpenNeighborhoods
import HolomorphicAnosov.Topology.FiniteGeometricSimplicialClassicalCW
import HolomorphicAnosov.Topology.GraphSpanningTreeLoopGeneration
import HolomorphicAnosov.Topology.HigherCellAttachmentPi1
import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometry
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Topology.Separation.Connected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A finite simplicial retract of a closed manifold

Source: Hatcher, *Algebraic Topology*, Theorem A.7 pp.525–527 and Corollaries
A.8–A.9 p.527; Proposition 1A.2 pp.84–85 and Proposition 1.26 pp.50–52.
DAG node: `topo.closed_manifold_finite_simplicial_retract_pi1_fg`.

The realization is the actual convex-hull union of a real geometric simplicial
complex in a finite-dimensional Euclidean space, with its subtype topology.
Its finite CW structure is chosen on that same subtype. The manifold is a literal
retract; no triangulation of the manifold is assumed or concluded.
-/

open scoped ContDiff

namespace HolomorphicAnosov

universe u

/-- Hatcher A.9, p.527: shrink the original coordinate chart to a convex ball inside the given neighborhood and transfer its straight-line contraction. -/
private theorem charted_real_weakly_locally_contractible
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [ChartedSpace E X]
    (x : X) (O : Set X) (hO : IsOpen O) (hx : x ∈ O) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∃ hVO : V ⊆ O, (ContinuousMap.inclusion hVO).Nullhomotopic := by
  let c := chartAt E x
  have hcx : x ∈ c.source := ChartedSpace.mem_chart_source (H := E) x
  have ho : IsOpen (c '' (c.source ∩ O)) := c.isOpen_image_source_inter hO
  have hmem : c x ∈ c '' (c.source ∩ O) := ⟨x, ⟨hcx, hx⟩, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho (c x) hmem
  have htarget : Metric.ball (c x) r ⊆ c.target := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := hball hz
    rw [← hzy]
    exact c.map_source hy.1
  let V := c.symm '' Metric.ball (c x) r
  have hV : IsOpen V := c.isOpen_image_symm_of_subset_target Metric.isOpen_ball htarget
  have hxV : x ∈ V := by
    refine ⟨c x, Metric.mem_ball_self hr, c.left_inv hcx⟩
  have hVO : V ⊆ O := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hball hz
    rw [← hwz, c.left_inv hw.1]
    exact hw.2
  have : ContractibleSpace (Metric.ball (c x) r) :=
    (convex_ball (c x) r).contractibleSpace ⟨c x, Metric.mem_ball_self hr⟩
  have : ContractibleSpace V :=
    (c.symm.homeomorphOfImageSubsetSource htarget rfl).symm.contractibleSpace
  refine ⟨V, hV, hxV, hVO, ?_⟩
  exact (id_nullhomotopic V).comp_right (ContinuousMap.inclusion hVO)

/-- Hatcher A.8, p.527: retain every face of each simplex meeting C. Coverage retains C; the diameter bound puts the whole selected realization in U. -/
private theorem finite_subcomplex_neighborhood
    (N : ℕ) (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (hP : P.faces.Finite) (C U : Set (EuclideanSpace ℝ (Fin N)))
    (hCP : C ⊆ P.space) (δ : ℝ)
    (hbuffer : ∀ c ∈ C, Metric.ball c δ ⊆ U)
    (hmesh : ∀ s ∈ P.faces, Metric.diam (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))) < δ) :
    ∃ Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)),
      Q.faces.Finite ∧ Q.faces ⊆ P.faces ∧ C ⊆ Q.space ∧ Q.space ⊆ U := by
  classical
  let Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)) :=
    { faces := {t | t ∈ P.faces ∧ ∃ s ∈ P.faces, t ⊆ s ∧
          (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N))) ∩ C).Nonempty}
      isRelLowerSet_faces := by
        intro t ht
        refine ⟨P.nonempty_of_mem_faces ht.1, ?_⟩
        intro w hwt hwn
        obtain ⟨s, hs, hts, hmeet⟩ := ht.2
        exact ⟨P.down_closed ht.1 hwt hwn, s, hs, hwt.trans hts, hmeet⟩
      indep := fun ht ↦ P.indep ht.1
      inter_subset_convexHull := fun ht hw ↦ P.inter_subset_convexHull ht.1 hw.1 }
  refine ⟨Q, hP.subset (fun _ h ↦ h.1), (fun _ h ↦ h.1), ?_, ?_⟩
  · intro c hc
    obtain ⟨s, hs, hcs⟩ := P.mem_space_iff.mp (hCP hc)
    exact Q.mem_space_iff.mpr ⟨s, ⟨hs, s, hs, Finset.Subset.refl _, c, hcs, hc⟩, hcs⟩
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := Q.mem_space_iff.mp hx
    obtain ⟨s, hs, hts, c, hcs, hc⟩ := ht.2
    have hxs : x ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N))) :=
      convexHull_mono (Finset.coe_subset.mpr hts) hxt
    have hb : Bornology.IsBounded (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))) :=
      (s.finite_toSet.isCompact_convexHull ℝ).isBounded
    apply hbuffer c hc
    exact (Metric.dist_le_diam_of_mem hb hxs hcs).trans_lt (hmesh s hs)

/-- Hatcher A.8 connected refinement: take the component containing the connected set C. Every convex simplex meeting it lies entirely in it, so this component is a finite subcomplex. -/
private theorem finite_connected_subcomplex
    (N : ℕ) (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (hP : P.faces.Finite) (C : Set (EuclideanSpace ℝ (Fin N)))
    (hC : IsConnected C) (hCP : C ⊆ P.space) :
    ∃ Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)),
      Q.faces.Finite ∧ IsConnected Q.space ∧ C ⊆ Q.space ∧ Q.space ⊆ P.space := by
  classical
  obtain ⟨c, hc⟩ := hC.nonempty
  let A := connectedComponentIn P.space c
  have hCA : C ⊆ A := hC.isPreconnected.subset_connectedComponentIn hc hCP
  let Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)) :=
    { faces := {s | s ∈ P.faces ∧ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N))) ⊆ A}
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨P.nonempty_of_mem_faces hs.1, ?_⟩
        intro t hts htn
        exact ⟨P.down_closed hs.1 hts htn,
          (convexHull_mono (Finset.coe_subset.mpr hts)).trans hs.2⟩
      indep := fun hs ↦ P.indep hs.1
      inter_subset_convexHull := fun hs ht ↦ P.inter_subset_convexHull hs.1 ht.1 }
  have hQA : Q.space = A := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := Q.mem_space_iff.mp hx
      exact hs.2 hxs
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := P.mem_space_iff.mp (connectedComponentIn_subset _ _ hx)
      have hhull : convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N))) ⊆ A := by
        have h := (convex_convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))).isPreconnected
          |>.subset_connectedComponentIn hxs (P.convexHull_subset_space hs)
        simpa only [← connectedComponentIn_eq hx] using h
      exact Q.mem_space_iff.mpr ⟨s, ⟨hs, hhull⟩, hxs⟩
  refine ⟨Q, hP.subset (fun _ hs ↦ hs.1), ?_, ?_, ?_⟩
  · rw [hQA]
    exact isConnected_connectedComponentIn_iff.mpr (hCP hc)
  · rwa [hQA]
  · rw [hQA]
    exact connectedComponentIn_subset _ _

/-- Hatcher A.8, p.527: restrict the original Euclidean neighborhood retraction and compose with the inverse embedding. The composite on M is literally the identity. -/
private theorem restrict_neighborhood_retraction
    {M : Type*} [TopologicalSpace M] (N : ℕ)
    (e : M → EuclideanSpace ℝ (Fin N)) (hemb : Topology.IsEmbedding e)
    (U : Set (EuclideanSpace ℝ (Fin N))) (hCU : Set.range e ⊆ U)
    (r : C(U, ↥(Set.range e))) (hr : ∀ c : ↥(Set.range e),
      r ⟨c.val, hCU c.property⟩ = c)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (hCP : Set.range e ⊆ P.space) (hPU : P.space ⊆ U) :
    let K := ↥P.space
    ∃ (j : C(M, K)) (q : C(K, M)), ∀ x, q (j x) = x := by
  let j : C(M, ↥P.space) :=
    ⟨fun x ↦ ⟨e x, hCP (Set.mem_range_self x)⟩, hemb.continuous.subtype_mk _⟩
  let eC := hemb.toHomeomorph
  let kU : C(↥P.space, U) := ContinuousMap.inclusion hPU
  let q : C(↥P.space, M) := (⟨eC.symm, eC.symm.continuous⟩ : C(↥(Set.range e), M)).comp (r.comp kU)
  refine ⟨j, q, fun x ↦ ?_⟩
  change eC.symm (r ⟨e x, hPU (hCP (Set.mem_range_self x))⟩) = x
  have hh := hr ⟨e x, Set.mem_range_self x⟩
  exact (congrArg eC.symm hh).trans (eC.symm_apply_apply x)

/-- Hatcher A.8, p.527: mapping a loop through j and then q returns the original loop, including the exact basepoint cast. Thus q induces a surjection. -/
private theorem retract_fundamentalGroup_map_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (j : C(X, Y)) (q : C(Y, X)) (h : ∀ x, q (j x) = x) (x : X) :
    Function.Surjective (FundamentalGroup.mapOfEq q (h x)) := by
  intro a
  refine ⟨FundamentalGroup.map j x a, ?_⟩
  rw [FundamentalGroup.mapOfEq_apply]
  change ((a.toPath.map j).map q).cast (h x).symm (h x).symm = a
  rw [← Path.Homotopic.Quotient.map_comp]
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
    change Path.Homotopic.Quotient.mk
      ((p.map (q.comp j).continuous).cast (h x).symm (h x).symm) =
        Path.Homotopic.Quotient.mk p
    congr 1
    ext t
    exact h (p t)

/-- Hatcher A.8, p.527: the surjective induced map carries any finite generating set to a generating set of the original fundamental group. -/
private theorem retract_fundamentalGroup_fg
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (j : C(X, Y)) (q : C(Y, X)) (h : ∀ x, q (j x) = x) (x : X)
    [Group.FG (FundamentalGroup Y (j x))] : Group.FG (FundamentalGroup X x) :=
  Group.fg_of_surjective (retract_fundamentalGroup_map_surjective j q h x)

/-- Place a compact embedded space in the standard simplex using bounded affine
barycentric coordinates. This is the large-simplex step of Hatcher A.8, p.527,
performed before subdivision, so no geometric complex is pushed through a map. -/
private theorem compact_embedding_in_standard_simplex
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (N : ℕ) (e : M → EuclideanSpace ℝ (Fin N))
    (he : Continuous e) (hi : Function.Injective e) :
    ∃ f : M → EuclideanSpace ℝ (Fin (N + 1)),
      Continuous f ∧ Topology.IsClosedEmbedding f ∧
        Set.range f ⊆ BarycentricGeometry.euclideanSimplex N := by
  classical
  obtain ⟨R, hR, hbound⟩ := (isCompact_range he).isBounded.exists_pos_norm_le
  let D : ℝ := (N + 1) * (2 * R)
  have hD : 0 < D := by dsimp [D]; positivity
  let w : M → Fin N → ℝ := fun x i ↦ (e x i + R) / D
  have hw : ∀ x i, 0 ≤ w x i := by
    intro x i
    apply div_nonneg _ hD.le
    have hh := (PiLp.norm_apply_le (e x) i).trans (hbound _ (Set.mem_range_self x))
    have hh' : |e x i| ≤ R := by simpa only [Real.norm_eq_abs] using hh
    linarith [abs_le.mp hh']
  have hsum : ∀ x, ∑ i, w x i ≤ 1 := by
    intro x
    have hwi : ∀ i, e x i + R ≤ 2 * R := by
      intro i
      have hh := (PiLp.norm_apply_le (e x) i).trans (hbound _ (Set.mem_range_self x))
      have hh' : |e x i| ≤ R := by simpa only [Real.norm_eq_abs] using hh
      linarith [(abs_le.mp hh').2]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hwi i)
    change (∑ i, (e x i + R) / D) ≤ 1
    rw [← Finset.sum_div, div_le_one hD]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    dsimp [D]
    nlinarith
  let f : M → EuclideanSpace ℝ (Fin (N + 1)) := fun x ↦
    WithLp.toLp 2 (Fin.cons (1 - ∑ i, w x i) (w x))
  have hcw : Continuous w := by
    apply continuous_pi
    intro i
    exact (((PiLp.continuous_apply 2 _ i).comp he).add continuous_const).div_const D
  have hcf : Continuous f := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact continuous_const.sub (continuous_finsetSum _ (fun j _ ↦ (continuous_apply j).comp hcw))
    · exact (continuous_apply j).comp hcw
  have hif : Function.Injective f := by
    intro x y hxy
    apply hi
    ext i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (N + 1)) ↦ z i.succ) hxy
    change (e x i + R) / D = (e y i + R) / D at hi
    exact add_right_cancel ((div_left_inj' (ne_of_gt hD)).mp hi)
  refine ⟨f, hcf, hcf.isClosedEmbedding hif, ?_⟩
  rintro z ⟨x, rfl⟩
  let weights : Fin (N + 1) → ℝ := Fin.cons (1 - ∑ i, w x i) (w x)
  let t : Convexity.StdSimplex ℝ (Fin (N + 1)) :=
    { weights := Finsupp.equivFunOnFinite.symm weights
      nonneg := by
        intro i
        change 0 ≤ weights i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact sub_nonneg.mpr (hsum x)
        · exact hw x j
      total := by
        rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
        change ∑ i, weights i = 1
        simp [weights, Fin.sum_univ_succ] }
  exact ⟨t, rfl⟩

/-- Hatcher A.7 and A.8 (pp.525–527): construct the actual finite connected
simplicial retract. Compactness puts an injective affine normalization of the
Whitney embedding in the standard simplex. Arbitrarily fine standard subdivisions
cover it. Keep every face of each simplex meeting the compact image, then keep
its connected component. Restrict the original neighborhood retraction; the maps
remain continuous in the original Euclidean subtype topology and compose to id. -/
private theorem closed_manifold_finite_simplicial_retract
    (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [Nonempty M] :
    ∃ (N : ℕ) (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      P.faces.Finite ∧ IsConnected P.space ∧
      ∃ (j : C(M, ↥P.space)) (q : C(↥P.space, M)), ∀ x, q (j x) = x := by
  classical
  obtain ⟨N, e₀, he₀, hemb₀, _⟩ := exists_embedding_euclidean_of_compact
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (M := M)
  obtain ⟨e, he, hemb, hsimplex⟩ :=
    compact_embedding_in_standard_simplex N e₀ he₀.continuous hemb₀.injective
  have hC : IsCompact (Set.range e) := isCompact_range he
  have hconn : IsConnected (Set.range e) := isConnected_range he
  let eC : M ≃ₜ ↥(Set.range e) := hemb.toIsEmbedding.toHomeomorph
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) ↥(Set.range e) := eC.chartedSpace
  obtain ⟨U, hCU, hU, r, hr⟩ :=
    compact_locally_contractible_neighborhood_retract (N+1) (Set.range e) hC
      (fun c O hO hc ↦ charted_real_weakly_locally_contractible
        (E := EuclideanSpace ℝ (Fin n)) c O hO hc)
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_thickening_subset_open hU hCU
  have hbuffer : ∀ c ∈ Set.range e, Metric.ball c δ ⊆ U := by
    intro c hc x hx
    exact hthick (Metric.mem_thickening_iff.mpr ⟨c, hc, hx⟩)
  obtain ⟨_, _, _, hsubdiv⟩ := BarycentricGeometry.singular_barycentric_subdivision_geometry N
  have hsmall : ∃ P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin (N+1))),
      P.faces.Finite ∧ Set.range e ⊆ P.space ∧
      ∀ s ∈ P.faces, Metric.diam (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin (N+1))))) < δ := by
    by_cases hN : N = 0
    · obtain ⟨P, _, hfin, hspace, _, _, _, hzero, _⟩ := hsubdiv 0
      refine ⟨P, hfin, hspace.symm ▸ hsimplex, ?_⟩
      intro s hs
      rw [hzero hN s hs]
      exact hδ
    · let ρ : ℝ := N / ((N : ℝ) + 1)
      have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
      have hρ1 : ρ < 1 := by
        dsimp [ρ]
        exact (div_lt_one (by positivity)).mpr (by linarith)
      have ht : Filter.Tendsto
          (fun k : ℕ ↦ ρ ^ k * Metric.diam (BarycentricGeometry.euclideanSimplex N))
          Filter.atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const
          (Metric.diam (BarycentricGeometry.euclideanSimplex N))
      obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
      obtain ⟨P, _, hfin, hspace, _, _, hmesh, _⟩ := hsubdiv k
      refine ⟨P, hfin, hspace.symm ▸ hsimplex, ?_⟩
      intro s hs
      exact (hmesh (Nat.pos_of_ne_zero hN) s hs).trans_lt hk
  obtain ⟨P, hfin, hCP, hmesh⟩ := hsmall
  obtain ⟨Q, hQfin, _, hCQ, hQU⟩ :=
    finite_subcomplex_neighborhood (N+1) P hfin (Set.range e) U hCP δ hbuffer hmesh
  obtain ⟨R, hRfin, hRconn, hCR, hRQ⟩ :=
    finite_connected_subcomplex (N+1) Q hQfin (Set.range e) hconn hCQ
  obtain ⟨j, q, hjq⟩ := restrict_neighborhood_retraction (N+1) e hemb.toIsEmbedding
    U hCU r hr R hCR (hRQ.trans hQU)
  exact ⟨N+1, R, hRfin, hRconn, j, q, hjq⟩

/-- Adapter from the original parent/depth incidence data to Mathlib simplicity.
This is an agent-written interface proof of the loop/parallel exclusions in Hatcher 1A.1. -/
theorem rooted_restricted_graph_simple
    {V E : Type*} (G : Graph V E) (r : V) (d : V → ℕ)
    (parent : {v : V // v ≠ r} → V) (edge : {v : V // v ≠ r} → E)
    (hlink : ∀ v, G.IsLink (edge v) v.val (parent v))
    (hdepth : ∀ v, d (parent v) + 1 = d v.val) :
    (G.restrict (Set.range edge)).Simple := by
  have levels : ∀ {e x y}, (G.restrict (Set.range edge)).IsLink e x y →
      ∃ v, edge v = e ∧ ((x = v.val ∧ y = parent v) ∨
        (y = v.val ∧ x = parent v)) := by
    rintro e x y ⟨⟨v, hv⟩, hl⟩
    refine ⟨v, hv, ?_⟩
    have h := hl.eq_and_eq_or_eq_and_eq (hv ▸ hlink v)
    tauto
  refine { not_isLoopAt := ?_, eq_of_isLink := ?_ }
  · intro e x h
    obtain ⟨v, _, h | h⟩ := levels h <;> have hd := hdepth v
    all_goals
      have hh : v.val = parent v := h.1.symm.trans h.2
      rw [← hh] at hd
      omega
  · intro e f x y he hf
    obtain ⟨v, hv, hve⟩ := levels he
    obtain ⟨w, hw, hwf⟩ := levels hf
    rcases hve with hve | hve <;> rcases hwf with hwf | hwf
    · have h : v = w := Subtype.ext (hve.1.symm.trans hwf.1)
      exact hv.symm.trans (h ▸ hw)
    · have hvd := hdepth v
      have hwd := hdepth w
      have hvw : v.val = parent w := hve.1.symm.trans hwf.2
      have hwv : w.val = parent v := hwf.1.symm.trans hve.2
      rw [← hwv] at hvd
      rw [← hvw] at hwd
      omega
    · have hvd := hdepth v
      have hwd := hdepth w
      have hvw : v.val = parent w := hve.1.symm.trans hwf.2
      have hwv : w.val = parent v := hwf.1.symm.trans hve.2
      rw [← hwv] at hvd
      rw [← hvw] at hwd
      omega
    · have h : v = w := Subtype.ext (hve.1.symm.trans hwf.1)
      exact hv.symm.trans (h ▸ hw)

/-- Original labelled edge arrays yield native simple-graph reachability. -/
theorem edgeWalk_reachable
    {V E : Type*} (G : Graph V E) [G.Loopless]
    (hall : G.vertexSet = Set.univ) {n : ℕ} {u v : V}
    (p : CWEdgeWalk G n u v) :
    G.toSimpleGraph.Reachable ⟨u, hall ▸ Set.mem_univ u⟩
      ⟨v, hall ▸ Set.mem_univ v⟩ := by
  induction n generalizing v with
  | zero =>
    have h := p.eq_of_zero
    subst v
    exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    have hp := ih p.init
    have hl := p.isLink (Fin.last n)
    rw [Fin.succ_last, p.last] at hl
    apply hp.trans
    apply SimpleGraph.Adj.reachable
    rw [Graph.toSimpleGraph_adj_iff]
    exact ⟨_, hl⟩

/-- The finite version of the spanning-tree interface: selected edges are indexed
by nonroot vertices, and connectedness gives the reverse edge-cardinality bound. -/
private theorem rooted_restricted_graph_tree
    {V E : Type*} [Finite V] (G : Graph V E) (r : V) (d : V → ℕ)
    (parent : {v : V // v ≠ r} → V) (edge : {v : V // v ≠ r} → E)
    (hlink : ∀ v, G.IsLink (edge v) v.val (parent v))
    (hdepth : ∀ v, d (parent v) + 1 = d v.val)
    (hall : (G.restrict (Set.range edge)).vertexSet = Set.univ)
    (hreach : ∀ u v, ∃ n, Nonempty (CWEdgeWalk (G.restrict (Set.range edge)) n u v)) :
    (G.restrict (Set.range edge)).toSimpleGraph.IsTree := by
  classical
  let H := G.restrict (Set.range edge)
  have : H.Simple := rooted_restricted_graph_simple G r d parent edge hlink hdepth
  have : Nonempty H.vertexSet := ⟨⟨r, hall ▸ Set.mem_univ r⟩⟩
  have hc : H.toSimpleGraph.Connected := by
    refine SimpleGraph.Connected.mk ?_
    intro u v
    obtain ⟨n, ⟨p⟩⟩ := hreach u v
    exact edgeWalk_reachable H hall p
  let verts (v : V) : H.vertexSet := ⟨v, hall ▸ Set.mem_univ v⟩
  have hadj (v : {v : V // v ≠ r}) : H.toSimpleGraph.Adj (verts v) (verts (parent v)) := by
    rw [Graph.toSimpleGraph_adj_iff]
    exact ⟨edge v, ⟨⟨v, rfl⟩, hlink v⟩⟩
  let f : {v : V // v ≠ r} → H.toSimpleGraph.edgeSet := fun v ↦
    ⟨s(verts v, verts (parent v)), (H.toSimpleGraph.mem_edgeSet).mpr (hadj v)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy := H.toSimpleGraph.mem_edgeSet.mp he
      rw [Graph.toSimpleGraph_adj_iff] at hxy
      obtain ⟨e, ⟨⟨v, hv⟩, hl⟩⟩ := hxy
      refine ⟨v, ?_⟩
      apply Subtype.ext
      have h := hl.eq_and_eq_or_eq_and_eq (hv ▸ hlink v)
      rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · apply Sym2.eq_iff.mpr
        exact Or.inl ⟨Subtype.ext hx.symm, Subtype.ext hy.symm⟩
      · apply Sym2.eq_iff.mpr
        exact Or.inr ⟨Subtype.ext hx.symm, Subtype.ext hy.symm⟩
  have hcard := Nat.card_le_card_of_surjective f hsurj
  have hV : Nat.card H.vertexSet = Nat.card V := by
    rw [hall]
    exact Nat.card_congr (Equiv.Set.univ V)
  have hnonroot : Nat.card {v : V // v ≠ r} + 1 = Nat.card V := by
    let _ := Fintype.ofFinite V
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
    omega
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hc, ?_⟩
  change Nat.card H.toSimpleGraph.edgeSet + 1 = Nat.card H.vertexSet
  have hlow := hc.card_vert_le_card_edgeSet_add_one
  omega


/-- The published oriented characteristic path stays in its selected closed cell. -/
private theorem linked_edge_path_in_subcomplex
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (T : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    {e : Topology.RelCWComplex.cell (Set.univ : Set X) 1}
    {v w : Topology.RelCWComplex.cell (Set.univ : Set X) 0}
    (hlink : ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict
      (T.I 1)).IsLink e v w) :
    ∃ p : Path (Topology.RelCWComplex.map 0 v 0) (Topology.RelCWComplex.map 0 w 0),
      ∀ t, p t ∈ (T : Set X) := by
  obtain ⟨σ, p, hσ, hp⟩ := cw_oriented_edge_path e v w hlink.2
  refine ⟨p, fun t ↦ T.closedCell_subset_of_mem hlink.1 ?_⟩
  refine ⟨(fun _ : Fin 1 ↦ σ * (2 * (t : ℝ) - 1)), ?_, (hp t).symm⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
  intro i
  rw [norm_mul, Real.norm_eq_abs σ]
  have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  rw [hs, one_mul, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [t.property.1, t.property.2]

/-- Realize a finite original-edge walk as a path in the same CW subcomplex. -/
private theorem edgeWalk_path_in_subcomplex
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)]
    (T : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (hT0 : T.I 0 = Set.univ)
    {n : ℕ} {u v : Topology.RelCWComplex.cell (Set.univ : Set X) 0}
    (p : CWEdgeWalk ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict
      (T.I 1)) n u v) :
    ∃ q : Path (Topology.RelCWComplex.map 0 u 0) (Topology.RelCWComplex.map 0 v 0),
      ∀ t, q t ∈ (T : Set X) := by
  induction n generalizing v with
  | zero =>
    have h := p.eq_of_zero
    subst v
    refine ⟨Path.refl _, fun _ ↦ ?_⟩
    apply T.closedCell_subset_of_mem (show u ∈ T.I 0 by rw [hT0]; trivial)
    exact ⟨0, by simp, rfl⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih p.init
    have hl := p.isLink (Fin.last n)
    rw [Fin.succ_last, p.last] at hl
    obtain ⟨s, hs⟩ := linked_edge_path_in_subcomplex T hl
    refine ⟨q.trans s, ?_⟩
    intro t
    have hm : (q.trans s) t ∈ Set.range q ∪ Set.range s := by
      rw [← Path.trans_range]
      exact ⟨t, rfl⟩
    rcases hm with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ha ▸ hq a
    · exact ha ▸ hs a

/-- Convert the published rooted CW tree into the exact certificates and root
paths consumed by the graph-loop generation theorem. No tree is reconstructed. -/
private theorem finite_cw_spanning_tree_graph_certificates
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.CWComplex.Finite (Set.univ : Set X)]
    (r : Topology.RelCWComplex.cell (Set.univ : Set X) 0) :
    ∃ T : Topology.CWComplex.Subcomplex (Set.univ : Set X),
      T.I 0 = Set.univ ∧
      ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict (T.I 1)).Simple ∧
      ((Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict
        (T.I 1)).toSimpleGraph.IsTree ∧
      ∃ q : ∀ v : Topology.RelCWComplex.cell (Set.univ : Set X) 0,
        Path (Topology.RelCWComplex.map 0 r 0)
        (Topology.RelCWComplex.map 0 v 0), ∀ v t, q v t ∈ (T : Set X) := by
  classical
  obtain ⟨d, parent, edge, T, _, _, hlink, hdepth, _, hall, _, hreach,
    _, _, hT0, hT1, _⟩ := cw_realization_spanning_tree r
  have : Finite (Topology.RelCWComplex.cell (Set.univ : Set X) 0) :=
    Topology.RelCWComplex.FiniteType.finite_cell 0
  refine ⟨T, hT0, ?_, ?_, ?_⟩
  · rw [hT1]
    exact rooted_restricted_graph_simple _ r d parent edge hlink hdepth
  · rw [hT1]
    exact rooted_restricted_graph_tree _ r d parent edge hlink hdepth hall hreach
  · have hp : ∀ v : Topology.RelCWComplex.cell (Set.univ : Set X) 0,
      ∃ q : Path (Topology.RelCWComplex.map 0 r 0)
        (Topology.RelCWComplex.map 0 v 0), ∀ t, q t ∈ (T : Set X) := by
      intro v
      obtain ⟨n, ⟨p⟩⟩ := hreach r v
      rw [← hT1] at p
      exact edgeWalk_path_in_subcomplex T hT0 p
    choose q hq using hp
    exact ⟨q, hq⟩

/-- Hatcher Proposition 1A.2, pp.84–85: finitely many specified loop
classes generate a finitely generated group when every class is a word in them.
The statement respects the original group multiplication; it needs no commutativity. -/
private theorem finite_word_generators_fg {G E : Type*} [Group G] [Finite E]
    (generator : E → G)
    (hword : ∀ a : G, ∃ word : List (E × Bool),
      a = (word.map (fun letter ↦
        if letter.2 then generator letter.1 else (generator letter.1)⁻¹)).prod) :
    Group.FG G := by
  classical
  apply Group.fg_iff.mpr
  refine ⟨Set.range generator, ?_, Set.finite_range _⟩
  apply top_unique
  intro a _
  obtain ⟨word, rfl⟩ := hword a
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨letter, _, rfl⟩ := List.mem_map.mp hx
  split
  · exact Subgroup.subset_closure (Set.mem_range_self _)
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self _))

/-- The finite graph case of Hatcher Proposition 1A.2, using original cell labels. -/
private theorem finite_one_dimensional_cw_pi1_fg
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    [Topology.CWComplex.Finite (Set.univ : Set X)]
    (hdim : ∀ n : ℕ, 1 < n → IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set X) n))
    (r : Topology.RelCWComplex.cell (Set.univ : Set X) 0) :
    Group.FG (FundamentalGroup X (Topology.RelCWComplex.map 0 r 0)) := by
  classical
  obtain ⟨T, hT0, hTsimple, hTtree, q, hq⟩ := finite_cw_spanning_tree_graph_certificates r
  have endpoints : ∀ e : Topology.RelCWComplex.cell (Set.univ : Set X) 1,
      ∃ u v, (Topology.CWComplex.OneSkeletonGraph (Set.univ : Set X)).IsLink e u v := by
    intro e
    exact Topology.CWComplex.exists_cellFrontier_one_eq e
  choose u v huv using endpoints
  have paths : ∀ e, ∃ (σ : ℝ) (p : Path (Topology.RelCWComplex.map 0 (u e) 0)
      (Topology.RelCWComplex.map 0 (v e) 0)), (σ = 1 ∨ σ = -1) ∧
        ∀ t : unitInterval, p t = Topology.RelCWComplex.map 1 e
          (fun _ ↦ σ * (2 * (t : ℝ) - 1)) :=
    fun e ↦ cw_oriented_edge_path e (u e) (v e) (huv e)
  choose σ p hσ hp using paths
  let rev : Topology.RelCWComplex.cell (Set.univ : Set X) 1 → Bool :=
    fun e ↦ decide (σ e = -1)
  have hpath : ∀ e t, p e t = Topology.RelCWComplex.map 1 e
      (fun _ ↦ if rev e then 1 - 2 * (t : ℝ) else 2 * (t : ℝ) - 1) := by
    intro e t
    rw [hp]
    congr 1
    funext i
    rcases hσ e with h | h <;> norm_num [rev, h]
  have : Finite (Topology.RelCWComplex.cell (Set.univ : Set X) 1) :=
    Topology.RelCWComplex.FiniteType.finite_cell 1
  have hwords := graph_spanning_tree_loop_generation hdim T hT0 hTsimple hTtree r
  have hz : (0 : Fin 0 → ℝ) = ![] := Subsingleton.elim _ _
  dsimp only at hwords
  rw [← hz] at hwords
  let generator : {e : Topology.RelCWComplex.cell (Set.univ : Set X) 1 // e ∉ T.I 1} →
      FundamentalGroup X (Topology.RelCWComplex.map 0 r 0) := fun e ↦
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((q (u e)).trans (p e)).trans (q (v e)).symm))
  exact finite_word_generators_fg generator (hwords u v rev p hpath q hq)

section SubtypeTransport

open _root_.Topology Set Metric

/-- Restrict a characteristic map to the actual CW carrier on its closed disk.
Outside that disk its total forward function uses the supplied carrier point. -/
private noncomputable def cwSubtypeMap
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C]
    (c0 : C) (n : ℕ) (i : RelCWComplex.cell C n) : PartialEquiv (Fin n → ℝ) C := by
  classical
  let f : (Fin n → ℝ) → C := fun z ↦
    if h : z ∈ closedBall 0 1 then
      ⟨RelCWComplex.map n i z, RelCWComplex.closedCell_subset_complex n i ⟨z, h, rfl⟩⟩
    else c0
  refine {
    toFun := f
    invFun := fun x ↦ (RelCWComplex.map n i).symm x.val
    source := ball 0 1
    target := Subtype.val ⁻¹' (RelCWComplex.map n i).target
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_ }
  · intro z hz
    have hc := ball_subset_closedBall hz
    simp only [mem_preimage, f, dite_eq_left hc]
    exact (RelCWComplex.map n i).map_source ((RelCWComplex.source_eq n i).symm ▸ hz)
  · intro x hx
    exact RelCWComplex.source_eq n i ▸ (RelCWComplex.map n i).map_target hx
  · intro z hz
    have hc := ball_subset_closedBall hz
    simp only [f, dite_eq_left hc]
    exact (RelCWComplex.map n i).left_inv ((RelCWComplex.source_eq n i).symm ▸ hz)
  · intro x hx
    have hz : (RelCWComplex.map n i).symm x.val ∈ closedBall 0 1 :=
      ball_subset_closedBall (RelCWComplex.source_eq n i ▸ (RelCWComplex.map n i).map_target hx)
    apply Subtype.ext
    simp only [f, dite_eq_left hz]
    exact (RelCWComplex.map n i).right_inv hx

private theorem cwSubtypeMap_coe
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C]
    (c0 : C) (n : ℕ) (i : RelCWComplex.cell C n)
    {z : Fin n → ℝ} (hz : z ∈ closedBall 0 1) :
    (cwSubtypeMap C c0 n i z).val = RelCWComplex.map n i z := by
  classical
  simp only [cwSubtypeMap, PartialEquiv.coe_mk, dite_eq_left hz]

private theorem cwSubtypeMap_image
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C]
    (c0 : C) (n : ℕ) (i : RelCWComplex.cell C n)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    cwSubtypeMap C c0 n i '' S =
      Subtype.val ⁻¹' ((RelCWComplex.map n i) '' S) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (cwSubtypeMap_coe C c0 n i (hS hz)).symm⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, Subtype.ext ((cwSubtypeMap_coe C c0 n i (hS hz)).trans hzx)⟩

/-- The finite classical CW structure transports to its literal subtype,
retaining the original cells and characteristic maps on every closed disk. -/
@[instance_reducible]
private noncomputable def finiteCWSubtype
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C] [CWComplex.Finite C]
    (c0 : C) : CWComplex (Set.univ : Set C) := by
  classical
  apply CWComplex.mkFinite Set.univ (RelCWComplex.cell C) (cwSubtypeMap C c0)
    (RelCWComplex.FiniteDimensional.eventually_isEmpty_cell)
    (RelCWComplex.FiniteType.finite_cell)
  · intro n i
    rfl
  · intro n i
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have h := (RelCWComplex.continuousOn n i).domRestrict
    convert h using 1
    funext z
    exact cwSubtypeMap_coe C c0 n i z.property
  · intro n i
    exact (RelCWComplex.continuousOn_symm n i).comp
      continuous_subtype_val.continuousOn (fun _ hx ↦ hx)
  · intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [cwSubtypeMap_image C c0 a.1 a.2 _ ball_subset_closedBall,
      cwSubtypeMap_image C c0 b.1 b.2 _ ball_subset_closedBall]
    exact (RelCWComplex.disjoint_openCell_of_ne hab).preimage _
  · intro n i z hz
    obtain ⟨J, hJ⟩ := CWComplex.mapsTo n i
    have hfront : RelCWComplex.map n i z ∈ ⋃ (m < n) (j : RelCWComplex.cell C m),
        RelCWComplex.closedCell m j := by
      have hh := hJ hz
      simp only [mem_iUnion] at hh ⊢
      obtain ⟨m, hm, j, _, hj⟩ := hh
      exact ⟨m, hm, j, hj⟩
    simp only [mem_iUnion] at hfront ⊢
    obtain ⟨m, hm, j, hj⟩ := hfront
    refine ⟨m, hm, j, ?_⟩
    rw [cwSubtypeMap_image C c0 m j _ (Subset.refl _)]
    change (cwSubtypeMap C c0 n i z).val ∈ RelCWComplex.closedCell m j
    rwa [cwSubtypeMap_coe C c0 n i (sphere_subset_closedBall hz)]
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hx : x.val ∈ ⋃ (n : ℕ) (j : RelCWComplex.cell C n), RelCWComplex.closedCell n j := by
      rw [CWComplex.union]
      exact x.property
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hn
    refine ⟨n, i, ?_⟩
    rw [cwSubtypeMap_image C c0 n i _ (Subset.refl _)]
    exact hi


private theorem finiteCWSubtype_finite
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C] [CWComplex.Finite C]
    (c0 : C) :
    letI := finiteCWSubtype C c0
    CWComplex.Finite (Set.univ : Set C) := by
  let := finiteCWSubtype C c0
  exact {
    eventually_isEmpty_cell := RelCWComplex.FiniteDimensional.eventually_isEmpty_cell (C := C)
    finite_cell := RelCWComplex.FiniteType.finite_cell (C := C) }

private theorem finiteCWSubtype_cell
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C] [CWComplex.Finite C]
    (c0 : C) (n : ℕ) :
    letI := finiteCWSubtype C c0
    RelCWComplex.cell (Set.univ : Set C) n = RelCWComplex.cell C n := rfl

private theorem finiteCWSubtype_characteristic
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C] [CWComplex.Finite C]
    (c0 : C) (n : ℕ) (i : RelCWComplex.cell C n) (z : Fin n → ℝ)
    (hz : z ∈ closedBall 0 1) :
    (letI := finiteCWSubtype C c0
     (RelCWComplex.map (C := (Set.univ : Set C)) n i z).val) =
       RelCWComplex.map n i z := cwSubtypeMap_coe C c0 n i hz

private theorem finiteCWSubtype_one_skeleton_dimension
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] [CWComplex.Finite (Set.univ : Set X)]
    (c0 : (CWComplex.skeletonLT (Set.univ : Set X) 2 : Set X)) :
    letI := finiteCWSubtype (CWComplex.skeletonLT (Set.univ : Set X) 2 : Set X) c0
    ∀ n, 1 < n → IsEmpty (RelCWComplex.cell
      (Set.univ : Set (CWComplex.skeletonLT (Set.univ : Set X) 2 : Set X)) n) := by
  intro n hn
  refine ⟨fun i ↦ ?_⟩
  have hi : (n : ℕ∞) < 2 := by
    simpa only [RelCWComplex.skeletonLT, RelCWComplex.Subcomplex.mk', Set.mem_ofPred_eq]
      using i.property
  have hge : (2 : ℕ∞) ≤ n := by exact_mod_cast hn
  exact (not_lt_of_ge hge) hi


/-- Every original one-skeleton point is joined to an original vertex inside
that literal subspace, by a characteristic closed-disk path. -/
private theorem one_skeleton_point_joined_vertex
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)]
    (x : (CWComplex.skeletonLT (Set.univ : Set X) 2 : Set X)) :
    ∃ v : RelCWComplex.cell (Set.univ : Set X) 0,
      JoinedIn (CWComplex.skeletonLT (Set.univ : Set X) 2 : Set X)
        (RelCWComplex.map 0 v 0) x.val := by
  let S := CWComplex.skeletonLT (Set.univ : Set X) 2
  have hhigh : ∀ n, IsEmpty (RelCWComplex.cell (S : Set X) (n + 2)) := by
    intro n
    refine ⟨fun i ↦ ?_⟩
    have hi : ((n + 2 : ℕ) : ℕ∞) < 2 := by
      simpa only [S, RelCWComplex.skeletonLT, RelCWComplex.Subcomplex.mk',
        mem_ofPred_eq] using i.property
    have hh : (2 : ℕ∞) ≤ n + 2 := by exact_mod_cast (show 2 ≤ n + 2 by omega)
    exact (not_lt_of_ge hh) hi
  rcases cw_one_dimensional_carrier_cases (S : Set X) hhigh x with ⟨v, hv⟩ | ⟨e, z, hz⟩
  · refine ⟨v.val, ?_⟩
    rw [hv]
    exact JoinedIn.refl (hv ▸ x.property)
  · obtain ⟨v, hv⟩ := cw_one_cell_boundary_is_vertex e.val
      (fun _ : Fin 1 ↦ (1 : ℝ)) (by simp)
    have hone : (fun _ : Fin 1 ↦ (1 : ℝ)) ∈ closedBall (0 : Fin 1 → ℝ) 1 := by
      simp [mem_closedBall, dist_zero_right]
    have hpath := ((convex_closedBall (0 : Fin 1 → ℝ) 1).isPathConnected
      ⟨_, hone⟩).joinedIn _ hone z.val z.property
    have himage := hpath.map (RelCWComplex.continuousOn 1 e.val)
    refine ⟨v, ?_⟩
    change x.val = RelCWComplex.map 1 e.val z.val at hz
    rw [hv, ← hz] at himage
    exact himage.mono (S.closedCell_subset_of_mem e.property)

/-- Connected original vertex walks and the closed-interval characteristic
paths make the literal one-skeleton path connected. -/
theorem one_skeleton_pathConnected
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)]
    (r : RelCWComplex.cell (Set.univ : Set X) 0) :
    PathConnectedSpace (CWComplex.skeletonLT (Set.univ : Set X) 2 : Set X) := by
  let S := CWComplex.skeletonLT (Set.univ : Set X) 2
  have hS0 : S.I 0 = Set.univ := by
    ext v
    simp [S, RelCWComplex.skeletonLT, RelCWComplex.Subcomplex.mk']
  have hS1 : S.I 1 = Set.univ := by
    ext e
    simp [S, RelCWComplex.skeletonLT, RelCWComplex.Subcomplex.mk']
  have hroot : RelCWComplex.map 0 r 0 ∈ (S : Set X) := by
    exact S.closedCell_subset_of_mem (hS0 ▸ Set.mem_univ r) ⟨0, by simp, rfl⟩
  apply isPathConnected_iff_pathConnectedSpace.mp
  refine ⟨RelCWComplex.map 0 r 0, hroot, ?_⟩
  intro x hx
  obtain ⟨v, hv⟩ := one_skeleton_point_joined_vertex ⟨x, hx⟩
  obtain ⟨n, a, b, ha, hb, hab⟩ := connected_cw_one_skeleton_finite_walk r v
  let p : CWEdgeWalk ((CWComplex.OneSkeletonGraph (Set.univ : Set X)).restrict
      (S.I 1)) n r v := {
    vertices := a, edges := b, first := ha, last := hb
    isLink := fun i ↦ ⟨hS1 ▸ Set.mem_univ (b i), hab i⟩ }
  exact JoinedIn.trans (edgeWalk_path_in_subcomplex S hS0 p) hv

/-- The finite graph generators map onto the actual fundamental group of the
ambient finite CW complex through its literal one-skeleton inclusion. -/
private theorem finite_cw_pi1_fg_at_vertex
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)] [CWComplex.Finite (Set.univ : Set X)]
    (r : RelCWComplex.cell (Set.univ : Set X) 0) :
    Group.FG (FundamentalGroup X (RelCWComplex.map 0 r 0)) := by
  let S := CWComplex.skeletonLT (Set.univ : Set X) 2
  have h0 : RelCWComplex.map 0 r 0 ∈
      (CWComplex.skeletonLT (Set.univ : Set X) 1 : Set X) := by
    exact RelCWComplex.closedCell_subset_skeletonLT 0 r ⟨0, by simp, rfl⟩
  have hmem : RelCWComplex.map 0 r 0 ∈ (S : Set X) :=
    CWComplex.skeletonLT_mono (show (1 : ℕ∞) ≤ 2 by decide) h0
  let r0 : (S : Set X) := ⟨RelCWComplex.map 0 r 0, hmem⟩
  let : CWComplex (Set.univ : Set (S : Set X)) := finiteCWSubtype (S : Set X) r0
  have : CWComplex.Finite (Set.univ : Set (S : Set X)) := finiteCWSubtype_finite _ r0
  have : PathConnectedSpace (S : Set X) := one_skeleton_pathConnected r
  let r1 : RelCWComplex.cell (Set.univ : Set (S : Set X)) 0 :=
    ⟨r, by simp [S, RelCWComplex.skeletonLT, RelCWComplex.Subcomplex.mk']⟩
  have heq : RelCWComplex.map (C := (Set.univ : Set (S : Set X))) 0 r1 0 = r0 := by
    apply Subtype.ext
    exact cwSubtypeMap_coe (S : Set X) r0 0 r1 (by simp)
  have hfg := finite_one_dimensional_cw_pi1_fg
    (finiteCWSubtype_one_skeleton_dimension r0) r1
  rw [heq] at hfg
  have hs := finite_cw_one_skeleton_pi1_surjective (RelCWComplex.map 0 r 0) h0
  exact Group.fg_of_surjective hs

end SubtypeTransport

/-- Hatcher's change-of-basepoint paths carry finite generating sets to the
same actual fundamental group at the requested point. -/
private theorem fundamentalGroup_fg_of_path {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) [Group.FG (FundamentalGroup X x)] :
    Group.FG (FundamentalGroup X y) :=
  Group.fg_of_surjective (G := FundamentalGroup X x)
    (f := (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom)
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p).surjective

/-- A nonempty closed connected smooth real manifold is a literal retract of a finite
connected geometric simplicial realization and has finitely generated fundamental group
at every original basepoint.

Source: Hatcher, *Algebraic Topology*, Theorem A.7 pp.525–527 and Corollaries
A.8–A.9 p.527, Proposition 1A.2 pp.84–85 and Proposition 1.26 pp.50–52.
Natural-language proof:

In dimension zero the manifold is discrete in its singleton charts. Connectedness
and nonemptiness make it a singleton. Take one vertex in the zero-dimensional
Euclidean space; the two maps are inverse, and constant loops give the trivial
fundamental group, generated by the empty set.

In positive dimension use the smooth Euclidean embedding of a compact manifold.
Its image C is compact, and the embedding identifies the original M homeomorphically
with C. Native convex coordinate balls give weak local contractibility by straight
line contraction. Transfer this to C and apply Hatcher A.7 to obtain an open
Euclidean neighborhood U of C and a continuous retraction r:U→C.

Place C inside the interior of a large simplex. Compactness gives a positive buffer
δ with the δ-neighborhood of C inside U (choose any positive δ when U is the whole
ambient space). Barycentric subdivision is finite, preserves realization and face
intersections, and makes the mesh arbitrarily small. In positive ambient dimension
its mesh decreases by the factor N/(N+1); the zero-dimensional simplex has mesh zero.
Choose mesh less than δ. Select all simplices meeting C and all their faces. Every
selected face is contained in a selected simplex meeting C, so its points have
distance less than δ from C. The selected geometric realization therefore lies in U
and contains C. Define j by the original embedding with this membership, and define
q by the restriction of r followed by the inverse embedding. Both are continuous
in the Euclidean subtype topology and q(j(m))=m exactly.

The finite incidence graph separates this finite simplicial complex into finitely
many connected subcomplexes: every simplex is in the component of its vertices,
each component union is closed, and its finite complementary union is closed.
Edge paths and straight simplex paths make these components path connected. The
nonempty connected C lies in one component. Keep that component and restrict j,q.
Its literal realization K retains the Euclidean subtype topology. Open simplices
and their proper-face characteristic boundaries give its classical CW structure;
finitely many faces give finitely many cells on this same structure.

Fix any original x₀∈M and k₀=j(x₀). Choose a vertex v of K. Its finite connected
one-skeleton has a spanning tree. The loops consisting of a tree path from v, a
complementary oriented edge, and the tree path back generate its fundamental group.
There are finitely many such edges. Attaching the remaining cells of dimension at
least two makes the induced map from the one-skeleton fundamental group surjective,
so these finitely many images generate π₁(K,v). A path from v to k₀ transports this
finite set to π₁(K,k₀).

The actual continuous maps j,q induce based homomorphisms, with q(k₀)=x₀ retained.
The literal identity q∘j=id sends each based loop back to itself, so q_*∘j_*=id on
π₁(M,x₀). Thus q_* is surjective. The images under q_* of the finite generating set
of π₁(K,k₀) generate π₁(M,x₀). This works for every x₀ in the original M. No
homotopy-retraction substitute, unspecified replacement group, triangulability
hypothesis, orientation, or standard smooth structure is used.
-/
theorem closed_manifold_finite_simplicial_retract_pi1_fg
    (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [Nonempty M] :
    ∃ (N : ℕ) (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
      P.faces.Finite ∧ IsConnected P.space ∧
      (let K := {x : EuclideanSpace ℝ (Fin N) // x ∈ P.space}
       ∃ cw : Topology.CWComplex (Set.univ : Set K),
         letI : Topology.CWComplex (Set.univ : Set K) := cw
         Topology.CWComplex.Finite (Set.univ : Set K) ∧
           ∃ (j : C(M, K)) (q : C(K, M)),
             (∀ x : M, q (j x) = x) ∧
               ∀ x₀ : M, Group.FG (FundamentalGroup M x₀)) := by
  obtain ⟨N, P, hP, hconn, j, q, hjq⟩ := closed_manifold_finite_simplicial_retract n M
  classical
  obtain ⟨cw, hcw, index, _⟩ := finite_geometric_simplicial_classical_cw.{0} N P hP
  let := cw
  let := hcw
  refine ⟨N, P, hP, hconn, cw, hcw, j, q, hjq, ?_⟩
  intro x
  suffices hfg : Group.FG (FundamentalGroup (↥P.space) (j x)) by
    let := hfg
    exact retract_fundamentalGroup_fg j q hjq x
  have : ConnectedSpace (↥P.space) := isConnected_iff_connectedSpace.mp hconn
  obtain ⟨s, hs, _⟩ := P.mem_space_iff.mp (j x).property
  obtain ⟨v, hv⟩ := P.nonempty_of_mem_faces hs
  have hface : ({v} : Finset (EuclideanSpace ℝ (Fin N))) ∈ P.faces :=
    P.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  let r : Topology.RelCWComplex.cell (Set.univ : Set (↥P.space)) 0 :=
    index 0 ⟨{v}, hface, by simp⟩
  have : Group.FG (FundamentalGroup (↥P.space) (Topology.RelCWComplex.map 0 r 0)) :=
    finite_cw_pi1_fg_at_vertex r
  have : PathConnectedSpace (↥P.space) :=
    cw_contractible_open_neighborhoods.2.2.2 inferInstance
  exact fundamentalGroup_fg_of_path
    (PathConnectedSpace.somePath (Topology.RelCWComplex.map 0 r 0) (j x))


end HolomorphicAnosov
