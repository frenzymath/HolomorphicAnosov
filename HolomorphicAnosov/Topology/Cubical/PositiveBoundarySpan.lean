import HolomorphicAnosov.Topology.Cubical.RelativeBoundarySpan
import HolomorphicAnosov.Topology.Cubical.SkeletonStepInjective
import HolomorphicAnosov.Topology.Cubical.SubcomplexCWStructureG15
import HolomorphicAnosov.Topology.Cubical.FullSkeletonCarrier
import HolomorphicAnosov.Topology.Cubical.RationalSingularHomologyInclusion
import HolomorphicAnosov.Topology.Homology.ContractibleSingularHomology
import Mathlib.Analysis.Convex.Contractible

noncomputable section
open Set CategoryTheory CategoryTheory.Limits _root_.Topology
open HolomorphicAnosov.CharacteristicCellComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace HolomorphicAnosov.Cubical

private theorem cube_cw_skeleton_eq {N : ℕ} (K : FiniteRectilinearSubdivision N)
    [CWComplex K.cube.carrier]
    (index : ∀ n, {c : ClosedCoordinateCell N // c ∈ K.cells ∧ c.dimension = n} ≃
      RelCWComplex.cell K.cube.carrier n)
    (hcells : ∀ n c, RelCWComplex.closedCell (C := K.cube.carrier) n (index n c) =
      c.val.carrier ∧ RelCWComplex.openCell (C := K.cube.carrier) n (index n c) =
      c.val.openCarrier) (q : ℕ) :
    (CWComplex.skeleton K.cube.carrier (q : ℕ∞) : Set (Fin N → ℝ)) = K.skeleton q := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (CWComplex.skeleton K.cube.carrier (q : ℕ∞) : Set (Fin N → ℝ)) := hx
    obtain ⟨n, hnq, i, hxi⟩ := (CWComplex.mem_skeleton_iff (C := K.cube.carrier) (n := (q : ℕ∞)) (x := x)).mp hx'
    obtain ⟨csub, hi⟩ := (index n).surjective i
    rcases csub with ⟨c, hc, hdim⟩
    rw [← hi] at hxi
    have hbox := (hcells n ⟨c, hc, hdim⟩).2
    rw [hbox] at hxi
    rw [FiniteRectilinearSubdivision.skeleton]
    refine mem_iUnion.mpr ⟨c, ?_⟩
    refine mem_iUnion.mpr ⟨hc, ?_⟩
    exact mem_iUnion.mpr ⟨le_trans (le_of_eq hdim) (by exact_mod_cast hnq), hxi.1⟩
  · intro hx
    rw [FiniteRectilinearSubdivision.skeleton] at hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨c, hc, hdim, hxi⟩ := hx
    obtain ⟨a, haface, hxa⟩ := c.exists_face_mem_openCarrier hxi
    have hadim : a.dimension ≤ q := le_trans (ClosedCoordinateCell.IsFace.dimension_le haface) hdim
    let i : RelCWComplex.cell K.cube.carrier a.dimension :=
      (index a.dimension) ⟨a, K.faces c hc a haface, rfl⟩
    have hbox := (hcells a.dimension ⟨a, K.faces c hc a haface, rfl⟩).2
    have hopen : x ∈ CWComplex.openCell a.dimension i := by
      rw [hbox]
      exact hxa
    exact (CWComplex.mem_skeleton_iff (C := K.cube.carrier) (n := (q : ℕ∞)) (x := x)).mpr
      ⟨a.dimension, by exact_mod_cast hadim, i, hopen⟩

private theorem cube_cw_boundary_mem {N : ℕ} (K : FiniteRectilinearSubdivision N)
    [CWComplex K.cube.carrier] (n : ℕ) (i : RelCWComplex.cell K.cube.carrier n)
    (c : ClosedCoordinateCell N)
    (hc : RelCWComplex.closedCell (C := K.cube.carrier) n i = c.carrier)
    (ho : RelCWComplex.openCell (C := K.cube.carrier) n i = c.openCarrier)
    (z : Fin n → ℝ) (hz : z ∈ Metric.sphere 0 1) :
    RelCWComplex.map n i z ∈ c.carrier ∧ ∃ j,
      c.lower j < c.upper j ∧ (RelCWComplex.map n i z j = c.lower j ∨
        RelCWComplex.map n i z j = c.upper j) := by
  have hf : RelCWComplex.map n i z ∈ RelCWComplex.cellFrontier n i := ⟨z, hz, rfl⟩
  have hcar : RelCWComplex.map n i z ∈ c.carrier :=
    hc ▸ RelCWComplex.cellFrontier_subset_closedCell n i hf
  have hnot : RelCWComplex.map n i z ∉ c.openCarrier := by
    rw [← ho]
    exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeletonLT_openCell
      (C := K.cube.carrier) (j := i) (le_refl (n : ℕ∞)))
      (RelCWComplex.cellFrontier_subset_skeletonLT n i hf)
  refine ⟨hcar, ?_⟩
  by_contra! hn
  apply hnot
  refine ⟨hcar, fun j hj ↦ ?_⟩
  have hne := hn j hj
  have hl := hcar.1 j
  have hu := hcar.2 j
  constructor <;> grind

/-- The oriented boundaries of all (q+1)-cells span the rational q-homology of
an original finite cubical q-skeleton when `0 < q < N`.

Source: Hatcher, Algebraic Topology, Lemma 2.34 and Theorem 2.35, pp.137–141.
Use the finite CW structure on the original coordinate cells. The outer cube
is contractible, and all attaching cells above dimension q+1 preserve H_q
injectively; hence the (q+1)-skeleton has zero H_q. Characteristic excision and
the finite disjoint-union chain decomposition generate its relative homology
by the disk pairs. Exactness and naturality of the connecting map then generate
H_q of the lower skeleton by the characteristic boundary maps. Each such map
factors through the literal boundary of its original coordinate cell: the
sphere maps into the closed cell and misses its open cell, so an active
coordinate is an endpoint. The subtype homeomorphism to K.skeleton q transports
the resulting spanning family to precisely the inclusions in the statement. -/
theorem cubical_positive_boundary_span
    (N : ℕ) (_hN : 1 ≤ N) (K : FiniteRectilinearSubdivision N)
    (q : ℕ) (hq : q ≤ N) (hqpos : 0 < q) (hqtop : q ≠ N) :
    let _S := K.skeleton q
    let _boundary := fun c : ClosedCoordinateCell N ↦
      {x : Fin N → ℝ | x ∈ c.carrier ∧ ∃ i : Fin N,
        c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)}
    Submodule.span ℚ
      (⋃ c, ⋃ hc : c ∈ K.cells, ⋃ hd : c.dimension = q + 1,
        Set.range (rationalSingularHomologyInclusion
          (cell_boundary_subset_skeleton K q c hc hd) q)) = ⊤ := by
  classical
  obtain ⟨cw, hfinite, index, hcells⟩ := finiteSubdivision_cwStructure K
  let := cw
  let := hfinite
  let X := K.cube.carrier
  let c0 : X := ⟨K.cube.lower, le_rfl, K.cube.lower_le_upper⟩
  have hs := cube_cw_skeleton_eq K index hcells
  let := cwCarrierStructureG6 K.cube.carrier c0
  let := cwCarrier_finite K.cube.carrier c0
  have hsk (n : ℕ) : (CWComplex.skeleton (univ : Set X) n : Set X) =
      Subtype.val ⁻¹' K.skeleton n := by
    rw [cwCarrier_skeleton_eq K.cube.carrier c0 n, hs n]
  have hfull : (CWComplex.skeletonLT (univ : Set X) (N + 1) : Set X) = univ := by
    change (CWComplex.skeleton (univ : Set X) N : Set X) = univ
    rw [hsk, full_skeleton_eq_cube_carrier]
    ext x
    simp only [mem_preimage, mem_univ, iff_true]
    exact x.property
  have hsub (n : ℕ) : K.skeleton n ⊆ K.cube.carrier := by
    intro x hx
    rw [← K.cover]
    obtain ⟨c, hc, hd, hx⟩ := by simpa only [FiniteRectilinearSubdivision.skeleton,
      mem_iUnion] using hx
    exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hc, hx⟩⟩
  let e (n : ℕ) : Skeleton X n ≃ₜ K.skeleton n := {
    toFun := fun x ↦ ⟨x.val.val,
      (congrArg (fun S : Set X ↦ x.val ∈ S) (hsk n)).mp x.property⟩
    invFun := fun x ↦ ⟨⟨x.val, hsub n x.property⟩,
      (congrArg (fun S : Set X ↦ (⟨x.val, hsub n x.property⟩ : X) ∈ S)
        (hsk n)).mpr x.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
    (ModuleCat.of ℚ ℚ)
  have hconv : Convex ℝ K.cube.carrier := convex_Icc _ _
  let : ContractibleSpace X := hconv.contractibleSpace ⟨c0.val, c0.property⟩
  have hzX := singular_homology_isZero_of_contractible (TopCat.of X)
    (ModuleCat.of ℚ ℚ) q (by omega)
  have hz := skeleton_homology_isZero_of_full X (q + 1) N q (by omega)
    (by omega) hfull hzX
  have hb := characteristic_boundary_homology_span X (q + 1) q rfl hz
  let ei : TopCat.of (lowerSkeleton X (q + 1)) ≅ TopCat.of (K.skeleton q) :=
    TopCat.isoOfHomeo ((lowerSkeletonHomeomorph X q).trans (e q))

  let boundary (c : ClosedCoordinateCell N) :=
    {x : Fin N → ℝ | x ∈ c.carrier ∧ ∃ j : Fin N,
      c.lower j < c.upper j ∧ (x j = c.lower j ∨ x j = c.upper j)}
  let I := RelCWComplex.cell (univ : Set X) (q + 1)
  let cell (i : I) := (index (q + 1)).symm i
  have hbound (i : I) (z : cellBoundary (q + 1)) :
      ((characteristicCell X (q + 1) i z.val).val).val ∈ boundary (cell i).val := by
    change (cwCarrierMapG6 K.cube.carrier c0 (q + 1) i z.val.down.val).val ∈ _
    rw [cwCarrierMapG6_coe K.cube.carrier c0 (q + 1) i z.val.down.property]
    apply cube_cw_boundary_mem K (q + 1) i (cell i).val
    · simpa only [cell, Equiv.apply_symm_apply] using (hcells (q + 1) (cell i)).1
    · simpa only [cell, Equiv.apply_symm_apply] using (hcells (q + 1) (cell i)).2
    · exact z.property
  let b (i : I) := singularSubspaceMap (TopCat.ofHom (characteristicCell X (q + 1) i))
    (cellBoundary (q + 1)) (lowerSkeleton X (q + 1)) (characteristicCell_mapsTo X (q + 1) i)
  let β (i : I) : TopCat.of (cellBoundary (q + 1)) ⟶ TopCat.of (boundary (cell i).val) :=
    TopCat.ofHom ⟨fun z ↦ ⟨((characteristicCell X (q + 1) i z.val).val).val,
      hbound i z⟩,
      (((characteristicCell X (q + 1) i).continuous.comp continuous_subtype_val).subtype_val).subtype_val.subtype_mk _⟩
  let inc (i : I) : TopCat.of (boundary (cell i).val) ⟶ TopCat.of (K.skeleton q) :=
    TopCat.ofHom (ContinuousMap.inclusion
      (cell_boundary_subset_skeleton K q (cell i).val (cell i).property.1 (cell i).property.2))
  have hcomp (i : I) : b i ≫ ei.hom = β i ≫ inc i := by
    ext z : 1
    rfl
  let W : Submodule ℚ ↥(F.obj (TopCat.of (K.skeleton q))) := Submodule.span ℚ
    (⋃ c, ⋃ hc : c ∈ K.cells, ⋃ hd : c.dimension = q + 1,
      Set.range (rationalSingularHomologyInclusion
        (cell_boundary_subset_skeleton K q c hc hd) q))
  have hle : Submodule.span ℚ (⋃ i : I, Set.range (F.map (b i))) ≤
      W.comap (F.map ei.hom).hom := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨i, y, rfl⟩ := mem_iUnion.mp hx
    change F.map ei.hom (F.map (b i) y) ∈ W
    have he := congrArg (fun g ↦ g y) (congrArg F.map (hcomp i))
    rw [F.map_comp, F.map_comp] at he
    change F.map ei.hom (F.map (b i) y) = F.map (inc i) (F.map (β i) y) at he
    rw [he]
    exact Submodule.subset_span (mem_iUnion.mpr ⟨(cell i).val, mem_iUnion.mpr
      ⟨(cell i).property.1, mem_iUnion.mpr ⟨(cell i).property.2, F.map (β i) y, rfl⟩⟩⟩)
  have hb' : Submodule.span ℚ (⋃ i : I, Set.range (F.map (b i))) = ⊤ := hb
  rw [hb'] at hle
  apply top_unique
  intro x hx
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (F.map ei.hom)).mp inferInstance x
  exact hle Submodule.mem_top

end HolomorphicAnosov.Cubical

