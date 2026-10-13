import HolomorphicAnosov.Topology.Cubical.RationalSingularHomologyInclusion
import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision
import HolomorphicAnosov.Topology.Cubical.CellCarrierSubsetSkeleton

/-!
# Vertex generators for the zero skeleton

Source: Hatcher, *Algebraic Topology*, Lemma 2.34(a), printed pp.137–138,
zero-dimensional case.  The ordinary rational H₀ of the finite zero skeleton
is spanned by the inclusion images of its zero-cell carriers.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.Cubical

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The carriers of all zero-dimensional cells span rational H₀ of the finite
cubical zero skeleton.

Source: Hatcher, Algebraic Topology, Lemma 2.34(a), pp.137–138, degree zero.
Proof: quotient H₀ by the displayed span. The quotient map vanishes on every
cell inclusion by definition. Every singular zero-simplex is a point of the
zero-skeleton, hence lies in one of its zero-dimensional cells and lifts to a
zero-simplex of that cell. Naturality of the cycle and homology projections
therefore makes its class zero in the quotient. Zero-chains are the coproduct
of their simplex summands and every zero-chain is a cycle. Surjectivity of the
homology projection now forces the quotient map to vanish, so the span is all
of H₀. This also covers an empty skeleton and ambient dimension zero. -/
theorem cubical_zero_vertex_span (K : FiniteRectilinearSubdivision N) :
    Submodule.span ℚ
      (⋃ c, ⋃ hc : c ∈ K.cells, ⋃ hd : c.dimension = 0,
        Set.range (rationalSingularHomologyInclusion
          (cell_carrier_subset_skeleton K 0 c hc (by omega)) 0)) = ⊤ := by
  classical
  let X : TopCat := TopCat.of (K.skeleton 0)
  let R := ModuleCat.of ℚ ℚ
  let C := (TopCat.toSSet.obj X).chainComplex R
  let P : Submodule ℚ (rationalSingularHomology (K.skeleton 0) 0) :=
    Submodule.span ℚ
      (⋃ c, ⋃ hc : c ∈ K.cells, ⋃ hd : c.dimension = 0,
        Set.range (rationalSingularHomologyInclusion
          (cell_carrier_subset_skeleton K 0 c hc (by omega)) 0))
  let q : C.homology 0 ⟶ ModuleCat.of ℚ (_ ⧸ P) := ModuleCat.ofHom P.mkQ
  have hq : q = 0 := by
    apply (cancel_epi (C.homologyπ 0)).mp
    apply (cancel_epi C.cycles₀Iso.inv).mp
    apply SSet.chainComplex_hom_ext
    intro s
    let s₀ : SimplexCategory.toTop.obj (SimplexCategory.mk 0) ⟶ X := s.down
    let x : X := s₀ default
    obtain ⟨c, hc, hd, hx⟩ : ∃ c ∈ K.cells, ∃ hd : c.dimension ≤ 0,
        (x : Fin N → ℝ) ∈ c.carrier := by
      have h := x.property
      change (x : Fin N → ℝ) ∈ K.skeleton 0 at h
      simp only [FiniteRectilinearSubdivision.skeleton, Set.mem_iUnion] at h
      obtain ⟨c, hc, hd, hx⟩ := h
      exact ⟨c, hc, hd, hx⟩
    let Y : TopCat := TopCat.of c.carrier
    let i : Y ⟶ X := TopCat.ofHom (ContinuousMap.inclusion
      (cell_carrier_subset_skeleton K 0 c hc hd))
    let t : (TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk 0)) :=
      ⟨TopCat.ofHom (ContinuousMap.const _ ⟨x.val, hx⟩)⟩
    have ht : (TopCat.toSSet.map i).app _ t = s := by
      apply ULift.ext
      change t.down ≫ i = s₀
      ext a : 1
      change x = s₀ a
      exact congrArg s₀ (Subsingleton.elim _ _)
    let D := (TopCat.toSSet.obj Y).chainComplex R
    let k := D.liftCycles ((TopCat.toSSet.obj Y).ιChainComplex t) 0
      (by simp) (by simp)
    have him : rationalSingularHomologyInclusion
        (cell_carrier_subset_skeleton K 0 c hc hd) 0 ≫ q = 0 := by
      ext y : 2
      apply (Submodule.Quotient.mk_eq_zero P).mpr
      exact Submodule.subset_span (by
        simp only [Set.mem_iUnion, Set.mem_range]
        exact ⟨c, hc, Nat.eq_zero_of_le_zero hd, y, rfl⟩)
    have he : C.cycles₀Iso.inv = C.liftCycles (𝟙 _) 0 (by simp) (by simp) := by
      apply (cancel_mono (C.iCycles 0)).mp
      simp
    rw [he]
    simp only [comp_zero]
    rw [← Category.assoc, ← Category.assoc, HomologicalComplex.comp_liftCycles]
    have hn : k ≫ D.homologyπ 0 ≫
        rationalSingularHomologyInclusion
          (cell_carrier_subset_skeleton K 0 c hc hd) 0 =
        C.liftCycles ((TopCat.toSSet.obj X).ιChainComplex s) 0 (by simp) (by simp) ≫
          C.homologyπ 0 := by
      change k ≫ D.homologyπ 0 ≫ HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map i) R) 0 = _
      rw [HomologicalComplex.homologyπ_naturality,
        ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
      simp only [SSet.ι_chainComplexMap_f, ht]
      rfl
    rw [Category.comp_id]
    rw [← hn, Category.assoc, Category.assoc, him, comp_zero,
      comp_zero]
  apply Submodule.eq_top_iff'.mpr
  intro z
  apply (Submodule.Quotient.mk_eq_zero P).mp
  exact congrArg (fun f : C.homology 0 ⟶ ModuleCat.of ℚ (_ ⧸ P) => f z) hq

end HolomorphicAnosov.Cubical

