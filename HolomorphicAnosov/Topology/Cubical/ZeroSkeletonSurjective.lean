import HolomorphicAnosov.Topology.Cubical.RationalSingularHomologyInclusion
import HolomorphicAnosov.Topology.Cubical.SkeletonCarrierSubset
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.Convex.Basic

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.Cubical

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Hatcher, Algebraic Topology, Lemma 2.34(b), pp.137–139, degree zero.
Every point of a selected cell is joined inside that convex cell to its lower
vertex, which lies in the selected zero-skeleton by face closure. Thus its
zero-dimensional singular homology class lies in the image of the skeleton.
The zero-chain coproduct and the surjective homology projection show that these
point classes generate all of H₀, including an empty subcomplex. -/
theorem subcomplex_zero_skeleton_homology_surjective {N : ℕ}
    {K : FiniteRectilinearSubdivision N} (M : CubicalSubcomplex K) :
    Function.Surjective (rationalSingularHomologyInclusion
      (subcomplex_skeleton_subset_carrier M 0) 0) := by
  classical
  let X : TopCat := TopCat.of M.carrier
  let S : TopCat := TopCat.of (M.skeleton 0)
  let i : S ⟶ X := TopCat.ofHom
    (ContinuousMap.inclusion (subcomplex_skeleton_subset_carrier M 0))
  let R := ModuleCat.of ℚ ℚ
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 0).obj R
  let C := (TopCat.toSSet.obj X).chainComplex R
  let P := LinearMap.range (F.map i).hom
  let π : C.homology 0 ⟶ ModuleCat.of ℚ (_ ⧸ P) := ModuleCat.ofHom P.mkQ
  have hi : F.map i ≫ π = 0 := by
    ext y : 2
    exact (Submodule.Quotient.mk_eq_zero P).mpr ⟨y, rfl⟩
  have hπ : π = 0 := by
    apply (cancel_epi (C.homologyπ 0)).mp
    apply (cancel_epi C.cycles₀Iso.inv).mp
    apply SSet.chainComplex_hom_ext
    intro s
    let s₀ : SimplexCategory.toTop.obj (SimplexCategory.mk 0) ⟶ X := s.down
    let x : X := s₀ default
    obtain ⟨c, hc, hx⟩ : ∃ c ∈ M.cells, x.val ∈ c.carrier := by
      have h := x.property
      change x.val ∈ M.carrier at h
      simp only [CubicalSubcomplex.carrier, Set.mem_iUnion] at h
      obtain ⟨c, hc, hx⟩ := h
      exact ⟨c, hc, hx⟩
    let v : ClosedCoordinateCell N := ⟨c.lower, c.lower, le_rfl⟩
    have hvface : ClosedCoordinateCell.IsFace v c := fun _ ↦ Or.inr (Or.inl ⟨rfl, rfl⟩)
    have hv : c.lower ∈ M.skeleton 0 := by
      simp only [CubicalSubcomplex.skeleton, Set.mem_iUnion]
      refine ⟨v, M.faces c hc v hvface, ?_, ?_⟩
      · simp [v, ClosedCoordinateCell.dimension]
      · exact ⟨le_rfl, le_rfl⟩
    let Y : TopCat := TopCat.of c.carrier
    let j : Y ⟶ X := TopCat.ofHom ⟨fun z ↦ ⟨z.val,
      Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, z.property⟩⟩⟩,
      continuous_subtype_val.subtype_mk _⟩
    let r : Y ⟶ S := TopCat.ofHom (ContinuousMap.const _ ⟨c.lower, hv⟩)
    let H : TopCat.Homotopy (r ≫ i) j := {
      toFun := fun z ↦ ⟨(1 - (z.1 : ℝ)) • c.lower + (z.1 : ℝ) • z.2.val,
        Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc,
          (convex_Icc c.lower c.upper : Convex ℝ c.carrier)
            (show c.lower ∈ c.carrier from ⟨le_rfl, c.lower_le_upper⟩)
            z.2.property (sub_nonneg.mpr z.1.property.2) z.1.property.1
            (sub_add_cancel _ _)⟩⟩⟩
      continuous_toFun := (((continuous_const.sub
          (continuous_subtype_val.comp continuous_fst)).smul continuous_const).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := fun z ↦ by
        apply Subtype.ext
        change (1 - (0 : ℝ)) • c.lower + (0 : ℝ) • z.val = c.lower
        simp
      map_one_left := fun z ↦ by
        apply Subtype.ext
        change (1 - (1 : ℝ)) • c.lower + (1 : ℝ) • z.val = z.val
        simp }
    have hj : F.map j ≫ π = 0 := by
      have hH : F.map (r ≫ i) = F.map j :=
        H.congr_homologyMap_singularChainComplexFunctor R 0
      rw [← hH, F.map_comp, Category.assoc, hi, comp_zero]
    let t : (TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk 0)) :=
      ⟨TopCat.ofHom (ContinuousMap.const _ ⟨x.val, hx⟩)⟩
    have ht : (TopCat.toSSet.map j).app _ t = s := by
      apply ULift.ext
      change t.down ≫ j = s₀
      ext a : 1
      change x = s₀ a
      exact congrArg s₀ (Subsingleton.elim _ _)
    let D := (TopCat.toSSet.obj Y).chainComplex R
    let k := D.liftCycles ((TopCat.toSSet.obj Y).ιChainComplex t) 0
      (by simp) (by simp)
    have he : C.cycles₀Iso.inv = C.liftCycles (𝟙 _) 0 (by simp) (by simp) := by
      apply (cancel_mono (C.iCycles 0)).mp
      simp
    rw [he]
    simp only [comp_zero]
    rw [← Category.assoc, ← Category.assoc, HomologicalComplex.comp_liftCycles]
    have hn : k ≫ D.homologyπ 0 ≫ F.map j =
        C.liftCycles ((TopCat.toSSet.obj X).ιChainComplex s) 0 (by simp) (by simp) ≫
          C.homologyπ 0 := by
      change k ≫ D.homologyπ 0 ≫ HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map j) R) 0 = _
      rw [HomologicalComplex.homologyπ_naturality,
        ← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
      simp only [SSet.ι_chainComplexMap_f, ht]
      rfl
    rw [Category.comp_id, ← hn, Category.assoc, Category.assoc, hj, comp_zero, comp_zero]
  intro z
  have hz : z ∈ P := (Submodule.Quotient.mk_eq_zero P).mp
    (congrArg (fun f : C.homology 0 ⟶ ModuleCat.of ℚ (_ ⧸ P) ↦ f z) hπ)
  exact hz

end HolomorphicAnosov.Cubical
