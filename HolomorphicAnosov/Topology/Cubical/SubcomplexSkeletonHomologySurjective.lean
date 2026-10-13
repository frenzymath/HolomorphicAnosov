import HolomorphicAnosov.Topology.Homology.SphereHighDegreeG15
import HolomorphicAnosov.Topology.Cubical.SkeletonStepHomology
import HolomorphicAnosov.Topology.Cubical.SkeletonFiltrationSurjective
import HolomorphicAnosov.Topology.Cubical.ZeroSkeletonSurjective
import HolomorphicAnosov.Topology.Cubical.SubcomplexCWStructureG15

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.Topology
open HolomorphicAnosov.CharacteristicCellComparison
namespace HolomorphicAnosov.Cubical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

lemma subcomplex_skeleton_step_surjective_of_disk {N : ℕ}
    (K : FiniteRectilinearSubdivision N) (M : CubicalSubcomplex K)
    (c0 : M.carrier) (m q : ℕ)
    (hz : IsZero ((singularSubspacePair (TopCat.of (CellDisk.{0} (m + 1)))
      (cellBoundary (m + 1))).homology (ModuleCat.of ℚ ℚ) q)) :
    Function.Surjective (rationalSingularHomologyInclusion
      (subcomplex_skeleton_monotone M (Nat.le_succ m)) q) := by
  obtain ⟨cw, hfinite, _, hs⟩ := cubical_subcomplex_cw_structure K M
  let := cw
  let := hfinite
  let := cwCarrierStructureG6 M.carrier c0
  let := cwCarrier_finite M.carrier c0
  have hsk (n : ℕ) :
      (CWComplex.skeleton (Set.univ : Set M.carrier) n : Set M.carrier) =
        Subtype.val ⁻¹' M.skeleton n := by
    rw [cwCarrier_skeleton_eq M.carrier c0 n, hs n]
  let e (n : ℕ) : Skeleton M.carrier n ≃ₜ M.skeleton n := {
    toFun := fun x ↦ ⟨x.val.val,
      (congrArg (fun S : Set M.carrier ↦ x.val ∈ S) (hsk n)).mp x.property⟩
    invFun := fun x ↦ ⟨⟨x.val, subcomplex_skeleton_subset_carrier M n x.property⟩,
      (congrArg (fun S : Set M.carrier ↦
        (⟨x.val, subcomplex_skeleton_subset_carrier M n x.property⟩ : M.carrier) ∈ S)
        (hsk n)).mpr x.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let ei (n : ℕ) : TopCat.of (Skeleton M.carrier n) ≅ TopCat.of (M.skeleton n) :=
    TopCat.isoOfHomeo (e n)
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
    (ModuleCat.of ℚ ℚ)
  have heq : TopCat.ofHom (ContinuousMap.inclusion
      (subcomplex_skeleton_monotone M (Nat.le_succ m))) =
      (ei m).inv ≫ skeletonStepInclusion M.carrier m ≫ (ei (m + 1)).hom := by
    ext x : 1
    rfl
  have := skeletonStep_homology_epi M.carrier m (ModuleCat.of ℚ ℚ) q hz
  change Function.Surjective (F.map _)
  rw [heq, F.map_comp, F.map_comp]
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The q-skeleton of a finite cubical subcomplex surjects onto its rational
q-homology through the literal embedded inclusion. Hatcher Lemma 2.34(b),
pp.137–139: degree zero is represented by vertices; in positive degree each
higher cell pair has zero relative homology, hence each skeletal step is epic.
Compose the finite steps up to the N-skeleton, which equals the carrier. -/
theorem cubical_subcomplex_skeleton_homology_surjective
    {N : ℕ} (K : FiniteRectilinearSubdivision N)
    (M : CubicalSubcomplex K) (q : ℕ) :
    ∃ hM : M.skeleton q ⊆ M.carrier,
      Function.Surjective (rationalSingularHomologyInclusion hM q) := by
  refine ⟨subcomplex_skeleton_subset_carrier M q, ?_⟩
  by_cases hq0 : q = 0
  · subst q
    exact subcomplex_zero_skeleton_homology_surjective M
  have hfull (n : ℕ) (hn : N ≤ n) : M.skeleton n = M.carrier := by
    apply Set.Subset.antisymm (subcomplex_skeleton_subset_carrier M n)
    intro x hx
    simp only [CubicalSubcomplex.carrier, Set.mem_iUnion] at hx
    obtain ⟨c, hc, hcx⟩ := hx
    simp only [CubicalSubcomplex.skeleton, Set.mem_iUnion]
    refine ⟨c, hc, ?_, hcx⟩
    apply le_trans ?_ hn
    simpa [ClosedCoordinateCell.dimension] using
      ({i : Fin N | c.lower i < c.upper i}.ncard_le_card)
  by_cases hs : M.skeleton q = M.carrier
  ·
    let e : TopCat.of (M.skeleton q) ≅ TopCat.of M.carrier := {
      hom := TopCat.ofHom {
        toFun := fun x ↦ ⟨x.val, hs ▸ x.property⟩
        continuous_toFun := continuous_subtype_val.subtype_mk _ }
      inv := TopCat.ofHom {
        toFun := fun x ↦ ⟨x.val, hs.symm ▸ x.property⟩
        continuous_toFun := continuous_subtype_val.subtype_mk _ }
      hom_inv_id := by ext x; rfl
      inv_hom_id := by ext x; rfl }
    let F := AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q
    have heq : TopCat.ofHom (ContinuousMap.inclusion
        (subcomplex_skeleton_subset_carrier M q)) = e.hom := by
      apply TopCat.hom_ext
      ext x
      rfl
    change Function.Surjective ((F.obj (ModuleCat.of ℚ ℚ)).map
      (TopCat.ofHom (ContinuousMap.inclusion
        (subcomplex_skeleton_subset_carrier M q)))).hom
    rw [heq]
    have : IsIso ((F.obj (ModuleCat.of ℚ ℚ)).map e.hom) :=
      (F.obj (ModuleCat.of ℚ ℚ)).mapIso e |>.isIso_hom
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.2
  · have hne : Nonempty M.carrier := by
      by_contra h
      apply hs
      apply Set.Subset.antisymm (subcomplex_skeleton_subset_carrier M q)
      intro x hx
      exact (h ⟨⟨x, hx⟩⟩).elim
    obtain ⟨c0⟩ := hne
    have hqN : q ≤ N := by
      by_contra h
      exact hs (hfull q (by omega))
    have hsteps := subcomplex_skeleton_homology_surjective_of_steps M q N hqN
      (fun m hm _ ↦ subcomplex_skeleton_step_surjective_of_disk K M c0 m q
        (cellDisk_low_degree_rational (m + 1) q (by omega)))
    have hN := hfull N le_rfl
    have hex : ∃ h : M.skeleton q ⊆ M.skeleton N,
        Function.Surjective (rationalSingularHomologyInclusion h q) := ⟨_, hsteps⟩
    rw [hN] at hex
    exact hex.choose_spec

end HolomorphicAnosov.Cubical
