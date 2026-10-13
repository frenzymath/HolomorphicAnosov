import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.InnerBallHomeomorph
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SkeletonCollarStrongDeformationRetraction
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCollar.SourceCollarDeformationLaws
import HolomorphicAnosov.Topology.Homology.RelativeHomologyMapIsoCoefficients
import HolomorphicAnosov.Topology.SingularHomologyExcision
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

open Set CategoryTheory CategoryTheory.Limits _root_.Topology
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace HolomorphicAnosov.CharacteristicCellComparison

lemma singularHomology_map_isIso_of_retract {X Y : TopCat.{0}}
    (i : X ⟶ Y) (r : Y ⟶ X) (hri : i ≫ r = 𝟙 X)
    (H : TopCat.Homotopy (𝟙 Y) (r ≫ i)) (R : ModuleCat ℚ) (n : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj R).map i) := by
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj R
  have hH : F.map (𝟙 Y) = F.map (r ≫ i) :=
    H.congr_homologyMap_singularChainComplexFunctor R n
  refine ⟨F.map r, ?_, ?_⟩
  · rw [← F.map_comp, hri, F.map_id]
  · rw [← F.map_comp, ← hH, F.map_id]

lemma rational_excision_homology_isIso (X : TopCat.{0}) (A B : Set X)
    (hcover : interior A ∪ interior B = univ) (R : ModuleCat ℚ) (n : ℕ) :
    IsIso (SSetPair.homologyMap (singularExcisionInclusion X A B) R n) := by
  obtain ⟨e, he⟩ := excision_source_equiv_of_small X A B R
    (NativeBarycentricOperators.smallRelativeHomotopyEquiv.{0,0} X A B hcover R) rfl
  have hh : (e.toHomologyIso n).hom =
      SSetPair.homologyMap (singularExcisionInclusion X A B) R n := by
    change HomologicalComplex.homologyMap e.hom n = _
    rw [he]
  rw [← hh]
  infer_instance

lemma singularSubspacePairMap_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Set X) (B : Set Y) (C : Set Z) (hf : MapsTo f A B) (hg : MapsTo g B C) :
    singularSubspacePairMap f A B hf ≫ singularSubspacePairMap g B C hg =
      singularSubspacePairMap (f ≫ g) A C (hg.comp hf) := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
    rw [← Functor.map_comp]
    rfl
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
    rw [← Functor.map_comp]

lemma singularSubspacePairMap_id (X : TopCat.{0}) (A : Set X) (h : MapsTo (𝟙 X) A A) :
    singularSubspacePairMap (𝟙 X) A A h = 𝟙 _ := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ = 𝟙 _
    convert TopCat.toSSet.map_id (TopCat.of A) using 1
    congr 1
  · exact TopCat.toSSet.map_id X

lemma singularPairHomology_map_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Set X) (B : Set Y) (C : Set Z) (hf : MapsTo f A B) (hg : MapsTo g B C)
    (R : ModuleCat ℚ) (n : ℕ) :
    SSetPair.homologyMap (singularSubspacePairMap f A B hf) R n ≫
      SSetPair.homologyMap (singularSubspacePairMap g B C hg) R n =
      SSetPair.homologyMap (singularSubspacePairMap (f ≫ g) A C (hg.comp hf)) R n := by
  change (SSetPair.homologyFunctor R n).map _ ≫ (SSetPair.homologyFunctor R n).map _ = _
  rw [← Functor.map_comp, singularSubspacePairMap_comp]
  rfl

lemma singularPairHomology_map_isIso_homeomorph {X Y : TopCat.{0}}
    (e : X ≃ₜ Y) (A : Set X) (B : Set Y) (he : ∀ x, e x ∈ B ↔ x ∈ A)
    (R : ModuleCat ℚ) (n : ℕ) :
    IsIso (SSetPair.homologyMap (singularSubspacePairMap
      (TopCat.ofHom ⟨e, e.continuous⟩) A B (fun x hx ↦ (he x).mpr hx)) R n) := by
  let f := TopCat.ofHom ⟨e, e.continuous⟩
  let g := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  let hf : MapsTo f A B := fun x hx ↦ (he x).mpr hx
  let hg : MapsTo g B A := fun y hy ↦ (he (e.symm y)).mp (by simpa using hy)
  let E : singularSubspacePair X A ≅ singularSubspacePair Y B := {
    hom := singularSubspacePairMap f A B hf
    inv := singularSubspacePairMap g B A hg
    hom_inv_id := by
      rw [singularSubspacePairMap_comp]
      have hfg : f ≫ g = 𝟙 X := by ext x; exact e.symm_apply_apply x
      simp only [hfg, singularSubspacePairMap_id]
    inv_hom_id := by
      rw [singularSubspacePairMap_comp]
      have hgf : g ≫ f = 𝟙 Y := by ext y; exact e.apply_symm_apply y
      simp only [hgf, singularSubspacePairMap_id] }
  exact ((SSetPair.homologyFunctor R n).mapIso E).isIso_hom

lemma singularPair_enlargement_homology_isIso (X : TopCat.{0}) {A U : Set X}
    (hAU : A ⊆ U) (r : C(U, A))
    (hr : ∀ a : A, r ⟨a.val, hAU a.property⟩ = a)
    (H : (ContinuousMap.id U).Homotopy ((ContinuousMap.inclusion hAU).comp r))
    (R : ModuleCat ℚ) (n : ℕ) :
    IsIso (SSetPair.homologyMap
      (singularSubspacePairMap (𝟙 X) A U hAU) R n) := by
  apply relative_homologyMap_isIso_of_absolute_coefficients
  · intro k
    change IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj R).map
      (singularSubspaceMap (𝟙 X) A U hAU))
    apply singularHomology_map_isIso_of_retract _ (TopCat.ofHom r)
    · ext a : 1
      exact hr a
    · exact H
  · intro k
    change IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj R).map (𝟙 X))
    rw [CategoryTheory.Functor.map_id]
    infer_instance

/-- Hatcher, Algebraic Topology, Lemma 2.34(a), pp.137–138: excising the lower
skeleton collar identifies the adjacent skeleton pair with the disjoint union
of characteristic disk pairs. The two collar inclusions are homology
isomorphisms by explicit strong deformation retractions. On the complementary
inner balls the characteristic map is a homeomorphism preserving the collars.
Excision and the commuting inclusion squares therefore identify the actual
characteristic map on relative homology as an isomorphism. -/
theorem characteristic_relative_homology_isIso
    (X : Type) [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]
    [CWComplex.Finite (univ : Set X)] (m : ℕ) (R : ModuleCat ℚ) (n : ℕ) :
    let D := TopCat.of (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{0} m)
    let S : Set D := {z | z.2 ∈ cellBoundary m}
    let Φ : D ⟶ TopCat.of (Skeleton X m) := TopCat.ofHom
      ⟨fun z ↦ characteristicCell X m z.1 z.2,
        continuous_sigma fun i ↦ (characteristicCell X m i).continuous⟩
    IsIso (SSetPair.homologyMap (singularSubspacePairMap Φ S (lowerSkeleton X m)
      (fun z hz ↦ characteristicCell_mapsTo X m z.1 hz)) R n) := by
  dsimp only
  let D : TopCat := TopCat.of (Σ _i : RelCWComplex.cell (univ : Set X) m, CellDisk.{0} m)
  let S : Set D := {z | z.2 ∈ cellBoundary m}
  let Z := TopCat.of (Skeleton X m)
  let A : Set Z := lowerSkeleton X m
  let U0 : Set D := {z | (1 / 2 : ℝ) < ‖z.2.down.1‖}
  let V0 : Set D := {z | ‖z.2.down.1‖ < (3 / 4 : ℝ)}
  let U : Set Z := skeletonCollar X m
  let V : Set Z := innerBallImage X m
  let Φ : D ⟶ Z := TopCat.ofHom
    ⟨fun z ↦ characteristicCell X m z.1 z.2,
      continuous_sigma fun i ↦ (characteristicCell X m i).continuous⟩
  have hΦ : MapsTo Φ S A := fun z hz ↦ characteristicCell_mapsTo X m z.1 hz
  have hU0 : IsOpen U0 := by
    rw [isOpen_sigma_iff]
    intro i
    exact isOpen_lt continuous_const ((continuous_subtype_val.comp continuous_uliftDown).norm)
  have hV0 : IsOpen V0 := by
    rw [isOpen_sigma_iff]
    intro i
    exact isOpen_lt ((continuous_subtype_val.comp continuous_uliftDown).norm) continuous_const
  have hc0 : interior U0 ∪ interior V0 = univ := by
    rw [hU0.interior_eq, hV0.interior_eq]
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : (1 / 2 : ℝ) < ‖z.2.down.1‖
    · exact Or.inl hz
    · exact Or.inr (by dsimp [V0]; linarith)
  have hgeom := innerBallImage_geometry X m
  have hc : interior U ∪ interior V = univ := by
    rw [(isOpen_skeletonCollar X m).interior_eq, hgeom.2.2.1.interior_eq]
    exact hgeom.2.2.2
  have hΦU : MapsTo Φ U0 U := fun z hz ↦ Or.inr ⟨⟨z.1, ⟨z.2, hz⟩⟩, rfl⟩
  have hΦV : MapsTo Φ V0 V := fun z hz ↦ ⟨z.1, z.2, hz, rfl⟩
  let f : TopCat.of V0 ⟶ TopCat.of V := singularSubspaceMap Φ V0 V hΦV
  have hf : MapsTo f {z : V0 | z.val ∈ U0} {z : V | z.val ∈ U} :=
    fun z hz ↦ hΦU hz
  let b := singularSubspacePairMap Φ U0 U hΦU
  let a := singularSubspacePairMap f {z : V0 | z.val ∈ U0} {z : V | z.val ∈ U} hf
  have ha : IsIso (SSetPair.homologyMap a R n) := by
    obtain ⟨e, he, heU, _⟩ := characteristic_innerBall_homeomorph X m
    have heq : TopCat.ofHom ⟨e, e.continuous⟩ = f := by
      ext z : 1
      exact Subtype.ext (he z)
    have H := singularPairHomology_map_isIso_homeomorph
      (X := TopCat.of V0) (Y := TopCat.of V) e
      {z : V0 | z.val ∈ U0} {z : V | z.val ∈ U} heU R n
    dsimp only [a]
    convert H using 1; congr 2
    exact heq.symm
  have hb : IsIso (SSetPair.homologyMap b R n) := by
    change IsIso ((SSetPair.homologyFunctor R n).map b)
    have e0 : IsIso ((SSetPair.homologyFunctor R n).map (singularExcisionInclusion D U0 V0)) :=
      rational_excision_homology_isIso D U0 V0 hc0 R n
    have eZ : IsIso ((SSetPair.homologyFunctor R n).map (singularExcisionInclusion Z U V)) :=
      rational_excision_homology_isIso Z U V hc R n
    have ha' : IsIso ((SSetPair.homologyFunctor R n).map a) := ha
    have hsquare : singularExcisionInclusion D U0 V0 ≫ b =
        a ≫ singularExcisionInclusion Z U V := by
      apply MorphismProperty.Arrow.Hom.ext
      · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
          TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl
      · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
          TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl
    have hsq := congrArg ((SSetPair.homologyFunctor R n).map) hsquare
    simp only [Functor.map_comp] at hsq
    have : IsIso ((SSetPair.homologyFunctor R n).map (singularExcisionInclusion D U0 V0) ≫
        (SSetPair.homologyFunctor R n).map b) := by
      rw [hsq]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((SSetPair.homologyFunctor R n).map (singularExcisionInclusion D U0 V0)) _
  have hSU : S ⊆ U0 := by
    intro z hz
    have hn : ‖z.2.down.1‖ = 1 := by
      simpa only [S, cellBoundary, Set.mem_ofPred_eq, Metric.mem_sphere,
        dist_zero_right] using hz
    change (1 / 2 : ℝ) < ‖z.2.down.1‖
    rw [hn]
    norm_num
  have hAU : A ⊆ U := fun _ hx ↦ Or.inl hx
  let c0 := singularSubspacePairMap (𝟙 D) S U0 hSU
  let cZ := singularSubspacePairMap (𝟙 Z) A U hAU
  have hc0iso : IsIso (SSetPair.homologyMap c0 R n) := by
    apply singularPair_enlargement_homology_isIso D hSU (sourceBoundaryRetraction X m)
    · intro z
      apply Subtype.ext
      have hz := (sourceCollarDeformation_laws X m ⟨z.val, hSU z.property⟩).2
      exact hz.1.symm.trans (congrArg Subtype.val (hz.2 1 z.property))
    · exact {
        toFun := sourceCollarDeformation X m
        continuous_toFun := (sourceCollarDeformation X m).continuous
        map_zero_left := fun z ↦ (sourceCollarDeformation_laws X m z).1
        map_one_left := fun z ↦ Subtype.ext (sourceCollarDeformation_laws X m z).2.1 }
  have hcZiso : IsIso (SSetPair.homologyMap cZ R n) := by
    obtain ⟨_, r, hr, ⟨H⟩⟩ := skeletonCollar_strongDeformationRetraction X m
    exact singularPair_enlargement_homology_isIso Z hAU r hr H.toHomotopy R n
  have hc0iso' : IsIso ((SSetPair.homologyFunctor R n).map c0) := hc0iso
  have hcZiso' : IsIso ((SSetPair.homologyFunctor R n).map cZ) := hcZiso
  have hb' : IsIso ((SSetPair.homologyFunctor R n).map b) := hb
  have hsquare : c0 ≫ b = singularSubspacePairMap Φ S A hΦ ≫ cZ := by
    dsimp only [c0, cZ, b]
    rw [singularSubspacePairMap_comp, singularSubspacePairMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  have hsq := congrArg ((SSetPair.homologyFunctor R n).map) hsquare
  simp only [Functor.map_comp] at hsq
  have : IsIso ((SSetPair.homologyFunctor R n).map (singularSubspacePairMap Φ S A hΦ) ≫
      (SSetPair.homologyFunctor R n).map cZ) := by
    rw [← hsq]
    infer_instance
  change IsIso ((SSetPair.homologyFunctor R n).map (singularSubspacePairMap Φ S A hΦ))
  exact IsIso.of_isIso_comp_right _ ((SSetPair.homologyFunctor R n).map cZ)

end HolomorphicAnosov.CharacteristicCellComparison
