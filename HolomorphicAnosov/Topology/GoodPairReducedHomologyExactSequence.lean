import HolomorphicAnosov.Topology.CollapseAugmentedHomologyNaturality
import HolomorphicAnosov.Topology.GoodPairCollapseSingularPairMap
import HolomorphicAnosov.Topology.GoodPairCollapseMorphism
import HolomorphicAnosov.Topology.GoodPairComplementHomeomorphism
import HolomorphicAnosov.Topology.GoodPairDeformationRelativeAcyclicity
import HolomorphicAnosov.Topology.GoodPairNeighborhoodQuotientImage
import HolomorphicAnosov.Topology.GoodPairQuotientHomotopyDescentG8
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Reduced integral homology exact sequence of a good pair. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set
open scoped ZeroObject
open scoped Simplicial

namespace HolomorphicAnosov.GoodPair

universe u

/-- The homology class represented by a cycle in the canonical kernel/image model of homology. (Hatcher) -/
def integralChainCycleClass (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ)
    (c : LinearMap.ker (K.sc n).g.hom) : K.homology n :=
  (K.sc n).moduleCatHomologyIso.inv ((K.sc n).moduleCatLeftHomologyData.π c)

/-- Enlarge the distinguished subspace while keeping the original ambient space. (Hatcher, Prop. 2.22) -/
def singularPairEnlargement (X : TopCat.{u}) {A V : Set X} (hAV : A ⊆ V) :
    singularSubspacePair X A ⟶ singularSubspacePair X V :=
  singularSubspacePairMap (𝟙 X) A V hAV

/-- Relative acyclicity forces the native absolute inclusion map to be an isomorphism. (Hatcher, Thm 2.16) -/
theorem pair_inclusion_homology_isIso_of_relative_zero
    (P : SSetPair.{u}) (R : ModuleCat.{u} ℤ)
    (hzero : ∀ n : ℕ, IsZero (P.homology R n)) (n : ℕ) :
    IsIso (SSet.homologyMap P.hom R n) := by
  have := (P.homology_exact₁ R (n + 1) n).mono_g ((hzero (n + 1)).eq_of_src _ _)
  have := (P.homology_exact₂ R n).epi_f ((hzero n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Identify the nested subspace in `(V,A)` with the original subspace `A`. The resulting absolute homology isomorphism is the left component of the enlargement map. (Hatcher, Prop. 2.22) -/
theorem enlargement_left_homology_isIso_of_relative_zero
    (X : TopCat.{u}) (A V : Set X) (hAV : A ⊆ V) (R : ModuleCat.{u} ℤ)
    (hzero : ∀ n : ℕ, IsZero
      ((singularSubspacePair (TopCat.of V) (fun v : V ↦ v.val ∈ A)).homology R n)) (n : ℕ) :
    IsIso (SSet.homologyMap (singularPairEnlargement X hAV).left R n) := by
  let B : Set V := fun x ↦ x.val ∈ A
  let e : A ≃ₜ B := {
    toFun := fun a ↦ ⟨⟨a.val, hAV a.property⟩, a.property⟩
    invFun := fun b ↦ ⟨b.val.val, b.property⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let E : TopCat.of A ≅ TopCat.of B := TopCat.isoOfHomeo e
  have heq : (singularPairEnlargement X hAV).left =
      TopCat.toSSet.map E.hom ≫ TopCat.toSSet.map (singularSubspaceInclusion (TopCat.of V) B) := by
    change TopCat.toSSet.map _ = TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp]
    rfl
  rw [heq]
  change IsIso (SSet.homologyMap (TopCat.toSSet.map E.hom ≫
    TopCat.toSSet.map (singularSubspaceInclusion (TopCat.of V) B)) R n)
  rw [SSet.homologyMap_comp]
  have : IsIso (SSet.homologyMap (TopCat.toSSet.map E.hom) R n) :=
    ((SSet.homologyFunctor R n).mapIso (TopCat.toSSet.mapIso E)).isIso_hom
  have : IsIso (SSet.homologyMap
      (TopCat.toSSet.map (singularSubspaceInclusion (TopCat.of V) B)) R n) :=
    pair_inclusion_homology_isIso_of_relative_zero
      (singularSubspacePair (TopCat.of V) B) R hzero n
  infer_instance

/-- Apply the deformation-relative acyclicity theorem to the left component of the upper enlargement. (Hatcher, Prop. 2.22) -/
theorem enlargement_left_homology_isIso_of_deformation
    (X : TopCat.{u}) (A V : Set X) (hAV : A ⊆ V)
    (d : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSet.homologyMap (singularPairEnlargement X hAV).left R n) := by
  apply enlargement_left_homology_isIso_of_relative_zero X A V hAV R
  intro m
  exact HolomorphicAnosov.Topology.Homotopy.good_pair_deformation_relative_acyclicity
    d (ModuleCat.{u} ℤ) R m

/-- Compare the native short exact pair chain sequences. -/
theorem pair_homologyMap_isIso_of_component_isos
    {P Q : SSetPair.{u}} (f : P ⟶ Q) (R : ModuleCat.{u} ℤ)
    (hl : ∀ n : ℕ, IsIso (SSet.homologyMap f.left R n))
    (hr : ∀ n : ℕ, IsIso (SSet.homologyMap f.right R n)) (n : ℕ) :
    IsIso (SSetPair.homologyMap f R n) := by
  let φ : P.chainComplexShortComplex R ⟶ Q.chainComplexShortComplex R := {
    τ₁ := ((SSetPair.chainComplexFunctorLeft (ModuleCat.{u} ℤ)).obj R).map f
    τ₂ := ((SSetPair.chainComplexFunctorRight (ModuleCat.{u} ℤ)).obj R).map f
    τ₃ := SSetPair.chainComplexMap f R
    comm₁₂ := ((SSetPair.chainComplexFunctorLeftToRight (ModuleCat.{u} ℤ)).app R).naturality f
    comm₂₃ := ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality f }
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ
    (P.shortExact_chainComplexShortComplex R) (Q.shortExact_chainComplexShortComplex R) n
  · change Epi (SSet.homologyMap f.left R n)
    have := hl n
    exact IsIso.epi_of_iso _
  · exact hr n
  · intro j _
    exact hl j
  · intro j _
    change Mono (SSet.homologyMap f.right R j)
    have := hr j
    exact IsIso.mono_of_iso _

/-- Acyclicity of `(V,A)` makes the enlargement of pairs invertible on homology. (Hatcher, Prop. 2.22) -/
theorem enlargement_homology_isIso_of_relative_zero
    (X : TopCat.{u}) (A V : Set X) (hAV : A ⊆ V) (R : ModuleCat.{u} ℤ)
    (hzero : ∀ n : ℕ, IsZero
      ((singularSubspacePair (TopCat.of V) (fun x : V ↦ x.val ∈ A)).homology R n)) (n : ℕ) :
    IsIso (SSetPair.homologyMap (singularPairEnlargement X hAV) R n) := by
  apply pair_homologyMap_isIso_of_component_isos
  · exact enlargement_left_homology_isIso_of_relative_zero X A V hAV R hzero
  · intro m
    change IsIso (SSet.homologyMap (TopCat.toSSet.map (𝟙 X)) R m)
    rw [CategoryTheory.Functor.map_id, SSet.homologyMap_id]
    infer_instance

/-- Deformation specialization of the enlargement comparison. (Hatcher, Prop. 2.22) -/
theorem enlargement_homology_isIso_of_deformation
    (X : TopCat.{u}) (A V : Set X) (hAV : A ⊆ V)
    (d : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSetPair.homologyMap (singularPairEnlargement X hAV) R n) := by
  apply enlargement_homology_isIso_of_relative_zero X A V hAV R
  intro m
  exact HolomorphicAnosov.Topology.Homotopy.good_pair_deformation_relative_acyclicity
    d (ModuleCat.{u} ℤ) R m

/-- The descended relative contraction gives a deformation retract on the quotient side. (Hatcher, Prop. 2.22) -/
theorem lower_enlargement_homology_isIso
    (X : TopCat.{u}) (A V : Set X) (hAV : A ⊆ V) (hneighborhood : A ⊆ interior V)
    (d : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (hA : A.Nonempty) (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSetPair.homologyMap
      (singularPairEnlargement (TopCat.of (Collapsed A))
        (A := collapsedPart A) (V := collapse A '' V) (Set.image_mono hAV)) R n) := by
  obtain ⟨a, ha⟩ := hA
  let B := collapsedPart A
  let W := collapse A '' V
  let b : B := ⟨collapse A a, ⟨a, ha, rfl⟩⟩
  let e := NeighborhoodImageG8.neighborhoodQuotientImageHomeomorph hneighborhood
  let H := StrongDeformationRetract.quotientContraction d ⟨a, ha⟩
  have hpoint (x : B) : x = b := by
    apply Subtype.ext
    obtain ⟨y, hy, hxy⟩ := x.property
    change x.val = collapse A a
    rw [← hxy]
    exact Quotient.sound (Or.inr ⟨hy, ha⟩)
  let r : C(W, B) := ContinuousMap.const W b
  let D : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract
      B W (Set.image_mono hAV) := {
    retraction := r
    retraction_inclusion := by
      ext x
      exact congrArg Subtype.val (hpoint x).symm
    homotopy := {
      toFun := fun z ↦ e (H (z.1, e.symm z.2))
      continuous_toFun := e.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
      map_zero_left := by
        intro x
        simp
      map_one_left := by
        intro x
        change e (H (1, e.symm x)) = _
        rw [H.apply_one]
        apply Subtype.ext
        exact congrFun (NeighborhoodImageG8.neighborhood_inclusion_projection_square
          hneighborhood) ⟨a, hAV ha⟩
      prop' := by
        intro t x hx
        have hx' : e.symm x ∈ collapsedPart (fun y : V ↦ y.val ∈ A) := by
          apply (NeighborhoodImageG8.neighborhoodQuotientImageHomeomorph_mem_collapsedPart
            hneighborhood (e.symm x)).mpr
          change (e (e.symm x)).val ∈ B
          rw [e.apply_symm_apply]
          exact hx
        change e (H (t, e.symm x)) = x
        rw [H.eq_fst t hx']
        exact e.apply_symm_apply x } }
  exact enlargement_homology_isIso_of_deformation (TopCat.of (Collapsed A))
    B W (Set.image_mono hAV) D R n

/-- The middle vertical map in the good-pair comparison diagram uses the collapse map on both ambient spaces and distinguished subspaces. (Hatcher, Prop. 2.22) -/
def collapseNeighborhoodSingularPairMap (X : TopCat.{u}) (A V : Set X) :
    singularSubspacePair X V ⟶
      singularSubspacePair (TopCat.of (Collapsed A)) (collapse A '' V) :=
  singularSubspacePairMap (collapseMorphism X A) V (collapse A '' V)
    (fun x hx ↦ ⟨x, hx, rfl⟩)

/-- An isomorphism of simplicial pairs induces an isomorphism on relative homology. -/
theorem ssetPair_homologyMap_isIso_of_iso {P P' : SSetPair.{u}} (e : P ≅ P')
    (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSetPair.homologyMap e.hom R n) := by
  change IsIso ((SSetPair.homologyFunctor R n).map e.hom)
  infer_instance

/-- A homeomorphism carrying a subspace to a subspace induces a map of singular pairs.-/
def complementPairMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (D : Set Y) (h : Set.MapsTo e A D) :
    singularSubspacePair (TopCat.of X) A ⟶ singularSubspacePair (TopCat.of Y) D :=
  singularSubspacePairMap (TopCat.ofHom ⟨e, e.continuous⟩) A D h

/-- A pair homeomorphism induces an isomorphism on native relative homology. -/
theorem complementPairMap_homology_isIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (D : Set Y)
    (h : Set.MapsTo e A D) (h' : Set.MapsTo e.symm D A)
    (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSetPair.homologyMap (complementPairMap e A D h) R n) := by
  let f := complementPairMap e A D h
  let g := complementPairMap e.symm D A h'
  have hfg : f ≫ g = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        𝟙 (TopCat.toSSet.obj (TopCat.of A))
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      exact e.symm_apply_apply x.val
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        𝟙 (TopCat.toSSet.obj (TopCat.of X))
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      exact e.symm_apply_apply x
  have hgf : g ≫ f = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        𝟙 (TopCat.toSSet.obj (TopCat.of D))
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      exact e.apply_symm_apply x.val
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        𝟙 (TopCat.toSSet.obj (TopCat.of Y))
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      exact e.apply_symm_apply x
  let E : singularSubspacePair (TopCat.of X) A ≅
      singularSubspacePair (TopCat.of Y) D :=
    { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }
  exact ((SSetPair.homologyFunctor R n).mapIso E).isIso_hom

/-- The complement homeomorphism induces the corresponding map of singular pairs and its relative homology map. -/
theorem good_pair_complement_pair_homology_isIso
    (X : TopCat.{u}) (A V : Set X) (hclosed : IsClosed A) (hAV : A ⊆ V)
    (R : ModuleCat.{u} ℤ) (n : ℕ) :
    let VC : Set ↥Aᶜ := {x | x.val ∈ V}
    let QVC : Set ↥(collapsedPart A)ᶜ := {y | y.val ∈ collapse A '' V}
    ∃ e : ↥Aᶜ ≃ₜ ↥(collapsedPart A)ᶜ,
      ∃ _eV : VC ≃ₜ QVC,
        ∃ h : Set.MapsTo e VC QVC, ∃ _h' : Set.MapsTo e.symm QVC VC,
          IsIso (SSetPair.homologyMap (complementPairMap e VC QVC h) R n) := by
  dsimp
  obtain ⟨e, he, hrest⟩ := good_pair_complement_homeomorphism
    (X := (X : Type u)) A hclosed
  obtain ⟨eV, heV, _, _, _⟩ := hrest V hAV
  let VC : Set ↥Aᶜ := {x | x.val ∈ V}
  let QVC : Set ↥(collapsedPart A)ᶜ := {y | y.val ∈ collapse A '' V}
  have h : Set.MapsTo e VC QVC := by
    intro x hx
    let xv : VC := ⟨x, hx⟩
    change (e x).val ∈ collapse A '' V
    rcases (eV xv).property with ⟨z, hz, hze⟩
    refine ⟨z, hz, ?_⟩
    simpa only [heV xv] using hze
  have h' : Set.MapsTo e.symm QVC VC := by
    intro y hy
    let yv : QVC := ⟨y, hy⟩
    have hEq : e.symm y = (eV.symm yv).val := by
      have hxy := congrArg e.symm (heV (eV.symm yv))
      simpa [yv] using hxy
    simp [hEq]
  exact ⟨e, eV, h, h', complementPairMap_homology_isIso e VC QVC h h' R n⟩

/-- The collapse maps the complement of A into the complement of its image. (Hatcher, Prop. 2.22) -/
theorem collapse_mapsTo_complement (X : TopCat.{u}) (A : Set X) :
    Set.MapsTo (collapseMorphism X A) Aᶜ (collapsedPart A)ᶜ := by
  intro x hx hq
  obtain ⟨a, ha, hax⟩ := hq
  have hr : a = x ∨ a ∈ A ∧ x ∈ A := Quotient.exact hax
  rcases hr with rfl | hr
  · exact hx ha
  · exact hx hr.2

/-- The excision source map of the collapse is an isomorphism on relative homology. (Hatcher, Prop. 2.22) -/
theorem collapse_excision_source_homology_isIso
    (X : TopCat.{u}) (A V : Set X) (hclosed : IsClosed A) (hAV : A ⊆ V)
    (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSetPair.homologyMap
      (singularExcisionSourceMap (collapseMorphism X A) V Aᶜ
        (collapse A '' V) (collapsedPart A)ᶜ
        (fun x hx ↦ ⟨x, hx, rfl⟩) (collapse_mapsTo_complement X A)) R n) := by
  obtain ⟨e, he, hrest⟩ := good_pair_complement_homeomorphism
    (X := (X : Type u)) A hclosed
  obtain ⟨eV, heV, _, _, _⟩ := hrest V hAV
  let VC : Set ↥Aᶜ := {x | x.val ∈ V}
  let QVC : Set ↥(collapsedPart A)ᶜ := {y | y.val ∈ collapse A '' V}
  have h : Set.MapsTo e VC QVC := by
    intro x hx
    change (e x).val ∈ collapse A '' V
    rw [he]
    exact ⟨x.val, hx, rfl⟩
  have h' : Set.MapsTo e.symm QVC VC := by
    intro y hy
    let yv : QVC := ⟨y, hy⟩
    have hEq : e.symm y = (eV.symm yv).val := by
      have hxy := congrArg e.symm (heV (eV.symm yv))
      simpa [yv] using hxy
    simp [hEq]
  have hmap : singularSubspaceMap (collapseMorphism X A) Aᶜ (collapsedPart A)ᶜ
      (collapse_mapsTo_complement X A) = TopCat.ofHom ⟨e, e.continuous⟩ := by
    ext x
    exact (he x).symm
  have hpair : singularExcisionSourceMap (collapseMorphism X A) V Aᶜ
      (collapse A '' V) (collapsedPart A)ᶜ
      (fun x hx ↦ ⟨x, hx, rfl⟩) (collapse_mapsTo_complement X A) =
      complementPairMap e VC QVC h := by
    unfold singularExcisionSourceMap complementPairMap
    congr 1
  rw [hpair]
  exact complementPairMap_homology_isIso e VC QVC h h' R n

/-- A subset containing A is saturated for the collapse equivalence relation. (Hatcher, Prop. 2.22) -/
theorem collapse_preimage_image_of_subset (X : TopCat.{u}) (A S : Set X) (hAS : A ⊆ S) :
    collapse A ⁻¹' (collapse A '' S) = S := by
  ext x
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hr : s = x ∨ s ∈ A ∧ x ∈ A := Quotient.exact hsx
    rcases hr with rfl | hr
    · exact hs
    · exact hAS hr.2
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The excised image is closed and lies in the interior of q(V). (Hatcher, Prop. 2.22) -/
theorem collapse_excision_topology (X : TopCat.{u}) (A V : Set X)
    (hclosed : IsClosed A) (hneighborhood : A ⊆ interior V) :
    IsClosed (collapsedPart A) ∧ collapsedPart A ⊆ interior (collapse A '' V) := by
  have hq : Topology.IsQuotientMap (collapse A) := isQuotientMap_quotient_mk'
  have hB : IsClosed (collapsedPart A) := by
    apply hq.isCoinducing.isClosed_preimage.mp
    change IsClosed (collapse A ⁻¹' (collapse A '' A))
    rw [collapse_preimage_image_of_subset X A A (Subset.refl A)]
    exact hclosed
  have hopen : IsOpen (collapse A '' interior V) := by
    apply hq.isCoinducing.isOpen_preimage.mp
    rw [collapse_preimage_image_of_subset X A (interior V) hneighborhood]
    exact isOpen_interior
  refine ⟨hB, ?_⟩
  exact (Set.image_mono hneighborhood).trans
    (interior_maximal (Set.image_mono interior_subset) hopen)

/-- The middle map in the good-pair comparison diagram is an isomorphism in every relative homology degree. (Hatcher, Prop. 2.22) -/
theorem collapse_neighborhood_homology_isIso
    (X : TopCat.{u}) (A V : Set X) (hclosed : IsClosed A)
    (hneighborhood : A ⊆ interior V) (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSetPair.homologyMap (collapseNeighborhoodSingularPairMap X A V) R n) := by
  have hAV : A ⊆ V := hneighborhood.trans interior_subset
  let Q := TopCat.of (Collapsed A)
  let B := collapsedPart A
  let W := collapse A '' V
  have hBW : B ⊆ W := Set.image_mono hAV
  obtain ⟨hBclosed, hBinterior⟩ := collapse_excision_topology X A V hclosed hneighborhood
  let hEx := singular_homology_excision_barycentric_subdivision.{u}
  have : IsIso (SSetPair.homologyMap (singularExcisionInclusion X V Aᶜ) R n) :=
    (hEx.2.2.2.2 X V A hAV (by simpa only [hclosed.closure_eq] using hneighborhood) R).2 n
  have : IsIso (SSetPair.homologyMap (singularExcisionInclusion Q W Bᶜ) R n) :=
    (hEx.2.2.2.2 Q W B hBW
      (by simpa only [B, W, hBclosed.closure_eq] using hBinterior) R).2 n
  have := collapse_excision_source_homology_isIso X A V hclosed hAV R n
  apply (isIso_comp_left_iff
    (SSetPair.homologyMap (singularExcisionInclusion X V Aᶜ) R n) _).mp
  change IsIso (SSetPair.homologyMap (singularExcisionInclusion X V Aᶜ) R n ≫
    SSetPair.homologyMap (singularSubspacePairMap (collapseMorphism X A) V W
      (fun x hx ↦ ⟨x, hx, rfl⟩)) R n)
  rw [hEx.2.2.1 X Q (collapseMorphism X A) V Aᶜ W Bᶜ
    (fun x hx ↦ ⟨x, hx, rfl⟩) (collapse_mapsTo_complement X A) R n]
  infer_instance

/-- The left square of the good-pair diagram commutes on the singular pairs. (Hatcher, Prop. 2.22) -/
theorem collapse_enlargement_square (X : TopCat.{u}) (A V : Set X) (hAV : A ⊆ V) :
    collapseSingularPairMap X A ≫
        singularPairEnlargement (TopCat.of (Collapsed A))
          (A := collapsedPart A) (V := collapse A '' V) (Set.image_mono hAV) =
      singularPairEnlargement X hAV ≫ collapseNeighborhoodSingularPairMap X A V := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl

/-- Applying relative homology preserves the left comparison square. (Hatcher, Prop. 2.22) -/
theorem collapse_enlargement_homology_square (X : TopCat.{u}) (A V : Set X)
    (hAV : A ⊆ V) (R : ModuleCat.{u} ℤ) (n : ℕ) :
    SSetPair.homologyMap (collapseSingularPairMap X A) R n ≫
        SSetPair.homologyMap
          (singularPairEnlargement (TopCat.of (Collapsed A))
          (A := collapsedPart A) (V := collapse A '' V) (Set.image_mono hAV)) R n =
      SSetPair.homologyMap (singularPairEnlargement X hAV) R n ≫
        SSetPair.homologyMap (collapseNeighborhoodSingularPairMap X A V) R n := by
  simpa only [SSetPair.homologyMap_comp] using
    congrArg (fun f ↦ SSetPair.homologyMap f R n) (collapse_enlargement_square X A V hAV)

/-- The left comparison square transfers three established isomorphisms to the quotient-induced relative map. (Hatcher, Prop. 2.22) -/
theorem collapse_homology_isIso_of_comparison (X : TopCat.{u}) (A V : Set X)
    (hAV : A ⊆ V) (R : ModuleCat.{u} ℤ) (n : ℕ)
    [IsIso (SSetPair.homologyMap (singularPairEnlargement X hAV) R n)]
    [IsIso (SSetPair.homologyMap
      (singularPairEnlargement (TopCat.of (Collapsed A))
          (A := collapsedPart A) (V := collapse A '' V) (Set.image_mono hAV)) R n)]
    [IsIso (SSetPair.homologyMap (collapseNeighborhoodSingularPairMap X A V) R n)] :
    IsIso (SSetPair.homologyMap (collapseSingularPairMap X A) R n) := by
  apply (isIso_comp_right_iff _ (SSetPair.homologyMap
    (singularPairEnlargement (TopCat.of (Collapsed A))
          (A := collapsedPart A) (V := collapse A '' V) (Set.image_mono hAV)) R n)).mp
  rw [collapse_enlargement_homology_square X A V hAV R n]
  infer_instance

/-- Excision and the two acyclic enlargements identify the quotient map on relative homology. (Hatcher, Prop. 2.22) -/
theorem collapse_homology_isIso_of_good_pair
    (X : TopCat.{u}) (A V : Set X) (hA : A.Nonempty) (hclosed : IsClosed A)
    (hAV : A ⊆ V) (hneighborhood : A ⊆ interior V)
    (d : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsIso (SSetPair.homologyMap (collapseSingularPairMap X A) R n) := by
  have := enlargement_homology_isIso_of_deformation X A V hAV d R n
  have := lower_enlargement_homology_isIso X A V hAV hneighborhood d hA R n
  have := collapse_neighborhood_homology_isIso X A V hclosed hneighborhood R n
  exact collapse_homology_isIso_of_comparison X A V hAV R n

/-- Subspace chains vanish under the augmented quotient projection. (Hatcher) -/
theorem augmented_inclusion_projection (X : TopCat.{u}) (A : Set X) :
    augmentedIntegralSingularChainsMap (singularSubspaceInclusion X A) ≫
      augmentedRelativeProjection X A = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      change (𝟙 reducedSingularIntegralCoefficients) ≫ (0 : _ ⟶ (0 : ModuleCat.{u} ℤ)) = 0
      exact comp_zero
  | succ n =>
      exact (singularSubspacePair X A).chainComplex_condition_f
        reducedSingularIntegralCoefficients n

/-- The augmented singular-pair short complex with its original inclusion and quotient projection. (Hatcher) -/
def augmentedPairShortComplex (X : TopCat.{u}) (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (augmentedIntegralSingularChainsMap (singularSubspaceInclusion X A))
    (augmentedRelativeProjection X A) (augmented_inclusion_projection X A)

/-- The augmented pair sequence is short exact, including index zero. (Hatcher) -/
theorem augmentedPairShortComplex_shortExact (X : TopCat.{u}) (A : Set X) :
    (augmentedPairShortComplex X A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  cases n with
  | zero =>
      have hf : Mono (((augmentedPairShortComplex X A).map
          (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) 0)).f) := by
        change Mono (𝟙 reducedSingularIntegralCoefficients)
        infer_instance
      have hg : Epi (((augmentedPairShortComplex X A).map
          (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) 0)).g) := by
        change Epi (0 : reducedSingularIntegralCoefficients ⟶ (0 : ModuleCat.{u} ℤ))
        infer_instance
      refine { exact := ?_ }
      rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      exact ⟨x, rfl⟩
  | succ n =>
      exact ((singularSubspacePair X A).shortExact_chainComplexShortComplex
        reducedSingularIntegralCoefficients).map
          (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n)

/-- The connecting map in the augmented pair sequence; its target is reduced homology also when n=0. (Hatcher) -/
def augmentedPairConnecting (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (augmentedRelativeChains X A).homology (n + 2) ⟶
      integralReducedSingularHomology (TopCat.of A) n :=
  (augmentedPairShortComplex_shortExact X A).δ (n + 2) (n + 1) (by simp)

/-- Exactness at all three types of terms, in the original augmented pair sequence. (Hatcher, Thm 2.16) -/
theorem augmented_pair_homology_exact (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    Function.Exact
      (integralReducedSingularHomologyMap (singularSubspaceInclusion X A) n)
      (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 1)) ∧
    Function.Exact
      (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 2))
      (augmentedPairConnecting X A n) ∧
    Function.Exact (augmentedPairConnecting X A n)
      (integralReducedSingularHomologyMap (singularSubspaceInclusion X A) n) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((augmentedPairShortComplex_shortExact X A).homology_exact₂ (n + 1))
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((augmentedPairShortComplex_shortExact X A).homology_exact₃ (n + 2) (n + 1) (by simp))
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      ((augmentedPairShortComplex_shortExact X A).homology_exact₁ (n + 2) (n + 1) (by simp))

/-- The concrete kernel/image cycle class is the canonical abstract cycle projection. (Hatcher) -/
theorem integralChainCycleClass_eq (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ)
    (c : LinearMap.ker (K.sc n).g.hom) :
    integralChainCycleClass K n c =
      K.homologyπ n ((K.sc n).moduleCatCyclesIso.inv c) := by
  exact (congrArg (fun f ↦ f c) ((K.sc n).moduleCatCyclesIso_inv_π)).symm

/-- The explicit kernel element and Mathlib's abstract cycle constructor are the same cycle. (Hatcher) -/
theorem integralChainCycleClass_eq_cyclesMk
    (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ)
    (c : LinearMap.ker (K.sc n).g.hom) :
    integralChainCycleClass K n c =
      K.homologyπ n ((K.sc n).cyclesMk c.val c.property) := by
  rw [integralChainCycleClass_eq]
  congr 1
  apply (ModuleCat.mono_iff_injective (K.sc n).iCycles).mp inferInstance
  have h := congrArg (fun f ↦ f c) ((K.sc n).moduleCatCyclesIso_inv_iCycles)
  change (K.sc n).iCycles ((K.sc n).moduleCatCyclesIso.inv c) = c.val at h
  change ((forget₂ (ModuleCat.{u} ℤ) Ab).map (K.sc n).iCycles)
      ((K.sc n).moduleCatCyclesIso.inv c) =
    ((forget₂ (ModuleCat.{u} ℤ) Ab).map (K.sc n).iCycles)
      ((K.sc n).cyclesMk c.val c.property)
  exact h.trans ((K.sc n).i_cyclesMk c.val c.property).symm

/-- Native short-complex homology maps carry the class of a cycle to the class of its middle-component image. (Hatcher) -/
theorem shortComplex_homologyMap_cycle
    {S T : ShortComplex (ModuleCat.{u} ℤ)} (f : S ⟶ T)
    (c : LinearMap.ker S.g.hom) (d : LinearMap.ker T.g.hom)
    (h : f.τ₂ c.val = d.val) :
    ShortComplex.homologyMap f (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π c)) =
      T.moduleCatHomologyIso.inv (T.moduleCatLeftHomologyData.π d) := by
  have hcy : ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv c) =
      T.moduleCatCyclesIso.inv d := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    change (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap f ≫ T.iCycles) c =
      (T.moduleCatCyclesIso.inv ≫ T.iCycles) d
    rw [ShortComplex.cyclesMap_i, ← Category.assoc,
      S.moduleCatCyclesIso_inv_iCycles, T.moduleCatCyclesIso_inv_iCycles]
    exact h
  change (S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv ≫
    ShortComplex.homologyMap f) c =
      (T.moduleCatLeftHomologyData.π ≫ T.moduleCatHomologyIso.inv) d
  rw [← Category.assoc, ← S.moduleCatCyclesIso_inv_π, ← T.moduleCatCyclesIso_inv_π,
    Category.assoc, ShortComplex.homologyπ_naturality]
  change T.homologyπ (ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv c)) =
    T.homologyπ (T.moduleCatCyclesIso.inv d)
  rw [hcy]

/-- The shift comparison preserves the underlying cycle and its class, including ordinary degree zero. (Hatcher) -/
theorem zeroAugmentHomologyIso_cycle
    (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ)
    (c : LinearMap.ker
      ((ChainComplex.augment K (0 : K.X 0 ⟶ 0) (by simp)).sc (n + 1)).g.hom)
    (d : LinearMap.ker (K.sc n).g.hom) (h : c.val = d.val) :
    (zeroAugmentHomologyIso K n).hom
      (integralChainCycleClass (ChainComplex.augment K (0 : K.X 0 ⟶ 0) (by simp)) (n + 1) c) =
        integralChainCycleClass K n d := by
  let L := ChainComplex.augment K (0 : K.X 0 ⟶ 0) (by simp)
  let φ : L.sc (n + 1) ⟶ K.sc n :=
    (L.isoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom ≫
      zeroAugmentShortComplexMap K n ≫
      (K.isoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)).inv
  have hmap : (zeroAugmentHomologyIso K n).hom = ShortComplex.homologyMap φ := by
    simp only [φ, ShortComplex.homologyMap_comp]
    rfl
  rw [hmap]
  apply shortComplex_homologyMap_cycle
  have hτ : φ.τ₂ = 𝟙 (K.X n) := by
    cases n with
    | zero =>
      change 𝟙 (K.X 0) ≫ 𝟙 (K.X 0) ≫ 𝟙 (K.X 0) = 𝟙 (K.X 0)
      simp
    | succ n =>
      change 𝟙 (K.X (n + 1)) ≫ 𝟙 (K.X (n + 1)) ≫ 𝟙 (K.X (n + 1)) = 𝟙 (K.X (n + 1))
      simp
  rw [hτ]
  exact h

/-- The grading bridge for relative chains preserves every cycle class. (Hatcher) -/
theorem augmentedRelativeHomologyIso_cycle (X : TopCat.{u}) (A : Set X) (n : ℕ)
    (c : LinearMap.ker ((augmentedRelativeChains X A).sc (n + 1)).g.hom)
    (d : LinearMap.ker
      (((singularSubspacePair X A).chainComplex reducedSingularIntegralCoefficients).sc n).g.hom)
    (h : c.val = d.val) :
    (augmentedRelativeHomologyIso X A n).hom
      (integralChainCycleClass (augmentedRelativeChains X A) (n + 1) c) =
      integralChainCycleClass
        ((singularSubspacePair X A).chainComplex reducedSingularIntegralCoefficients) n d :=
  zeroAugmentHomologyIso_cycle _ n c d h

/-- The connecting morphism has the original positive boundary sign on the augmented cycle classes. (Hatcher) -/
theorem augmented_pair_connecting_cycle (X : TopCat.{u}) (A : Set X) (n : ℕ)
    (c : (augmentedIntegralSingularChains X).X (n + 2))
    (a : LinearMap.ker ((augmentedIntegralSingularChains (TopCat.of A)).sc (n + 1)).g.hom)
    (rc : LinearMap.ker ((augmentedRelativeChains X A).sc (n + 2)).g.hom)
    (hproj : (augmentedRelativeProjection X A).f (n + 2) c = rc.val)
    (hboundary : (augmentedIntegralSingularChainsMap
        (singularSubspaceInclusion X A)).f (n + 1) a.val =
      (augmentedIntegralSingularChains X).d (n + 2) (n + 1) c) :
    augmentedPairConnecting X A n
      (integralChainCycleClass (augmentedRelativeChains X A) (n + 2) rc) =
      integralChainCycleClass (augmentedIntegralSingularChains (TopCat.of A)) (n + 1) a := by
  rw [integralChainCycleClass_eq_cyclesMk, integralChainCycleClass_eq_cyclesMk]
  have hrc : ((forget₂ (ModuleCat.{u} ℤ) Ab).map
      ((augmentedRelativeChains X A).d (n + 2) (n + 1))) rc.val = 0 := by
    have hnext : (ComplexShape.down ℕ).next (n + 2) = n + 1 :=
      (ComplexShape.down ℕ).next_eq' (by simp)
    have hr := rc.property
    change ((augmentedRelativeChains X A).d (n + 2)
      ((ComplexShape.down ℕ).next (n + 2))) rc.val = 0 at hr
    rw [hnext] at hr
    exact hr
  exact (augmentedPairShortComplex_shortExact X A).δ_apply (n + 2) (n + 1)
    (by simp) rc.val hrc c hproj a.val hboundary n (by simp)

/-- Nonemptiness makes the coefficient-sum augmentation surjective. (Hatcher) -/
theorem integralSingularAugmentation_epi (X : TopCat.{u}) (hX : Nonempty X) :
    Epi (integralSingularAugmentation X) := by
  obtain ⟨x⟩ := hX
  let σ : (TopCat.toSSet.obj X) _⦋0⦌ :=
    (TopCat.toSSetObjEquiv X _).symm (ContinuousMap.const _ x)
  have hs : (TopCat.toSSet.obj X).ιChainComplex
      (R := reducedSingularIntegralCoefficients) σ ≫ integralSingularAugmentation X =
        𝟙 reducedSingularIntegralCoefficients := by
    simp [SSet.ιChainComplex, integralSingularAugmentation]
  exact epi_of_epi_fac hs

/-- For a nonempty singleton space the coefficient-sum augmentation is an isomorphism. (Hatcher) -/
theorem integralSingularAugmentation_isIso_of_subsingleton
    (X : TopCat.{u}) [Subsingleton X] (hX : Nonempty X) :
    IsIso (integralSingularAugmentation X) := by
  obtain ⟨x⟩ := hX
  let σ : (TopCat.toSSet.obj X) _⦋0⦌ :=
    (TopCat.toSSetObjEquiv X _).symm (ContinuousMap.const _ x)
  let j := (TopCat.toSSet.obj X).ιChainComplex
    (R := reducedSingularIntegralCoefficients) σ
  have hj : j ≫ integralSingularAugmentation X = 𝟙 _ := by
    simp [j, SSet.ιChainComplex, integralSingularAugmentation]
  have hj' : integralSingularAugmentation X ≫ j = 𝟙 _ := by
    apply SSet.chainComplex_hom_ext
    intro τ
    have heq : τ = σ := (TopCat.toSSetObjEquiv X _).injective (Subsingleton.elim _ _)
    subst τ
    change j ≫ integralSingularAugmentation X ≫ j = j ≫ 𝟙 _
    rw [← Category.assoc, hj]
    simp
  let E : ((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients).X 0 ≅
      reducedSingularIntegralCoefficients :=
    { hom := integralSingularAugmentation X, inv := j, hom_inv_id := hj', inv_hom_id := hj }
  exact E.isIso_hom

/-- The singleton augmented complex is acyclic at index one, hence its reduced H₀ vanishes. (Hatcher) -/
theorem reducedHomology_zero_of_subsingleton
    (X : TopCat.{u}) [Subsingleton X] (hX : Nonempty X) :
    IsZero (integralReducedSingularHomology X 0) := by
  have := integralSingularAugmentation_isIso_of_subsingleton X hX
  let S := (augmentedIntegralSingularChains X).sc 1
  have hg : Mono S.g := by
    change Mono ((augmentedIntegralSingularChains X).d 1 ((ComplexShape.down ℕ).next 1))
    rw [ChainComplex.next_nat_succ]
    exact IsIso.mono_of_iso (integralSingularAugmentation X)
  have hf : S.f = 0 := by
    apply (cancel_mono S.g).mp
    simpa only [zero_comp] using S.zero
  exact (ShortComplex.exact_iff_isZero_homology S).mp ((S.exact_iff_mono hf).mpr hg)

/-- Reduced degree −1 vanishes for a nonempty space. (Hatcher) -/
theorem augmentedHomology_zero_of_nonempty (X : TopCat.{u}) (hX : Nonempty X) :
    IsZero ((augmentedIntegralSingularChains X).homology 0) := by
  apply (ShortComplex.exact_iff_isZero_homology _).mp
  apply (ShortComplex.exact_iff_epi _ (by
    change (augmentedIntegralSingularChains X).d 0 ((ComplexShape.down ℕ).next 0) = 0
    exact (augmentedIntegralSingularChains X).shape _ _ (by simp))).mpr
  change Epi ((augmentedIntegralSingularChains X).d ((ComplexShape.down ℕ).prev 0) 0)
  have hprev : (ComplexShape.down ℕ).prev 0 = 1 :=
    (ComplexShape.down ℕ).prev_eq' (by simp)
  rw [hprev]
  exact integralSingularAugmentation_epi X hX

/-- The augmented relative degree-zero projection is surjective when A is nonempty, with no positive-degree restriction. (Hatcher) -/
theorem augmented_pair_degree_zero_surjective (X : TopCat.{u}) (A : Set X)
    (hA : A.Nonempty) :
    Function.Surjective
      (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) 1) := by
  let hS := augmentedPairShortComplex_shortExact X A
  have hzero := augmentedHomology_zero_of_nonempty (TopCat.of A)
    ⟨⟨hA.choose, hA.choose_spec⟩⟩
  have hδ : hS.δ 1 0 (by simp) = 0 := hzero.eq_of_tgt _ _
  have he := (hS.homology_exact₃ 1 0 (by simp)).epi_f hδ
  exact (ModuleCat.epi_iff_surjective _).mp he

/-- The augmented projection of a nonempty singleton pair is invertible on reduced degree zero. (Hatcher) -/
theorem singleton_augmented_projection_zero_isIso
    (X : TopCat.{u}) (A : Set X) [Subsingleton A] (hA : A.Nonempty) :
    IsIso (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) 1) := by
  have hzero := reducedHomology_zero_of_subsingleton (TopCat.of A)
    ⟨⟨hA.choose, hA.choose_spec⟩⟩
  have hmono : Mono (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) 1) :=
    ((augmentedPairShortComplex_shortExact X A).homology_exact₂ 1).mono_g
      (hzero.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) 1) :=
    (ModuleCat.epi_iff_surjective _).mpr (augmented_pair_degree_zero_surjective X A hA)
  exact isIso_of_mono_of_epi _

/-- The canonical relative/reduced comparison for a singleton subspace in degree zero is the inverse of the augmented quotient projection. (Hatcher, Prop. 2.22) -/
def singletonBasepointComparisonZero
    (X : TopCat.{u}) (A : Set X) [Subsingleton A] (hA : A.Nonempty) :
    (singularSubspacePair X A).homology reducedSingularIntegralCoefficients 0 ≅
      integralReducedSingularHomology X 0 := by
  have := singleton_augmented_projection_zero_isIso X A hA
  exact (asIso (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) 1) ≪≫
    augmentedRelativeHomologyIso X A 0).symm

/-- The singleton basepoint comparison is natural with the grading bridge: its composite with the bridge is exactly the augmented relative projection. (Hatcher) -/
theorem singletonBasepointComparisonZero_naturality
    (X : TopCat.{u}) (A : Set X) [Subsingleton A] (hA : A.Nonempty) :
    (singletonBasepointComparisonZero X A hA).hom ≫
      HomologicalComplex.homologyMap (augmentedRelativeProjection X A) 1 =
      (augmentedRelativeHomologyIso X A 0).inv := by
  have hi := singleton_augmented_projection_zero_isIso X A hA
  let := hi
  change ((asIso (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) 1) ≪≫
      augmentedRelativeHomologyIso X A 0).symm).hom ≫
      HomologicalComplex.homologyMap (augmentedRelativeProjection X A) 1 =
      (augmentedRelativeHomologyIso X A 0).inv
  simp

/-- The native short-exact chain-complex morphism induced by a map of simplicial pairs. -/
def pairChainShortComplexMap {P Q : SSetPair.{u}} (f : P ⟶ Q)
    (R : ModuleCat.{u} ℤ) : P.chainComplexShortComplex R ⟶ Q.chainComplexShortComplex R := {
  τ₁ := ((SSetPair.chainComplexFunctorLeft (ModuleCat.{u} ℤ)).obj R).map f
  τ₂ := ((SSetPair.chainComplexFunctorRight (ModuleCat.{u} ℤ)).obj R).map f
  τ₃ := SSetPair.chainComplexMap f R
  comm₁₂ := ((SSetPair.chainComplexFunctorLeftToRight (ModuleCat.{u} ℤ)).app R).naturality f
  comm₂₃ := ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality f }

/-- The pair connecting morphisms are natural under the native pair map.  (Hatcher, Thm 2.16) -/
theorem pair_connecting_naturality
    {P Q : SSetPair.{u}} (f : P ⟶ Q) (R : ModuleCat.{u} ℤ)
    (n : ℕ) :
    (P.shortExact_chainComplexShortComplex R).δ (n + 2) (n + 1) (by simp) ≫
        HomologicalComplex.homologyMap (pairChainShortComplexMap f R).τ₁ (n + 1) =
      HomologicalComplex.homologyMap (pairChainShortComplexMap f R).τ₃ (n + 2) ≫
        (Q.shortExact_chainComplexShortComplex R).δ (n + 2) (n + 1) (by simp) := by
  exact HomologicalComplex.HomologySequence.δ_naturality (pairChainShortComplexMap f R)
    (P.shortExact_chainComplexShortComplex R) (Q.shortExact_chainComplexShortComplex R)
    (n + 2) (n + 1) (by simp)

/-- The collapse pair map transports the native relative connecting map through its induced chain-complex map. (Hatcher, Prop. 2.22) -/
theorem collapse_pair_connecting_naturality
    (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    ((singularSubspacePair X A).shortExact_chainComplexShortComplex
      reducedSingularIntegralCoefficients).δ (n + 2) (n + 1) (by simp) ≫
        HomologicalComplex.homologyMap
          (pairChainShortComplexMap (collapseSingularPairMap X A)
            reducedSingularIntegralCoefficients).τ₁ (n + 1) =
      HomologicalComplex.homologyMap
          (pairChainShortComplexMap (collapseSingularPairMap X A)
            reducedSingularIntegralCoefficients).τ₃ (n + 2) ≫
        ((singularSubspacePair (TopCat.of (Collapsed A)) (collapsedPart A)).shortExact_chainComplexShortComplex
          reducedSingularIntegralCoefficients).δ (n + 2) (n + 1) (by simp) := by
  exact pair_connecting_naturality (collapseSingularPairMap X A)
    reducedSingularIntegralCoefficients n

/-- The native homology-sequence connecting morphism is natural for the identity morphism of the augmented pair short complex. (Hatcher) -/
theorem augmented_pair_connecting_identity_naturality
    (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    let S := augmentedPairShortComplex X A
    let hS := augmentedPairShortComplex_shortExact X A
    hS.δ (n + 2) (n + 1) (by simp) ≫
        HomologicalComplex.homologyMap ((𝟙 S : S ⟶ S).τ₁) (n + 1) =
      HomologicalComplex.homologyMap ((𝟙 S : S ⟶ S).τ₃) (n + 2) ≫
        hS.δ (n + 2) (n + 1) (by simp) := by
  dsimp
  exact HomologicalComplex.HomologySequence.δ_naturality
    (𝟙 (augmentedPairShortComplex X A))
    (augmentedPairShortComplex_shortExact X A)
    (augmentedPairShortComplex_shortExact X A) (n + 2) (n + 1) (by simp)

/-- Positive-degree singular homology of a nonempty subsingleton vanishes by Mathlib's totally-disconnected-space calculation. -/
theorem ordinaryHomology_zero_of_subsingleton
    (X : TopCat.{u}) [Subsingleton X] (n : ℕ) (hn : n ≠ 0) :
    IsZero ((TopCat.toSSet.obj X).homology reducedSingularIntegralCoefficients.{u} n) := by
  let : TotallyDisconnectedSpace X := ⟨by
    intro t _ _ x _ y _
    exact Subsingleton.elim x y⟩
  change IsZero (((AlgebraicTopology.singularHomologyFunctor
    (ModuleCat.{u} ℤ) n).obj reducedSingularIntegralCoefficients.{u}).obj X)
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{u} ℤ) n reducedSingularIntegralCoefficients.{u} X hn

set_option backward.isDefEq.respectTransparency false in
/-- In positive degree, reduced homology agrees with ordinary singular homology via the augmentation shift.-/
def integralReducedPositiveOrdinaryIso_local (X : TopCat.{u}) (n : ℕ) :
    integralReducedSingularHomology X (n + 1) ≅
      ((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients.{u}).homology
        (n + 1) := by
  let A := augmentedIntegralSingularChains X
  let C := (TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients.{u}
  exact A.homologyIsoSc' (n + 3) (n + 2) (n + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [A,
        augmentedIntegralSingularChains, Category.id_comp, Category.comp_id])
        (by simp [A, augmentedIntegralSingularChains, Category.id_comp, Category.comp_id])) ≪≫
    (C.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).symm

/-- Every nonnegative reduced homology group of a nonempty subsingleton is zero. -/
theorem reducedHomology_zero_of_subsingleton_all
    (X : TopCat.{u}) [Subsingleton X] (hX : Nonempty X) (n : ℕ) :
    IsZero (integralReducedSingularHomology X n) := by
  cases n with
  | zero => exact reducedHomology_zero_of_subsingleton X hX
  | succ n =>
      apply IsZero.of_iso (ordinaryHomology_zero_of_subsingleton X (n + 1) (by omega))
        (integralReducedPositiveOrdinaryIso_local X n)

/-- The augmented relative projection for a singleton subspace is invertible in every positive augmented degree.-/
theorem singleton_augmented_projection_isIso_succ
    (X : TopCat.{u}) (A : Set X) [Subsingleton A] (hA : A.Nonempty) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 2)) := by
  have hzero_src : IsZero
      ((augmentedIntegralSingularChains (TopCat.of A)).homology (n + 2)) := by
    change IsZero (integralReducedSingularHomology (TopCat.of A) (n + 1))
    exact reducedHomology_zero_of_subsingleton_all (TopCat.of A)
      ⟨⟨hA.choose, hA.choose_spec⟩⟩ (n + 1)
  have hzero_tgt : IsZero
      ((augmentedIntegralSingularChains (TopCat.of A)).homology (n + 1)) := by
    change IsZero (integralReducedSingularHomology (TopCat.of A) n)
    exact reducedHomology_zero_of_subsingleton_all (TopCat.of A)
      ⟨⟨hA.choose, hA.choose_spec⟩⟩ n
  have hmono : Mono (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 2)) :=
    ((augmentedPairShortComplex_shortExact X A).homology_exact₂ (n + 2)).mono_g
      (hzero_src.eq_of_src _ _)
  have hepi : Epi (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 2)) :=
    ((augmentedPairShortComplex_shortExact X A).homology_exact₃ (n + 2) (n + 1) (by simp)).epi_f
      (hzero_tgt.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The native relative-to-reduced comparison is an isomorphism in every nonnegative degree for a nonempty singleton subspace.-/
def singletonBasepointComparison
    (X : TopCat.{u}) (A : Set X) [Subsingleton A] (hA : A.Nonempty) (n : ℕ) :
    (singularSubspacePair X A).homology reducedSingularIntegralCoefficients.{u} n ≅
      integralReducedSingularHomology X n := by
  cases n with
  | zero => exact singletonBasepointComparisonZero X A hA
  | succ n =>
      have hi := singleton_augmented_projection_isIso_succ X A hA n
      exact (asIso (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 2)) ≪≫
        augmentedRelativeHomologyIso X A (n + 1)).symm

set_option backward.isDefEq.respectTransparency false

/-- The inverse singleton comparison is the augmented projection followed by the grading comparison.-/
theorem singletonBasepointComparison_inv
    (X : TopCat.{u}) (A : Set X) [Subsingleton A] (hA : A.Nonempty) (n : ℕ) :
    (singletonBasepointComparison X A hA n).inv =
      HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 1) ≫
        (augmentedRelativeHomologyIso X A n).hom := by
  cases n <;> rfl

/-- A chain map preserves the concrete cycle class. -/
theorem integralChainCycleClass_map
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) (n : ℕ)
    (c : LinearMap.ker (K.sc n).g.hom) (d : LinearMap.ker (L.sc n).g.hom)
    (h : f.f n c.val = d.val) :
    HomologicalComplex.homologyMap f n (integralChainCycleClass K n c) =
      integralChainCycleClass L n d := by
  exact shortComplex_homologyMap_cycle ((HomologicalComplex.shortComplexFunctor _ _ n).map f) c d h

/-- The image of a concrete cycle is a concrete cycle. -/
theorem integralChainCycle_map_mem
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) (n : ℕ)
    (c : LinearMap.ker (K.sc n).g.hom) :
    (L.sc n).g.hom (f.f n c.val) = 0 := by
  change (L.d n ((ComplexShape.down ℕ).next n)).hom ((f.f n).hom c.val) = 0
  have h := congrArg (fun g ↦ g c.val) (f.comm n ((ComplexShape.down ℕ).next n)).symm
  change (f.f ((ComplexShape.down ℕ).next n)) ((K.sc n).g.hom c.val) =
    (L.sc n).g.hom (f.f n c.val) at h
  have hc : (K.d n ((ComplexShape.down ℕ).next n)).hom c.val = 0 := c.property
  change (f.f ((ComplexShape.down ℕ).next n)).hom ((K.d n ((ComplexShape.down ℕ).next n)).hom c.val) =
    (L.d n ((ComplexShape.down ℕ).next n)).hom ((f.f n).hom c.val) at h
  simpa only [hc, map_zero] using h.symm

/-- A good pair has the full reduced integral homology exact sequence, with the relative-to-quotient isomorphism and connecting boundary formula. (Hatcher, Thm 2.13) -/
theorem good_pair_reduced_homology_exact_sequence
    (X : TopCat.{u}) (A V : Set X) (hA : A.Nonempty) (hclosed : IsClosed A)
    (hAV : A ⊆ V) (hneighborhood : A ⊆ interior V)
    (d : Topology.Homotopy.StrongDeformationRetract A V hAV) :
    let Q := TopCat.of (Collapsed A)
    let B := collapsedPart A
    let P := singularSubspacePair X A
    let PB := singularSubspacePair Q B
    let R := reducedSingularIntegralCoefficients
    let CX := (TopCat.toSSet.obj X).chainComplex R
    let CA := augmentedIntegralSingularChains (TopCat.of A)
    let CQ := augmentedIntegralSingularChains Q
    let inc := singularSubspaceInclusion X A
    let q := collapseMorphism X A
    let qr := collapseSingularPairMap X A
    ∃ (base : ∀ n : ℕ, PB.homology R n ≅ integralReducedSingularHomology Q n)
      (δ : ∀ n : ℕ, integralReducedSingularHomology Q (n + 1) ⟶
        integralReducedSingularHomology (TopCat.of A) n),
      (∀ n : ℕ, IsIso (SSetPair.homologyMap qr R n)) ∧
      (∀ n : ℕ, IsIso (SSetPair.homologyMap qr R n ≫ (base n).hom)) ∧
      (∀ n : ℕ, Function.Exact
        (integralReducedSingularHomologyMap inc n)
        (integralReducedSingularHomologyMap q n)) ∧
      (∀ n : ℕ, Function.Exact
        (integralReducedSingularHomologyMap q (n + 1)) (δ n)) ∧
      (∀ n : ℕ, Function.Exact (δ n)
        (integralReducedSingularHomologyMap inc n)) ∧
      Function.Surjective (integralReducedSingularHomologyMap q 0) ∧
      (∀ (n : ℕ) (c : LinearMap.ker (CQ.sc (n + 1)).g.hom)
        (hc : ((PB.chainComplex R).sc n).g.hom
          ((PB.chainComplexπ R).f n c.val) = 0),
        (base n).inv (integralChainCycleClass CQ (n + 1) c) =
          integralChainCycleClass (PB.chainComplex R) n
            ⟨(PB.chainComplexπ R).f n c.val, hc⟩) ∧
      (∀ (n : ℕ) (c : CX.X (n + 1))
        (a : LinearMap.ker (CA.sc (n + 1)).g.hom),
        CX.d (n + 1) n c = (augmentedIntegralSingularChainsMap inc).f (n + 1) a.val →
        ∀ hc : ((P.chainComplex R).sc (n + 1)).g.hom
          ((P.chainComplexπ R).f (n + 1) c) = 0,
          δ n ((SSetPair.homologyMap qr R (n + 1) ≫ (base (n + 1)).hom)
            (integralChainCycleClass (P.chainComplex R) (n + 1)
              ⟨(P.chainComplexπ R).f (n + 1) c, hc⟩)) =
            integralChainCycleClass CA (n + 1) a) := by
  have hquotient (n : ℕ) : IsIso (SSetPair.homologyMap
      (collapseSingularPairMap X A) reducedSingularIntegralCoefficients n) :=
    collapse_homology_isIso_of_good_pair X A V hA hclosed hAV hneighborhood d
      reducedSingularIntegralCoefficients n
  let : Subsingleton (collapsedPart A) := ⟨by
    intro x y
    apply Subtype.ext
    obtain ⟨a, ha, hax⟩ := x.property
    obtain ⟨b, hb, hby⟩ := y.property
    rw [← hax, ← hby]
    exact Quotient.sound (Or.inr ⟨ha, hb⟩)⟩
  have hB : (collapsedPart A).Nonempty := by
    exact Set.Nonempty.image (collapse A) hA
  let base : ∀ n : ℕ,
      (singularSubspacePair (TopCat.of (Collapsed A)) (collapsedPart A)).homology
        reducedSingularIntegralCoefficients n ≅
      integralReducedSingularHomology (TopCat.of (Collapsed A)) n := fun n ↦
    singletonBasepointComparison (TopCat.of (Collapsed A)) (collapsedPart A) hB n
  have hbaseiso (n : ℕ) : IsIso (SSetPair.homologyMap
      (collapseSingularPairMap X A) reducedSingularIntegralCoefficients n ≫ (base n).hom) := by
    dsimp [base]
    infer_instance
  let e (n : ℕ) : (augmentedRelativeChains X A).homology (n + 1) ≅
      integralReducedSingularHomology (TopCat.of (Collapsed A)) n :=
    augmentedRelativeHomologyIso X A n ≪≫
      asIso (SSetPair.homologyMap (collapseSingularPairMap X A)
        reducedSingularIntegralCoefficients n) ≪≫ base n
  have hq (n : ℕ) : integralReducedSingularHomologyMap (collapseMorphism X A) n =
      HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 1) ≫
        (e n).hom := by
    apply (cancel_mono (base n).inv).mp
    simp only [e, Iso.trans_hom, asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [show (base n).inv = _ from singletonBasepointComparison_inv _ _ hB n]
    exact collapse_augmented_homology_naturality X A n
  let δ (n : ℕ) := (e (n + 1)).inv ≫ augmentedPairConnecting X A n
  refine ⟨base, δ, hquotient, hbaseiso, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [hq]
    exact (augmented_pair_homology_exact X A n).1.comp_injective (e n).hom
      (ModuleCat.mono_iff_injective (e n).hom |>.mp inferInstance) (map_zero _)
  · intro n y
    change augmentedPairConnecting X A n ((e (n + 1)).inv y) = 0 ↔ _
    rw [(augmented_pair_homology_exact X A n).2.1]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [hq]
      change (e (n + 1)).hom
        (HomologicalComplex.homologyMap (augmentedRelativeProjection X A) (n + 2) x) = y
      rw [hx]
      exact ConcreteCategory.congr_hom (e (n + 1)).inv_hom_id y
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      rw [hq]
      change _ = (e (n + 1)).inv ((e (n + 1)).hom _)
      exact (ConcreteCategory.congr_hom (e (n + 1)).hom_inv_id _).symm
  · intro n y
    rw [(augmented_pair_homology_exact X A n).2.2]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(e (n + 1)).hom x, ?_⟩
      change augmentedPairConnecting X A n ((e (n + 1)).inv ((e (n + 1)).hom x)) = _
      rw [show (e (n + 1)).inv ((e (n + 1)).hom x) = x from
        ConcreteCategory.congr_hom (e (n + 1)).hom_inv_id x]
    · rintro ⟨x, rfl⟩
      exact ⟨(e (n + 1)).inv x, rfl⟩
  · rw [hq]
    exact (ModuleCat.epi_iff_surjective (e 0).hom |>.mp inferInstance).comp
      (augmented_pair_degree_zero_surjective X A hA)
  · intro n c hc
    rw [show (base n).inv = _ from singletonBasepointComparison_inv _ _ hB n]
    let rc : LinearMap.ker ((augmentedRelativeChains
        (TopCat.of (Collapsed A)) (collapsedPart A)).sc (n + 1)).g.hom :=
      ⟨_, integralChainCycle_map_mem (augmentedRelativeProjection
        (TopCat.of (Collapsed A)) (collapsedPart A)) (n + 1) c⟩
    change (augmentedRelativeHomologyIso (TopCat.of (Collapsed A)) (collapsedPart A) n).hom
      (HomologicalComplex.homologyMap (augmentedRelativeProjection
        (TopCat.of (Collapsed A)) (collapsedPart A)) (n + 1)
        (integralChainCycleClass _ _ c)) = _
    rw [integralChainCycleClass_map _ _ c rc rfl]
    exact augmentedRelativeHomologyIso_cycle _ _ n rc _ rfl
  · intro n c a ha hc
    let rc : LinearMap.ker ((augmentedRelativeChains X A).sc (n + 2)).g.hom :=
      ⟨((singularSubspacePair X A).chainComplexπ reducedSingularIntegralCoefficients).f
        (n + 1) c, by
          change ((augmentedRelativeChains X A).d (n + 2)
            ((ComplexShape.down ℕ).next (n + 2))).hom _ = 0
          rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) by simp)]
          have hc' := hc
          change (((singularSubspacePair X A).chainComplex reducedSingularIntegralCoefficients).d
            (n + 1) ((ComplexShape.down ℕ).next (n + 1))).hom _ = 0 at hc'
          rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n by simp)] at hc'
          exact hc'⟩
    have heclass := augmentedRelativeHomologyIso_cycle X A (n + 1) rc
      ⟨((singularSubspacePair X A).chainComplexπ reducedSingularIntegralCoefficients).f
        (n + 1) c, hc⟩ rfl
    rw [← heclass]
    change augmentedPairConnecting X A n ((e (n + 1)).inv
      ((e (n + 1)).hom (integralChainCycleClass (augmentedRelativeChains X A) (n + 2) rc))) = _
    rw [ModuleCat.inv_hom_apply]
    exact augmented_pair_connecting_cycle X A n c a rc rfl ha.symm

end HolomorphicAnosov.GoodPair













