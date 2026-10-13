import HolomorphicAnosov.AlgebraicTopology.SingularSumSimplexBijection
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

noncomputable section
open Classical
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace HolomorphicAnosov.Cubical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev sigmaInclusion {ι : Type} (Y : TopCat) (i : ι) :
    Y ⟶ TopCat.of (Σ _ : ι, Y) := TopCat.ofHom ⟨fun y : Y ↦ (⟨i, y⟩ : Σ _ : ι, Y), by
      change Continuous (@Sigma.mk ι (fun _ ↦ (Y : Type)) i)
      exact continuous_sigmaMk⟩

abbrev sigmaChains {ι : Type} (Y : TopCat) (R : ModuleCat ℚ) :=
  (TopCat.toSSet.obj (TopCat.of (Σ _ : ι, Y))).chainComplex R

abbrev summandChains (Y : TopCat) (R : ModuleCat ℚ) := (TopCat.toSSet.obj Y).chainComplex R

abbrev sigmaSimplexEquiv {ι : Type} (Y : TopCat) (n : ℕ) :=
  Equiv.ofBijective _ (singular_sum_simplex_bijective (fun _ : ι ↦ Y) (op ⦋n⦌))

def sigmaChainProjectionF {ι : Type} (Y : TopCat) (R : ModuleCat ℚ) (i : ι) (n : ℕ) :
    (sigmaChains (ι := ι) Y R).X n ⟶ (summandChains Y R).X n := by
  classical
  let e := sigmaSimplexEquiv (ι := ι) Y n
  exact Sigma.desc fun σ ↦ if (e.symm σ).1 = i then
    (TopCat.toSSet.obj Y).ιChainComplex (e.symm σ).2 else 0

lemma sigmaChainProjectionF_generator {ι : Type} (Y : TopCat) (R : ModuleCat ℚ)
    (i j : ι) (n : ℕ) (τ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj (TopCat.of (Σ _ : ι, Y))).ιChainComplex
        ((TopCat.toSSet.map (sigmaInclusion Y j)).app _ τ) ≫
      sigmaChainProjectionF Y R i n =
        if j = i then (TopCat.toSSet.obj Y).ιChainComplex τ else 0 := by
  classical
  change Sigma.ι (fun _ ↦ R) ((sigmaSimplexEquiv Y n) ⟨j, τ⟩) ≫ _ = _
  simp only [sigmaChainProjectionF, Sigma.ι_comp_desc, Equiv.symm_apply_apply]

lemma sigmaChainProjectionF_map {ι : Type} (Y : TopCat) (R : ModuleCat ℚ)
    (i j : ι) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map (sigmaInclusion Y j)) R).f n ≫
      sigmaChainProjectionF Y R i n = if j = i then 𝟙 _ else 0 := by
  classical
  apply SSet.chainComplex_hom_ext
  intro τ
  rw [SSet.ι_chainComplexMap_f_assoc, sigmaChainProjectionF_generator]
  split_ifs <;> simp

def sigmaChainProjection {ι : Type} (Y : TopCat) (R : ModuleCat ℚ) (i : ι) :
    sigmaChains (ι := ι) Y R ⟶ summandChains Y R where
  f := sigmaChainProjectionF Y R i
  comm' := by
    intro a b hab
    classical
    apply SSet.chainComplex_hom_ext
    intro σ
    obtain ⟨⟨j, τ⟩, rfl⟩ := (singular_sum_simplex_bijective (fun _ : ι ↦ Y) (op ⦋a⦌)).surjective σ
    let k := SSet.chainComplexMap (TopCat.toSSet.map (sigmaInclusion Y j)) R
    have hleft : k.f a ≫ sigmaChainProjectionF Y R i a =
        if j = i then 𝟙 _ else 0 := sigmaChainProjectionF_map Y R i j a
    have hright : k.f b ≫ sigmaChainProjectionF Y R i b =
        if j = i then 𝟙 _ else 0 := sigmaChainProjectionF_map Y R i j b
    have hh : k.f a ≫ sigmaChainProjectionF Y R i a ≫ (summandChains Y R).d a b =
        k.f a ≫ (sigmaChains Y R).d a b ≫ sigmaChainProjectionF Y R i b := by
      rw [← Category.assoc, hleft, ← Category.assoc, k.comm, Category.assoc, hright]
      split_ifs <;> simp
    have H := congrArg (fun f ↦ (TopCat.toSSet.obj Y).ιChainComplex τ ≫ f) hh
    simpa only [k, ← Category.assoc, SSet.ι_chainComplexMap_f] using H

lemma sigmaChainProjection_map {ι : Type} (Y : TopCat) (R : ModuleCat ℚ)
    (i j : ι) :
    SSet.chainComplexMap (TopCat.toSSet.map (sigmaInclusion Y j)) R ≫
      sigmaChainProjection Y R i = if j = i then 𝟙 _ else 0 := by
  classical
  ext n : 1
  change _ ≫ sigmaChainProjectionF Y R i n = _
  rw [sigmaChainProjectionF_map]
  split_ifs <;> rfl

lemma sigmaChainProjection_sum {ι : Type} [Fintype ι] (Y : TopCat) (R : ModuleCat ℚ) :
    ∑ i : ι, sigmaChainProjection Y R i ≫
      SSet.chainComplexMap (TopCat.toSSet.map (sigmaInclusion Y i)) R = 𝟙 _ := by
  classical
  ext n : 1
  apply SSet.chainComplex_hom_ext
  intro σ
  obtain ⟨⟨j, τ⟩, rfl⟩ := (singular_sum_simplex_bijective (fun _ : ι ↦ Y) (op ⦋n⦌)).surjective σ
  rw [show (∑ i : ι, sigmaChainProjection Y R i ≫
      SSet.chainComplexMap (TopCat.toSSet.map (sigmaInclusion Y i)) R).f n =
      ∑ i : ι, (sigmaChainProjection Y R i ≫
        SSet.chainComplexMap (TopCat.toSSet.map (sigmaInclusion Y i)) R).f n from
      map_sum (HomologicalComplex.Hom.fAddMonoidHom n) _ _]
  simp only [HomologicalComplex.comp_f,
    HomologicalComplex.id_f, Preadditive.comp_sum, Category.comp_id]
  have hh (i : ι) : (TopCat.toSSet.obj (TopCat.of (Σ _ : ι, Y))).ιChainComplex
      ((TopCat.toSSet.map (sigmaInclusion Y j)).app _ τ) ≫
      (sigmaChainProjection Y R i).f n ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (sigmaInclusion Y i)) R).f n =
      if j = i then (TopCat.toSSet.obj (TopCat.of (Σ _ : ι, Y))).ιChainComplex
        ((TopCat.toSSet.map (sigmaInclusion Y j)).app _ τ) else 0 := by
    rw [← Category.assoc]
    change (_ ≫ sigmaChainProjectionF Y R i n) ≫ _ = _
    rw [sigmaChainProjectionF_generator]
    split_ifs with h
    · subst i
      simp only [SSet.ι_chainComplexMap_f]
    · simp
  simp_rw [hh]
  simp

lemma sigmaChainProjection_natural {ι : Type} (X Y : TopCat) (f : X ⟶ Y)
    (R : ModuleCat ℚ) (i : ι) :
    let sf : TopCat.of (Σ _ : ι, X) ⟶ TopCat.of (Σ _ : ι, Y) := TopCat.ofHom
      ⟨fun z ↦ ⟨z.1, f z.2⟩, continuous_sigma fun _j ↦ continuous_sigmaMk.comp f.hom.continuous⟩
    SSet.chainComplexMap (TopCat.toSSet.map sf) R ≫ sigmaChainProjection Y R i =
      sigmaChainProjection X R i ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  intro sf
  ext n : 1
  apply SSet.chainComplex_hom_ext
  intro σ
  obtain ⟨⟨j, τ⟩, rfl⟩ := (singular_sum_simplex_bijective (fun _ : ι ↦ X) (op ⦋n⦌)).surjective σ
  change _ ≫ (SSet.chainComplexMap _ R).f n ≫ sigmaChainProjectionF Y R i n =
    _ ≫ sigmaChainProjectionF X R i n ≫ (SSet.chainComplexMap _ R).f n
  rw [SSet.ι_chainComplexMap_f_assoc, ← Category.assoc, sigmaChainProjectionF_generator]
  have he : (TopCat.toSSet.map sf).app (op ⦋n⦌)
      ((TopCat.toSSet.map (sigmaInclusion X j)).app _ τ) =
      (TopCat.toSSet.map (sigmaInclusion Y j)).app _ ((TopCat.toSSet.map f).app _ τ) := rfl
  rw [he, sigmaChainProjectionF_generator]
  split_ifs <;> simp [SSet.ι_chainComplexMap_f]

def sigmaSubspaceInclusion {ι : Type} (Y : TopCat) (A : Set Y) :
    TopCat.of (Σ _ : ι, A) ⟶ TopCat.of (Σ _ : ι, Y) := TopCat.ofHom
  ⟨fun z ↦ ⟨z.1, z.2.val⟩, continuous_sigma fun _ ↦
    continuous_sigmaMk.comp continuous_subtype_val⟩

instance sigmaSubspaceInclusion_mono {ι : Type} (Y : TopCat) (A : Set Y) :
    Mono (sigmaSubspaceInclusion (ι := ι) Y A) := by
  apply (TopCat.mono_iff_injective _).mpr
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst j
  have hxy : x = y := Subtype.ext (congrArg Sigma.snd h)
  subst y
  rfl

abbrev sigmaSubspacePair {ι : Type} (Y : TopCat) (A : Set Y) : SSetPair :=
  SSetPair.of (TopCat.toSSet.map (sigmaSubspaceInclusion (ι := ι) Y A))

def sigmaPairInclusion {ι : Type} (Y : TopCat) (A : Set Y) (i : ι) :
    singularSubspacePair Y A ⟶ sigmaSubspacePair (ι := ι) Y A :=
  SSetPair.homMk (TopCat.toSSet.map (sigmaInclusion (TopCat.of A) i))
    (TopCat.toSSet.map (sigmaInclusion Y i)) (by
      change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

lemma sigmaPair_projection_condition {ι : Type} (Y : TopCat) (A : Set Y)
    (R : ModuleCat ℚ) (i : ι) :
    SSet.chainComplexMap (sigmaSubspacePair (ι := ι) Y A).hom R ≫
      sigmaChainProjection Y R i ≫ (singularSubspacePair Y A).chainComplexπ R = 0 := by
  have h := sigmaChainProjection_natural (TopCat.of A) Y
    (singularSubspaceInclusion Y A) R i
  dsimp only at h
  change SSet.chainComplexMap (TopCat.toSSet.map (sigmaSubspaceInclusion (ι := ι) Y A)) R ≫
    sigmaChainProjection Y R i = _ at h
  change SSet.chainComplexMap (TopCat.toSSet.map (sigmaSubspaceInclusion (ι := ι) Y A)) R ≫ _ = 0
  rw [← Category.assoc, h, Category.assoc]
  exact congrArg (fun f ↦ sigmaChainProjection (TopCat.of A) R i ≫ f)
    ((singularSubspacePair Y A).chainComplex_condition R) |>.trans (comp_zero)

def sigmaRelativeProjection {ι : Type} (Y : TopCat) (A : Set Y)
    (R : ModuleCat ℚ) (i : ι) :
    (sigmaSubspacePair (ι := ι) Y A).chainComplex R ⟶
      (singularSubspacePair Y A).chainComplex R :=
  ((sigmaSubspacePair (ι := ι) Y A).isColimitCokernelCoforkChainComplex R).desc
    (CokernelCofork.ofπ (sigmaChainProjection Y R i ≫
      (singularSubspacePair Y A).chainComplexπ R) (sigmaPair_projection_condition Y A R i))

lemma sigmaRelativeProjection_π {ι : Type} (Y : TopCat) (A : Set Y)
    (R : ModuleCat ℚ) (i : ι) :
    (sigmaSubspacePair (ι := ι) Y A).chainComplexπ R ≫ sigmaRelativeProjection Y A R i =
      sigmaChainProjection Y R i ≫ (singularSubspacePair Y A).chainComplexπ R :=
  by
    exact Cofork.IsColimit.π_desc
      ((sigmaSubspacePair (ι := ι) Y A).isColimitCokernelCoforkChainComplex R)

lemma sigmaRelativeProjection_sum {ι : Type} [Fintype ι] (Y : TopCat) (A : Set Y)
    (R : ModuleCat ℚ) :
    ∑ i : ι, sigmaRelativeProjection Y A R i ≫
      SSetPair.chainComplexMap (sigmaPairInclusion Y A i) R = 𝟙 _ := by
  apply (cancel_epi ((sigmaSubspacePair (ι := ι) Y A).chainComplexπ R)).mp
  rw [Preadditive.comp_sum, Category.comp_id]
  have hnat (i : ι) : (singularSubspacePair Y A).chainComplexπ R ≫
      SSetPair.chainComplexMap (sigmaPairInclusion Y A i) R =
      SSet.chainComplexMap (TopCat.toSSet.map (sigmaInclusion Y i)) R ≫
        (sigmaSubspacePair (ι := ι) Y A).chainComplexπ R :=
    (((SSetPair.chainComplexFunctorπ (ModuleCat ℚ)).app R).naturality
      (sigmaPairInclusion Y A i)).symm
  simp_rw [← Category.assoc, sigmaRelativeProjection_π, Category.assoc, hnat]
  simp_rw [← Category.assoc]
  rw [← Preadditive.sum_comp]
  rw [sigmaChainProjection_sum]
  exact Category.id_comp _

/-- Hatcher, Algebraic Topology, pp.137–138: singular relative homology of a
finite disjoint union of identical pairs vanishes when the component homology
vanishes. Each simplex has a unique component. Selecting its component defines
chain projections, compatible with boundary and relative quotient. The sum of
projection followed by inclusion is identity. Applying homology gives a sum of
maps through the zero component homology, so the identity is zero. -/
theorem sigmaRelativeHomology_isZero {ι : Type} [Fintype ι]
    (Y : TopCat) (A : Set Y) (R : ModuleCat ℚ) (n : ℕ)
    (hz : IsZero ((singularSubspacePair Y A).homology R n)) :
    IsZero ((sigmaSubspacePair (ι := ι) Y A).homology R n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have h := congrArg (fun f ↦ HomologicalComplex.homologyMap f n)
    (sigmaRelativeProjection_sum (ι := ι) Y A R)
  simp only [HomologicalComplex.homologyMap_id] at h
  rw [← h]
  change (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map _ = 0
  rw [Functor.map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Functor.map_comp]
  rw [hz.eq_zero_of_tgt ((HomologicalComplex.homologyFunctor (ModuleCat ℚ)
    (ComplexShape.down ℕ) n).map (sigmaRelativeProjection Y A R i)), zero_comp]


def sigmaSubtypeHomeomorph {ι : Type} (Y : TopCat) (A : Set Y) :
    (Σ _ : ι, A) ≃ₜ {z : (Σ _ : ι, Y) // z.2 ∈ A} := by
  let f : (Σ _ : ι, A) → {z : (Σ _ : ι, Y) // z.2 ∈ A} :=
    fun z ↦ ⟨⟨z.1, z.2.val⟩, z.2.property⟩
  have hf : Topology.IsEmbedding f := by
    have h := (Topology.isEmbedding_sigmaMap (σ := fun _ : ι ↦ A) (τ := fun _ : ι ↦ (Y : Type)) (f₁ := id)
      (f₂ := fun _ : ι ↦ (Subtype.val : A → Y)) Function.injective_id).mpr
      (fun _ ↦ Topology.IsEmbedding.subtypeVal)
    exact h.codRestrict _ (fun z ↦ z.2.property)
  exact hf.toHomeomorphOfSurjective (by
    rintro ⟨⟨i, y⟩, hy⟩
    exact ⟨⟨i, ⟨y, hy⟩⟩, rfl⟩)

def sigmaSubspacePairIso {ι : Type} (Y : TopCat) (A : Set Y) :
    sigmaSubspacePair (ι := ι) Y A ≅
      singularSubspacePair (TopCat.of (Σ _ : ι, Y)) {z | z.2 ∈ A} := by
  let e : TopCat.of (Σ _ : ι, A) ≅ TopCat.of {z : (Σ _ : ι, Y) // z.2 ∈ A} :=
    TopCat.isoOfHomeo (sigmaSubtypeHomeomorph (ι := ι) Y A)
  refine MorphismProperty.Arrow.isoMk (TopCat.toSSet.mapIso e) (Iso.refl _) ?_
  change TopCat.toSSet.map e.hom ≫ TopCat.toSSet.map _ =
    TopCat.toSSet.map _ ≫ 𝟙 _
  rw [Category.comp_id, ← Functor.map_comp]
  congr 1

theorem sigmaSingularSubspaceHomology_isZero {ι : Type} [Fintype ι]
    (Y : TopCat) (A : Set Y) (R : ModuleCat ℚ) (n : ℕ)
    (hz : IsZero ((singularSubspacePair Y A).homology R n)) :
    IsZero ((singularSubspacePair (TopCat.of (Σ _ : ι, Y))
      {z | z.2 ∈ A}).homology R n) :=
  (sigmaRelativeHomology_isZero (ι := ι) Y A R n hz).of_iso
    ((SSetPair.homologyFunctor R n).mapIso (sigmaSubspacePairIso Y A)).symm

end HolomorphicAnosov.Cubical


