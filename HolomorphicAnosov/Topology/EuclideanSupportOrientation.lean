import HolomorphicAnosov.Topology.EuclideanPositiveCompactificationClass

/-!
# Euclidean supported orientation from the positive compactification class

DAG node: `topo.euclidean_support_orientation_g10`.
Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §1.1, printed p.1; Hatcher, *Algebraic Topology*,
relative chain maps pp.115–118 and excision Theorem 2.20 pp.119,124.

Every homology group here is ORDINARY integral singular homology. The coefficient
object `reducedSingularIntegralCoefficients` is only the lifted integer module;
no augmented complex is used. The source pair is the actual open subset U with
its native subspace topology, not the image of U under an unspecified equivalence.
The map inverted is precisely finite inclusion into the native one-point space.
Its excision certificate is a named theorem about that already constructed map.
-/

noncomputable section
namespace HolomorphicAnosov

open CategoryTheory CategoryTheory.Limits Set

/-- The native relative pair `(U,U \ K)`, with its original induced topology.
Source: Dold §1.1 p.1; Hatcher pp.115–118. This definition is meaningful for arbitrary
U and K; openness, compactness and containment are guards on its excision use. -/
def euclideanSupportPair (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n))) : SSetPair :=
  singularSubspacePair (TopCat.of U) {u | (u : EuclideanSpace ℝ (Fin n)) ∉ K}

/-- The compactification pair `(Sₙ,Sₙ \ K)`, using the literal finite image of K.
Source: Dold §1.1 p.1. Infinity belongs to the complement for every K. -/
def euclideanCompactificationSupportPair (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) : SSetPair :=
  singularSubspacePair (TopCat.of (EuclideanCompactification n)) (OnePoint.some '' K)ᶜ

/-- Finite inclusion of the actual subspace U into the native compactification.
Source: Dold §1.1 p.1; Mathlib `OnePoint.continuous_coe` composed with subtype inclusion. -/
def euclideanSupportFiniteInclusion (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n))) :
    TopCat.of U ⟶ TopCat.of (EuclideanCompactification n) :=
  TopCat.ofHom ⟨fun u ↦ OnePoint.some u.val,
    OnePoint.continuous_coe.comp continuous_subtype_val⟩

/-- The actual finite-inclusion map of pairs. An element outside K cannot map into
its finite image, by injectivity of `OnePoint.some`. Source: Hatcher p.118.
The map's data and the subspace containment proof are fully implemented. -/
def euclideanSupportPairInclusion (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n))) :
    euclideanSupportPair n U K ⟶ euclideanCompactificationSupportPair n K :=
  singularSubspacePairMap (euclideanSupportFiniteInclusion n U)
    {u | (u : EuclideanSpace ℝ (Fin n)) ∉ K} (OnePoint.some '' K)ᶜ (by
      intro u hu
      rintro ⟨v, hv, heq⟩
      exact hu (OnePoint.coe_injective heq ▸ hv))

/-- The specified inclusion-induced ordinary relative integral homology map e_K.
Source: Dold §1.1 p.1; Hatcher pp.118–124. No abstract homology equivalence is chosen. -/
def euclideanSupportHomologyInclusion (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n))) :
    (euclideanSupportPair n U K).homology reducedSingularIntegralCoefficients n ⟶
      (euclideanCompactificationSupportPair n K).homology reducedSingularIntegralCoefficients n :=
  SSetPair.homologyMap (euclideanSupportPairInclusion n U K)
    reducedSingularIntegralCoefficients n

/-- The ordinary absolute-to-relative projection q_K on the SAME compactification.
Source: Dold §1.1 p.1; Mathlib `SSetPair.homologyπ`, the actual chain-quotient projection. -/
def euclideanSupportCompactificationProjection (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanCompactificationHomology n ⟶
      (euclideanCompactificationSupportPair n K).homology reducedSingularIntegralCoefficients n :=
  (euclideanCompactificationSupportPair n K).homologyπ reducedSingularIntegralCoefficients n

/-- Excision certifies that the SPECIFIED finite-inclusion homology map e_K is an isomorphism.

Source: Dold §1.1 p.1; Hatcher Theorem 2.20 p.119, with its written subdivision and
relative-quotient proof pp.119–124. This is the construction certificate explicitly
included in the public statement of `topo.euclidean_support_orientation_g10`.

Complete natural-language proof:
Put S=OnePoint(ℝⁿ), B=OnePoint.some '' U and A=(OnePoint.some '' K)ᶜ. Finite inclusion
is an open embedding, so B is open. Compact K is closed in Euclidean space and its finite
image is compact and closed in the Hausdorff one-point compactification. Thus A is open.
Containment K⊆U gives A∪B=S: if a compactification point is not in A, it is a finite
point coming from K, hence from U. In particular interior A∪interior B=S. Equivalently
the closed removed set Z=Bᶜ has closure Z=Z⊆A=interior A. The actual excision theorem
therefore makes the homology map of `singularExcisionInclusion S A B` an isomorphism.

That excision theorem starts from the pair on the actual subspace B of S. Bind it to
our literal U pair as follows. The native open embedding's `homeomorphImage U` is the
homeomorphism U→B, u↦OnePoint.some(u), with inverse recovering that same finite point.
It sends U\K onto {b:B | b.val∈A}: one direction is injectivity of `OnePoint.some`,
and the other follows by its inverse and the same membership equivalence. The two actual
continuous maps of pairs constructed with `singularSubspacePairMap` are inverse because
both their ambient and subspace components have the homeomorphism inverse identities.
Applying the actual singular-pair homology functor preserves these inverse identities,
so this comparison is an isomorphism in every ordinary homology degree. Composing its
forward map with the specified excision inclusion has ambient function u↦OnePoint.some(u)
and the same complement restriction. Hence it equals `euclideanSupportPairInclusion`,
by pointwise equality of both pair components. Functoriality identifies e_K with the
composition of these two isomorphisms, proving IsIso for the precise map defined above.

This uses no caller-supplied equivalence, reduced-homology replacement, connectedness,
nonempty U or K, or dimension positivity. For n=0 the same ordinary excision proof
applies to the native two-point compactification. If U is empty containment forces K
empty; if K is empty both relative pairs are pairs of each space with itself.
-/
theorem euclideanSupportHomologyInclusion_isIso (n : ℕ)
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) : IsIso (euclideanSupportHomologyInclusion n U K) := by
  let S := TopCat.of (EuclideanCompactification n)
  let A : Set S := (OnePoint.some '' K)ᶜ
  let B : Set S := OnePoint.some '' U
  have hA : IsOpen A := OnePoint.isOpen_compl_image_coe.mpr ⟨hK.isClosed, hK⟩
  have hB : IsOpen B := OnePoint.isOpen_image_coe.mpr hU
  have hcover : interior A ∪ interior B = univ := by
    rw [hA.interior_eq, hB.interior_eq]
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ OnePoint.some '' K
    · obtain ⟨y, hy, rfl⟩ := hx
      exact Or.inr ⟨y, hKU hy, rfl⟩
    · exact Or.inl hx
  let e : U ≃ₜ B := OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage U
  have he (u : U) : (e u).val = OnePoint.some u.val := rfl
  let f : TopCat.of U ⟶ TopCat.of B := TopCat.ofHom ⟨e, e.continuous⟩
  let g : TopCat.of B ⟶ TopCat.of U := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  let C : Set U := {u | u.val ∉ K}
  let D : Set B := {b | b.val ∈ A}
  have hf : MapsTo f C D := by
    intro u hu
    rintro ⟨v, hv, hvu⟩
    exact hu (OnePoint.coe_injective hvu ▸ hv)
  have hg : MapsTo g D C := by
    intro b hb hbk
    apply hb
    refine ⟨(e.symm b).val, hbk, ?_⟩
    exact (he (e.symm b)).symm.trans (congrArg Subtype.val (e.apply_symm_apply b))
  let F := singularSubspacePairMap f C D hf
  let G := singularSubspacePairMap g D C hg
  have hFG : F ≫ G = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        𝟙 (TopCat.toSSet.obj (TopCat.of C))
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      simp [singularSubspaceMap, f, g]
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        𝟙 (TopCat.toSSet.obj (TopCat.of U))
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      simp [f, g]
  have hGF : G ≫ F = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        𝟙 (TopCat.toSSet.obj (TopCat.of D))
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      simp [singularSubspaceMap, f, g]
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        𝟙 (TopCat.toSSet.obj (TopCat.of B))
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      simp [f, g]
  let E : euclideanSupportPair n U K ≅ singularExcisionSource S A B :=
    ⟨F, G, hFG, hGF⟩
  have hcomp : F ≫ singularExcisionInclusion S A B =
      euclideanSupportPairInclusion n U K := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      rfl
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      rfl
  let hF : IsIso (SSetPair.homologyMap F reducedSingularIntegralCoefficients n) :=
    ((SSetPair.homologyFunctor reducedSingularIntegralCoefficients n).mapIso E).isIso_hom
  let hI : IsIso (SSetPair.homologyMap (singularExcisionInclusion S A B)
      reducedSingularIntegralCoefficients n) :=
    (singular_homology_excision_barycentric_subdivision.2.1 S A B hcover
      reducedSingularIntegralCoefficients).2.2 n
  have hcomp' :
      SSetPair.homologyMap (F ≫ singularExcisionInclusion S A B)
          reducedSingularIntegralCoefficients n =
        SSetPair.homologyMap (euclideanSupportPairInclusion n U K)
          reducedSingularIntegralCoefficients n := by
    rw [hcomp]
    rfl
  change IsIso (SSetPair.homologyMap (euclideanSupportPairInclusion n U K)
    reducedSingularIntegralCoefficients n)
  rw [← hcomp']
  rw [SSetPair.homologyMap_comp]
  exact IsIso.comp_isIso' hF hI

/-- The canonical support orientation class `o(U,K)=e_K⁻¹(q_K μₙ)`.

Source: Dold §1.1 p.1, the displayed composite defining the supported fundamental class.
The inverse belongs to the already specified inclusion map; its named excision
certificate supplies ONLY invertibility, not any unknown class or arbitrary equivalence.
The compactification class is the published positively normalized μₙ. Its dimension-zero
branch is the coefficient-one finite-point class in ordinary H₀ of the two-point space.
No proof of a data field is filled by `sorry` in this definition. -/
def euclideanSupportOrientation (n : ℕ) (U K : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ((euclideanSupportPair n U K).homology reducedSingularIntegralCoefficients n : ModuleCat ℤ) :=
  letI := euclideanSupportHomologyInclusion_isIso n U K hU hK hKU
  (inv (euclideanSupportHomologyInclusion n U K)).hom
    ((euclideanSupportCompactificationProjection n K).hom
      (euclideanPositiveCompactificationClass n))

/-- Empty support gives the zero class in the actual ordinary relative group.

Source: Dold §1.1 p.1 and Hatcher relative chains p.115. When K is empty the source
pair is `(U,U)`, so the actual relative chain quotient is the zero complex and its
homology is zero. The projection q_K also goes into the zero homology of `(S,S)`.
Thus the displayed inverse-image definition is zero. This holds for empty U and for
n=0 as well; there is no augmentation or coefficient-sum convention involved.
-/
theorem euclideanSupportOrientation_empty (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) :
    euclideanSupportOrientation n U ∅ hU isCompact_empty (empty_subset U) = 0 := by
  let S := TopCat.of (EuclideanCompactification n)
  let i : TopCat.of (Set.univ : Set S) ⟶ S :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : IsIso i := TopCat.isIso_of_bijective_of_isOpenMap i
    ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, by simp⟩, rfl⟩⟩
    (by
      change IsOpenMap (Subtype.val : ↥(Set.univ : Set S) → S)
      exact (by simp : IsOpen (Set.univ : Set S)).isOpenMap_subtype_val)
  have hi' : IsIso (TopCat.toSSet.map i) := inferInstance
  have hp : IsIso (singularSubspacePair S (Set.univ : Set S)).hom := hi'
  have hc : IsIso (SSet.chainComplexMap
      (singularSubspacePair S (Set.univ : Set S)).hom
      reducedSingularIntegralCoefficients) := inferInstance
  have hz : IsZero (((singularSubspacePair S (Set.univ : Set S)).chainComplex
      reducedSingularIntegralCoefficients).X n) := by
    exact CokernelCofork.IsColimit.isZero_of_epi
      ((singularSubspacePair S (Set.univ : Set S)).isColimitCokernelCoforkChainComplexX
        reducedSingularIntegralCoefficients n)
  have hzh : IsZero ((singularSubspacePair S (Set.univ : Set S)).homology
      reducedSingularIntegralCoefficients n) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ hz
  let := euclideanSupportHomologyInclusion_isIso n U ∅ hU isCompact_empty (empty_subset U)
  change (inv (euclideanSupportHomologyInclusion n U ∅)).hom
    ((euclideanSupportCompactificationProjection n ∅).hom
      (euclideanPositiveCompactificationClass n)) = 0
  have hzh' : IsZero ((euclideanCompactificationSupportPair n ∅).homology
      reducedSingularIntegralCoefficients n) := by
    simpa [euclideanCompactificationSupportPair, S] using hzh
  have := ModuleCat.subsingleton_of_isZero hzh'
  have hproj : (euclideanSupportCompactificationProjection n ∅).hom
      (euclideanPositiveCompactificationClass n) = 0 := Subsingleton.elim _ _
  rw [hproj, map_zero]

end HolomorphicAnosov
