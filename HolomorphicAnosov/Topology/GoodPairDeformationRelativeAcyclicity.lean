import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Topology.Category.TopPair
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian

/-! Relative acyclicity of a strong deformation retract. -/

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homotopy

universe w u v

/-- A strong deformation retract has zero relative singular homology in every natural-number degree, with arbitrary categorical coefficient object. (Hatcher, Prop. 2.22) -/
theorem good_pair_deformation_relative_acyclicity
    {X : Type w} [TopologicalSpace X] {A V : Set X} {hAV : A ⊆ V}
    (d : StrongDeformationRetract A V hAV)
    (C : Type u) [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    let B : Set V := {x | x.val ∈ A}
    let Q := TopPair.ofSubset (X := TopCat.of V) B
    letI : Mono Q.map := (TopCat.mono_iff_injective _).2 Q.isEmbedding_map.injective
    let P := SSetPair.of (TopCat.toSSet.map Q.map)
    IsZero (P.homology R n) := by
  dsimp
  let B : Set V := {x | x.val ∈ A}
  let rb : C(V, B) :=
    { toFun := fun v =>
        ⟨⟨(d.retraction v).val, hAV (d.retraction v).property⟩,
          d.retraction v |>.property⟩
      continuous_toFun :=
        Continuous.subtype_mk
          ((ContinuousMap.inclusion hAV).comp d.retraction).continuous
          (fun v => (d.retraction v).property) }
  let j : C(B, V) :=
    { toFun := fun x => x.val
      continuous_toFun := continuous_subtype_val }
  have hjr : rb.comp j = ContinuousMap.id B := by
    ext x
    let a0 : A := ⟨x.val.val, x.property⟩
    have h := congrArg (fun f : C(A, A) => f a0) d.retraction_inclusion
    have hx : ContinuousMap.inclusion hAV a0 = x.val := by
      ext
      rfl
    have h' : d.retraction x.val = a0 := by simpa [hx] using h
    have hv : ContinuousMap.inclusion hAV (d.retraction x.val) = x.val := by
      rw [h']
      exact hx
    change (ContinuousMap.inclusion hAV (d.retraction x.val)).val = x.val.val
    exact congrArg Subtype.val hv
  let Q : TopPair := TopPair.ofSubset (X := TopCat.of V) B
  let : Mono Q.map := (TopCat.mono_iff_injective _).2 Q.isEmbedding_map.injective
  let P := SSetPair.of (TopCat.toSSet.map Q.map)
  change IsZero (P.homology R n)
  let D : TopPair := TopPair.of (𝟙 (TopCat.of B)) Topology.IsEmbedding.id
  have hQmap : Q.map = TopCat.ofHom j := by rfl
  have ha : (𝟙 (TopCat.of B)) ≫ D.map = Q.map ≫ TopCat.ofHom rb := by
    change (𝟙 (TopCat.of B)) ≫ (𝟙 (TopCat.of B)) = Q.map ≫ TopCat.ofHom rb
    rw [hQmap]
    simp only [Category.id_comp]
    apply TopCat.Hom.ext
    apply ContinuousMap.ext
    intro x
    change x = rb (j x)
    have hx := congrArg (fun f : C(B, B) => f x) hjr
    simpa [B, j, ContinuousMap.comp_apply] using hx.symm
  have hb : (𝟙 (TopCat.of B)) ≫ Q.map = D.map ≫ TopCat.ofHom j := by
    change (𝟙 (TopCat.of B)) ≫ TopCat.ofHom j =
      (𝟙 (TopCat.of B)) ≫ TopCat.ofHom j
    rfl
  let a : Q ⟶ D := TopPair.ofHom (X := Q) (Y := D) (TopCat.ofHom rb) (𝟙 _) ha
  let b : D ⟶ Q := TopPair.ofHom (X := D) (Y := Q) (TopCat.ofHom j) (𝟙 _) hb
  have hc : (𝟙 (TopCat.of B)) ≫ Q.map = Q.map ≫ TopCat.ofHom (j.comp rb) := by
    change (𝟙 (TopCat.of B)) ≫ TopCat.ofHom j =
      TopCat.ofHom j ≫ TopCat.ofHom (j.comp rb)
    apply TopCat.Hom.ext
    apply ContinuousMap.ext
    intro x
    change j x = j (rb (j x))
    have hx := congrArg (fun f : C(B, B) => f x) hjr
    simpa [ContinuousMap.comp_apply] using congrArg j hx.symm
  let c : Q ⟶ Q := TopPair.ofHom (X := Q) (Y := Q)
    (TopCat.ofHom (j.comp rb)) (𝟙 _) hc
  have hab : a ≫ b = c := by
    apply MorphismProperty.Arrow.Hom.ext
    · dsimp [a, b, c]
      rfl
    · change TopCat.ofHom rb ≫ TopCat.ofHom j = TopCat.ofHom (j.comp rb)
      apply TopCat.Hom.ext
      apply ContinuousMap.ext
      intro x
      rfl
  have H : TopPair.Homotopy (𝟙 Q) (a ≫ b) := by
    rw [hab]
    refine ⟨?_, TopCat.Homotopy.refl (𝟙 _), ?_⟩
    · have heq : TopCat.ofHom (j.comp rb) =
          TopCat.ofHom ((ContinuousMap.inclusion hAV).comp d.retraction) := by
        apply TopCat.Hom.ext
        apply ContinuousMap.ext
        intro x
        rfl
      change TopCat.Homotopy (𝟙 (TopCat.of V)) (TopCat.ofHom (j.comp rb))
      rw [heq]
      exact d.homotopy.toHomotopy
    · ext z
      rcases z with ⟨x, t⟩
      change d.homotopy (TopCat.I.homeomorph t, x.val) = x.val
      exact d.homotopy.eq_fst (TopCat.I.homeomorph t) x.property
  have hSing := HolomorphicAnosov.relative_singular_homotopy_invariance C H R
  have hmap := hSing.2 n
  have hzeroD : IsZero ((HolomorphicAnosov.singularPairFunctor.obj D).homology R n) := by
    let SD := HolomorphicAnosov.singularPairFunctor.obj D
    have hi : IsIso SD.hom := by
      change IsIso (TopCat.toSSet.map (𝟙 (TopCat.of B)))
      rw [TopCat.toSSet.map_id]
      infer_instance
    let hzchain : IsZero (SD.chainComplex R) := SSetPair.isZero_chainComplex SD R
    exact Functor.map_isZero (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n) hzchain
  have hzeroQ : IsZero ((HolomorphicAnosov.singularPairFunctor.obj Q).homology R n) := by
    apply (IsZero.iff_id_eq_zero _).2
    have hz : SSetPair.homologyMap (HolomorphicAnosov.singularPairFunctor.map a) R n = 0 := by
      apply hzeroD.eq_of_tgt
    have hz' : SSetPair.homologyMap (HolomorphicAnosov.singularPairFunctor.map (a ≫ b)) R n = 0 := by
      rw [HolomorphicAnosov.singularPairFunctor.map_comp, SSetPair.homologyMap_comp]
      rw [hz, CategoryTheory.Limits.zero_comp]
    have hid := hmap.trans hz'
    simpa [HolomorphicAnosov.singularPairFunctor.map_id, SSetPair.homologyMap_id] using hid
  exact hzeroQ

/-- Every ordinary relative singular homology class of a strong deformation retract is zero, with any abelian coefficient group and including degree zero. (Hatcher, Prop. 2.22) -/
theorem good_pair_deformation_relative_acyclicity_abelian
    {X : Type w} [TopologicalSpace X] {A V : Set X} {hAV : A ⊆ V}
    (d : StrongDeformationRetract A V hAV) (G : Type u) [AddCommGroup G] (n : ℕ) :
    let B : Set V := {x | x.val ∈ A}
    let Q := TopPair.ofSubset (X := TopCat.of V) B
    letI : Mono Q.map := (TopCat.mono_iff_injective _).2 Q.isEmbedding_map.injective
    let P := SSetPair.of (TopCat.toSSet.map Q.map)
    ∀ x : P.homology (C := AddCommGrpCat.{max w u})
      (AddCommGrpCat.of (ULift.{w} G)) n, x = 0 := by
  dsimp
  intro x
  have hz := good_pair_deformation_relative_acyclicity d (AddCommGrpCat.{max w u})
    (AddCommGrpCat.of (ULift.{w} G)) n
  have hid := (IsZero.iff_id_eq_zero _).1 hz
  have hx := congrArg (fun f => f x) hid
  simpa using hx

end HolomorphicAnosov.Topology.Homotopy

