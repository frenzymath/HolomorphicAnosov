import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeEvaluation
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity

noncomputable section
open Set Topology
namespace HolomorphicAnosov

/-- An original point and a vector in possibly different bundles over the same
base, with the topology induced from the pair of original total spaces. -/
structure ParameterGraphMixedPoint {A : Type*} (E F : A → Type*) where
  base : A
  point : E base
  vector : F base

namespace ParameterGraphMixedPoint
variable {A Z : Type*} {E F : A → Type*}
  [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
instance : TopologicalSpace (ParameterGraphMixedPoint E F) :=
  TopologicalSpace.induced (fun z ↦ ((⟨z.base,z.point⟩ : Sigma E),
    (⟨z.base,z.vector⟩ : Sigma F))) inferInstance

theorem continuous_pair : Continuous (fun z : ParameterGraphMixedPoint E F ↦
    ((⟨z.base,z.point⟩ : Sigma E),(⟨z.base,z.vector⟩ : Sigma F))) := continuous_induced_dom

theorem continuous_point : Continuous (fun z : ParameterGraphMixedPoint E F ↦
    (⟨z.base,z.point⟩ : Sigma E)) := continuous_pair.fst

theorem continuous_vector : Continuous (fun z : ParameterGraphMixedPoint E F ↦
    (⟨z.base,z.vector⟩ : Sigma F)) := continuous_pair.snd

theorem continuous_mk [TopologicalSpace Z] (b : Z → A) (x : ∀z,E (b z))
    (v : ∀z,F (b z))
    (hx : Continuous (fun z ↦ (⟨b z,x z⟩ : Sigma E)))
    (hv : Continuous (fun z ↦ (⟨b z,v z⟩ : Sigma F))) :
    Continuous (fun z ↦ (⟨b z,x z,v z⟩ : ParameterGraphMixedPoint E F)) := by
  apply continuous_induced_rng.mpr
  exact hx.prodMk hv
end ParameterGraphMixedPoint

/-- HPS pp.57–58 and 62: the rational preimage slope action preserves
continuous evaluation in the original bundles. Its numerator is the difference
of the composed receiving slope evaluation and the upper-right block evaluation.
For the horizontal denominator, evaluate the upper-left block minus the receiving
slope applied to the lower-left block on fixed source-frame vectors. All these
sections are continuous by the given block evaluations and the continuous graph
return. The uniform inverse bound and parameter inverse continuity then prove
continuity of the resulting preimage slope on every tangent point. -/
theorem parameter_graph_preimage_slope_evaluation_continuous
    {A : Type*} [TopologicalSpace A] {X Y : A → Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    (e : FiniteRankNormedAtlas (E := X)) (f : FiniteRankNormedAtlas (E := Y))
    (h : A → A) (hh : Continuous h) (K : ∀p,Y p → Y (h p))
    (hK : Continuous (fun z : Sigma Y ↦ (⟨h z.1,K z.1 z.2⟩ : Sigma Y)))
    (AA : ∀p,Y p → X p →L[ℝ] X (h p))
    (BB : ∀p,Y p → Y p →L[ℝ] X (h p))
    (CC : ∀p,Y p → X p →L[ℝ] Y (h p))
    (DD : ∀p,Y p → Y p →L[ℝ] Y (h p))
    (hAA : Continuous (fun z : ParameterGraphMixedPoint Y X ↦
      (⟨h z.base,AA z.base z.point z.vector⟩ : Sigma X)))
    (hBB : Continuous (fun z : ParameterGraphTangentPoint Y ↦
      (⟨h z.base,BB z.base z.point z.vector⟩ : Sigma X)))
    (hCC : Continuous (fun z : ParameterGraphMixedPoint Y X ↦
      (⟨h z.base,CC z.base z.point z.vector⟩ : Sigma Y)))
    (hDD : Continuous (fun z : ParameterGraphTangentPoint Y ↦
      (⟨h z.base,DD z.base z.point z.vector⟩ : Sigma Y)))
    (P : ∀p,Y p → Y p →L[ℝ] X p)
    (hP : Continuous (fun z : ParameterGraphTangentPoint Y ↦
      (⟨z.base,P z.base z.point z.vector⟩ : Sigma X)))
    (J : ∀p,Y p → X p ≃L[ℝ] X (h p))
    (hJ : ∀p y,(J p y).toContinuousLinearMap =
      AA p y - (P (h p) (K p y)).comp (CC p y))
    (b : ℝ) (hbound : ∀p y,‖(J p y).symm.toContinuousLinearMap‖ ≤ b) :
    Continuous (fun z : ParameterGraphTangentPoint Y ↦
      (⟨z.base,(J z.base z.point).symm
        (P (h z.base) (K z.base z.point) (DD z.base z.point z.vector) -
          BB z.base z.point z.vector)⟩ : Sigma X)) := by
  let Z := ParameterGraphTangentPoint Y
  have hbase : Continuous (fun z : Z ↦ z.base) :=
    (parameter_graph_atlas_projection_continuous f).comp
      ParameterGraphTangentPoint.continuous_point
  have hreturn : Continuous (fun z : Z ↦
      (⟨h z.base,K z.base z.point⟩ : Sigma Y)) :=
    hK.comp ParameterGraphTangentPoint.continuous_point
  have hnum : Continuous (fun z : Z ↦
      (⟨h z.base,P (h z.base) (K z.base z.point) (DD z.base z.point z.vector) -
        BB z.base z.point z.vector⟩ : Sigma X)) :=
    parameter_graph_atlas_sub_continuous e _ (hh.comp hbase) _ _
      (hP.comp (ParameterGraphTangentPoint.continuous_mk _ _ _ hreturn hDD)) hBB
  apply parameter_graph_atlas_inverse_apply_continuous e e
    (fun z : Z ↦ z.base) (fun z : Z ↦ h z.base) hbase (hh.comp hbase)
    (fun z ↦ J z.base z.point) b (fun z ↦ hbound z.base z.point) _ hnum
  intro i w
  let U := {z : Z // z.base ∈ (e.chart i).baseSet}
  let v : ∀z : U,X z.val.base := fun z ↦ (e.coordinates i z.val.base z.property).symm w
  have hv : Continuous (fun z : U ↦ (⟨z.val.base,v z⟩ : Sigma X)) := by
    exact (atlas_frame_continuous e i).comp
      (((hbase.comp continuous_subtype_val).subtype_mk (fun z : U ↦ z.property)).prodMk
        continuous_const)
  have hm : Continuous (fun z : U ↦
      (⟨z.val.base,z.val.point,v z⟩ : ParameterGraphMixedPoint Y X)) :=
    ParameterGraphMixedPoint.continuous_mk _ _ _
      (ParameterGraphTangentPoint.continuous_point.comp continuous_subtype_val) hv
  have hPc : Continuous (fun z : U ↦
      (⟨h z.val.base,P (h z.val.base) (K z.val.base z.val.point)
        (CC z.val.base z.val.point (v z))⟩ : Sigma X)) :=
    hP.comp (ParameterGraphTangentPoint.continuous_mk _ _ _
      (hreturn.comp continuous_subtype_val) (hCC.comp hm))
  have hdiff := parameter_graph_atlas_sub_continuous e _
    ((hh.comp hbase).comp continuous_subtype_val) _ _ (hAA.comp hm) hPc
  apply hdiff.congr
  intro z
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    exact (DFunLike.congr_fun (hJ z.val.base z.val.point) (v z)).symm

/-- HPS pp.55–56 and 62: the image rational slope action preserves original
bundle evaluation continuity after any continuous choice of source anchor and
receiving vector. On fixed source-frame vectors the horizontal operator is the
continuous sum A+BP. Its uniformly bounded inverse applied to the receiving
vector is continuous by parameter inverse continuity. Applying C and DP to this
continuous inverse vector and adding gives the continuous image slope evaluation.
The source anchor may be selected by an inverse graph return; its continuity is
the only property of that selection needed here. -/
theorem parameter_graph_image_slope_evaluation_continuous
    {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z] {X Y : A → Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    (e : FiniteRankNormedAtlas (E := X)) (f : FiniteRankNormedAtlas (E := Y))
    (h : A → A) (hh : Continuous h)
    (AA : ∀p,X p → X p →L[ℝ] X (h p))
    (BB : ∀p,X p → Y p →L[ℝ] X (h p))
    (CC : ∀p,X p → X p →L[ℝ] Y (h p))
    (DD : ∀p,X p → Y p →L[ℝ] Y (h p))
    (hAA : Continuous (fun z : ParameterGraphTangentPoint X ↦
      (⟨h z.base,AA z.base z.point z.vector⟩ : Sigma X)))
    (hBB : Continuous (fun z : ParameterGraphMixedPoint X Y ↦
      (⟨h z.base,BB z.base z.point z.vector⟩ : Sigma X)))
    (hCC : Continuous (fun z : ParameterGraphTangentPoint X ↦
      (⟨h z.base,CC z.base z.point z.vector⟩ : Sigma Y)))
    (hDD : Continuous (fun z : ParameterGraphMixedPoint X Y ↦
      (⟨h z.base,DD z.base z.point z.vector⟩ : Sigma Y)))
    (P : ∀p,X p → X p →L[ℝ] Y p)
    (hP : Continuous (fun z : ParameterGraphTangentPoint X ↦
      (⟨z.base,P z.base z.point z.vector⟩ : Sigma Y)))
    (J : ∀p,X p → X p ≃L[ℝ] X (h p))
    (hJ : ∀p x,(J p x).toContinuousLinearMap = AA p x + (BB p x).comp (P p x))
    (b : ℝ) (hbound : ∀p x,‖(J p x).symm.toContinuousLinearMap‖ ≤ b)
    (p : Z → A) (hp : Continuous p) (x : ∀z,X (p z))
    (hx : Continuous (fun z ↦ (⟨p z,x z⟩ : Sigma X)))
    (v : ∀z,X (h (p z)))
    (hv : Continuous (fun z ↦ (⟨h (p z),v z⟩ : Sigma X))) :
    Continuous (fun z ↦ (⟨h (p z),
      CC (p z) (x z) ((J (p z) (x z)).symm (v z)) +
      DD (p z) (x z) (P (p z) (x z) ((J (p z) (x z)).symm (v z)))⟩ : Sigma Y)) := by
  let w : ∀z,X (p z) := fun z ↦ (J (p z) (x z)).symm (v z)
  have hw : Continuous (fun z ↦ (⟨p z,w z⟩ : Sigma X)) := by
    apply parameter_graph_atlas_inverse_apply_continuous e e p (fun z ↦ h (p z)) hp
      (hh.comp hp) (fun z ↦ J (p z) (x z)) b (fun z ↦ hbound (p z) (x z)) v hv
    intro i u
    let U := {z : Z // p z ∈ (e.chart i).baseSet}
    let t : ∀z : U,X (p z.val) := fun z ↦ (e.coordinates i (p z.val) z.property).symm u
    have ht : Continuous (fun z : U ↦ (⟨p z.val,t z⟩ : Sigma X)) :=
      (atlas_frame_continuous e i).comp
        (((hp.comp continuous_subtype_val).subtype_mk (fun z : U ↦ z.property)).prodMk
          continuous_const)
    have htan : Continuous (fun z : U ↦
        (⟨p z.val,x z.val,t z⟩ : ParameterGraphTangentPoint X)) :=
      ParameterGraphTangentPoint.continuous_mk _ _ _ (hx.comp continuous_subtype_val) ht
    have hmix : Continuous (fun z : U ↦
        (⟨p z.val,x z.val,P (p z.val) (x z.val) (t z)⟩ : ParameterGraphMixedPoint X Y)) :=
      ParameterGraphMixedPoint.continuous_mk _ _ _ (hx.comp continuous_subtype_val)
        (hP.comp htan)
    have hsum := parameter_graph_atlas_add_continuous e _
      ((hh.comp hp).comp continuous_subtype_val) _ _ (hAA.comp htan) (hBB.comp hmix)
    apply hsum.congr
    intro z
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      exact (DFunLike.congr_fun (hJ (p z.val) (x z.val)) (t z)).symm
  have htan : Continuous (fun z ↦ (⟨p z,x z,w z⟩ : ParameterGraphTangentPoint X)) :=
    ParameterGraphTangentPoint.continuous_mk p x w hx hw
  have hmix : Continuous (fun z ↦
      (⟨p z,x z,P (p z) (x z) (w z)⟩ : ParameterGraphMixedPoint X Y)) :=
    ParameterGraphMixedPoint.continuous_mk _ _ _ hx (hP.comp htan)
  exact parameter_graph_atlas_add_continuous f _ (hh.comp hp) _ _
    (hCC.comp htan) (hDD.comp hmix)

end HolomorphicAnosov
