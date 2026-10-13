import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Complex.Basic
import HolomorphicAnosov.Topology.DiskChartOpenInteriorBoundary

namespace HolomorphicAnosov
open Set

/-- The two presentations of a subset of a subtype have the same topology. -/
def subsetSubtypeHomeomorph {X : Type*} [TopologicalSpace X] (A U : Set X) (hU : U ⊆ A) :
    U ≃ₜ {x : A | (x : X) ∈ U} where
  toFun x := ⟨⟨x,hU x.property⟩,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Restrict a homeomorphism between carriers to corresponding ambient subsets.
The correspondence is given pointwise, retaining the same literal map. -/
def homeomorphRestrictSubsets {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (U : Set X) (V : Set Y)
    (hU : U ⊆ A) (hV : V ⊆ B) (H : A ≃ₜ B)
    (hUV : ∀ x : A, (x : X) ∈ U ↔ (H x : Y) ∈ V) : U ≃ₜ V :=
  ((subsetSubtypeHomeomorph A U hU).trans (H.subtype (p := fun x : A ↦ (x : X) ∈ U) (q := fun y : B ↦ (y : Y) ∈ V) hUV)).trans
    (subsetSubtypeHomeomorph B V hV).symm

/-- A carrier homeomorphism taking an ambient subset onto another transports
their closures wherever the carriers contain those closures. Relative closure
is the preimage of ambient closure under the subtype embedding. -/
theorem homeomorph_carriers_closure_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (U : Set X) (V : Set Y)
    (hU : U ⊆ A) (hV : V ⊆ B) (H : A ≃ₜ B)
    (hUV : ∀ x : A, (x : X) ∈ U ↔ (H x : Y) ∈ V) :
    ∀ x : A, (x : X) ∈ closure U ↔ (H x : Y) ∈ closure V := by
  let U' : Set A := Subtype.val ⁻¹' U
  let V' : Set B := Subtype.val ⁻¹' V
  have hUi : Subtype.val '' U' = U := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩; exact hz
    · intro hx; exact ⟨⟨x,hU hx⟩,hx,rfl⟩
  have hVi : Subtype.val '' V' = V := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩; exact hz
    · intro hx; exact ⟨⟨x,hV hx⟩,hx,rfl⟩
  have hHimage : H '' U' = V' := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩; exact (hUV x).mp hx
    · intro hy
      exact ⟨H.symm y,(hUV (H.symm y)).mpr (by simpa only [H.apply_symm_apply] using (show (y : Y) ∈ V from hy)),H.apply_symm_apply y⟩
  have hUcl := Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image U'
  have hVcl := Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image V'
  have hHcl := H.isEmbedding.closure_eq_preimage_closure_image U'
  rw [hUi] at hUcl
  rw [hVi] at hVcl
  rw [hHimage,hUcl,hVcl] at hHcl
  intro x
  exact Set.ext_iff.mp hHcl x

/-- A homeomorphism of carriers that matches an open set with a bounded open
convex set restricts to a closed-disk chart, with the correct interior and
frontier. Transport closures through the subtype embeddings, then compose
with the ambient convex-body gauge homeomorphism. -/
theorem carrier_homeomorph_closed_disk_chart (A B U V : Set ℂ)
    (hU : IsOpen U) (hV : IsOpen V) (hVne : V.Nonempty)
    (hVconvex : Convex ℝ V) (hVbounded : Bornology.IsBounded V)
    (hUA : closure U ⊆ A) (hVB : closure V ⊆ B) (H : A ≃ₜ B)
    (hUV : ∀ x : A, (x : ℂ) ∈ U ↔ (H x : ℂ) ∈ V) :
    ∃ G : closure U ≃ₜ Metric.closedBall (0 : ℂ) 1,
      (∀ x : closure U, (x : ℂ) ∈ U ↔ (G x : ℂ) ∈ Metric.ball (0 : ℂ) 1) ∧
      (∀ x : closure U, (x : ℂ) ∈ frontier U ↔ (G x : ℂ) ∈ Metric.sphere (0 : ℂ) 1) := by
  have hUsub : U ⊆ A := subset_closure.trans hUA
  have hVsub : V ⊆ B := subset_closure.trans hVB
  have hcl := homeomorph_carriers_closure_iff A B U V hUsub hVsub H hUV
  let Hcl := homeomorphRestrictSubsets A B (closure U) (closure V) hUA hVB H hcl
  obtain ⟨F,hi,hclosed,hfront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hVconvex
      (hV.interior_eq.symm ▸ hVne) hVbounded
  rw [hV.interior_eq] at hi
  let G := Hcl.trans ((F.image (closure V)).trans (Homeomorph.setCongr hclosed))
  have hGval (x : closure U) : (G x : ℂ) = F (H ⟨x,hUA x.property⟩ : ℂ) := rfl
  have hFball (y : ℂ) : F y ∈ Metric.ball (0 : ℂ) 1 ↔ y ∈ V := by
    rw [← hi]
    exact F.injective.mem_set_image
  have hFsphere (y : ℂ) : F y ∈ Metric.sphere (0 : ℂ) 1 ↔ y ∈ frontier V := by
    rw [← hfront]
    exact F.injective.mem_set_image
  refine ⟨G,?_,?_⟩
  · intro x
    rw [hGval,hFball]
    exact hUV ⟨x,hUA x.property⟩
  · intro x
    rw [hGval,hFsphere,hU.frontier_eq,hV.frontier_eq]
    have hh := hcl ⟨x,hUA x.property⟩
    have hu := hUV ⟨x,hUA x.property⟩
    exact and_congr hh (not_congr hu)

/-- Restricting a carrier homeomorphism to an ambient open plane set has open
image in the plane. Apply the independent planar open-image theorem to the
continuous injective map from that open set. -/
theorem carrier_homeomorph_open_image (A B U : Set ℂ) (H : A ≃ₜ B)
    (hU : IsOpen U) (hUA : U ⊆ A) :
    IsOpen ((fun x : A ↦ (H x : ℂ)) '' (Subtype.val ⁻¹' U)) := by
  let f : U → ℂ := fun x ↦ H ⟨x,hUA x.property⟩
  have hc : Continuous f := continuous_subtype_val.comp
    (H.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : A ↦ (z : ℂ)) (H.injective (Subtype.ext he)))
  have heq : range f = (fun x : A ↦ (H x : ℂ)) '' (Subtype.val ⁻¹' U) := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,hUA x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  rw [← heq]
  exact complex_planar_open_range U hU f hc hi

/-- The literal image of a compact closure under a continuous map is the
closure of the image. One inclusion is continuity, the other follows because
the compact image is closed and contains the image of the original set. -/
theorem image_closure_eq_of_compact_closure {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (U : Set X) (f : X → Y) (hc : IsCompact (closure U))
    (hf : ContinuousOn f (closure U)) : f '' closure U = closure (f '' U) := by
  apply Subset.antisymm hf.image_closure
  exact closure_minimal (image_mono subset_closure) (hc.image_of_continuousOn hf).isClosed

end HolomorphicAnosov
