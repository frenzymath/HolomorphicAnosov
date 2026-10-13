import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusChartedSpace
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusChartInverse
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusProjection
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.LiftedTorusProjectionLocalHomeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

/-- Two lifts of the same torus point differ in an integer coordinate vector.
The continuous displacement of an atlas transition is therefore locally constant,
so the transition is locally a translation and is smooth. This is the explicit
product-quotient chart argument of source Step 8. -/
theorem liftedTorus_isManifold (r : ℕ) :
    letI := liftedTorusChartedSpace.{u} r
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin r))) ∞
      (ULift.{u} (UnitAddTorus (Fin r))) := by
  let := liftedTorusChartedSpace.{u} r
  apply isManifold_of_contDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin r))) ∞ _
  intro e e' he he'
  suffices hs : ContDiffOn ℝ ∞ (e.symm.trans e') (e.symm.trans e').source by
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ] using hs
  let t := e.symm.trans e'
  have hq : ∀ w ∈ t.source, liftedTorusProjection.{u} r (t w) = liftedTorusProjection r w := by
    intro w hw
    calc
      liftedTorusProjection r (t w) = e'.symm (e' (e.symm w)) :=
        (congrFun (liftedTorus_chart_inverse r e' he') _).symm
      _ = e.symm w := e'.left_inv hw.2
      _ = liftedTorusProjection r w := congrFun (liftedTorus_chart_inverse r e he) w
  have hm : ∀ w : t.source, ∀ i : Fin r,
      (t w - (w : EuclideanSpace ℝ (Fin r))) i ∈ AddSubgroup.zmultiples (1 : ℝ) := by
    intro w i
    have heq := congrArg (fun x : ULift.{u} (UnitAddTorus (Fin r)) ↦ x.down i)
      (hq w w.property)
    change ((t w) i : UnitAddCircle) = (w.val i : UnitAddCircle) at heq
    exact QuotientAddGroup.eq_iff_sub_mem.mp heq
  let D : t.source → (Fin r → AddSubgroup.zmultiples (1 : ℝ)) :=
    fun w i ↦ ⟨(t w - (w : EuclideanSpace ℝ (Fin r))) i, hm w i⟩
  have hD : Continuous D := by
    apply continuous_pi
    intro i
    exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin r ↦ ℝ) i).continuous.comp
      (t.continuousOn.domRestrict.sub continuous_subtype_val)).subtype_mk _)
  have hloc : IsLocallyConstant D := (IsLocallyConstant.iff_continuous D).mpr hD
  intro z hz
  obtain ⟨W, hW, hzW, hconst⟩ := hloc.exists_open (⟨z, hz⟩ : t.source)
  let V := Subtype.val '' W
  have hV : IsOpen V := t.open_source.isOpenMap_subtype_val W hW
  have hzV : z ∈ V := ⟨⟨z, hz⟩, hzW, rfl⟩
  have heq : Set.EqOn t (fun w ↦ w + (t z - z)) V := by
    rintro w ⟨v, hv, rfl⟩
    have hd := hconst v hv
    ext i
    have hi := congrArg (fun f : Fin r → AddSubgroup.zmultiples (1 : ℝ) ↦ (f i : ℝ)) hd
    change (t v) i - (v : EuclideanSpace ℝ (Fin r)) i = (t z) i - z i at hi
    change (t v) i = v.val i + ((t z) i - z i)
    linarith
  have htrans : ContDiff ℝ ∞ (fun w : EuclideanSpace ℝ (Fin r) ↦ w + (t z - z)) :=
    contDiff_id.add contDiff_const
  exact ((htrans.contDiffOn.congr heq).contDiffAt (hV.mem_nhds hzV)).contDiffWithinAt

end HolomorphicAnosov
