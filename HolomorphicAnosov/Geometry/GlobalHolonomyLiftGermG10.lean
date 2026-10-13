import HolomorphicAnosov.Geometry.GlobalHolonomy
import Mathlib.Topology.Covering.Basic

namespace HolomorphicAnosov

open Filter Set _root_.Topology
universe u v w

variable {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
  (F : TransverseContinuousFoliations.{u, v} s t M)
  (C : IntrinsicComplexUnstableLeaves F) (G : GlobalSHolonomyData F C)

/-- Global holonomy sends the marked source point to the marked target point. (Ghys, pp.594, 598) -/
theorem global_holonomy_map_point_g10
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y) :
    G.transport γ (F.uPoint x.val) = F.uPoint y.val := by
  have hcastPoint {a b : M} (h : a = b) :
      castIntrinsicULeaf F h (F.uPoint a) = F.uPoint b := by
    cases h
    rfl
  have h := (Germ.coe_eq.mp (G.extends_local γ)).eq_of_nhds
  rw [hcastPoint, (G.localContinuation γ).representative 0 1 (by simp) |>.map_point,
    hcastPoint] at h
  exact h

/-- Global holonomy lifted through a pointed target-leaf covering lift has the germ of any
continuous local lift with the same projected germ and marked value. (Ghys, proof of Thm B,
p.598; Hatcher, Prop. 1.34, pp.62–63) -/
theorem global_holonomy_lift_germ_g10
    {q : Quotient F.stablePartition}
    {x y : IntrinsicFoliationLeaf F.stablePartition q} (γ : Path x y)
    {E : Type w} [TopologicalSpace E] (p : E → M) (hp : IsCoveringMap p)
    (lift : F.ULeaf y.val → E) (hlift : Continuous lift)
    (hproj : ∀ z, p (lift z) = z.val)
    (localLift : F.ULeaf x.val → E)
    (hlocal : ContinuousAt localLift (F.uPoint x.val))
    (hpoint : localLift (F.uPoint x.val) = lift (F.uPoint y.val))
    (hgerm : (fun z ↦ p (localLift z)) =ᶠ[𝓝 (F.uPoint x.val)]
      (fun z ↦ (castIntrinsicULeaf F (congrArg Subtype.val γ.target)
        ((G.localContinuation γ).representative 0 1 (by simp) |>.map
          (castIntrinsicULeaf F (congrArg Subtype.val γ.source).symm z))).val)) :
    (fun z ↦ lift (G.transport γ z)) =ᶠ[𝓝 (F.uPoint x.val)] localLift := by
  let := C.charts (Quotient.mk F.unstablePartition x.val)
  let := C.charts (Quotient.mk F.unstablePartition y.val)
  have hstart : lift (G.transport γ (F.uPoint x.val)) = localLift (F.uPoint x.val) := by
    rw [global_holonomy_map_point_g10 F C G γ, hpoint]
  obtain ⟨U, hU, hxU, hinj⟩ :=
    hp.isLocalHomeomorph.isLocallyInjective (localLift (F.uPoint x.val))
  have hwhole := (hlift.comp (G.transport γ).toHomeomorph.continuous).continuousAt
    (x := F.uPoint x.val)
  have hUwhole : ∀ᶠ z in 𝓝 (F.uPoint x.val), lift (G.transport γ z) ∈ U :=
    hwhole.eventually (hU.mem_nhds (by
      change lift (G.transport γ (F.uPoint x.val)) ∈ U
      rw [hstart]
      exact hxU))
  have hUlocal := hlocal.eventually (hU.mem_nhds hxU)
  filter_upwards [hUwhole, hUlocal, hgerm, Germ.coe_eq.mp (G.extends_local γ)]
    with z hz₁ hz₂ hz₃ hz₄
  apply hinj hz₁ hz₂
  rw [hproj, hz₄]
  exact hz₃.symm

end HolomorphicAnosov
