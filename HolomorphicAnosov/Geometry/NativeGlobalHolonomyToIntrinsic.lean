import HolomorphicAnosov.Geometry.OriginalAnosovGlobalUnstableHolonomy
import HolomorphicAnosov.Geometry.GlobalHolonomy

/-! This file transfers whole-leaf holonomy, its local germs, and its path laws to intrinsic
partition leaves through point-preserving biholomorphisms. (Zhang, Prop. 2.9, p. 10; Ghys, pp.
594, 597–598; Hirsch–Pugh–Shub, p. 116) -/

noncomputable section
namespace HolomorphicAnosov
open Filter Set
open scoped ContDiff Manifold Topology _root_.Topology
universe u

variable {d s t : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
  (B : NativeTransverseAsymptoticIdentification.{u, u} f Ps Pu s t)

/-- Whole-leaf holonomy transfers to intrinsic partition leaves under point-preserving biholomorphic
identifications, preserving its local germs and path laws. (Zhang, Prop. 2.9, p. 10; Ghys, Thm
B, pp. 594, 597–598; Hirsch–Pugh–Shub, p. 116) -/
theorem native_global_holonomy_to_intrinsic
    (C : letI := B.realAmbientCharts; IntrinsicComplexUnstableLeaves B.F)
    (E : ∀ x : M, letI := B.realAmbientCharts
      letI := C.charts (Quotient.mk B.F.unstablePartition x)
      letI := B.unstableTopology x
      letI := B.unstableCharts x
      letI := (B.complexU1 x).charts
      Biholomorph 1 1 (B.F.ULeaf x) (UnstableAsymptoticLeaf f x))
    (hE : letI := B.realAmbientCharts
      ∀ x : M, letI := B.unstableTopology x
        letI := B.unstableCharts x
        letI := (B.complexU1 x).charts
        letI := C.charts (Quotient.mk B.F.unstablePartition x)
        (E x).toHomeomorph = B.unstableClassHomeomorph x)
    (G : NativeGlobalSHolonomyData B) :
    letI := B.realAmbientCharts; HasGlobalSHolonomy B.F C := by
  let := B.realAmbientCharts
  let : ∀ x : M, TopologicalSpace (UnstableAsymptoticLeaf f x) :=
    fun x ↦ B.unstableTopology x
  let : ∀ x : M, ChartedSpace (ComplexModel 1) (UnstableAsymptoticLeaf f x) :=
    fun x ↦ letI := B.unstableCharts x; (B.complexU1 x).charts
  let : ∀ q : Quotient B.F.unstablePartition,
      TopologicalSpace (IntrinsicFoliationLeaf B.F.unstablePartition q) :=
    B.F.unstableTopology
  let : ∀ q : Quotient B.F.unstablePartition,
      ChartedSpace (ComplexModel 1) (IntrinsicFoliationLeaf B.F.unstablePartition q) :=
    C.charts
  have hforward (x : M) : (E x : _ → _) = B.unstableClassHomeomorph x := by
    change ((E x).toHomeomorph : _ → _) = _
    rw [hE]
  have hcast {x y : M} (h : x = y) (z : B.F.ULeaf x) :
      E y (castIntrinsicULeaf B.F h z) = castNativeReceivingLeaf h (E x z) := by
    cases h
    rfl
  refine ⟨{
    localContinuation := G.localContinuation
    transport := fun {q} {x y} γ ↦ ((E x.val).trans (G.transport γ)).trans (E y.val).symm
    extends_local := ?_
    restriction := ?_
    concatenation := ?_
    reversal := ?_ }⟩
  · intro q x y γ
    apply Germ.coe_eq.mpr
    have hpoint : E x.val (B.F.uPoint x.val) = nativeReceivingPoint B x.val := by
      rw [hforward]
      rfl
    have ht : Tendsto (E x.val) (𝓝 (B.F.uPoint x.val))
        (𝓝 (nativeReceivingPoint B x.val)) := by
      rw [← hpoint]
      exact (E x.val).continuous.continuousAt
    have hh := ht.eventually (Germ.coe_eq.mp (G.extends_local γ))
    filter_upwards [hh] with z hz
    change (E y.val).symm (G.transport γ (E x.val z)) = _
    apply (E y.val).injective
    change E y.val ((E y.val).symm (G.transport γ (E x.val z))) = E y.val _
    rw [(E y.val).apply_symm_apply, hz, hcast]
    apply congrArg (castNativeReceivingLeaf (congrArg Subtype.val γ.target))
    rw [← hcast]
    rw [hforward, hforward]
    change B.unstableClassHomeomorph (γ 1).val
      (((B.unstableClassHomeomorph (γ 0).val).symm
        (B.unstableClassHomeomorph (γ 0).val
          (castIntrinsicULeaf B.F (congrArg Subtype.val γ.source).symm z))) |> 
        ((G.localContinuation γ).representative 0 1 (by simp)).map) = _
    rw [Homeomorph.symm_apply_apply]
  · intro q x y γ a b c hab hbc z
    change (E (γ c).val).symm (G.transport (γ.subpath a c) (E (γ a).val z)) =
      (E (γ c).val).symm (G.transport (γ.subpath b c)
        (E (γ b).val ((E (γ b).val).symm
          (G.transport (γ.subpath a b) (E (γ a).val z)))))
    rw [Diffeomorph.apply_symm_apply, G.restriction γ a b c hab hbc]
  · intro q x y z γ η w
    change (E z.val).symm (G.transport (γ.trans η) (E x.val w)) =
      (E z.val).symm (G.transport η
        (E y.val ((E y.val).symm (G.transport γ (E x.val w)))))
    rw [Diffeomorph.apply_symm_apply, G.concatenation γ η]
  · intro q x y γ z
    change (E x.val).symm (G.transport γ.symm (E y.val z)) =
      (E x.val).symm ((G.transport γ).symm (E y.val z))
    exact congrArg (E x.val).symm (G.reversal γ (E y.val z))

end HolomorphicAnosov

