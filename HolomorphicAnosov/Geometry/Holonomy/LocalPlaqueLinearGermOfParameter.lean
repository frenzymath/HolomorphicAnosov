import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Maps.Basic

noncomputable section
open Set Filter Topology _root_.Topology
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- A linear coordinate identity in the common transverse parameter gives the same identity for the original intrinsic plaque-transport germ.    Motivating source: Nisoli, Chapter 1, Remark 1.3.2 and equation (1.9), pp.21–22; Zhang Lemma 2.8, pp.9–10. -/
theorem local_plaque_linear_germ_of_parameter {s t : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations s t M) {x y : M}
    (e : LocalPlaqueTransport F x y)
    (φx : F.ULeaf x → ℂ) (φy : F.ULeaf y → ℂ) (D : ℂ ≃L[ℂ] ℂ)
    (jx : FoliationCoordinateDisk t → F.ULeaf x)
    (jy : FoliationCoordinateDisk t → F.ULeaf y)
    (hx : ∀ v, (jx v).val = ((F.box e.box).chart (e.first, v)).val)
    (hy : ∀ v, (jy v).val = ((F.box e.box).chart (e.second, v)).val)
    (hD : (fun v ↦ φy (jy v)) =ᶠ[𝓝 e.transverse] fun v ↦ D (φx (jx v))) :
    (fun z ↦ φy (e.map z)) =ᶠ[𝓝 (F.uPoint x)] fun z ↦ D (φx z) := by
  have hlabel : F.unstableLabel e.box e.first = Quotient.mk F.unstablePartition x :=
    (F.unstable_label e.box e.first e.transverse).symm.trans
      (congrArg (Quotient.mk F.unstablePartition) e.first_point)
  let j : FoliationCoordinateDisk t → F.ULeaf x := fun v ↦
    ⟨((F.box e.box).chart (e.first, v)).val,
      (F.unstable_label e.box e.first v).trans hlabel⟩
  have hj : IsOpenEmbedding j := by
    exact Eq.rec (motive := fun q h ↦
      letI := F.unstableTopology q
      IsOpenEmbedding (fun v : FoliationCoordinateDisk t ↦
        (⟨((F.box e.box).chart (e.first,v)).val,
          (F.unstable_label e.box e.first v).trans h⟩ :
            IntrinsicFoliationLeaf F.unstablePartition q)))
      (F.unstable_plaque e.box e.first) hlabel
  have hjx : jx = j := funext fun v ↦ Subtype.ext (hx v)
  have hw : jx e.transverse = F.uPoint x :=
    Subtype.ext ((hx e.transverse).trans e.first_point)
  have ho : IsOpenEmbedding jx := hjx.symm ▸ hj
  have hs : ∀ᶠ v in 𝓝 e.transverse, jx v ∈ e.map.source :=
    (ho.continuous.continuousAt).eventually
      (e.map.open_source.mem_nhds (hw.symm ▸ e.source_point))
  rw [← hw, ← ho.map_nhds_eq e.transverse]
  change (fun v ↦ φy (e.map (jx v))) =ᶠ[𝓝 e.transverse] fun v ↦ D (φx (jx v))
  filter_upwards [hs, hD] with v hv hDv
  have he : e.map (jx v) = jy v := by
    apply Subtype.ext
    exact (e.coordinate_map (jx v) v hv (hx v).symm).trans (hy v).symm
  exact (congrArg φy he).trans hDv


end HolomorphicAnosov
