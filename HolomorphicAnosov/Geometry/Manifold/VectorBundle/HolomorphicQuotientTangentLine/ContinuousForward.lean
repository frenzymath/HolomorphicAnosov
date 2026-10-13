import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Pretrivialization
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ContinuousQuotientBase
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.QuotientProjectionMap

/-! Continuity of the forward local tangent quotient coordinates (Demailly, V §1, pp.253–254, §11,
p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The forward local quotient coordinate map is continuous on its source for the coinduced total-
space topology (Demailly, V §1, pp.253–254, §11, p.267, (14.1), p.273). -/
theorem QuotientLocalData.continuousOn_forward
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLocalData P) :
    ContinuousOn D.pretrivialization D.pretrivialization.source := by
  have hopen : IsOpen D.pretrivialization.source :=
    D.V.isOpen.preimage (continuous_quotient_base P)
  apply ((quotient_projection_quotient_map P).continuousOn_isOpen_iff hopen).mpr
  have hs : ContinuousOn (fun p : TangentBundle (complexModel d) X ↦ D.θ p.proj p.snd)
      (TotalSpace.proj ⁻¹' (D.V : Set X)) := by
    intro p hp
    exact (D.hscalar p hp).continuousAt.continuousWithinAt
  refine (((FiberBundle.continuous_proj (ComplexModel d)
    (TangentSpace (complexModel d))).continuousOn).prodMk hs).congr ?_
  intro p hp
  change (p.proj, if h : p.proj ∈ D.V then D.L p.proj h ((P p.proj).mkQ p.snd) else 0) =
    (p.proj, D.θ p.proj p.snd)
  have hx : p.proj ∈ D.V := hp
  rw [dite_eq_left hx, D.apply_mk]


end HolomorphicAnosov
