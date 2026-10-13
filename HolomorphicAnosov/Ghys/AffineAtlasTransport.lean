import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Ghys.AffineChartsCompatibleTransport

/-!
This file transports a complex affine atlas along a biholomorphism. (Ghys, Lemma 3.2) -/

noncomputable section
open Set Filter
open scoped Topology _root_.Topology Manifold ContDiff

namespace HolomorphicAnosov.Ghys

universe u v
variable {L : Type u} {L' : Type v}
  [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
  [TopologicalSpace L'] [ChartedSpace (ComplexModel 1) L']

/-- A biholomorphism `T` transports an affine atlas to an affine atlas with exactly the charts `c ∘
T⁻¹`. (Ghys, Lemma 3.2, pp. 590–591) -/
theorem exists_complexAffineAtlas_transport
    (T : Diffeomorph (complexModel 1) (complexModel 1) L L' ∞)
    (A : ComplexAffineAtlas L) :
    ∃ B : ComplexAffineAtlas L',
      B.charts = {d | ∃ c ∈ A.charts,
        d = T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c} := by
  let t := T.toHomeomorph.symm.toOpenPartialHomeomorph
  refine ⟨{
    charts := {d | ∃ c ∈ A.charts, d = t.trans c}
    cover := ?_
    holomorphic := ?_
    compatible := ?_
  }, rfl⟩
  · intro x
    obtain ⟨c, hc, hx⟩ := A.cover (T.symm x)
    refine ⟨t.trans c, ⟨c, hc, rfl⟩, ?_⟩
    simpa [t] using hx
  · rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hc₁, hc₂⟩ := A.holomorphic c hc
    constructor
    · exact hc₁.comp T.symm.contMDiff.contMDiffOn (fun x hx ↦ hx.2)
    · have ht : (t.trans c).target = c.target := by simp [t]
      rw [ht]
      exact T.contMDiff.comp_contMDiffOn hc₂
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ x hx
    have hcx : T.symm x ∈ c.source := by
      simpa [t] using hx.1
    have hdx : T.symm x ∈ d.source := by
      simpa [t] using hx.2
    exact affineChartsCompatible_transport T c d
      (A.compatible c hc d hd) x hx


end HolomorphicAnosov.Ghys
