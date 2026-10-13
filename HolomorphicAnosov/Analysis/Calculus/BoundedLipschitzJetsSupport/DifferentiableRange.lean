import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.DifferentiableContinuous

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- HPS Theorem (3.3), p.29: differentiable jets equal linear jets. The derivative remainder identifies a differentiable representative with its derivative. Conversely every bounded linear map is differentiable at zero, so its jet belongs to the differentiable subspace. -/
theorem differentiableJets_eq_linearJet_range :
    differentiableJets X Y = LinearMap.range (linearJet X Y) := by
  apply le_antisymm
  · intro j hj
    rcases hj with ⟨q, hqj, hqdiff⟩
    let L : X →L[ℝ] Y := fderiv ℝ (q : X → Y) 0
    have hF : HasFDerivAt (q : X → Y) L 0 := hqdiff.hasFDerivAt
    have hO := hF.isLittleO
    rw [Asymptotics.isLittleO_iff] at hO
    have hq0 : (q : X → Y) 0 = 0 := q.property.1
    have hclass : jetClass X Y q = jetClass X Y (linearRepresentative X Y L) := by
      apply (jetClass_eq_iff X Y q (linearRepresentative X Y L)).2
      intro ε hε
      filter_upwards [(hO hε).filter_mono nhdsWithin_le_nhds] with x hx
      change ‖(q : X → Y) x - (linearRepresentative X Y L : X → Y) x‖ ≤ ε * ‖x‖
      simpa [linearRepresentative, hq0, sub_eq_add_neg] using hx
    refine ⟨L, ?_⟩
    exact hclass.symm.trans hqj
  · rintro j ⟨L, rfl⟩
    change HasDifferentiableRepresentative X Y (linearJet X Y L)
    refine ⟨linearRepresentative X Y L, rfl, ?_⟩
    exact (L.hasFDerivAt (x := (0 : X))).differentiableAt

def linearJetSubtype :
    (X →L[ℝ] Y) →ₗ[ℝ] ↥(differentiableJets X Y) where
  toFun L := ⟨linearJet X Y L, by
    rw [differentiableJets_eq_linearJet_range X Y]
    exact ⟨L, rfl⟩⟩
  map_add' L K := by ext; rfl
  map_smul' a L := by ext; rfl


end HolomorphicAnosov.BoundedLipschitzJets

