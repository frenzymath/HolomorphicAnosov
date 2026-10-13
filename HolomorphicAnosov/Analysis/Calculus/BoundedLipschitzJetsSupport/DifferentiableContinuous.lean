import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LinearRepresentativeBound

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- HPS Theorem (3.3), p.29: the derivative at zero represents the same jet as a differentiable map. The derivative remainder is little-o of the input norm because q(0)=0. Equality of jet classes then supplies the globally continuous linear representative. -/
theorem differentiableJets_le_continuousJets :
    differentiableJets X Y ≤ continuousJets X Y := by
  intro j hj
  rcases hj with ⟨q, hqj, hqdiff⟩
  let L : X →L[ℝ] Y := fderiv ℝ (q : X → Y) 0
  have hF : HasFDerivAt (q : X → Y) L 0 := by
    exact hqdiff.hasFDerivAt
  have hO := hF.isLittleO
  rw [Asymptotics.isLittleO_iff] at hO
  have hq0 : (q : X → Y) 0 = 0 := q.property.1
  have hclass : jetClass X Y q = jetClass X Y (linearRepresentative X Y L) := by
    apply (jetClass_eq_iff X Y q (linearRepresentative X Y L)).2
    intro ε hε
    filter_upwards [(hO hε).filter_mono nhdsWithin_le_nhds] with x hx
    change ‖(q : X → Y) x - (linearRepresentative X Y L : X → Y) x‖ ≤ ε * ‖x‖
    simpa [linearRepresentative, hq0, sub_eq_add_neg] using hx
  refine ⟨linearRepresentative X Y L, hclass.symm.trans hqj, Set.univ,
    isOpen_univ, Set.mem_univ _, L.continuous.continuousOn⟩


end HolomorphicAnosov.BoundedLipschitzJets

