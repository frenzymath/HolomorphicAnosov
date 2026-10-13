import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.SlopeLimsup

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Descent of the concrete slope to the quotient, HPS p. 27.
If q-r is little-o, an eventual bound C for r and epsilon for q-r give
the eventual bound C+epsilon for q, by the norm triangle inequality. Infima
then give slope(q) ≤ slope(r)+epsilon; let epsilon tend to zero and reverse
q,r. Nonemptiness and lower boundedness come from boundedness and the
nonnegative bound convention. No norm on the quotient is assumed here. -/
theorem representativeSlope_eq_of_quotientRel
    (q r : BoundedRepresentative X Y)
    (h : (littleORepresentatives X Y).quotientRel q r) :
    representativeSlope X Y q = representativeSlope X Y r := by
  have hsub := (Submodule.quotientRel_def (littleORepresentatives X Y)).mp h
  change IsLittleORepresentative X Y ((q : X → Y) - (r : X → Y)) at hsub
  have slope_le (p t : BoundedRepresentative X Y)
      (hpt : IsLittleORepresentative X Y ((p : X → Y) - (t : X → Y))) :
      representativeSlope X Y p ≤ representativeSlope X Y t := by
    have hp : BddBelow (slopeBounds X Y p) :=
      ⟨0, fun _ hC ↦ hC.1⟩
    obtain ⟨_, D, hD, htD⟩ := t.property
    have ht : (slopeBounds X Y t).Nonempty := ⟨D, hD, htD⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    have hmain : representativeSlope X Y p - ε ≤ representativeSlope X Y t := by
      change sInf (slopeBounds X Y p) - ε ≤ sInf (slopeBounds X Y t)
      apply le_csInf ht
      intro C hC
      have hpc : C + ε ∈ slopeBounds X Y p := by
        refine ⟨add_nonneg hC.1 hε.le, ?_⟩
        filter_upwards [hC.2, hpt ε hε] with x htx hdiff
        calc
          ‖(p : X → Y) x‖ =
              ‖((p : X → Y) x - (t : X → Y) x) + (t : X → Y) x‖ := by simp
          _ ≤ ‖(p : X → Y) x - (t : X → Y) x‖ + ‖(t : X → Y) x‖ :=
            norm_add_le _ _
          _ ≤ ε * ‖x‖ + C * ‖x‖ := add_le_add hdiff htx
          _ = (C + ε) * ‖x‖ := by ring
      have hpinf := csInf_le hp hpc
      linarith
    linarith
  apply le_antisymm (slope_le q r hsub)
  apply slope_le r q
  intro ε hε
  filter_upwards [hsub ε hε] with x hx
  simpa only [Pi.sub_apply, norm_sub_rev] using hx

/-- The quotient norm data are obtained by descent of the actual slope, HPS p. 27. -/
def jetNorm : BoundedJet X Y → ℝ :=
  Quotient.lift (representativeSlope X Y)
    (fun q r h => representativeSlope_eq_of_quotientRel X Y q r h)

/-- The norm function on J_b is the concrete descended slope, HPS (3.3), p. 27. -/
instance : Norm (BoundedJet X Y) := ⟨jetNorm X Y⟩


end HolomorphicAnosov.BoundedLipschitzJets

