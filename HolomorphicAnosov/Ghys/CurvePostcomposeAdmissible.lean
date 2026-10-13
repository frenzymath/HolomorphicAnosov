import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Biholomorphic postcomposition preserves admissibility of curve germs. (Ghys, Lemma 3.2, p.591)
-/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov.Ghys
universe u v
variable {L : Type u} [TopologicalSpace L] [ChartedSpace ℂ L]
variable {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]
variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L']

omit [IsManifold 𝓘(ℂ) ∞ L] [IsManifold 𝓘(ℂ) ∞ L'] in
/-- Postcomposition by a biholomorphism preserves admissibility of curve germs. (Ghys, Lemma 3.2,
p.591) -/
theorem curve_postcompose_admissible
    (T : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) L L' ∞)
    (γ : CurveParamGerm L) : CurveGermAdmissible L' (γ.1.map (T : L → L')) := by
  obtain ⟨e, h0, he, hesym, hγ⟩ := γ.2
  let t : OpenPartialHomeomorph L L' := T.toHomeomorph.toOpenPartialHomeomorph
  let r : OpenPartialHomeomorph ℂ L' := e.trans t
  have hs : r.source = e.source := by
    simp [r, t]
  have ht : ∀ z ∈ r.target, T.symm z ∈ e.target := by
    intro z hz
    simpa [r, t, OpenPartialHomeomorph.trans_target] using hz.2
  have hr : ContMDiffOn (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞ r r.source := by
    rw [hs]
    have hT : ContMDiffOn (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) ∞ (T : L → L') Set.univ :=
      T.contMDiff.contMDiffOn
    apply hT.comp he
    intro z hz
    exact Set.mem_univ _
  have hrs : ContMDiffOn (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞ r.symm r.target := by
    have hTs : ContMDiffOn (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) ∞ (T.symm : L' → L) Set.univ :=
      T.symm.contMDiff.contMDiffOn
    simpa [r, t, Function.comp_def] using
      (hesym.comp (hTs.mono (Set.subset_univ _)) ht)
  refine ⟨r, ?_, hr, hrs, ?_⟩
  · rw [hs]
    exact h0
  rw [← hγ]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [] with z
  rfl


end HolomorphicAnosov.Ghys
