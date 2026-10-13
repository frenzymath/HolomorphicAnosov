import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity

open Set Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- The inverse fibre coordinates of a finite-rank normed atlas define a continuous total-space
frame over each chart domain (Hirsch–Pugh–Shub, p. 8). -/
lemma atlas_frame_continuous
    {A : Type*} [TopologicalSpace A] {E : A → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [TopologicalSpace (Sigma E)]
    (e : FiniteRankNormedAtlas (E := E)) (i : A) :
    Continuous (fun z : (e.chart i).baseSet × FiniteFiberModel (e.rank i) ↦
      (⟨z.1.val, (e.coordinates i z.1.val z.1.property).symm z.2⟩ : Sigma E)) := by
  have hc : Continuous (fun z : (e.chart i).baseSet × FiniteFiberModel (e.rank i) ↦
      (e.chart i).toOpenPartialHomeomorph.symm (z.1.val, z.2)) :=
    (e.chart i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z ↦ (e.chart i).mem_target.mpr z.1.property)
  apply hc.congr
  intro z
  have happ : e.chart i
      (⟨z.1.val, (e.coordinates i z.1.val z.1.property).symm z.2⟩ : Sigma E) =
      (z.1.val, z.2) := by
    rw [e.chart_apply i z.1.val z.1.property]
    simp
  rw [← happ]
  exact (e.chart i).toOpenPartialHomeomorph.left_inv
    ((e.chart i).mem_source.mpr z.1.property)

end
end HolomorphicAnosov
