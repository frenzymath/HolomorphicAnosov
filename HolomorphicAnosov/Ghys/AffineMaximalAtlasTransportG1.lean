import HolomorphicAnosov.Ghys.AffineAtlasTransport

/-! This file describes maximal affine atlases under biholomorphic transport and proves preservation
of completeness. (Ghys, §3, pp.590–593) -/
noncomputable section
open Set Filter
open scoped Topology _root_.Topology Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u v
variable {L : Type u} {L' : Type v}
  [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
  [TopologicalSpace L'] [ChartedSpace (ComplexModel 1) L']

/-- A chart belongs to the transported maximal affine atlas exactly when its pullback belongs to the
original maximal atlas. (Ghys, §3, pp.590–591; Lemma 3.2) -/
theorem affine_maximalAtlas_transport_iff_g1
    (T : Diffeomorph (complexModel 1) (complexModel 1) L L' ∞)
    (A : ComplexAffineAtlas L) (B : ComplexAffineAtlas L')
    (hB : B.charts = {d | ∃ c ∈ A.charts,
      d = T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c})
    (d : OpenPartialHomeomorph L' ℂ) :
    d ∈ ComplexAffineStructure.maximalAtlas L'
        (Quotient.mk (complexAffineAtlasSetoid L') B) ↔
      T.toHomeomorph.toOpenPartialHomeomorph.trans d ∈
        ComplexAffineStructure.maximalAtlas L
          (Quotient.mk (complexAffineAtlasSetoid L) A) := by
  rw [ComplexAffineStructure.maximalAtlas_eq_of_representative,
    ComplexAffineStructure.maximalAtlas_eq_of_representative]
  let c := T.toHomeomorph.toOpenPartialHomeomorph.trans d
  constructor
  · rintro ⟨hd, hcompat⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hd.1.comp T.contMDiff.contMDiffOn (fun _ hx ↦ hx.2)
    · have ht : c.target = d.target := by simp [c]
      change ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ c.symm c.target
      rw [ht]
      exact T.symm.contMDiff.comp_contMDiffOn hd.2
    · intro e he x hx
      have hm : T.toHomeomorph.symm.toOpenPartialHomeomorph.trans e ∈ B.charts := by
        rw [hB]; exact ⟨e, he, rfl⟩
      obtain ⟨b, hb⟩ := hcompat _ hm (T x) (by simpa using hx)
      refine ⟨b, ?_⟩
      have hp := T.continuous.tendsto x hb
      filter_upwards [hp] with y hy
      simpa [OpenPartialHomeomorph.trans_apply] using hy
  · rintro ⟨hc, hcompat⟩
    have hdhol : IsHolomorphicScalarChart L' d := by
      constructor
      · have h := hc.1.comp T.symm.contMDiff.contMDiffOn
          (show MapsTo T.symm d.source c.source from fun x hx ↦ by simpa [c] using hx)
        simpa [c, Function.comp_def, OpenPartialHomeomorph.trans_apply] using h
      · have ht : c.target = d.target := by simp [c]
        have h := T.contMDiff.comp_contMDiffOn hc.2
        rw [ht] at h
        simpa [c, Function.comp_def, OpenPartialHomeomorph.trans_apply,
          OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using h
    refine ⟨hdhol, ?_⟩
    intro e he x hx
    rw [hB] at he
    obtain ⟨a, ha, rfl⟩ := he
    have hx' : T.symm x ∈ a.source ∩ c.source := by simpa [c] using hx
    obtain ⟨b, hb⟩ := hcompat a ha (T.symm x) hx'
    refine ⟨b, ?_⟩
    have hp := T.symm.continuous.tendsto x hb
    filter_upwards [hp] with y hy
    simpa [c, OpenPartialHomeomorph.trans_apply] using hy

/-- An atlas consisting of the biholomorphic transports of the charts of a complete affine structure
is complete. (Ghys, §3, pp.590–593) -/
theorem affine_complete_transported_atlas_g1
    (T : Diffeomorph (complexModel 1) (complexModel 1) L L' ∞)
    (A : ComplexAffineStructure L) (B : ComplexAffineAtlas L')
    (hB : B.charts = {d | ∃ c ∈ A.out.charts,
      d = T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c})
    (hA : ComplexAffineStructure.Complete L A) :
    ComplexAffineStructure.Complete L'
      (Quotient.mk (complexAffineAtlasSetoid L') B) := by
  rcases hA with ⟨hsc, hdev⟩
  constructor
  · exact T.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mp hsc
  · rcases hdev with ⟨D, hD⟩
    refine ⟨T.symm.trans D, ?_⟩
    intro c hc x hxc
    have hQA : AffineAtlasesEquivalent L' (Quotient.out (Quotient.mk (complexAffineAtlasSetoid L') B)) B :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (complexAffineAtlasSetoid L') B))
    obtain ⟨c₀, hc₀, hxc₀⟩ := B.cover x
    have hc₀' : c₀ ∈ {d | ∃ c ∈ (Quotient.out A).charts,
        d = T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c} := hB ▸ hc₀
    rcases hc₀' with ⟨t, ht, htc⟩
    subst c₀
    have hy : T.symm x ∈ t.source := by simpa using hxc₀
    obtain ⟨b, hb⟩ := hD t ht (T.symm x) hy
    obtain ⟨a, ha⟩ := hQA c hc
      (T.toHomeomorph.symm.toOpenPartialHomeomorph.trans t)
      hc₀ x ⟨hxc, hxc₀⟩
    refine ⟨⟨b.slope * a.slope, mul_ne_zero b.slope_ne_zero a.slope_ne_zero,
      b.slope * a.translation + b.translation⟩, ?_⟩
    filter_upwards [ha, (T.symm.continuous.tendsto x).eventually hb] with y hay hby
    dsimp [ComplexAffineTransformation.apply] at hay hby ⊢
    have hay' : t (T.symm y) = a.apply (c y) := by
      simpa [OpenPartialHomeomorph.trans_apply, ComplexAffineTransformation.apply] using hay
    rw [hby, hay']
    dsimp [ComplexAffineTransformation.apply]
    ring

end HolomorphicAnosov.Ghys

