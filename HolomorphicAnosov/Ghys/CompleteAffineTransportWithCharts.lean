import HolomorphicAnosov.Ghys.AffineMaximalAtlasTransportG1

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u v

variable {L : Type u} {L' : Type v}
  [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
  [TopologicalSpace L'] [ChartedSpace (ComplexModel 1) L']

/-! This file transports complete affine structures and their maximal charts along biholomorphisms. -/
/-- A biholomorphism transports a complete affine structure to a complete affine structure whose
maximal charts are exactly those with pullbacks in the original maximal atlas. (Ghys, §3,
pp.590–593) -/
theorem complete_affine_structure_transport_with_charts
    (T : Diffeomorph (complexModel 1) (complexModel 1) L L' ∞)
    (A : ComplexAffineStructure L)
    (hA : ComplexAffineStructure.Complete L A) :
    ∃ B : ComplexAffineStructure L', ComplexAffineStructure.Complete L' B ∧
      ∀ c : OpenPartialHomeomorph L' ℂ,
        c ∈ ComplexAffineStructure.maximalAtlas L' B ↔
          T.toHomeomorph.toOpenPartialHomeomorph.trans c ∈
            ComplexAffineStructure.maximalAtlas L A := by
  obtain ⟨B₀, hB₀⟩ := exists_complexAffineAtlas_transport T A.out
  let B : ComplexAffineStructure L' :=
    Quotient.mk (complexAffineAtlasSetoid L') B₀
  refine ⟨B, affine_complete_transported_atlas_g1 T A B₀ hB₀ hA, ?_⟩
  intro c
  have hrep : (Quotient.mk (complexAffineAtlasSetoid L) A.out :
      ComplexAffineStructure L) = A := Quotient.out_eq A
  simpa only [hrep] using affine_maximalAtlas_transport_iff_g1 T A.out B₀ hB₀ c

/-- A maximal affine chart transports forward to a maximal affine chart with the corresponding
coordinate formula. -/
theorem affine_chart_of_transport_with_charts
    (T : Diffeomorph (complexModel 1) (complexModel 1) L L' ∞)
    (A : ComplexAffineStructure L) (B : ComplexAffineStructure L')
    (hB : ∀ d : OpenPartialHomeomorph L' ℂ,
      d ∈ ComplexAffineStructure.maximalAtlas L' B ↔
        T.toHomeomorph.toOpenPartialHomeomorph.trans d ∈
          ComplexAffineStructure.maximalAtlas L A)
    (c : OpenPartialHomeomorph L ℂ)
    (hc : c ∈ ComplexAffineStructure.maximalAtlas L A) :
    ∃ d ∈ ComplexAffineStructure.maximalAtlas L' B,
      (∀ y : L', y ∈ d.source ↔ T.symm y ∈ c.source) ∧
      (∀ y : L', d y = c (T.symm y)) := by
  let d := T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c
  refine ⟨d, (hB d).mpr ?_, ?_, ?_⟩
  · have heq : T.toHomeomorph.toOpenPartialHomeomorph.trans d = c := by
      dsimp only [d]
      rw [← OpenPartialHomeomorph.trans_assoc, ← Homeomorph.trans_toOpenPartialHomeomorph]
      simp
    rwa [heq]
  · intro y
    simp [d]
  · intro y
    rfl

/-- A local projective formula in affine coordinates transfers across a biholomorphic identification
with the stated maximal-chart correspondence. (Ghys, §3–5, pp.590–598) -/
theorem projective_affine_germ_of_transport_with_charts
    (T : Diffeomorph (complexModel 1) (complexModel 1) L L' ∞)
    (A : ComplexAffineStructure L) (B : ComplexAffineStructure L')
    (hB : ∀ d : OpenPartialHomeomorph L' ℂ,
      d ∈ ComplexAffineStructure.maximalAtlas L' B ↔
        T.toHomeomorph.toOpenPartialHomeomorph.trans d ∈
          ComplexAffineStructure.maximalAtlas L A)
    {M : Type*} (j : L → M) (j' : L' → M)
    (hj : ∀ z, j' (T z) = j z) (D : Set M) (q : M → ComplexProjectiveLine)
    (y : L')
    (h : ∃ c ∈ ComplexAffineStructure.maximalAtlas L A,
      T.symm y ∈ c.source ∧ ∃ g : ComplexMobiusTransformation,
        ∀ᶠ z in 𝓝 (T.symm y), z ∈ c.source ∧ j z ∈ D ∧
          q (j z) = g.apply (complexProjectiveLineFinite (c z))) :
    ∃ d ∈ ComplexAffineStructure.maximalAtlas L' B,
      y ∈ d.source ∧ ∃ g : ComplexMobiusTransformation,
        ∀ᶠ z in 𝓝 y, z ∈ d.source ∧ j' z ∈ D ∧
          q (j' z) = g.apply (complexProjectiveLineFinite (d z)) := by
  obtain ⟨c, hc, hyc, g, hg⟩ := h
  obtain ⟨d, hd, hds, hdv⟩ := affine_chart_of_transport_with_charts T A B hB c hc
  refine ⟨d, hd, (hds y).mpr hyc, g, ?_⟩
  have hinv (z : L') : j (T.symm z) = j' z := by
    simpa only [T.apply_symm_apply] using (hj (T.symm z)).symm
  filter_upwards [(T.symm.continuous.tendsto y).eventually hg] with z hz
  refine ⟨(hds z).mpr hz.1, ?_, ?_⟩
  · rw [← hinv z]
    exact hz.2.1
  · rw [hdv z, ← hinv z]
    exact hz.2.2

end HolomorphicAnosov.Ghys


