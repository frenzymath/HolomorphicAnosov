import HolomorphicAnosov.Topology.CairnsHalfDiskBoundaryTransport
import Mathlib.Analysis.Convex.Segment

noncomputable section
open Set Metric
namespace HolomorphicAnosov

/-- An embedded interval occupies a proper directed arc of the circle.
Source: Cairns §4(D), p.866. Classification gives a directed arc; an interior
point of the reverse directed arc lies outside it by the endpoint intersection law. -/
lemma embedded_interval_circle_not_surjective (f : unitInterval → Circle)
    (hf : Topology.IsEmbedding f) : ¬ Function.Surjective f := by
  intro hs
  have hn : f 0 ≠ f 1 := hf.injective.ne zero_ne_one
  have hfull : range f = univ := range_eq_univ.mpr hs
  have path_not_full (x y : Circle) (hxy : x ≠ y) : range (Circle.path x y) ≠ univ := by
    intro h
    let t : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
    have ht0 : t ≠ 0 := by intro h; have := congrArg Subtype.val h; norm_num [t] at this
    have ht1 : t ≠ 1 := by intro h; have := congrArg Subtype.val h; norm_num [t] at this
    have hm : Circle.path y x t ∈ range (Circle.path x y) ∩ range (Circle.path y x) :=
      ⟨by rw [h]; trivial, ⟨t, rfl⟩⟩
    rw [Circle.range_path_inter_range_path hxy] at hm
    rcases mem_insert_iff.mp hm with h | h
    · apply ht1
      apply Circle.path_injective_of_ne hxy.symm
      simpa using h
    · apply ht0
      apply Circle.path_injective_of_ne hxy.symm
      simpa using Set.mem_singleton_iff.mp h
  rcases Topology.cairns_circle_arc_range f hf with h | h
  · exact path_not_full _ _ hn (h.symm.trans hfull)
  · exact path_not_full _ _ hn.symm (h.symm.trans hfull)

/-- The affine segment parametrization is an embedding when its endpoints differ.
Source: the affine line-map description of a segment; injectivity follows from
nondegeneracy, and compactness promotes the continuous injection to an embedding. -/
lemma segment_embedded_arc (a b : ℂ) (hab : a ≠ b) :
    ∃ f : unitInterval → ℂ, Topology.IsEmbedding f ∧ range f = segment ℝ a b ∧
      f 0 = a ∧ f 1 = b := by
  let f : unitInterval → ℂ := fun t ↦ AffineMap.lineMap a b (t : ℝ)
  have hf : Continuous f := by fun_prop
  have hfi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (AffineMap.lineMap_injective ℝ hab h)
  refine ⟨f, (hf.isClosedEmbedding hfi).isEmbedding, ?_, ?_, ?_⟩
  · rw [segment_eq_image_lineMap]
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  · simp [f]
  · simp [f]

/-- A nondegenerate straight segment contained in an ambient image of the circle is a proper subset of that circle; the segment is parametrized by an embedding of the closed unit interval with the prescribed endpoints.

Source: Cairns (1951), preliminary 2(B), p.860; arc classification used in §4(D), p.866.

Proof: The affine line map from a to b restricted to [0,1] is continuous and injective, hence an embedding by compactness, and its range is precisely the segment. If the segment were the entire boundary circle, compose this parametrization with the ambient circle homeomorphism to obtain a surjective interval embedding into the circle. The circle arc-classification theorem identifies its range with one of the two directed circle paths between its distinct endpoint images. A midpoint of the opposite directed path is not in this range: the two paths intersect only in their endpoints, and injectivity of the opposite path excludes its midpoint from both endpoints. This contradicts surjectivity. -/
lemma segment_ne_ambient_circle (c : Set ℂ) (F : ℂ ≃ₜ ℂ)
    (hF : F '' c = sphere (0 : ℂ) 1) (a b : ℂ) (hab : a ≠ b)
    (hsub : segment ℝ a b ⊆ c) : segment ℝ a b ≠ c := by
  intro heq
  obtain ⟨f, hf, hrange, h0, h1⟩ := segment_embedded_arc a b hab
  let g : unitInterval → Circle := fun t ↦
    ⟨F (f t), by change F (f t) ∈ sphere (0 : ℂ) 1; rw [← hF]; exact ⟨f t, hsub (hrange ▸ mem_range_self t), rfl⟩⟩
  have hg : Continuous g := by fun_prop
  have hgi : Function.Injective g := by
    intro x y h
    exact hf.injective (F.injective (congrArg Subtype.val h))
  apply embedded_interval_circle_not_surjective g (hg.isClosedEmbedding hgi).isEmbedding
  intro z
  have hz : (z : ℂ) ∈ F '' c := by rw [hF]; exact z.property
  obtain ⟨w, hw, he⟩ := hz
  rw [← heq, ← hrange] at hw
  obtain ⟨t, rfl⟩ := hw
  exact ⟨t, Subtype.ext he⟩
end HolomorphicAnosov
