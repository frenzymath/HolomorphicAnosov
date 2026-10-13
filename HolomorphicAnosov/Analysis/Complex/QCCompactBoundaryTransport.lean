import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

namespace HolomorphicAnosov
open Set Filter _root_.Topology

/-- Restrict a continuous compact-closure embedding to the frontier.
Continuity and compactness identify the image of the closure with the
closure of the image; injectivity then commutes with the difference of the
closure and the open interior. The compact embedding supplies the stated
homeomorphism with the literal boundary map. -/
lemma qc_compact_boundary_transport {Q : Set ℂ} {f : ℂ → ℂ}
    (hQ : IsOpen Q) (hcompact : IsCompact (closure Q))
    (hf : ContinuousOn f (closure Q)) (hi : InjOn f (closure Q))
    (himage : IsOpen (f '' Q)) :
    ∃ e : frontier Q ≃ₜ frontier (f '' Q),
      ∀ z : frontier Q, (e z : ℂ) = f z := by
  classical
  have hclosure : f '' closure Q = closure (f '' Q) := by
    apply Subset.antisymm hf.image_closure
    exact closure_minimal (image_mono subset_closure)
      (hcompact.image_of_continuousOn hf).isClosed
  have hfront : f '' frontier Q = frontier (f '' Q) := by
    rw [hQ.frontier_eq, himage.frontier_eq, hi.image_sdiff_subset subset_closure, hclosure]
  have hcompactF : IsCompact (frontier Q) :=
    hcompact.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have : CompactSpace (frontier Q) := isCompact_iff_compactSpace.mp hcompactF
  let F : frontier Q → ℂ := fun z ↦ f z
  have hFc : Continuous F := (hf.mono frontier_subset_closure).domRestrict
  have hFi : Function.Injective F := by
    intro z w h
    exact Subtype.ext (hi (frontier_subset_closure z.property)
      (frontier_subset_closure w.property) h)
  have hrange : range F = frontier (f '' Q) := by
    rw [← hfront]
    ext z
    exact ⟨fun ⟨w, hw⟩ ↦ ⟨w, w.property, hw⟩,
      fun ⟨w, hw, he⟩ ↦ ⟨⟨w, hw⟩, he⟩⟩
  let e := (hFc.isClosedEmbedding hFi).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)
  exact ⟨e, fun _ ↦ rfl⟩


/-- Uniformly converging parametrizations inside a common compact set can be
composed with a uniformly converging sequence of maps on that set. Uniform
continuity of the limiting map controls the moved input; uniform convergence
controls the map error at that input. -/
lemma qc_uniform_compact_parametrizations {α : Type*} {C : Set ℂ}
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {E : α → ℂ} {En : ℕ → α → ℂ}
    (hC : IsCompact C) (hg : ContinuousOn g C)
    (hF : TendstoUniformlyOn F g atTop C)
    (hE : ∀ z, E z ∈ C) (hEn : ∀ n z, En n z ∈ C)
    (hlim : TendstoUniformly En E atTop) :
    TendstoUniformly (fun n z ↦ F n (En n z)) (fun z ↦ g (E z)) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.mp
    (hC.uniformContinuousOn_of_continuous hg) (ε / 2) (half_pos hε)
  have hnear := Metric.tendstoUniformly_iff.mp hlim δ hδ
  have hmaps := Metric.tendstoUniformlyOn_iff.mp hF (ε / 2) (half_pos hε)
  filter_upwards [hnear, hmaps] with n hn hFn z
  have hinput : dist (g (E z)) (g (En n z)) < ε / 2 :=
    hδg _ (hE z) _ (hEn n z) (hn z)
  exact (dist_triangle _ (g (En n z)) _).trans_lt
    ((add_lt_add hinput (hFn _ (hEn n z))).trans_eq (add_halves ε))


/-- A homeomorphism of closures that matches the open interiors restricts to
a frontier homeomorphism with the same literal values. -/
lemma qc_frontier_homeomorph_of_closure {Q P : Set ℂ}
    (hQ : IsOpen Q) (hP : IsOpen P) (e : closure Q ≃ₜ closure P)
    (hi : ∀ z : closure Q, (e z : ℂ) ∈ P ↔ (z : ℂ) ∈ Q) :
    ∃ b : frontier Q ≃ₜ frontier P,
      ∀ z : frontier Q, (b z : ℂ) = e ⟨z, frontier_subset_closure z.property⟩ := by
  have hmap (z : frontier Q) :
      (e ⟨z, frontier_subset_closure z.property⟩ : ℂ) ∈ frontier P := by
    rw [hP.frontier_eq]
    refine ⟨(e _).property, ?_⟩
    intro hp
    have hz : (z : ℂ) ∉ Q := by
      have hz := z.property
      exact (show (z : ℂ) ∈ closure Q \ Q by simpa only [hQ.frontier_eq] using hz).2
    exact hz ((hi _).mp hp)
  have hmap' (z : frontier P) :
      (e.symm ⟨z, frontier_subset_closure z.property⟩ : ℂ) ∈ frontier Q := by
    rw [hQ.frontier_eq]
    refine ⟨(e.symm _).property, ?_⟩
    intro hq
    have hz : (z : ℂ) ∉ P := by
      have hz := z.property
      exact (show (z : ℂ) ∈ closure P \ P by simpa only [hP.frontier_eq] using hz).2
    apply hz
    simpa using (hi (e.symm ⟨z, frontier_subset_closure z.property⟩)).mpr hq
  let b : frontier Q ≃ₜ frontier P :=
    { toFun := fun z ↦ ⟨e ⟨z, frontier_subset_closure z.property⟩, hmap z⟩
      invFun := fun z ↦ ⟨e.symm ⟨z, frontier_subset_closure z.property⟩, hmap' z⟩
      left_inv := by
        intro z
        apply Subtype.ext
        change (e.symm (e ⟨z, frontier_subset_closure z.property⟩) : ℂ) = z
        rw [e.symm_apply_apply]
      right_inv := by
        intro z
        apply Subtype.ext
        change (e (e.symm ⟨z, frontier_subset_closure z.property⟩) : ℂ) = z
        rw [e.apply_symm_apply]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (e.continuous.comp
          (continuous_subtype_val.subtype_mk (fun z ↦ frontier_subset_closure z.property)))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (e.symm.continuous.comp
          (continuous_subtype_val.subtype_mk (fun z ↦ frontier_subset_closure z.property))) }
  exact ⟨b, fun _ ↦ rfl⟩


/-- Restrict a partial homeomorphism to a compact closure inside its source.
The resulting closure homeomorphism has the literal values of the map and
matches membership in the two original interiors. -/
lemma qc_partial_homeomorph_closure (g : OpenPartialHomeomorph ℂ ℂ)
    {Q : Set ℂ} (hcompact : IsCompact (closure Q)) (hsrc : closure Q ⊆ g.source) :
    ∃ e : closure Q ≃ₜ closure (g '' Q),
      (∀ z : closure Q, (e z : ℂ) = g z) ∧
      ∀ z : closure Q, (e z : ℂ) ∈ g '' Q ↔ (z : ℂ) ∈ Q := by
  have hc := g.continuousOn.mono hsrc
  have heq : g '' closure Q = closure (g '' Q) := by
    apply Subset.antisymm hc.image_closure
    exact closure_minimal (image_mono subset_closure)
      (hcompact.image_of_continuousOn hc).isClosed
  let e := g.homeomorphOfImageSubsetSource hsrc heq
  refine ⟨e, fun z ↦ rfl, ?_⟩
  intro z
  change g z ∈ g '' Q ↔ (z : ℂ) ∈ Q
  constructor
  · rintro ⟨w, hw, he⟩
    have heq := g.injOn (hsrc (subset_closure hw)) (hsrc z.property) he
    exact heq ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

end HolomorphicAnosov



