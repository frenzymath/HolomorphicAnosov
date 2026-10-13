import HolomorphicAnosov.Topology.CairnsStarTargetConvexity
import HolomorphicAnosov.Topology.CairnsGapStrictSide
import HolomorphicAnosov.Topology.CairnsClosedCellRestriction

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- The two initial literal target stars meet along exactly their common closed
base. They are convex hull interiors of contacts on opposite parameter arcs.
The prescribed boundary map is a circle homeomorphism, so the opposite-arc
contact-hull intersection theorem applies even when it reverses orientation. -/
theorem cairns_initial_target_closure_intersection
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (hσ : Topology.IsEmbedding σ) (h : range σ ≃ₜ Circle)
    (d : InitialData σ a p q)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h) :
    closure (d.firstStar.targetStar h) ∩ closure (d.secondStar.targetStar h) =
      segment ℝ (h ⟨σ p,⟨p,rfl⟩⟩ : ℂ) (h ⟨σ q,⟨q,rfl⟩⟩ : ℂ) := by
  let τ := fun t : Circle ↦ (h ⟨σ t,⟨t,rfl⟩⟩ : ℂ)
  let e : Circle ≃ₜ Circle := hσ.toHomeomorph.trans h
  have hτe (t : Circle) : τ t = (e t : ℂ) := rfl
  have hτ : Continuous τ := continuous_subtype_val.comp e.continuous
  have hτinj : Function.Injective τ := fun s t he ↦ e.injective (Subtype.ext he)
  have hτnorm : ∀ t, ‖τ t‖ = 1 := fun t ↦ Circle.norm_coe _
  have hτsurj : ∀ z : ℂ, ‖z‖ = 1 → ∃ t, τ t = z := by
    intro z hz
    let zc : Circle := ⟨z,mem_sphere_zero_iff_norm.mpr hz⟩
    exact ⟨e.symm zc,congrArg Subtype.val (e.apply_symm_apply zc)⟩
  have hg2first : d.secondGap.first = d.firstGap.last := by
    change Circle.exp d.secondGap.start = Circle.exp d.firstGap.stop
    rw [d.second_start]
  have hg2last : d.secondGap.last = d.firstGap.first := by
    change Circle.exp d.secondGap.stop = Circle.exp d.firstGap.start
    rw [d.second_stop,Circle.periodic_exp]
  have hcontacts {g : CairnsCircleGap} (b : StarChoice σ a g) (hb : StarGeometry b h) :
      σ ⁻¹' (b.front ∩ range σ) ⊆ g.closedArc := by
    intro t ht
    have hCsub : b.front ∩ range σ ⊆ σ '' range g.parameter := hb.2.2.2.2.2.2.2.2.2.1
    obtain ⟨u,hu,he⟩ := hCsub ht
    have hut : u = t := hσ.injective he
    rw [← hut,← (CairnsCircleGap.parameter_embedding_range g).2.1]
    exact hu
  have hD₁ : σ d.firstGap.first ∈ d.firstStar.front ∩ range σ :=
    h₁.2.2.2.2.2.2.2.2.2.2.1
  have hD₂ : σ d.firstGap.last ∈ d.firstStar.front ∩ range σ :=
    h₁.2.2.2.2.2.2.2.2.2.2.2.1
  have hE₁ : σ d.secondGap.first ∈ d.secondStar.front ∩ range σ :=
    h₂.2.2.2.2.2.2.2.2.2.2.1
  have hE₂ : σ d.secondGap.last ∈ d.secondStar.front ∩ range σ :=
    h₂.2.2.2.2.2.2.2.2.2.2.2.1
  rw [cairns_geometric_star_target_closure hσ d.firstStar h h₁,
    cairns_geometric_star_target_closure hσ d.secondStar h h₂]
  have heq := cairns_opposite_arc_contact_hulls_intersection τ hτ hτinj hτnorm hτsurj
    d.firstGap d.secondGap d.second_start d.second_stop hg2first hg2last
    (σ ⁻¹' (d.firstStar.front ∩ range σ)) (σ ⁻¹' (d.secondStar.front ∩ range σ))
    (hcontacts _ h₁) (hcontacts _ h₂) hD₁ hD₂
    (by simpa only [Set.mem_preimage,hg2last] using hE₂)
    (by simpa only [Set.mem_preimage,hg2first] using hE₁)
  simpa only [d.first_eq,d.last_eq] using heq

/-- The two literal patch maps agree on the common base, with the reversed
orientation of the second gap correctly changing t to 1-t. Both maps agree
with the prescribed original boundary homeomorphism at curve points. -/
theorem cairns_initial_patch_agreement
    {σ : Circle → ℂ} {a : Set ℂ} {p q : Circle}
    (h : range σ ≃ₜ Circle) (d : InitialData σ a p q)
    (h₁ : StarGeometry d.firstStar h) (h₂ : StarGeometry d.secondStar h) :
    ∀ z ∈ range σ ∪ segment ℝ (σ p) (σ q),
      d.firstStar.patchMap h z = d.secondStar.patchMap h z := by
  classical
  obtain ⟨H₁,he₁,hi₁,hbase₁,hrest₁⟩ := cairns_geometric_star_literal_extension d.firstStar h h₁
  obtain ⟨H₂,he₂,hi₂,hbase₂,hrest₂⟩ := cairns_geometric_star_literal_extension d.secondStar h h₂
  have hf₂ : d.secondGap.first = q := by
    change Circle.exp d.secondGap.start = q
    rw [d.second_start]
    exact d.last_eq
  have hl₂ : d.secondGap.last = p := by
    change Circle.exp d.secondGap.stop = p
    rw [d.second_stop,Circle.periodic_exp]
    exact d.first_eq
  intro z hz
  rcases hz with hz | hz
  · simp only [StarChoice.patchMap,dite_eq_left hz]
  · rw [segment_eq_image] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    let u : I := ⟨t,ht⟩
    have he₁ := hbase₁ u
    have he₂ := hbase₂ (unitInterval.symm u)
    simp only [d.first_eq,d.last_eq] at he₁
    simp only [hf₂,hl₂,unitInterval.coe_symm_eq] at he₂
    have hparam : (1 - (1 - t)) • σ q + (1 - t) • σ p = (1-t) • σ p + t • σ q := by
      rw [sub_sub_cancel]
      exact add_comm _ _
    have hparamt : (1 - (1 - t)) • (h ⟨σ q,⟨q,rfl⟩⟩ : ℂ) +
        (1-t) • (h ⟨σ p,⟨p,rfl⟩⟩ : ℂ) =
        (1-t) • (h ⟨σ p,⟨p,rfl⟩⟩ : ℂ) + t • (h ⟨σ q,⟨q,rfl⟩⟩ : ℂ) := by
      rw [sub_sub_cancel]
      exact add_comm _ _
    change d.secondStar.patchMap h ((1-(1-t)) • σ q + (1-t) • σ p) = _ at he₂
    rw [hparam,hparamt] at he₂
    exact he₁.trans he₂.symm

end HolomorphicAnosov.Topology.Plane
