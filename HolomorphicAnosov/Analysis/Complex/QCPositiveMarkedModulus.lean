import HolomorphicAnosov.Analysis.Complex.MarkedConformalModulus
import HolomorphicAnosov.Topology.OpenConnectedFrontierComponent

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle

/-- A bounded connected open region with four positively ordered Jordan
boundary marks has a marked conformal modulus. This is the region form of
the existing marked rectangle model theorem (Ahlfors, Lectures on
Quasiconformal Mappings, II A p.21; Lehto--Virtanen I.§2.3 pp.14--15).
The positive boundary parametrization supplies the Jordan curve and its
labeled arcs. The open connected region is the complementary component
through any of its points, so the existing rectangle theorem applies.
Discard its extra side and uniqueness conclusions, retaining exactly the
marked conformal modulus witness. -/
theorem qc_positive_marked_modulus {Q : Set ℂ} {p : Fin 4 → ℂ}
    (hQopen : IsOpen Q) (hQconn : IsConnected Q) (hQbounded : Bornology.IsBounded Q)
    (hp : PositiveBoundaryFour Q p) : ∃ m : ℝ, HasMarkedConformalModulus Q p m := by
  rcases hp with ⟨β, hβ, u, hu, hp⟩
  let γ : Circle → ℂ := fun z ↦ (β z : ℂ)
  have hγ : _root_.Topology.IsEmbedding γ := _root_.Topology.IsEmbedding.subtypeVal.comp β.isEmbedding
  have hfront : range γ = frontier Q := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (β w).property
    · intro hz
      obtain ⟨w, hw⟩ := β.surjective ⟨z, hz⟩
      exact ⟨w, congrArg Subtype.val hw⟩
  obtain ⟨q, hq⟩ := hQconn.nonempty
  have hqγ : q ∉ range γ := by
    rw [hfront, hQopen.frontier_eq]
    exact fun h ↦ h.2 hq
  have hcomponent : connectedComponentIn (range γ)ᶜ q = Q := by
    rw [hfront]
    exact open_connected_frontier_component hQopen hQconn.isPreconnected hq
  let J : Fin 4 → Set ℂ := fun i ↦ γ ''
    {ζ | (ζ : ℂ) ∈ PositiveClosedCircleArc (u i) (u (i + 1))}
  have hbounded : Bornology.IsBounded (connectedComponentIn (range γ)ᶜ q) :=
    hcomponent.symm ▸ hQbounded
  have harcs : ∃ β' : Circle ≃ₜ frontier (connectedComponentIn (range γ)ᶜ q),
      PositiveBoundaryParametrization (connectedComponentIn (range γ)ᶜ q) β' ∧
      ∃ u' : Fin 4 → Circle, PositiveCircleFour u' ∧
        (∀ i, (β' (u' i) : ℂ) = p i) ∧
        ∀ i, J i = (fun ζ : Circle ↦ (β' ζ : ℂ)) ''
          {ζ | (ζ : ℂ) ∈ PositiveClosedCircleArc (u' i) (u' (i + 1))} := by
    rw [hcomponent]
    exact ⟨β, hβ, u, hu, hp, fun _ ↦ rfl⟩
  have hmodel := qc_signed_distortion_modulus_rectangle_conformal_model
    γ hγ q hqγ hbounded p J harcs
  dsimp only at hmodel
  rw [hcomponent] at hmodel
  obtain ⟨⟨a, b, ha, hb, F, Fi, hF, hFi, hbij, hmaps, hFiF, hFFi,
    e, he, hcorner, _, _⟩, _⟩ := hmodel
  exact ⟨a / b, a, b, ha, hb, rfl, F, Fi, hF, hFi, hbij, hmaps, hFiF, hFFi,
    e, he, hcorner⟩

end HolomorphicAnosov
