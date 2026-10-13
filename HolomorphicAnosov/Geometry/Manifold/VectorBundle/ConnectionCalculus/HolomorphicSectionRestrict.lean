import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov
namespace ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- Holomorphic quotient sections remain holomorphic on smaller open sets. (Demailly, V §11, (11.1),
p.267 and §14, (14.1), p.273) -/
theorem holomorphic_section_restrict
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    {V W : Opens X} (hWV : W ≤ V)
    {s : (x : X) → QuotientLineConnection.Fibre P x}
    (hs : QuotientLineConnection.IsHolomorphicSection P V s) :
    QuotientLineConnection.IsHolomorphicSection P W s := by
  intro x hx
  obtain ⟨O, t, hO, hxO, hOV, ht, hts⟩ := hs x (hWV hx)
  exact ⟨O ∩ W, t, hO.inter W.isOpen, ⟨hxO, hx⟩, inter_subset_right,
    ht.mono inter_subset_left, fun y hy ↦ hts y hy.1⟩


end ConnectionCalculus
end HolomorphicAnosov
