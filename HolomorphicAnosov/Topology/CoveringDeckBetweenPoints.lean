import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Deck

/-! Universal-cover deck transitivity: Hatcher Propositions 1.33–1.34 and 1.39. -/

namespace HolomorphicAnosov.Ghys

/-- A universal covering admits a genuine deck transformation between any two
points of one fibre. Source: Hatcher Propositions 1.33–1.34, pp.61–63,
and pp.70–71. Lift the covering map with either marked endpoint, then
use uniqueness to show that the two lifts are inverse homeomorphisms.
No nontrivial deck group or transitivity hypothesis is assumed. -/
theorem covering_deck_between_points
    {Y B : Type*} [TopologicalSpace Y] [TopologicalSpace B]
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
    {q : Y → B} (hq : IsCoveringMap q) (y₀ y₁ : Y) (hy : q y₀ = q y₁) :
    ∃ γ : deck q, γ • y₀ = y₁ := by
  let Q : C(Y, B) := ⟨q, hq.continuous⟩
  obtain ⟨g, hg, _⟩ := hq.existsUnique_continuousMap_lifts Q y₀ y₁ hy.symm
  obtain ⟨h, hh, _⟩ := hq.existsUnique_continuousMap_lifts Q y₁ y₀ hy
  have hleft : (h : Y → Y) ∘ g = id := by
    apply hq.eq_of_comp_eq (h.continuous.comp g.continuous) continuous_id
      (by funext y; exact (congrFun hh.2 (g y)).trans (congrFun hg.2 y)) y₀
    simpa only [Function.comp_apply, hg.1, id_eq] using hh.1
  have hright : (g : Y → Y) ∘ h = id := by
    apply hq.eq_of_comp_eq (g.continuous.comp h.continuous) continuous_id
      (by funext y; exact (congrFun hg.2 (h y)).trans (congrFun hh.2 y)) y₁
    simpa only [Function.comp_apply, hh.1, id_eq] using hg.1
  let e : Y ≃ₜ Y :=
    { toEquiv :=
        { toFun := g
          invFun := h
          left_inv := congrFun hleft
          right_inv := congrFun hright }
      continuous_toFun := g.continuous
      continuous_invFun := h.continuous }
  exact ⟨⟨e, hg.2⟩, hg.1⟩


end HolomorphicAnosov.Ghys
