import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace HolomorphicAnosov

universe u

open CategoryTheory

/-- Surjectivity of the actual based fundamental-group map is equivalent to
representing every target loop by an endpoint-fixed homotopic image loop.
This is the quotient-level reduction used in Hatcher Proposition 1.26,
pp.50--51. -/
lemma pi1_surjective_iff_loop_homotopic
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    Function.Surjective (FundamentalGroup.map f x) ↔
      ∀ γ : Path (f x) (f x), ∃ δ : Path x x,
        Path.Homotopic (δ.map f.continuous) γ := by
  constructor
  · intro h γ
    obtain ⟨a, ha⟩ := h (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
    obtain ⟨δ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
    refine ⟨δ, Path.Homotopic.Quotient.exact ?_⟩
    simpa only [FundamentalGroup.map_apply, Path.Homotopic.Quotient.mk_map] using ha
  · intro h a
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
    obtain ⟨δ, hδ⟩ := h γ
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ), ?_⟩
    change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk δ) f =
      Path.Homotopic.Quotient.mk γ
    rw [← Path.Homotopic.Quotient.mk_map]
    exact Path.Homotopic.Quotient.eq.mpr hδ

end HolomorphicAnosov
