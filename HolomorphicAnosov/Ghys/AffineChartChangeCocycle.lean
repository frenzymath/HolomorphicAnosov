import HolomorphicAnosov.Ghys.AffineTransformationGermRigidity

open Set Filter _root_.Topology

namespace HolomorphicAnosov.Ghys

universe u

/-- Affine chart germs admit locally constant coordinate changes on overlaps satisfying the identity
and cocycle laws. (Thurston, Ch. 3 §3.5, pp. 34–35) -/
theorem affine_chart_change_cocycle
    {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineAtlas L) :
    ∃ κ : A.charts → A.charts → L → ComplexAffineTransformation →
        ComplexAffineTransformation,
      (∀ (c d : A.charts) (x : L), x ∈ c.val.source ∩ d.val.source →
        ∀ a : ComplexAffineTransformation,
        ∀ᶠ y in 𝓝 x, a.apply (c.val y) = (κ c d x a).apply (d.val y)) ∧
      (∀ (c : A.charts) (x : L), x ∈ c.val.source →
        ∀ a : ComplexAffineTransformation, κ c c x a = a) ∧
      (∀ (c d e : A.charts) (x : L), x ∈ c.val.source ∩ d.val.source ∩ e.val.source →
        ∀ a : ComplexAffineTransformation,
        κ d e x (κ c d x a) = κ c e x a) ∧
      (∀ (c d : A.charts) (x : L), x ∈ c.val.source ∩ d.val.source →
        ∀ a : ComplexAffineTransformation,
        ∀ᶠ y in 𝓝 x, κ c d y a = κ c d x a) := by
  classical
  have hex (c d : A.charts) (x : L) (hx : x ∈ c.val.source ∩ d.val.source)
      (a : ComplexAffineTransformation) :
      ∃ b : ComplexAffineTransformation,
        ∀ᶠ y in 𝓝 x, a.apply (c.val y) = b.apply (d.val y) := by
    obtain ⟨e, he⟩ := A.compatible d.val d.property c.val c.property x ⟨hx.2, hx.1⟩
    let b : ComplexAffineTransformation :=
      { slope := a.slope * e.slope
        slope_ne_zero := mul_ne_zero a.slope_ne_zero e.slope_ne_zero
        translation := a.slope * e.translation + a.translation }
    refine ⟨b, ?_⟩
    filter_upwards [he] with y hy
    rw [hy]
    dsimp [b, ComplexAffineTransformation.apply]
    ring
  let κ (c d : A.charts) (x : L) (a : ComplexAffineTransformation) :=
    if hx : x ∈ c.val.source ∩ d.val.source then (hex c d x hx a).choose else a
  have hspec (c d : A.charts) (x : L) (hx : x ∈ c.val.source ∩ d.val.source)
      (a : ComplexAffineTransformation) :
      ∀ᶠ y in 𝓝 x, a.apply (c.val y) = (κ c d x a).apply (d.val y) := by
    simp only [κ, dite_eq_left hx]
    exact (hex c d x hx a).choose_spec
  have heq (c d : A.charts) (x : L) (hx : x ∈ c.val.source ∩ d.val.source)
      (a b : ComplexAffineTransformation)
      (hb : ∀ᶠ y in 𝓝 x, a.apply (c.val y) = b.apply (d.val y)) : κ c d x a = b :=
    affineTransformation_eq_of_eventuallyEq d.val hx.2 (Filter.EventuallyEq.trans (Filter.EventuallyEq.symm (hspec c d x hx a)) hb)
  refine ⟨κ, hspec, ?_, ?_, ?_⟩
  · intro c x hx a
    exact heq c c x ⟨hx, hx⟩ a a (Eventually.of_forall fun _ ↦ rfl)
  · intro c d e x hx a
    apply (heq c e x ⟨hx.1.1, hx.2⟩ a _ ?_).symm
    exact Filter.EventuallyEq.trans (hspec c d x hx.1 a) (hspec d e x ⟨hx.1.2, hx.2⟩ _)
  · intro c d x hx a
    have hformula := (hspec c d x hx a).eventually_nhds
    have hdom := (c.val.open_source.inter d.val.open_source).mem_nhds hx
    filter_upwards [hdom, hformula] with y hy heq'
    exact heq c d y hy a _ heq'

end HolomorphicAnosov.Ghys
