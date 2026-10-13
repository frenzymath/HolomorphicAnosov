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
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The scalar difference of two pulled-back quotient-line connections is the ordinary pullback of
their scalar difference. (Zhang, (5)) -/
theorem pullback_scalar_difference
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V))
    (f : Biholomorph d d X X)
    (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))
    (D D' Dp Dp' : QuotientLineConnection.Connection P)
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hp : ∀ (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (e' : QuotientLineConnection.HolomorphicFrame P W) (x : X),
      x ∈ V → f x ∈ W →
      Dp.form V e x =
        (QuotientLineConnection.imageFrameCoefficient f hf e e' x)⁻¹ •
          QuotientLineConnection.realDifferential
            (QuotientLineConnection.imageFrameCoefficient f hf e e') x +
        (D.form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x))
    (hp' : ∀ (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (e' : QuotientLineConnection.HolomorphicFrame P W) (x : X),
      x ∈ V → f x ∈ W →
      Dp'.form V e x =
        (QuotientLineConnection.imageFrameCoefficient f hf e e' x)⁻¹ •
          QuotientLineConnection.realDifferential
            (QuotientLineConnection.imageFrameCoefficient f hf e e') x +
        (D'.form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x))
    (hα : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (x : X), x ∈ V → D'.form V e x = D.form V e x + α x) :
    ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (x : X), x ∈ V → Dp'.form V e x = Dp.form V e x +
        (α (f x)).comp (mfderiv (realModel d) (realModel d) f x) := by
  intro V e x hx
  obtain ⟨W, hfx, ⟨e'⟩⟩ := hcover (f x)
  rw [hp' V W e e' x hx hfx, hp V W e e' x hx hfx, hα W e' (f x) hfx]
  ext v
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  abel



end ConnectionCalculus
end HolomorphicAnosov
