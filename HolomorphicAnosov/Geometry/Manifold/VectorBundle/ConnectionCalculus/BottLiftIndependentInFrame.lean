import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CovariantDerivativeSectionCongr

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
/-- Zhang (2), local Bott lift-independence from an existing compatible connection. -/
theorem bott_lift_independent_in_frame
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLineConnection.Connection P)
    (hD : QuotientLineConnection.IsCompatible D)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (Y T T' : (x : X) → TangentSpace (complexModel d) x)
    (hY : QuotientLineConnection.IsSmoothTangentField V Y)
    (hT : QuotientLineConnection.IsSmoothTangentField V T)
    (hT' : QuotientLineConnection.IsSmoothTangentField V T')
    (hYP : ∀ x ∈ V, Y x ∈ P x)
    (hTT' : ∀ x ∈ V, QuotientLineConnection.projection P x (T x) =
      QuotientLineConnection.projection P x (T' x))
    (x : X) (hx : x ∈ V) :
    QuotientLineConnection.projection P x (QuotientLineConnection.bottBracket Y T x) =
      QuotientLineConnection.projection P x (QuotientLineConnection.bottBracket Y T' x) := by
  rw [← hD.2 V e Y T hY hT hYP x hx, ← hD.2 V e Y T' hY hT' hYP x hx]
  rw [covariantDerivative_section_congr D V e _ _ hTT' x hx,
    covariantDerivative_section_congr D V e _ _ hTT' x hx]



end ConnectionCalculus
end HolomorphicAnosov
