import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicFrameRestrict
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.BottLiftIndependentInFrame
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

/-- Zhang (2), p.4 and Demailly V §14, p.273: a compatible connection on a quotient line makes the projected Bott bracket independent of the smooth local lift on every open set. -/
theorem bott_lift_independent_of_compatible
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V))
    (D : QuotientLineConnection.Connection P)
    (hD : QuotientLineConnection.IsCompatible D)
    (U : Opens X) (Y T T' : (x : X) → TangentSpace (complexModel d) x)
    (hY : QuotientLineConnection.IsSmoothTangentField U Y)
    (hT : QuotientLineConnection.IsSmoothTangentField U T)
    (hT' : QuotientLineConnection.IsSmoothTangentField U T')
    (hYP : ∀ x ∈ U, Y x ∈ P x)
    (hTT' : ∀ x ∈ U, QuotientLineConnection.projection P x (T x) =
      QuotientLineConnection.projection P x (T' x))
    (x : X) (hx : x ∈ U) :
    QuotientLineConnection.projection P x (QuotientLineConnection.bottBracket Y T x) =
      QuotientLineConnection.projection P x (QuotientLineConnection.bottBracket Y T' x) := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hcover x
  let W : Opens X := U ⊓ V
  let eW : QuotientLineConnection.HolomorphicFrame P W :=
    holomorphicFrameRestrict e inf_le_right
  exact bott_lift_independent_in_frame D hD W eW Y T T'
    (hY.mono inter_subset_left) (hT.mono inter_subset_left) (hT'.mono inter_subset_left)
    (fun y hy ↦ hYP y hy.1) (fun y hy ↦ hTT' y hy.1) x ⟨hx, hxV⟩


end ConnectionCalculus
end HolomorphicAnosov
