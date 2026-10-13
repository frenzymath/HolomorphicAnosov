import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicSectionRestrict
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

/-- The restriction of a holomorphic quotient-line frame to a smaller open set. (Demailly, V §11,
(11.1), p.267 and §14, (14.1), p.273) -/
def holomorphicFrameRestrict
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    {V W : Opens X} (e : QuotientLineConnection.HolomorphicFrame P V) (hWV : W ≤ V) :
    QuotientLineConnection.HolomorphicFrame P W where
  sectionValue := e.sectionValue
  holomorphic := holomorphic_section_restrict hWV e.holomorphic
  coordinate x hx := e.coordinate x (hWV hx)
  normalized x hx := e.normalized x (hWV hx)


end ConnectionCalculus
end HolomorphicAnosov
