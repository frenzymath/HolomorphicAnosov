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
/-- Quotient sections that agree on an open frame domain have the same covariant derivative there.
(Zhang, (3)) -/
theorem covariantDerivative_section_congr
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLineConnection.Connection P)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (s t : (x : X) → QuotientLineConnection.Fibre P x)
    (hst : ∀ y ∈ V, s y = t y)
    (x : X) (hx : x ∈ V) (v : TangentSpace (realModel d) x) :
    QuotientLineConnection.covariantDerivative D e s x hx v =
      QuotientLineConnection.covariantDerivative D e t x hx v := by
  have hc : e.coefficient s =ᶠ[nhds x] e.coefficient t := by
    filter_upwards [V.isOpen.mem_nhds hx] with y hy
    simp [QuotientLineConnection.HolomorphicFrame.coefficient, hst y hy]
  have hd : QuotientLineConnection.realDifferential (d := d) (e.coefficient s) x =
      QuotientLineConnection.realDifferential (d := d) (e.coefficient t) x := by
    unfold QuotientLineConnection.realDifferential
    rw [hc.eq_of_nhds, hc.mfderiv_eq]
    rfl
  simp only [QuotientLineConnection.covariantDerivative, hd, hc.eq_of_nhds]



end ConnectionCalculus
end HolomorphicAnosov
