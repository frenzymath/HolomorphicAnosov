import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.QuotientDifferentialContinuousEquivalence
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.LocalFrameConnectionForm
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ExistsLocalData
import HolomorphicAnosov.Geometry.BiholomorphToReal

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- The scalar coefficient of the quotient differential of a subbundle-preserving biholomorphism in
normalized source and target frames is nonzero on the source frame domain. (Zhang, §2.1, (5),
p.5; Demailly, V §11, p.267) -/
theorem quotient_frame_multiplier_nonzero
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (f : Biholomorph d d X X)
    (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))
    {V W : Opens X} (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (hV : ∀ x, x ∈ V → f x ∈ W) :
    ∀ x ∈ V,
      QuotientLineConnection.imageFrameCoefficient f hf e e' x ≠ 0 := by
  intro x hx hzero
  have hfx : f x ∈ W := hV x hx
  have hcoord : e'.coordinate (f x) hfx
      (QuotientLineConnection.quotientDerivative f hf x (e.sectionValue x)) = 0 := by
    simpa [QuotientLineConnection.imageFrameCoefficient, hfx] using hzero
  have hqzero : QuotientLineConnection.quotientDerivative f hf x (e.sectionValue x) = 0 :=
    (e'.coordinate (f x) hfx).injective (by simpa using hcoord)
  obtain ⟨Q, hQ⟩ := quotient_differential_equivalence P hP hline f hf
  have hsource : e.sectionValue x = 0 := by
    apply (Q x).injective
    have hQzero : (Q x) (e.sectionValue x) = 0 := by
      change (Q x).toLinearMap (e.sectionValue x) = 0
      rw [hQ x]
      exact hqzero
    simpa using hQzero
  have hn := e.normalized x hx
  rw [hsource, map_zero] at hn
  exact zero_ne_one hn

end HolomorphicAnosov.ConnectionCalculus

