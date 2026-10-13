import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.QuotientDifferentialContinuousEquivalence
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.LocalFrameConnectionForm
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ExistsLocalData
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.QuotientFrameMultiplierSmoothCoefficientG12Bridge

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
local holomorphic quotient frames is holomorphic on the source frame domain. (Zhang, §2.1, (5),
p.5; Demailly, V §11, p.267 and §14.1, p.273) -/
theorem quotient_frame_multiplier_smooth_coefficient
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (f : Biholomorph d d X X)
    (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))
    {V W : Opens X} (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (hV : ∀ x, x ∈ V → f x ∈ W) :
    ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞
      (QuotientLineConnection.imageFrameCoefficient f hf e e') V := by
  intro x hx
  obtain ⟨N, hNopen, hxN, hNV, hNsmooth⟩ :=
    quotient_frame_multiplier_smooth_coefficient_bridge_g12
      P hP hline f hf e e' hV x hx
  exact (hNsmooth.contMDiffAt (hNopen.mem_nhds hxN)).contMDiffWithinAt

end HolomorphicAnosov.ConnectionCalculus

