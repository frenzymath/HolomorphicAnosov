import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.CodimensionOne
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Paper.Zhang.TorusModel
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import HolomorphicAnosov.Targets.Theorem11
import HolomorphicAnosov.Targets.Theorem12
import HolomorphicAnosov.Targets.Theorem13
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.anosov_selected_complex_line_two_le_dimension
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseAnosovDatum
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.anosov_semiconj_complex_hyperbolic
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.TheoremASupport.has_model_of_symm

/-! A hyperbolic complex torus model for codimension-one holomorphic Anosov diffeomorphisms,
assuming homotopy-torus rigidity. (Zhang, Theorem A, p.2; §1.2, p.4) -/

namespace HolomorphicAnosov

universe u

attribute [local instance] complex_isManifold_real

/-- Assuming homotopy-torus rigidity, a holomorphic Anosov diffeomorphism of a compact complex
manifold with a complex rank-one stable or unstable bundle has a hyperbolic complex torus model.
(Zhang, Theorem A, pp.2–4) -/
theorem theorem_A {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hcodim : HasComplexRankOne a.splitting.stable.toDistribution ∨
      HasComplexRankOne a.splitting.unstable.toDistribution)
    (HS : HomotopyTorusRigidity.{u}) :
    HasHyperbolicComplexTorusModel (d := d) (fun x ↦ f x) := by
  have hd : 2 ≤ d :=
    TheoremAProof.Dimension.anosov_selected_complex_line_two_le_dimension f a hcodim
  have stableCore (g : Biholomorph d d X X) (b : AnosovDatum g)
      (hs : HasComplexRankOne b.splitting.stable.toDistribution) :
      HasHyperbolicComplexTorusModel (d := d) (fun x ↦ g x) := by
    obtain ⟨B, hT, _⟩ := theorem_1_1 hd g b hs HS
    obtain ⟨S, U, hS, hU, hShol, hUhol⟩ := theorem_1_3 g b hs HS
    obtain ⟨L, A, h, hc⟩ := theorem_1_2 g b
      ⟨1, S, hShol, hS⟩ ⟨d - 1, U, hUhol, hU⟩ ⟨2 * d, ⟨hT⟩⟩
    exact ⟨L, A, h,
      TheoremAProof.FixedPointSpectrum.anosov_semiconj_complex_hyperbolic A g b h hc, hc⟩
  rcases hcodim with hs | hu
  · exact stableCore f a hs
  · have hi : HasComplexRankOne
        (TheoremAProof.inverseAnosovDatum f a).splitting.stable.toDistribution := by
      exact hu
    exact TheoremAProof.ModelInverse.has_model_of_symm f
      (stableCore f.symm (TheoremAProof.inverseAnosovDatum f a) hi)

end HolomorphicAnosov

