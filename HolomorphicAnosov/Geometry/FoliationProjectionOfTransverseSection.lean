import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import HolomorphicAnosov.Geometry.FoliationLeafConstantContMDiff
import HolomorphicAnosov.Geometry.FoliationTransversalProjectionContMDiffAt
import HolomorphicAnosov.Geometry.FoliationTransversalDerivativeBijective

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov

/-- Projection along a holomorphic foliation onto a holomorphic section of complementary dimension
transverse to the foliation is holomorphic. (Zhang, Lemma 4.2; Nisoli, §1.3, pp.21–23) -/
theorem foliation_projection_of_transverse_section
    {d r c : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation d r c M)
    (q : M → ComplexModel c) (τ : ComplexModel c → M)
    (hfibres : ∀ a b, F.partition a b ↔ q a = q b)
    (hsection : ∀ z, q (τ z) = z)
    (hτ : ContMDiff (complexModel c) (complexModel d) ∞ τ)
    (hinj : ∀ z, Function.Injective (mfderiv (complexModel c) (complexModel d) τ z))
    (hdisjoint : ∀ z, Disjoint (mfderiv (complexModel c) (complexModel d) τ z).range
      (F.tangent (τ z))) :
    ContMDiff (complexModel d) (complexModel c) ∞ q := by
  have hconstant : ∀ a b, F.partition a b → q a = q b :=
    fun a b ↦ (hfibres a b).mp
  apply foliation_leaf_constant_contMDiff F q hconstant
  intro b
  obtain ⟨i, hi⟩ := F.cover (τ (q b))
  refine ⟨τ (q b), (hfibres _ _).mpr (hsection _), ?_⟩
  exact foliation_transversal_projection_contMDiffAt F q τ hconstant hsection
    (q b) i hi (hτ _) (foliation_transversal_derivative_bijective F τ (q b) i hi
      (hτ _) (hinj _) (hdisjoint _))


end HolomorphicAnosov
