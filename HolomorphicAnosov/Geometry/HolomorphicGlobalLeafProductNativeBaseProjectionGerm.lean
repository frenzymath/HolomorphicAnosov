import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransversalInverseGerm
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeSameBoxPartition

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- At an original stable leaf point, the inverse transversal yields a smooth projection germ whose values lie on the corresponding unstable partition class. -/
theorem native_base_projection_germ {d p q : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (Fs : RegularHolomorphicFoliation.{u, v} d p q M)
    (Fu : RegularHolomorphicFoliation.{u, w} d q p M)
    (htransverse : ∀ y : M, IsCompl (Fs.tangent y) (Fu.tangent y))
    (o : M) (s : Fs.Leaf o) :
    ∃ φ : M → Fs.Leaf o,
      ContMDiffAt (complexModel d) (complexModel p) ∞ φ s.val ∧
      ∀ᶠ y in 𝓝 s.val, Fu.partition y (φ y).val := by
  obtain ⟨i, hi⟩ := Fu.cover s.val
  obtain ⟨ψ, hψ, hψs, hψeq⟩ :=
    native_transversal_inverse_germ Fs Fu htransverse o i s hi
  let Q : M → ComplexModel p := fun y ↦ ((Fu.box i) y).2
  have hQ : ContMDiffAt (complexModel d) (complexModel p) ∞ Q s.val :=
    contMDiffAt_snd.comp s.val ((Fu.box_holomorphic i).contMDiffAt
      ((Fu.box i).open_source.mem_nhds hi))
  refine ⟨ψ ∘ Q, hψ.comp s.val hQ, ?_⟩
  have hpre := hQ.continuousAt.eventually hψeq
  filter_upwards [(Fu.box i).open_source.mem_nhds hi, hpre] with y hy hpy
  exact native_same_box_partition Fu i y (ψ (Q y)).val hy hpy.1 hpy.2.symm

