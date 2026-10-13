import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransverseDerivativeKernel
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeInclusionRange

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- Complementary native tangent distributions make the transverse coordinate map restricted to the original intrinsic stable leaf have a bijective complex derivative.    The box derivative itself is never identified with the global H. -/
theorem native_transversal_derivative_bijective {d p q : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (Fs : RegularHolomorphicFoliation.{u, v} d p q M)
    (Fu : RegularHolomorphicFoliation.{u, w} d q p M)
    (htransverse : ∀ y : M, IsCompl (Fs.tangent y) (Fu.tangent y))
    (x : M) (i : Fu.boxIndex) (z : Fs.Leaf x)
    (hz : z.val ∈ (Fu.box i).source) :
    Function.Bijective (mfderiv (complexModel p) (complexModel p)
      (fun y : Fs.Leaf x ↦ ((Fu.box i) y.val).2) z) := by
  let D := mfderiv (complexModel d) (complexModel p)
    (fun y : M ↦ ((Fu.box i) y).2) z.val
  let J := mfderiv (complexModel p) (complexModel d)
    (fun y : Fs.Leaf x ↦ y.val) z
  have hker : D.ker = Fu.tangent z.val :=
    native_transverse_derivative_kernel Fu i z.val hz
  have hrange : J.range = Fs.tangent z.val :=
    native_inclusion_range Fs (Quotient.mk Fs.partition x) z
  have hJ : Function.Injective J :=
    Fs.inclusion_immersion (Quotient.mk Fs.partition x) z
  have hDJ : Function.Injective (D.comp J) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro v hv
    have hDv : J v ∈ Fu.tangent z.val := by
      rw [← hker]
      exact hv
    have hJv : J v ∈ Fs.tangent z.val := by
      rw [← hrange]
      exact ⟨v, rfl⟩
    have hvzero : J v = 0 := by
      have hh := (disjoint_iff_inf_le.mp (htransverse z.val).disjoint) ⟨hJv, hDv⟩
      exact hh
    exact hJ (by simpa using hvzero)
  have hbox := (Fu.box_holomorphic i).contMDiffAt
    ((Fu.box i).open_source.mem_nhds hz)
  have hQ := (contMDiffAt_snd.comp z.val hbox).mdifferentiableAt (by simp)
  have hinc := (Fs.inclusion_holomorphic (Quotient.mk Fs.partition x)).mdifferentiableAt
    (by simp) (x := z)
  have hder : mfderiv (complexModel p) (complexModel p)
      (fun y : Fs.Leaf x ↦ ((Fu.box i) y.val).2) z = D.comp J := by
    change mfderiv (complexModel p) (complexModel p)
      ((fun y : M ↦ ((Fu.box i) y).2) ∘ (fun y : Fs.Leaf x ↦ y.val)) z = _
    exact mfderiv_comp z hQ hinc
  rw [hder]
  exact ⟨hDJ, LinearMap.surjective_of_injective hDJ⟩

