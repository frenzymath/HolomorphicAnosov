import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransverseAnnihilatesLeaf
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransverseDerivativeSurjective
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeInclusionRange

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- The kernel of the original transverse coordinate differential is exactly the native tangent distribution.    Inclusion follows from intrinsic local constancy; equality follows from actual immersion rank and rank--nullity. -/
theorem native_transverse_derivative_kernel {d r c : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation.{u, v} d r c M)
    (i : F.boxIndex) (x : M) (hx : x ∈ (F.box i).source) :
    (mfderiv (complexModel d) (complexModel c)
      (fun y : M ↦ ((F.box i) y).2) x).ker = F.tangent x := by
  let D := mfderiv (complexModel d) (complexModel c)
    (fun y : M ↦ ((F.box i) y).2) x
  let J := mfderiv (complexModel r) (complexModel d)
    (fun y : F.Leaf x ↦ y.val) (⟨x, rfl⟩ : F.Leaf x)
  have hcomp : D.comp J = 0 :=
    native_transverse_annihilates_leaf F (Quotient.mk F.partition x) i ⟨x, rfl⟩ hx
  have hle : F.tangent x ≤ D.ker := by
    rintro v ⟨w, rfl⟩
    have hh := congrArg (fun L ↦ L w) hcomp
    exact hh
  have hJ : Function.Injective J :=
    F.inclusion_immersion (Quotient.mk F.partition x) ⟨x, rfl⟩
  have hrankJ : Module.finrank ℂ (F.tangent x) = r := by
    change Module.finrank ℂ J.toLinearMap.range = r
    rw [LinearMap.finrank_range_of_inj hJ]
    change Module.finrank ℂ (Fin r → ℂ) = r
    exact (Module.finrank_pi ℂ).trans (Fintype.card_fin r)
  have hD : D.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr
    (native_transverse_derivative_surjective F i x hx)
  have hrankD := D.toLinearMap.finrank_range_add_finrank_ker
  rw [hD, finrank_top] at hrankD
  have hker : Module.finrank ℂ D.ker = r := by
    have hn : d = r + c := F.dimension
    have hc : Module.finrank ℂ (ComplexModel c) = c :=
      (Module.finrank_pi ℂ).trans (Fintype.card_fin c)
    have hd : Module.finrank ℂ (TangentSpace (complexModel d) x) = d :=
      (Module.finrank_pi ℂ).trans (Fintype.card_fin d)
    change Module.finrank ℂ (ComplexModel c) + Module.finrank ℂ D.ker =
      Module.finrank ℂ (TangentSpace (complexModel d) x) at hrankD
    rw [hc, hd] at hrankD
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (hrankJ.trans hker.symm)).symm

