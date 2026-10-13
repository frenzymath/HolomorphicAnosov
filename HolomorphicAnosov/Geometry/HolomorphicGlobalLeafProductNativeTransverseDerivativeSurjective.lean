import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- The actual transverse differential is surjective because the original box has a two-sided holomorphic inverse and the coordinate second projection is surjective.    This is independent of the global topological conjugacy. -/
theorem native_transverse_derivative_surjective {d r c : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation.{u, v} d r c M)
    (i : F.boxIndex) (x : M) (hx : x ∈ (F.box i).source) :
    Function.Surjective (mfderiv (complexModel d) (complexModel c)
      (fun y : M ↦ ((F.box i) y).2) x) := by
  have he : (F.box i).MDifferentiable (complexModel d)
      ((complexModel r).prod (complexModel c)) :=
    ⟨(F.box_holomorphic i).mdifferentiableOn (by simp),
      (F.box_inverse_holomorphic i).mdifferentiableOn (by simp)⟩
  have hder : mfderiv (complexModel d) (complexModel c)
      (fun y : M ↦ ((F.box i) y).2) x =
      (ContinuousLinearMap.snd ℂ (ComplexModel r) (ComplexModel c)).comp
        (mfderiv (complexModel d) ((complexModel r).prod (complexModel c))
          (F.box i) x) := by
    change mfderiv (complexModel d) (complexModel c) (Prod.snd ∘ F.box i) x = _
    rw [mfderiv_comp x mdifferentiableAt_snd (he.mdifferentiableAt hx), mfderiv_snd]
    rfl
  rw [hder]
  intro w
  obtain ⟨v, hv⟩ := he.mfderiv_surjective hx ((0 : ComplexModel r), w)
  exact ⟨v, congrArg Prod.snd hv⟩

