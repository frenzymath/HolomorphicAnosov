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

/-- Uniqueness of the original global intersections makes the projection constant on each unstable intrinsic leaf.    Its actual derivative therefore annihilates that native tangent distribution. -/
theorem native_projection_annihilates_other {d p q : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (Fs : RegularHolomorphicFoliation.{u, v} d p q M)
    (Fu : RegularHolomorphicFoliation.{u, w} d q p M)
    (hunique : ∀ a b : M, ∃! y : M, Fs.partition a y ∧ Fu.partition b y)
    (o : M) (P : M → Fs.Leaf o)
    (hP : ContMDiff (complexModel d) (complexModel p) ∞ P)
    (hPrel : ∀ y : M, Fu.partition y (P y).val) (x : M) :
    Fu.tangent x ≤ (mfderiv (complexModel d) (complexModel p) P x).ker := by
  let z : Fu.Leaf x := ⟨x, rfl⟩
  have heq : (fun s : Fu.Leaf x ↦ P s.val) = fun _ ↦ P x := by
    funext s
    apply Subtype.ext
    obtain ⟨v, hv, huniq⟩ := hunique o x
    exact (huniq (P s.val).val
      ⟨Fs.partition.symm (Quotient.exact (P s.val).property),
        Fu.partition.trans (Fu.partition.symm (Quotient.exact s.property)) (hPrel s.val)⟩).trans
      (huniq (P x).val ⟨Fs.partition.symm (Quotient.exact (P x).property), hPrel x⟩).symm
  have hcomp : (mfderiv (complexModel d) (complexModel p) P x).comp
      (mfderiv (complexModel q) (complexModel d)
        (fun s : Fu.Leaf x ↦ s.val) z) = 0 := by
    have hh : mfderiv (complexModel q) (complexModel p)
        (fun s : Fu.Leaf x ↦ P s.val) z = 0 := by rw [heq, mfderiv_const]
    change mfderiv (complexModel q) (complexModel p)
      (P ∘ (fun s : Fu.Leaf x ↦ s.val)) z = 0 at hh
    rw [mfderiv_comp z ((hP x).mdifferentiableAt (by simp))
      ((Fu.inclusion_holomorphic (Quotient.mk Fu.partition x) z).mdifferentiableAt
        (by simp))] at hh
    exact hh
  rintro v ⟨w, rfl⟩
  exact congrArg (fun L ↦ L w) hcomp

