import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeProjectionGermTransport
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeBaseProjectionGerm

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- Reverse finite holonomy gives a left inverse to the projection on each original stable leaf.    Thus its actual restricted derivative is bijective. -/
theorem native_projection_restricted_derivative {d p q : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (Fs : RegularHolomorphicFoliation.{u, v} d p q M)
    (Fu : RegularHolomorphicFoliation.{u, w} d q p M)
    (htransverse : ∀ y : M, IsCompl (Fs.tangent y) (Fu.tangent y))
    (hunique : ∀ a b : M, ∃! y : M, Fs.partition a y ∧ Fu.partition b y)
    (o : M) (P : M → Fs.Leaf o)
    (hP : ContMDiff (complexModel d) (complexModel p) ∞ P)
    (hPrel : ∀ y : M, Fu.partition y (P y).val) (x : M) :
    Function.Bijective ((mfderiv (complexModel d) (complexModel p) P x).comp
      (mfderiv (complexModel p) (complexModel d)
        (fun y : Fs.Leaf x ↦ y.val) (⟨x, rfl⟩ : Fs.Leaf x))) := by
  let z : Fs.Leaf x := ⟨x, rfl⟩
  obtain ⟨θ, hθ, hθrel⟩ := native_projection_germ_transport Fs Fu x x (P x).val
    (hPrel x) (native_base_projection_germ Fs Fu htransverse x z)
  let A : Fs.Leaf o → Fs.Leaf x := fun s ↦ θ s.val
  let B : Fs.Leaf x → Fs.Leaf o := fun s ↦ P s.val
  have hA : ContMDiffAt (complexModel p) (complexModel p) ∞ A (B z) :=
    hθ.comp (P x) (Fs.inclusion_holomorphic (Quotient.mk Fs.partition o) (P x))
  have hB : ContMDiffAt (complexModel p) (complexModel p) ∞ B z :=
    (hP x).comp z (Fs.inclusion_holomorphic (Quotient.mk Fs.partition x) z)
  have heq : A ∘ B =ᶠ[𝓝 z] id := by
    have hcont : Filter.Tendsto (fun s : Fs.Leaf x ↦ (P s.val).val)
        (𝓝 z) (𝓝 (P x).val) := by
      have hh : ContinuousAt (fun s : Fs.Leaf o ↦ s.val) (B z) :=
        (Fs.inclusion_holomorphic (Quotient.mk Fs.partition o) (B z)).continuousAt
      exact hh.comp hB.continuousAt
    have hpre := hcont.eventually (p := fun y ↦ Fu.partition y (θ y).val) hθrel
    filter_upwards [hpre] with s hs
    apply Subtype.ext
    obtain ⟨v, hv, huniq⟩ := hunique x s.val
    exact (huniq (θ (P s.val).val).val
      ⟨Fs.partition.symm (Quotient.exact (θ (P s.val).val).property),
        Fu.partition.trans (hPrel s.val) hs⟩).trans
      (huniq s.val ⟨Fs.partition.symm (Quotient.exact s.property),
        Fu.partition.refl s.val⟩).symm
  have hcomp := heq.mfderiv_eq (I := complexModel p) (I' := complexModel p)
  rw [mfderiv_id, mfderiv_comp z (hA.mdifferentiableAt (by simp))
    (hB.mdifferentiableAt (by simp))] at hcomp
  have hbinj : Function.Injective (mfderiv (complexModel p) (complexModel p) B z) :=
    (ContinuousLinearMap.leftInverse_of_comp hcomp).injective
  have hbder : mfderiv (complexModel p) (complexModel p) B z =
      (mfderiv (complexModel d) (complexModel p) P x).comp
        (mfderiv (complexModel p) (complexModel d)
          (fun y : Fs.Leaf x ↦ y.val) z) := by
    exact mfderiv_comp z ((hP x).mdifferentiableAt (by simp))
      ((Fs.inclusion_holomorphic (Quotient.mk Fs.partition x) z).mdifferentiableAt (by simp))
  rw [hbder] at hbinj
  exact ⟨hbinj, LinearMap.surjective_of_injective hbinj⟩

