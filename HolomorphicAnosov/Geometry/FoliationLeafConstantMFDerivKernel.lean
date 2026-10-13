import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov

/-- The derivative kernel of a differentiable leaf-constant map of full transverse rank equals the
foliation tangent subspace. (Zhang, Lemma 4.2; Nisoli, Definitions 1.1.1–1.1.3, pp.9–10) -/
theorem foliation_leaf_constant_mfderiv_kernel
    {d r c : ℕ} {M E : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (F : RegularHolomorphicFoliation d r c M) (q : M → E)
    (hconstant : ∀ a b, F.partition a b → q a = q b)
    (hE : Module.finrank ℂ E = c) (x : M)
    (hq : MDifferentiableAt (complexModel d) 𝓘(ℂ, E) q x)
    (hsurj : Function.Surjective (mfderiv (complexModel d) 𝓘(ℂ, E) q x)) :
    (mfderiv (complexModel d) 𝓘(ℂ, E) q x).ker = F.tangent x := by
  let z : F.Leaf x := ⟨x, rfl⟩
  let D := mfderiv (complexModel d) 𝓘(ℂ, E) q x
  let J := mfderiv (complexModel r) (complexModel d) (fun s : F.Leaf x ↦ s.val) z
  have heq : (fun s : F.Leaf x ↦ q s.val) = fun _ ↦ q x := by
    funext s
    exact hconstant s.val x (Quotient.exact s.property)
  have hcomp : D.comp J = 0 := by
    have hh : mfderiv (complexModel r) 𝓘(ℂ, E) (fun s : F.Leaf x ↦ q s.val) z = 0 := by
      rw [heq, mfderiv_const]
    change mfderiv (complexModel r) 𝓘(ℂ, E) (q ∘ (fun s : F.Leaf x ↦ s.val)) z = 0 at hh
    rw [mfderiv_comp z hq
      ((F.inclusion_holomorphic (Quotient.mk F.partition x) z).mdifferentiableAt
        (by simp))] at hh
    exact hh
  have hle : F.tangent x ≤ D.ker := by
    rintro v ⟨w, rfl⟩
    exact congrArg (fun L ↦ L w) hcomp
  have hJ : Function.Injective J :=
    F.inclusion_immersion (Quotient.mk F.partition x) z
  have hrankJ : Module.finrank ℂ (F.tangent x) = r := by
    change Module.finrank ℂ J.toLinearMap.range = r
    rw [LinearMap.finrank_range_of_inj hJ]
    change Module.finrank ℂ (Fin r → ℂ) = r
    exact (Module.finrank_pi ℂ).trans (Fintype.card_fin r)
  have hD : D.toLinearMap.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrankD := D.toLinearMap.finrank_range_add_finrank_ker
  rw [hD, finrank_top] at hrankD
  have hker : Module.finrank ℂ D.ker = r := by
    have hn : d = r + c := F.dimension
    have hd : Module.finrank ℂ (TangentSpace (complexModel d) x) = d :=
      (Module.finrank_pi ℂ).trans (Fintype.card_fin d)
    change Module.finrank ℂ E + Module.finrank ℂ D.ker =
      Module.finrank ℂ (TangentSpace (complexModel d) x) at hrankD
    rw [hE, hd] at hrankD
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (hrankJ.trans hker.symm)).symm

end HolomorphicAnosov
