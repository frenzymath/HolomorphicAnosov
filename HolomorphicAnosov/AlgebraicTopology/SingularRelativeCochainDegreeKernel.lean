import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition

/-!
# Relative cochains as the degreewise restriction kernel

Source: Hatcher, *Algebraic Topology*, pp.199–200, exact relative cochain sequence.
DAG node: `topo.singular_relative_cochain_degree_kernel_g6`.
-/

open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- The native relative-cochain inclusion is injective in every degree, and its
image is exactly the ordinary cochains restricting to zero on the subspace.

Source: Hatcher, *Algebraic Topology*, pp.199–200. Relative cochains are the
kernel complex of restriction. Degree evaluation preserves this kernel, and
Mathlib's kernel in modules is the concrete linear-map kernel. Transporting
the element (a, restriction(a)=0) through these two canonical isomorphisms
constructs its preimage; their inclusion equations give its actual value.
Conversely the kernel condition makes every included relative cochain restrict
to zero. Monicity of the evaluated kernel inclusion gives injectivity. -/
theorem relativeCochain_degree_kernel (R : Type u) [CommRing R]
    (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    Function.Injective ((cupInclusion R X A true).f n) ∧
      ∀ a : cochains R X n,
        (∃ b : (relativeComplex R X A).X n, (cupInclusion R X A true).f n b = a) ↔
          (pullback R (subspaceInclusion X A)).f n a = 0 := by
  constructor
  · apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n).map
      (kernel.ι (pullback R (subspaceInclusion X A))))
    infer_instance
  · intro a
    constructor
    · rintro ⟨b, rfl⟩
      exact congrArg (fun f ↦ f.f n b)
        (kernel.condition (pullback R (subspaceInclusion X A)))
    · intro ha
      let F := HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n
      let f := pullback R (subspaceInclusion X A)
      refine ⟨(PreservesKernel.iso F f).inv
        ((ModuleCat.kernelIsoKer (F.map f)).inv ⟨a, ha⟩), ?_⟩
      change ((ModuleCat.kernelIsoKer (F.map f)).inv ≫ (PreservesKernel.iso F f).inv ≫
        F.map (kernel.ι f)) ⟨a, ha⟩ = a
      rw [PreservesKernel.iso_inv_ι, ModuleCat.kernelIsoKer_inv_kernel_ι]
      rfl

end HolomorphicAnosov.SingularCochain
