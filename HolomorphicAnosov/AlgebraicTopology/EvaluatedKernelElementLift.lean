import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexKernels
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov

/-- Every element annihilated by a degreewise differential map lifts to the corresponding
degree of the categorical kernel complex. The evaluated-kernel comparison followed by
ModuleCat.kernelIsoKer identifies it with the ordinary linear kernel.
Source: Mathlib HomologicalComplexKernels and ModuleCat/Kernels;
DAG `algebra.evaluated_kernel_element_lift_g13`. -/
theorem evaluated_kernel_element_lift {R : Type u} [CommRing R]
    {P Q : CochainComplex (ModuleCat.{u} R) ℕ} (p : P ⟶ Q) (n : ℕ)
    (x : P.X n) (hx : p.f n x = 0) :
    ∃ y : (kernel p).X n, (kernel.ι p).f n y = x := by
  let e := PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{u} R)
    (ComplexShape.up ℕ) n) p
  let z : LinearMap.ker (p.f n).hom := ⟨x, hx⟩
  refine ⟨e.inv ((ModuleCat.kernelIsoKer (p.f n)).inv z), ?_⟩
  have he : e.inv ≫ (kernel.ι p).f n = kernel.ι (p.f n) :=
    PreservesKernel.iso_inv_ι _ _
  change (e.inv ≫ (kernel.ι p).f n) ((ModuleCat.kernelIsoKer (p.f n)).inv z) = x
  rw [he]
  change ((ModuleCat.kernelIsoKer (p.f n)).inv ≫ kernel.ι (p.f n)) z = x
  rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
  rfl

end HolomorphicAnosov
