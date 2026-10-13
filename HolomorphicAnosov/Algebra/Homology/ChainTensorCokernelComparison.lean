import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Tensor products commute with cokernels of nonnegative chain complexes

This is an agent-written categorical expansion of the relative tensor-quotient
step in `topo.singular_eilenberg_zilber_acyclic_models_g7`.
DAG node: `algebra.chain_tensor_cokernel_comparison_g19`. The exact algebraic
inputs are Mathlib's module tensor/Hom adjunction, its preservation of colimits,
and the native tensor-total coproduct and degreewise colimit APIs. No proof is
attributed to an unwritten passage of Bredon. The application in Bredon VI§1,
pp.316–318, motivates the comparison; all mathematics used below is over an
arbitrary commutative ring, without flatness or injectivity hypotheses.
-/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomologicalComplex CategoryTheory.Category CategoryTheory.MonoidalPreadditive
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace HolomorphicAnosov
variable {R : Type u} [CommRing R]
variable {C₀ C : ChainComplex (ModuleCat.{u} R) ℕ}
  (f : C₀ ⟶ C) (D : ChainComplex (ModuleCat.{u} R) ℕ)

private lemma ι_tensorRight_map (p q n : ℕ) (hpq : p + q = n) :
    ιTensorObj C₀ D p q n hpq ≫ (HomologicalComplex.tensorHom f (𝟙 D)).f n =
      (tensorRight (D.X q)).map (f.f p) ≫ ιTensorObj C D p q n hpq := by
  rw [ι_mapBifunctorMap]
  simp only [id_f, curriedTensor, whiskerLeft_id, id_comp]
  rfl

private lemma tensor_condition :
    HomologicalComplex.tensorHom f (𝟙 D) ≫
      HomologicalComplex.tensorHom (cokernel.π f) (𝟙 D) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [comp_f, zero_f, comp_zero, ← Category.assoc, ι_tensorRight_map]
  rw [Category.assoc, ι_tensorRight_map, ← Category.assoc, ← Functor.map_comp]
  have h := congrArg (fun k ↦ k.f p) (cokernel.condition f)
  simp only [comp_f, zero_f] at h
  rw [h, Functor.map_zero, zero_comp]

private def degreeCofork (n : ℕ) : CokernelCofork ((HomologicalComplex.tensorHom f (𝟙 D)).f n) :=
  CokernelCofork.ofπ ((HomologicalComplex.tensorHom (cokernel.π f) (𝟙 D)).f n)
    (by simpa only [comp_f, zero_f] using congrArg (fun h ↦ h.f n) (tensor_condition f D))

private def summandColimit (p q : ℕ) :=
  ((CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)).map
    (eval (ModuleCat R) (.down ℕ) p)).mapIsColimit
      ((CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)).mapIsColimit
        (cokernelIsCokernel f) (eval (ModuleCat R) (.down ℕ) p))
      (tensorRight (D.X q))

private def degreeColimit (n : ℕ) : IsColimit (degreeCofork f D n) := by
  let desc (s : CokernelCofork ((HomologicalComplex.tensorHom f (𝟙 D)).f n)) :
      (HomologicalComplex.tensorObj (cokernel f) D).X n ⟶ s.pt :=
    mapBifunctorDesc (fun p q hpq ↦ (summandColimit f D p q).desc
      (CokernelCofork.ofπ (ιTensorObj C D p q n hpq ≫ s.π) (by
        have hs := congrArg (fun k ↦ ιTensorObj C₀ D p q n hpq ≫ k) s.condition
        simp only [comp_zero, ← Category.assoc, ι_tensorRight_map] at hs
        simpa! only [Category.assoc, eval_map, eval_obj] using hs)))
  have fac (s) : (degreeCofork f D n).π ≫ desc s = s.π := by
    apply mapBifunctor.hom_ext
    intro p q hpq
    simp only [degreeCofork, CokernelCofork.π_ofπ]
    simp only [← Category.assoc, ι_tensorRight_map,
      desc]
    simp only [Category.assoc, ι_mapBifunctorDesc]
    exact Cofork.IsColimit.π_desc (summandColimit f D p q)
  refine Cofork.IsColimit.mk _ desc fac ?_
  intro s m hm
  apply mapBifunctor.hom_ext
  intro p q hpq
  apply Cofork.IsColimit.hom_ext (summandColimit f D p q)
  have he := congrArg (fun k ↦ ιTensorObj C D p q n hpq ≫ k) hm
  simp only [degreeCofork, CokernelCofork.π_ofπ, ← Category.assoc,
    ι_tensorRight_map] at he
  have hf := congrArg (fun k ↦ ιTensorObj C D p q n hpq ≫ k) (fac s)
  simp only [degreeCofork, CokernelCofork.π_ofπ, ← Category.assoc,
    ι_tensorRight_map] at hf
  simpa only [CokernelCofork.map_π, CokernelCofork.π_ofπ, eval_map,
    Category.assoc] using he.trans hf.symm


private def tensorCofork : CokernelCofork (HomologicalComplex.tensorHom f (𝟙 D)) :=
  CokernelCofork.ofπ (HomologicalComplex.tensorHom (cokernel.π f) (𝟙 D))
    (tensor_condition f D)

private def tensorColimit : IsColimit (tensorCofork f D) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact (isColimitMapCoconeCoforkEquiv'
    (eval (ModuleCat R) (.down ℕ) n) (tensor_condition f D)).symm (degreeColimit f D n)

/-- Tensoring a nonnegative chain complex of modules on the right preserves a
cokernel, with the canonical quotient projection.

Source/provenance: agent-written expansion of the relative quotient comparison
in `topo.singular_eilenberg_zilber_acyclic_models_g7`, using the exact Mathlib
module tensor/Hom adjunction (`ModuleCat.Monoidal.Closed`), colimit preservation
by a left adjoint, and `HomologicalComplex.isColimitOfEval`. This is the
categorical form of module tensor right exactness, rather than a claimed
application of an unproved chain-complex closed-monoidal instance.

Complete proof: Let Q=coker(f) and let q:C→Q be its projection. Tensoring its
chain equation with the identity of D shows (f⊗id)(q⊗id)=0. Evaluation in degree
p preserves cokernels, so Q_p is the cokernel of f_p with projection q_p.
Tensoring modules on the right by D_q preserves that colimit, by the
module tensor/Hom adjunction and the symmetry of module tensor products. Thus
Q_p⊗D_q is the cokernel of f_p⊗id, with its original projection q_p⊗id.
In total degree n, a map from C⊗D killing f⊗id restricts on every summand
p+q=n to a map killing f_p⊗id. Descend it uniquely through q_p⊗id and assemble
the resulting maps using the native coproduct universal property. The projection
identity and uniqueness are checked on each summand. Hence in every degree
(q⊗id)_n exhibits (Q⊗D)_n as the required cokernel. Evaluation detects colimits
of complexes, so these degreewise universal properties give the chain-complex
cokernel universal property, including differential compatibility. Uniqueness
of colimits gives the comparison isomorphism; its defining cocone equation is
exactly the displayed quotient-projection equation. Zero complexes, zero maps,
and degree zero are included. No splitting, flatness or monomorphism is used. -/
theorem chain_tensor_cokernel_comparison :
    ∃ e : cokernel (HomologicalComplex.tensorHom f (𝟙 D)) ≅
        HomologicalComplex.tensorObj (cokernel f) D,
      cokernel.π (HomologicalComplex.tensorHom f (𝟙 D)) ≫ e.hom =
        HomologicalComplex.tensorHom (cokernel.π f) (𝟙 D) := by
  let e := (cokernelIsCokernel (HomologicalComplex.tensorHom f (𝟙 D))).coconePointUniqueUpToIso
    (tensorColimit f D)
  refine ⟨e, ?_⟩
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (HomologicalComplex.tensorHom f (𝟙 D)))
    (tensorColimit f D) WalkingParallelPair.one

end HolomorphicAnosov

