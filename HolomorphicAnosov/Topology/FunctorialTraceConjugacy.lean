import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Trace

/-!
# Trace invariance under functorial conjugacy

This is the algebraic transport used in Dold (1965), proof of (4.1), pp.5–6,
when identifying the homology endomorphism on an ENR with the endomorphism on
its section image. It applies to every functor into modules.
-/

noncomputable section

open CategoryTheory

namespace HolomorphicAnosov

universe u v w r

/-- A functor into modules preserves the trace of conjugate endomorphisms.

Apply the functor to the conjugacy square. The image of the isomorphism is a
linear equivalence; cancel its inverse in the square to identify the second
endomorphism with the linear conjugate of the first. Mathlib's `trace_conj'`
then proves equality. No finite-dimensional hypothesis is needed for this
identity of Mathlib traces, so zero modules and infinite-dimensional modules
are covered as well. -/
theorem functor_trace_eq_of_conjugacy
    {C : Type u} [Category.{v} C] {R : Type r} [CommRing R]
    (F : C ⥤ ModuleCat.{w} R) {X Y : C} (e : X ≅ Y)
    (f : X ⟶ X) (g : Y ⟶ Y) (h : f ≫ e.hom = e.hom ≫ g) :
    LinearMap.trace R (F.obj Y) (F.map g).hom =
      LinearMap.trace R (F.obj X) (F.map f).hom := by
  let E := (F.mapIso e).toLinearEquiv
  have hmap : (F.map e.hom).hom.comp (F.map f).hom =
      (F.map g).hom.comp (F.map e.hom).hom := by
    simpa only [Functor.map_comp, ModuleCat.hom_comp] using
      congrArg (fun t ↦ (F.map t).hom) h
  have heq : E.conj (F.map f).hom = (F.map g).hom := by
    ext y
    have hy := LinearMap.congr_fun hmap (E.symm y)
    change E ((F.map f).hom (E.symm y)) = (F.map g).hom (E (E.symm y)) at hy
    simpa only [LinearEquiv.conj_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hy
  rw [← heq]
  exact LinearMap.trace_conj' _ E

/-- The finite alternating trace of a family of module-valued functors is
invariant under conjugacy. Apply the functorial trace identity in each degree
and retain its original alternating coefficient. This gives the homological
trace transport in Dold's proof of (4.1), including an empty degree set. -/
theorem functor_alternating_trace_eq_of_conjugacy
    {C : Type u} [Category.{v} C] {R : Type r} [CommRing R]
    (F : ℕ → C ⥤ ModuleCat.{w} R) {X Y : C} (e : X ≅ Y)
    (f : X ⟶ X) (g : Y ⟶ Y) (h : f ≫ e.hom = e.hom ≫ g) (s : Finset ℕ) :
    (∑ k ∈ s, (-1 : R) ^ k * LinearMap.trace R ((F k).obj Y) ((F k).map g).hom) =
      ∑ k ∈ s, (-1 : R) ^ k * LinearMap.trace R ((F k).obj X) ((F k).map f).hom := by
  apply Finset.sum_congr rfl
  intro k _
  rw [functor_trace_eq_of_conjugacy (F k) e f g h]

end HolomorphicAnosov

