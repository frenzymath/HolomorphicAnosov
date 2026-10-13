import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexKernels

/-!
# Homotopies transported through evaluated homological-complex kernels

This is the generic algebraic adapter needed after a prism homotopy gives a
commuting square on every graded component.  The proof uses the evaluated
kernel-preservation isomorphism, rather than identifying a homological-complex
kernel with an evaluated kernel by definitional equality.

Source: the categorical kernel universal property in Mathlib, together with
Hatcher, *Algebraic Topology*, pp. 112--113 and 201 for the supported prism
identity to which this adapter is applied.
-/

open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section

namespace HolomorphicAnosov

/-- A componentwise commuting homotopy square induces a homotopy between the
corresponding maps of homological-complex kernels. -/
theorem kernel_homotopy_component_lift
    {R : Type u} [CommRing R]
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℕ}
    (p : P ⟶ P') (q : Q ⟶ Q')
    (a b : P ⟶ Q) (a' b' : P' ⟶ Q')
    (sa : p ≫ a' = a ≫ q) (sb : p ≫ b' = b ≫ q)
    (ha : _root_.Homotopy a b) (ha' : _root_.Homotopy a' b')
    (hsquare : ∀ i j, p.f i ≫ ha'.hom i j = ha.hom i j ≫ q.f j) :
    Nonempty (_root_.Homotopy (kernel.map p q a a' sa)
      (kernel.map p q b b' sb)) := by
  let h : ∀ i j, (kernel p).X i ⟶ (kernel q).X j := fun i j => by
    letI := HomologicalComplex.eval_preservesLimit_of_hasKernel_f q j
    let z := kernel.lift (q.f j) ((kernel.ι p).f i ≫ ha.hom i j) (by
      simp only [Category.assoc]
      rw [← hsquare i j]
      have hcond : (kernel.ι p).f i ≫ p.f i = 0 := by
        simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
          congrArg (fun k => k.f i) (kernel.condition p)
      rw [← Category.assoc, hcond, zero_comp])
    let e := PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{u} R)
      (ComplexShape.up ℕ) j) q
    exact z ≫ e.inv
  have hfac (i j : ℕ) : h i j ≫ (kernel.ι q).f j =
      (kernel.ι p).f i ≫ ha.hom i j := by
    dsimp only [h]
    rw [Category.assoc]
    change _ ≫ (PreservesKernel.iso (HomologicalComplex.eval (ModuleCat.{u} R)
      (ComplexShape.up ℕ) j) q).inv ≫
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) j).map
        (kernel.ι q) = _
    rw [PreservesKernel.iso_inv_ι]
    exact kernel.lift_ι _ _ _
  have hfacfun : (fun i j => h i j ≫ (kernel.ι q).f j) =
      (fun i j => (kernel.ι p).f i ≫ ha.hom i j) :=
    funext fun i => funext (hfac i)
  refine ⟨{ hom := h, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    apply (cancel_mono ((kernel.ι q).f j)).mp
    rw [hfac, ha.zero i j hij, comp_zero, zero_comp]
  · intro i
    apply (cancel_mono ((kernel.ι q).f i)).mp
    simp only [Preadditive.add_comp]
    rw [← dNext_comp_right, ← prevD_comp_right,
      hfacfun, dNext_comp_left, prevD_comp_left]
    have haf : (kernel.map p q a a' sa).f i ≫ (kernel.ι q).f i =
        (kernel.ι p).f i ≫ a.f i := by
      change (kernel.map p q a a' sa ≫ kernel.ι q).f i = _
      simp [kernel.map]
    have hbf : (kernel.map p q b b' sb).f i ≫ (kernel.ι q).f i =
        (kernel.ι p).f i ≫ b.f i := by
      change (kernel.map p q b b' sb ≫ kernel.ι q).f i = _
      simp [kernel.map]
    rw [haf, hbf, ha.comm i]
    simp only [Preadditive.comp_add]

end HolomorphicAnosov
