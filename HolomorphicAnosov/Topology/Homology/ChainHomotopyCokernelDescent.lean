import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Descent of compatible chain homotopies to cokernels

Source: Bredon, Topology and Geometry, IV16.1 pp.221–222 and VI1.4 p.318.
A homotopy preserving the subcomplex descends degree by degree, and its
identity follows by precomposing with the quotient projections. The statement
uses native cokernels and works without an injectivity hypothesis on the maps
whose cokernels are taken.
-/

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov

/-- Compatible maps and a compatible homotopy descend to the actual cokernel
complexes, retaining their projection equations. Source: Bredon IV16.1 and
VI1.4, the relative comparison construction. The chain maps descend by the
cokernel universal property. Evaluation preserves cokernels, so each homotopy
component also descends. Precomposition with the degreewise quotient projection
reduces the shape condition and homotopy equation to the original ones. -/
theorem chain_homotopy_cokernel_descent
    {V : Type*} [Category* V] [Preadditive V] [HasFiniteColimits V]
    {P₀ P Q₀ Q : ChainComplex V ℕ}
    (a : P₀ ⟶ P) (b : Q₀ ⟶ Q)
    (f₀ g₀ : P₀ ⟶ Q₀) (f g : P ⟶ Q)
    (hf : a ≫ f = f₀ ≫ b) (hg : a ≫ g = g₀ ≫ b)
    (H₀ : Homotopy f₀ g₀) (H : Homotopy f g)
    (hH : ∀ i j, a.f i ≫ H.hom i j = H₀.hom i j ≫ b.f j) :
    ∃ (fR gR : cokernel a ⟶ cokernel b) (HR : Homotopy fR gR),
      cokernel.π a ≫ fR = f ≫ cokernel.π b ∧
      cokernel.π a ≫ gR = g ≫ cokernel.π b ∧
      ∀ i j, H.hom i j ≫ (cokernel.π b).f j =
        (cokernel.π a).f i ≫ HR.hom i j := by
  let fR := cokernel.desc a (f ≫ cokernel.π b) (by
    rw [← Category.assoc, hf, Category.assoc, cokernel.condition, comp_zero])
  let gR := cokernel.desc a (g ≫ cokernel.π b) (by
    rw [← Category.assoc, hg, Category.assoc, cokernel.condition, comp_zero])
  have hfR : cokernel.π a ≫ fR = f ≫ cokernel.π b := cokernel.π_desc _ _ _
  have hgR : cokernel.π a ≫ gR = g ≫ cokernel.π b := cokernel.π_desc _ _ _
  let hcol (i : ℕ) := (CokernelCofork.ofπ (cokernel.π a) (cokernel.condition a)).mapIsColimit
    (cokernelIsCokernel a) (HomologicalComplex.eval V (.down ℕ) i)
  have hzero (i j : ℕ) : a.f i ≫ (H.hom i j ≫ (cokernel.π b).f j) = 0 := by
    rw [← Category.assoc, hH, Category.assoc]
    have hb := congrArg (fun k ↦ k.f j) (cokernel.condition b)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, comp_zero] using
      congrArg (fun k ↦ H₀.hom i j ≫ k) hb
  let h (i j : ℕ) : (cokernel a).X i ⟶ (cokernel b).X j :=
    (hcol i).desc (CokernelCofork.ofπ (H.hom i j ≫ (cokernel.π b).f j) (hzero i j))
  have hp (i j : ℕ) : (cokernel.π a).f i ≫ h i j =
      H.hom i j ≫ (cokernel.π b).f j := Cofork.IsColimit.π_desc (hcol i)
  have hext (i : ℕ) {Z : V} (u v : (cokernel a).X i ⟶ Z)
      (huv : (cokernel.π a).f i ≫ u = (cokernel.π a).f i ≫ v) : u = v :=
    Cofork.IsColimit.hom_ext (hcol i) huv
  let HR : Homotopy fR gR :=
    { hom := h
      zero := fun i j hij ↦ hext i _ _ (by rw [hp, H.zero i j hij, zero_comp, comp_zero])
      comm := fun i ↦ by
        apply hext i
        have hfamilies : (fun i j ↦ (cokernel.π a).f i ≫ h i j) =
            (fun i j ↦ H.hom i j ≫ (cokernel.π b).f j) := funext (fun i ↦ funext (hp i))
        have hf' := congrArg (fun k ↦ k.f i) hfR
        have hg' := congrArg (fun k ↦ k.f i) hgR
        simp only [HomologicalComplex.comp_f] at hf' hg'
        rw [Preadditive.comp_add, Preadditive.comp_add,
          ← dNext_comp_left, ← prevD_comp_left, hfamilies,
          dNext_comp_right, prevD_comp_right, hf', hg']
        exact congrArg (fun k ↦ k ≫ (cokernel.π b).f i) (H.comm i) |>.trans
          (by simp only [Preadditive.add_comp]) }
  exact ⟨fR, gR, HR, hfR, hgR, fun i j ↦ (hp i j).symm⟩

end HolomorphicAnosov
