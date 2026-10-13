import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.Topology

/-- Quotienting a short exact sequence by a short exact subsequence is short exact.
Apply the snake lemma to the inclusion. Its leftmost kernel terms vanish because
the third inclusion is monic; hence the first quotient map is monic. The last
three terms of the snake sequence give exactness, and the last quotient map is
epic because the last map of the original row is epic.
Source: Hatcher, Algebraic Topology, relative Mayer–Vietoris pp.152–153;
Mac Lane, Categories for the Working Mathematician, VIII §4 (snake lemma). -/
theorem shortExact_cokernel_sequence {C : Type*} [Category* C] [Abelian C]
    {S T U : ShortComplex C} (f : S ⟶ T) (q : T ⟶ U)
    (w : f ≫ q = 0) (hq : IsColimit (CokernelCofork.ofπ q w))
    (hS : S.ShortExact) (hT : T.ShortExact) [Mono f.τ₃] : U.ShortExact := by
  let D : ShortComplex.SnakeInput C := {
    L₀ := kernel f
    L₁ := S
    L₂ := T
    L₃ := U
    v₀₁ := kernel.ι f
    v₁₂ := f
    v₂₃ := q
    w₀₂ := kernel.condition f
    w₁₃ := w
    h₀ := kernelIsKernel f
    h₃ := hq
    L₁_exact := hS.exact
    epi_L₁_g := hS.epi_g
    L₂_exact := hT.exact
    mono_L₂_f := hT.mono_f }
  have hzero : IsZero D.L₀.X₃ := KernelFork.IsLimit.isZero_of_mono D.h₀τ₃
  have : Epi T.g := hT.epi_g
  exact {
    exact := D.L₃_exact
    mono_f := (D.L₂'.exact_iff_mono (hzero.eq_of_src D.δ 0)).mp D.L₂'_exact
    epi_g := D.epi_L₃_g }

section BiproductCokernel
variable {C : Type*} [Category* C] [Abelian C]
  {A₁ A₂ B₁ B₂ Q₁ Q₂ : C} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂}
  {q₁ : B₁ ⟶ Q₁} {q₂ : B₂ ⟶ Q₂}
  (w₁ : f₁ ≫ q₁ = 0) (w₂ : f₂ ≫ q₂ = 0)

/-- The direct sum of two cokernel projections is a cokernel projection. -/
def biprodCokernelCofork : CokernelCofork (biprod.map f₁ f₂) :=
  CokernelCofork.ofπ (biprod.map q₁ q₂) (by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [w₁, w₂])

set_option backward.isDefEq.respectTransparency false in
/-- Cokernels commute with the finite direct sum, by their universal property. -/
def biprodCokernelIsColimit
    (h₁ : IsColimit (CokernelCofork.ofπ q₁ w₁))
    (h₂ : IsColimit (CokernelCofork.ofπ q₂ w₂)) :
    IsColimit (biprodCokernelCofork w₁ w₂) := by
  refine CokernelCofork.IsColimit.ofπ _ (biprodCokernelCofork w₁ w₂).condition
    (fun s hs ↦ biprod.desc
      (h₁.desc (CokernelCofork.ofπ (biprod.inl ≫ s) ?_))
      (h₂.desc (CokernelCofork.ofπ (biprod.inr ≫ s) ?_))) ?_ ?_
  · simpa using biprod.inl ≫= hs
  · simpa using biprod.inr ≫= hs
  · intro Z s hs
    apply biprod.hom_ext'
    · simpa [biprodCokernelCofork] using h₁.fac (CokernelCofork.ofπ (biprod.inl ≫ s) _) WalkingParallelPair.one
    · simpa [biprodCokernelCofork] using h₂.fac (CokernelCofork.ofπ (biprod.inr ≫ s) _) WalkingParallelPair.one
  · intro Z s hs m hm
    apply biprod.hom_ext'
    · apply Cofork.IsColimit.hom_ext h₁
      trans biprod.inl ≫ s
      · simpa [biprodCokernelCofork] using biprod.inl ≫= hm
      · simp only [biprod.inl_desc]
        exact (h₁.fac (CokernelCofork.ofπ (biprod.inl ≫ s) _) WalkingParallelPair.one).symm
    · apply Cofork.IsColimit.hom_ext h₂
      trans biprod.inr ≫ s
      · simpa [biprodCokernelCofork] using biprod.inr ≫= hm
      · simp only [biprod.inr_desc]
        exact (h₂.fac (CokernelCofork.ofπ (biprod.inr ≫ s) _) WalkingParallelPair.one).symm
end BiproductCokernel

end HolomorphicAnosov.Topology
