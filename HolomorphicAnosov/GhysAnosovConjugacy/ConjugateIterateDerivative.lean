import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.GhysAnosovConjugacy.ConjugateIterate

open scoped ContDiff Manifold
namespace HolomorphicAnosov.GhysAnosovConjugacy
noncomputable section
universe u v
variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
  [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y]

attribute [local instance] complex_isManifold_real

omit [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y] in
/-- The derivative of each conjugated iterate is obtained by composing the derivatives in the conjugacy identity. -/
theorem conjugate_iterate_derivative
    (h : Biholomorph d d X Y) (f : Biholomorph d d X X) (n : ℕ) (x : X) :
    (mfderiv (realModel d) (realModel d)
      (((h.symm.trans f).trans h : Y → Y)^[n]) (h x)).comp
        (mfderiv (realModel d) (realModel d) h x) =
    (mfderiv (realModel d) (realModel d) h (((f : X → X)^[n]) x)).comp
      (mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x) := by
  have hh := h.toReal.contMDiff.mdifferentiable (by simp)
  have hf := (f.toReal.contMDiff.iterate n).mdifferentiable (by simp)
  have hg := ((Biholomorph.toReal ((h.symm.trans f).trans h)).contMDiff.iterate n).mdifferentiable
    (by simp)
  have hc₁ := mfderiv_comp x (hh (((f : X → X)^[n]) x)) (hf x)
  have hc₂ := mfderiv_comp x (hg (h x)) (hh x)
  change mfderiv (realModel d) (realModel d) ((h : X → Y) ∘ ((f : X → X)^[n])) x = _ at hc₁
  change mfderiv (realModel d) (realModel d)
    ((((h.symm.trans f).trans h : Y → Y)^[n]) ∘ h) x = _ at hc₂
  have heq : (h : X → Y) ∘ ((f : X → X)^[n]) =
      (((h.symm.trans f).trans h : Y → Y)^[n]) ∘ h := by
    funext z
    exact (conjugate_iterate h f n z).symm
  rw [heq, hc₂] at hc₁
  exact hc₁


end
end HolomorphicAnosov.GhysAnosovConjugacy
