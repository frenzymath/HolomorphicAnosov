import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.Anosov

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
/-- Iterates of a map conjugated by a diffeomorphism are conjugate to the corresponding original iterates. -/
theorem conjugate_iterate (h : Biholomorph d d X Y) (f : Biholomorph d d X X)
    (n : ℕ) (x : X) :
    (((h.symm.trans f).trans h : Y → Y)^[n]) (h x) = h (((f : X → X)^[n]) x) := by
  have hs : Function.Semiconj h f ((h.symm.trans f).trans h) := by
    intro z
    change h (f z) = h (f (h.symm (h z)))
    rw [h.symm_apply_apply]
  exact (hs.iterate_right n x).symm


end
end HolomorphicAnosov.GhysAnosovConjugacy
