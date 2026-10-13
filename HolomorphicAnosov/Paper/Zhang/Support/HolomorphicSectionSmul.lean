import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u
/-- The product of a holomorphic scalar function and a holomorphic quotient section is holomorphic.
(Zhang, Lemma 2.4, p. 7) -/
theorem holomorphic_section_smul
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    {V : Set X} (s : (x : X) → QuotientLineConnection.Fibre U x)
    (hs : QuotientLineConnection.IsHolomorphicSection U V s)
    (g : X → ℂ) (hg : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ g V) :
    QuotientLineConnection.IsHolomorphicSection U V (fun x ↦ g x • s x) := by
  intro x hx
  obtain ⟨W, v, hopen, hxW, hWV, hv, hvs⟩ := hs x hx
  refine ⟨W, (fun y ↦ g y • v y), hopen, hxW, hWV, ?_, ?_⟩
  · exact (hg.mono hWV).smul_section hv
  · intro y hy
    simp only [map_smul, hvs y hy]
end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
