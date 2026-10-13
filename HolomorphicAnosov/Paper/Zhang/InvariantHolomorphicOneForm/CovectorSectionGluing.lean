import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- Holomorphic local cotangent sections that agree on overlaps glue to a global holomorphic
cotangent section agreeing with every local section. (Zhang, Lemma 4.2) -/
theorem covector_section_gluing
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (O : X → Set X) (hO : ∀ x, IsOpen (O x)) (hxO : ∀ x, x ∈ O x)
    (localForm : X → ∀ y : X, TangentSpace (complexModel d) y →L[ℂ] ℂ)
    (hlocal : ∀ x, ContMDiffOn (complexModel d)
      ((complexModel d).prod 𝓘(ℂ, ComplexModel d →L[ℂ] ℂ)) ∞
      (fun y ↦ (⟨y, localForm x y⟩ : Bundle.TotalSpace
        (ComplexModel d →L[ℂ] ℂ)
        (fun z : X ↦ TangentSpace (complexModel d) z →L[ℂ] ℂ))) (O x))
    (hagree : ∀ x y z, z ∈ O x → z ∈ O y → localForm x z = localForm y z) :
    ContMDiff (complexModel d)
      ((complexModel d).prod 𝓘(ℂ, ComplexModel d →L[ℂ] ℂ)) ∞
      (fun y ↦ (⟨y, localForm y y⟩ : Bundle.TotalSpace
        (ComplexModel d →L[ℂ] ℂ)
        (fun z : X ↦ TangentSpace (complexModel d) z →L[ℂ] ℂ))) := by
  intro x
  have hc := (hlocal x x (hxO x)).contMDiffAt ((hO x).mem_nhds (hxO x))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(hO x).mem_nhds (hxO x)] with y hy
  congr 1
  exact hagree y x y (hxO y) hy


end HolomorphicAnosov.Paper.Zhang
