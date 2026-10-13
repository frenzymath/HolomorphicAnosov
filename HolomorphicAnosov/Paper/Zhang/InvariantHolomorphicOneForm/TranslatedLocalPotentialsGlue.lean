import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.CovectorSectionGluing
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.ScalarDifferentialHolomorphicOn
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.TranslatedNativePotentialsSameCovector

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- Holomorphic local potentials differing by constants near each overlap point have differentials
that glue to a global holomorphic one-form. (Zhang, Lemma 4.2) -/
theorem translated_local_potentials_glue
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (O : X → Set X) (hO : ∀ x, IsOpen (O x)) (hxO : ∀ x, x ∈ O x)
    (t : X → X → ℂ)
    (ht : ∀ x, ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ (t x) (O x))
    (htrans : ∀ x y z, z ∈ O x → z ∈ O y →
      ∃ c : ℂ, t y =ᶠ[𝓝 z] fun w ↦ t x w + c) :
    ∃ θ : ∀ y : X, TangentSpace (complexModel d) y →L[ℂ] ℂ,
      ContMDiff (complexModel d)
        ((complexModel d).prod 𝓘(ℂ, ComplexModel d →L[ℂ] ℂ)) ∞
        (fun y ↦ (⟨y, θ y⟩ : Bundle.TotalSpace (ComplexModel d →L[ℂ] ℂ)
          (fun z : X ↦ TangentSpace (complexModel d) z →L[ℂ] ℂ))) ∧
      ∀ x y, y ∈ O x → θ y = transverseScalarDifferential (d := d) (t x) y := by
  let localForm : X → ∀ y : X, TangentSpace (complexModel d) y →L[ℂ] ℂ :=
    fun x y ↦ transverseScalarDifferential (d := d) (t x) y
  have hagree : ∀ x y z, z ∈ O x → z ∈ O y → localForm x z = localForm y z := by
    intro x y z hx hy
    obtain ⟨c, hc⟩ := htrans x y z hx hy
    exact (translated_native_potentials_same_covector (t x) (t y) z c
      (((ht x z hx).contMDiffAt ((hO x).mem_nhds hx)).mdifferentiableAt (by simp))
      hc).symm
  refine ⟨fun y ↦ localForm y y, ?_, ?_⟩
  · exact covector_section_gluing O hO hxO localForm
      (fun x ↦ scalar_differential_holomorphic_on (t x) (O x) (hO x) (ht x)) hagree
  · intro x y hy
    exact hagree y x y (hxO y) hy


end HolomorphicAnosov.Paper.Zhang
