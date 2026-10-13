import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.InverseSheetsDifferByDeckLocally
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.TranslatedLocalPotentialsGlue

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- A holomorphic projection that transforms by translations under deck maps defines a holomorphic
one-form downstairs by differentiating its compositions with covering inverse sheets. (Zhang,
Lemma 4.2) -/
theorem covering_projection_holomorphic_form
    {d : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
    [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y]
    {Γ : Type*} (p : Y → X) (q : Y → ℂ) (D : Γ → Y → Y)
    (hq : ContMDiff (complexModel d) 𝓘(ℂ, ℂ) ∞ q)
    (hD : ∀ γ, Continuous (D γ)) (hpD : ∀ γ y, p (D γ y) = p y)
    (hqD : ∀ γ, ∃ c : ℂ, ∀ y, q (D γ y) = q y + c)
    (hinj : ∀ y, ∃ W : Set Y, W ∈ 𝓝 y ∧ Set.InjOn p W)
    (O : X → Set X) (hO : ∀ x, IsOpen (O x)) (hxO : ∀ x, x ∈ O x)
    (s : X → X → Y)
    (hs : ∀ x, ContMDiffOn (complexModel d) (complexModel d) ∞ (s x) (O x))
    (hps : ∀ x z, z ∈ O x → p (s x z) = z)
    (hmatch : ∀ x y z, z ∈ O x → z ∈ O y →
      ∃ γ, D γ (s x z) = s y z) :
    ∃ θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ,
      ContMDiff (complexModel d)
        ((complexModel d).prod 𝓘(ℂ, ComplexModel d →L[ℂ] ℂ)) ∞
        (fun x ↦ (⟨x, θ x⟩ : Bundle.TotalSpace (ComplexModel d →L[ℂ] ℂ)
          (fun z : X ↦ TangentSpace (complexModel d) z →L[ℂ] ℂ))) ∧
      ∀ x z, z ∈ O x → θ z =
        transverseScalarDifferential (d := d) (q ∘ s x) z := by
  apply translated_local_potentials_glue O hO hxO (fun x ↦ q ∘ s x)
  · intro x
    exact hq.comp_contMDiffOn (hs x)
  · intro x y z hx hy
    obtain ⟨γ, hγ⟩ := hmatch x y z hx hy
    obtain ⟨W, hW, hi⟩ := hinj (s y z)
    have hsc := ((hD γ).continuousAt).comp
      (((hs x z hx).contMDiffAt ((hO x).mem_nhds hx)).continuousAt)
    have htc := ((hs y z hy).contMDiffAt ((hO y).mem_nhds hy)).continuousAt
    have heq := inverse_sheets_differ_by_deck_locally p (s x) (s y) (D γ) z
      hsc htc hγ W hW hi (hpD γ)
      (by filter_upwards [(hO x).mem_nhds hx] with w hw; exact hps x w hw)
      (by filter_upwards [(hO y).mem_nhds hy] with w hw; exact hps y w hw)
    obtain ⟨c, hc⟩ := hqD γ
    refine ⟨c, ?_⟩
    filter_upwards [heq] with w hw
    change q (s y w) = q (s x w) + c
    rw [hw, hc]


end HolomorphicAnosov.Paper.Zhang
