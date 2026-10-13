import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.TranslatedNativePotentialsSameCovector
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeScalarDifferentialComp

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- The one-form defined by local covering inverse sheets pulls back to `dq` at every covering point
when deck maps act transitively on fibres and translate `q`. (Zhang, Lemma 4.2) -/
theorem descended_form_pullback_of_deck_sheets
    {d : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
    [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y]
    {Γ : Type*} (p : Y → X) (q : Y → ℂ) (D : Γ → Y → Y)
    (hp : ContMDiff (complexModel d) (complexModel d) ∞ p)
    (hq : ContMDiff (complexModel d) 𝓘(ℂ, ℂ) ∞ q)
    (hD : ∀ γ, Continuous (D γ)) (hpD : ∀ γ y, p (D γ y) = p y)
    (hqD : ∀ γ, ∃ c : ℂ, ∀ y, q (D γ y) = q y + c)
    (hinj : ∀ y, ∃ W : Set Y, W ∈ 𝓝 y ∧ Set.InjOn p W)
    (O : X → Set X) (hO : ∀ x, IsOpen (O x)) (hxO : ∀ x, x ∈ O x)
    (s : X → X → Y)
    (hs : ∀ x, ContMDiffOn (complexModel d) (complexModel d) ∞ (s x) (O x))
    (hps : ∀ x z, z ∈ O x → p (s x z) = z)
    (hmatch : ∀ y, ∃ γ, D γ y = s (p y) (p y))
    (θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ : ∀ x z, z ∈ O x → θ z =
      transverseScalarDifferential (d := d) (q ∘ s x) z) :
    ∀ y, (θ (p y)).comp (mfderiv (complexModel d) (complexModel d) p y) =
      transverseScalarDifferential (d := d) q y := by
  intro y
  obtain ⟨γ, hγ⟩ := hmatch y
  obtain ⟨W, hW, hi⟩ := hinj (s (p y) (p y))
  have hspc : ContinuousAt (fun z ↦ s (p y) (p z)) y :=
    (((hs (p y) (p y) (hxO (p y))).contMDiffAt
      ((hO (p y)).mem_nhds (hxO (p y)))).continuousAt).comp (hp y).continuousAt
  have hDc : ContinuousAt (D γ) y := (hD γ).continuousAt
  have hWs := hspc hW
  have hWD := hDc (by simpa only [hγ] using hW)
  have hOp : ∀ᶠ z in 𝓝 y, p z ∈ O (p y) :=
    (hp y).continuousAt ((hO (p y)).mem_nhds (hxO (p y)))
  obtain ⟨c, hc⟩ := hqD γ
  have heq : (q ∘ s (p y)) ∘ p =ᶠ[𝓝 y] fun z ↦ q z + c := by
    filter_upwards [hWs, hWD, hOp] with z hzS hzD hzO
    have hz : s (p y) (p z) = D γ z := hi hzS hzD (by rw [hps _ _ hzO, hpD])
    change q (s (p y) (p z)) = q z + c
    rw [hz, hc]
  rw [hθ (p y) (p y) (hxO (p y)),
    ← native_scalar_differential_comp (q ∘ s (p y)) p y
      (((hq.comp_contMDiffOn (hs (p y))) (p y) (hxO (p y))).contMDiffAt
        ((hO (p y)).mem_nhds (hxO (p y))) |>.mdifferentiableAt (by simp))
      ((hp y).mdifferentiableAt (by simp))]
  exact translated_native_potentials_same_covector q ((q ∘ s (p y)) ∘ p) y c
    ((hq y).mdifferentiableAt (by simp)) heq


end HolomorphicAnosov.Paper.Zhang
