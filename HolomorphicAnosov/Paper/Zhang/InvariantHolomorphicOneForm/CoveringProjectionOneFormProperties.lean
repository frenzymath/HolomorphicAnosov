import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.CoveringProjectionHolomorphicForm
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeFormClosedOfLocalPotential
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeScalarDifferentialEquivariance
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.CovectorEquivarianceDescends
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.DescendedFormPullbackOfDeckSheets

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- A holomorphic submersion on a covering, with deck translation invariance and `q ∘ F = μ * q`,
descends to a nowhere vanishing closed holomorphic one-form with unstable kernel and `f*θ = μθ`.
The supplied multiplier bounds give `0 < ‖μ‖ < 1`. (Zhang, Lemma 4.2) -/
theorem covering_projection_one_form_properties
    {d : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
    [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y]
    {Γ : Type*} (p : Y → X) (q : Y → ℂ) (D : Γ → Y → Y)
    (f : X → X) (F : Y → Y) (μ : ℂ)
    (U : ∀ x : X, Submodule ℝ (TangentSpace (realModel d) x))
    (hp : ContMDiff (complexModel d) (complexModel d) ∞ p)
    (hq : ContMDiff (complexModel d) 𝓘(ℂ, ℂ) ∞ q)
    (hf : ContMDiff (complexModel d) (complexModel d) ∞ f)
    (hF : ContMDiff (complexModel d) (complexModel d) ∞ F)
    (hpsurj : Function.Surjective p)
    (Dp : ∀ y, TangentSpace (complexModel d) y ≃L[ℂ]
      TangentSpace (complexModel d) (p y))
    (hDp : ∀ y, (Dp y).toContinuousLinearMap =
      mfderiv (complexModel d) (complexModel d) p y)
    (hqsurj : ∀ y, Function.Surjective (transverseScalarDifferential (d := d) q y))
    (hkernel : ∀ y v, transverseScalarDifferential (d := d) q y v = 0 ↔
      complexTangentToReal d (p y) (Dp y v) ∈ U (p y))
    (hD : ∀ γ, Continuous (D γ)) (hpD : ∀ γ y, p (D γ y) = p y)
    (hqD : ∀ γ, ∃ c : ℂ, ∀ y, q (D γ y) = q y + c)
    (hinj : ∀ y, ∃ W : Set Y, W ∈ 𝓝 y ∧ Set.InjOn p W)
    (O : X → Set X) (hO : ∀ x, IsOpen (O x)) (hxO : ∀ x, x ∈ O x)
    (s : X → X → Y)
    (hs : ∀ x, ContMDiffOn (complexModel d) (complexModel d) ∞ (s x) (O x))
    (hps : ∀ x z, z ∈ O x → p (s x z) = z)
    (hmatch : ∀ y z, p y = p z → ∃ γ, D γ y = z)
    (hcomm : p ∘ F = f ∘ p) (hqF : q ∘ F = μ • q)
    (hμpos : 0 < ‖μ‖) (hμlt : ‖μ‖ < 1) :
    ∃ θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ,
      ContMDiff (complexModel d)
        ((complexModel d).prod 𝓘(ℂ, ComplexModel d →L[ℂ] ℂ)) ∞
        (fun x ↦ (⟨x, θ x⟩ : Bundle.TotalSpace (ComplexModel d →L[ℂ] ℂ)
          (fun z : X ↦ TangentSpace (complexModel d) z →L[ℂ] ℂ))) ∧
      (∀ x, θ x ≠ 0) ∧
      (∀ x : X, ∀ z ∈ (chartAt (ComplexModel d) x).target,
        extDeriv (fun w : ComplexModel d ↦
          ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel d) ℂ (0 : Fin 1)
            (((θ ((chartAt (ComplexModel d) x).symm w)).comp
              (mfderiv 𝓘(ℂ, ComplexModel d) (complexModel d)
                (chartAt (ComplexModel d) x).symm w)).restrictScalars ℝ)) z = 0) ∧
      (∀ x v, θ x v = 0 ↔ complexTangentToReal d x v ∈ U x) ∧
      0 < ‖μ‖ ∧ ‖μ‖ < 1 ∧
      (∀ x, (θ (f x)).comp (mfderiv (complexModel d) (complexModel d) f x) =
        μ • θ x) := by
  obtain ⟨θ, hθhol, hθ⟩ := covering_projection_holomorphic_form p q D hq hD hpD hqD
    hinj O hO hxO s hs hps (fun x y z hx hy ↦ hmatch (s x z) (s y z)
      ((hps x z hx).trans (hps y z hy).symm))
  have hpull := descended_form_pullback_of_deck_sheets p q D hp hq hD hpD hqD
    hinj O hO hxO s hs hps
    (fun y ↦ hmatch y (s (p y) (p y)) (hps (p y) (p y) (hxO (p y))).symm) θ hθ
  have hDpsurj : ∀ y, Function.Surjective
      (mfderiv (complexModel d) (complexModel d) p y) := by
    intro y
    rw [← hDp y]
    exact (Dp y).surjective
  refine ⟨θ, hθhol, ?_, ?_, ?_, hμpos, hμlt, ?_⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := hpsurj x
    obtain ⟨v, hv⟩ := hqsurj y 1
    have h := DFunLike.congr_fun (hpull y) v
    rw [hx] at h
    simp only [ContinuousLinearMap.zero_comp, zero_apply, hv] at h
    exact zero_ne_one h
  · apply native_form_closed_of_local_potential θ
    intro x
    exact ⟨O x, q ∘ s x, hO x, hxO x, hq.comp_contMDiffOn (hs x), hθ x⟩
  · intro x v
    obtain ⟨y, rfl⟩ := hpsurj x
    let w := (Dp y).symm v
    have hw : mfderiv (complexModel d) (complexModel d) p y w = v := by
      rw [← hDp y]
      exact (Dp y).apply_symm_apply v
    have h := DFunLike.congr_fun (hpull y) w
    have hreal : Dp y w = v := (Dp y).apply_symm_apply v
    change θ (p y) (mfderiv (complexModel d) (complexModel d) p y w) =
      transverseScalarDifferential (d := d) q y w at h
    rw [hw] at h
    rw [h, hkernel y w, hreal]
  · exact covector_equivariance_descends f F p μ θ
      (fun y ↦ transverseScalarDifferential (d := d) q y) hpsurj hDpsurj hcomm
      (hp.mdifferentiable (by simp)) (hf.mdifferentiable (by simp))
      (hF.mdifferentiable (by simp)) hpull
      (fun y ↦ native_scalar_differential_equivariance q F μ y
        (hq.mdifferentiable (by simp)) ((hF y).mdifferentiableAt (by simp)) hqF)


end HolomorphicAnosov.Paper.Zhang
