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

/-- The eigenform equation descends through a surjective covering whose differential is surjective,
provided the projection square commutes and the covector pulls back to `dq`. (Zhang, Lemma 4.2) -/
theorem covector_equivariance_descends
    {d : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
    (f : X → X) (F : Y → Y) (p : Y → X) (μ : ℂ)
    (θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (dq : ∀ y : Y, TangentSpace (complexModel d) y →L[ℂ] ℂ)
    (hpsurj : Function.Surjective p)
    (hDp : ∀ y, Function.Surjective (mfderiv (complexModel d) (complexModel d) p y))
    (hcomm : p ∘ F = f ∘ p)
    (hp : MDifferentiable (complexModel d) (complexModel d) p)
    (hf : MDifferentiable (complexModel d) (complexModel d) f)
    (hF : MDifferentiable (complexModel d) (complexModel d) F)
    (hpull : ∀ y, (θ (p y)).comp (mfderiv (complexModel d) (complexModel d) p y) = dq y)
    (heigen : ∀ y, (dq (F y)).comp (mfderiv (complexModel d) (complexModel d) F y) =
      μ • dq y) :
    ∀ x, (θ (f x)).comp (mfderiv (complexModel d) (complexModel d) f x) = μ • θ x := by
  intro x
  obtain ⟨y, rfl⟩ := hpsurj x
  have hchain := mfderiv_comp y (hp (F y)) (hF y)
  rw [hcomm, mfderiv_comp y (hf (p y)) (hp y)] at hchain
  have hpoint : p (F y) = f (p y) := congrFun hcomm y
  ext v
  obtain ⟨w, hw⟩ := hDp y v
  have he := DFunLike.congr_fun (heigen y) w
  rw [← hpull (F y), ← hpull y] at he
  have hcv := DFunLike.congr_fun hchain w
  change mfderiv (complexModel d) (complexModel d) f (p y)
    (mfderiv (complexModel d) (complexModel d) p y w) =
    mfderiv (complexModel d) (complexModel d) p (F y)
      (mfderiv (complexModel d) (complexModel d) F y w) at hcv
  simp only [ContinuousLinearMap.comp_apply, smul_apply] at he ⊢
  rw [← hw, hcv]
  convert! he using 1
  congr 2
  exact hpoint.symm


end HolomorphicAnosov.Paper.Zhang
