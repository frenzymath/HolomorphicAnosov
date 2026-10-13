import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Hom

/-! Continuity of cotangent-section evaluation on tangent sections. (Zhang, Lemma 4.3, p. 15) -/

namespace HolomorphicAnosov

universe u

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle
attribute [local instance] complex_isManifold_real

/-- A continuous cotangent section evaluates continuously at a point on a tangent section
that is continuous there. (Zhang, Lemma 4.3, p. 15) -/
theorem oneForm_evaluation_continuousAt
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ : Continuous (fun x ↦
      (⟨x, θ x⟩ : Bundle.TotalSpace (ComplexModel d →L[ℂ] ℂ)
        (fun y : X ↦ TangentSpace (complexModel d) y →L[ℂ] ℂ))))
    (x : X) (v : ∀ y : X, TangentSpace (complexModel d) y)
    (hv : ContinuousAt (fun y ↦ (⟨y, v y⟩ : TangentBundle (complexModel d) X)) x) :
    ContinuousAt (fun y ↦ θ y (v y)) x := by
  have heval := hθ.continuousAt.clm_bundle_apply
    (F₂ := ℂ) (E₂ := fun _ : X ↦ ℂ) (b := id) (ϕ := θ) hv
  have hscalar := (FiberBundle.continuousAt_totalSpace ℂ _).mp heval |>.2
  change ContinuousAt (fun y ↦ θ y (v y)) x at hscalar
  exact hscalar



end HolomorphicAnosov
