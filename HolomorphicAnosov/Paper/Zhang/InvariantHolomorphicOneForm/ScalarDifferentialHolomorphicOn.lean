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

/-- The scalar differential of a holomorphic potential on an open set is a holomorphic
cotangent-bundle section on that set. (Zhang, Lemma 4.2; Demailly, I §3.B–C) -/
theorem scalar_differential_holomorphic_on
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (t : X → ℂ) (O : Set X) (hO : IsOpen O)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t O) :
    ContMDiffOn (complexModel d)
      ((complexModel d).prod 𝓘(ℂ, ComplexModel d →L[ℂ] ℂ)) ∞
      (fun y ↦ (⟨y, transverseScalarDifferential t y⟩ : Bundle.TotalSpace
        (ComplexModel d →L[ℂ] ℂ)
        (fun z : X ↦ TangentSpace (complexModel d) z →L[ℂ] ℂ))) O := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hd := (ht x hx).contMDiffAt (hO.mem_nhds hx) |>.mfderiv_const (m := ∞) (by simp)
  convert hd using 1
  funext y
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    transverseScalarDifferential, Bundle.Trivial.fiberBundle_trivializationAt',
    tangentSpaceCastModel]
  ext v
  rfl


end HolomorphicAnosov.Paper.Zhang
