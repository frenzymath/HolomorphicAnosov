import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.Tactic

open Set TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection










theorem compatible_difference_on_smooth_field
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D D' : Connection U) (hD : IsCompatible D) (hD' : IsCompatible D')
    (V : Opens X) (e : HolomorphicFrame U V)
    (Y Z : (x : X) → TangentSpace (complexModel d) x)
    (hY : IsSmoothTangentField V Y) (hZ : IsSmoothTangentField V Z)
    (hYU : ∀ x ∈ V, Y x ∈ U x) (x : X) (hx : x ∈ V)
    (hz : e.coefficient (fun y ↦ projection U y (Z y)) x ≠ 0) :
    D'.form V e x (complexTangentToReal d x (Y x)) =
      D.form V e x (complexTangentToReal d x (Y x)) := by
  have h := congrArg (e.coordinate x hx)
    (((hD'.2 V e Y Z hY hZ hYU x hx)).trans
      (hD.2 V e Y Z hY hZ hYU x hx).symm)
  simp only [map_smul, map_sub, covariantDerivative, LinearEquiv.apply_symm_apply,
    smul_eq_mul] at h
  rw [hD.1 V e x hx (Y x), hD'.1 V e x hx (Y x)] at h
  have he : e.coefficient (fun y ↦ projection U y (Z y)) x *
      (D'.form V e x (complexTangentToReal d x (Y x)) -
        D.form V e x (complexTangentToReal d x (Y x))) = 0 := by
    linear_combination (norm := ring_nf) h
    simp [Complex.I_sq]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hz)

end HolomorphicAnosov
