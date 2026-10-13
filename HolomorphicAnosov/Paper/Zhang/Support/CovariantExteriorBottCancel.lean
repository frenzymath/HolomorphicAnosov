import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

/-! Bott cancellation for the intrinsic covariant exterior expression. (Zhang, eq. (13), p. 7) -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

/-- The intrinsic covariant exterior expression of a Bott-compatible connection vanishes when its
first field is unstable. (Zhang, eq. (13), p. 7, eq. (2), p. 4) -/
theorem covariant_exterior_bott_cancel
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (nabla : QuotientLineConnection.Connection U)
    (hcompatible : QuotientLineConnection.IsCompatible nabla)
    (V : TopologicalSpace.Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
    (Y Z : (x : X) → TangentSpace (complexModel d) x)
    (hY : QuotientLineConnection.IsSmoothTangentField V Y)
    (hZ : QuotientLineConnection.IsSmoothTangentField V Z)
    (hYU : ∀ x ∈ V, Y x ∈ U x) (x : X) (hx : x ∈ V) :
    (1 / 2 : ℂ) •
        (QuotientLineConnection.covariantDerivative nabla e
            (fun y ↦ QuotientLineConnection.projection U y (Z y)) x hx
            (complexTangentToReal d x (Y x)) -
          Complex.I • QuotientLineConnection.covariantDerivative nabla e
            (fun y ↦ QuotientLineConnection.projection U y (Z y)) x hx
            (complexTangentToReal d x (Complex.I • Y x))) -
      (1 / 2 : ℂ) •
        (QuotientLineConnection.covariantDerivative nabla e
            (fun y ↦ QuotientLineConnection.projection U y (Y y)) x hx
            (complexTangentToReal d x (Z x)) -
          Complex.I • QuotientLineConnection.covariantDerivative nabla e
            (fun y ↦ QuotientLineConnection.projection U y (Y y)) x hx
            (complexTangentToReal d x (Complex.I • Z x))) -
      QuotientLineConnection.projection U x (QuotientLineConnection.bottBracket Y Z x) = 0 := by
  have hz (v : TangentSpace (realModel d) x) :
      QuotientLineConnection.covariantDerivative nabla e
        (fun y ↦ QuotientLineConnection.projection U y (Y y)) x hx v = 0 := by
    let s := fun y ↦ QuotientLineConnection.projection U y (Y y)
    have hs (y : X) (hy : y ∈ V) : s y = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (hYU y hy)
    have heq : e.coefficient s =ᶠ[nhds x] (fun _ ↦ (0 : ℂ)) := by
      filter_upwards [V.isOpen.mem_nhds hx] with y hy
      simp [QuotientLineConnection.HolomorphicFrame.coefficient, hs y hy]
    have hd : QuotientLineConnection.realDifferential (d := d) (e.coefficient s) x = 0 := by
      unfold QuotientLineConnection.realDifferential
      rw [heq.mfderiv_eq, mfderiv_const]
      simp
    change (e.coordinate x hx).symm
      (QuotientLineConnection.realDifferential (d := d) (e.coefficient s) x v +
        e.coefficient s x * nabla.form V e x v) = 0
    simp [hd, heq.eq_of_nhds]
  rw [hcompatible.2 V e Y Z hY hZ hYU x hx, hz, hz]
  simp

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
