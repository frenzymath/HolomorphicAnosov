import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.FrameDifferenceIndependent

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov
namespace ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- Two quotient-line connections have a unique scalar real one-form whose value is their difference
in every holomorphic frame. (Zhang, §2.1, (3)) -/
theorem scalar_difference_exists_unique
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V))
    (D D' : QuotientLineConnection.Connection P) :
    ∃! α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ,
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (x : X), x ∈ V → D'.form V e x = D.form V e x + α x := by
  classical
  choose V hx he using hcover
  let e : ∀ x : X, QuotientLineConnection.HolomorphicFrame P (V x) :=
    fun x ↦ (he x).some
  let α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ :=
    fun x ↦ D'.form (V x) (e x) x - D.form (V x) (e x) x
  refine ⟨α, ?_, ?_⟩
  · intro W e' x hx'
    have hh := frame_difference_independent D D' W (V x) e' (e x) x hx' (hx x)
    change D'.form W e' x - D.form W e' x = α x at hh
    rw [← hh]
    abel
  · intro β hβ
    funext x
    have hb := hβ (V x) (e x) x (hx x)
    change β x = D'.form (V x) (e x) x - D.form (V x) (e x) x
    rw [hb]
    abel



end ConnectionCalculus
end HolomorphicAnosov
