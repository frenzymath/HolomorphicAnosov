import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

/-- A holomorphic frame with zero connection form is parallel on its domain. (Zhang, Lemma 2.4, p.
7, eq. (5), p. 4) -/
theorem parallel_of_zero_frame_form
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (nabla : QuotientLineConnection.Connection U)
    {V : Opens X} (e : QuotientLineConnection.HolomorphicFrame U V)
    (hzero : ∀ x ∈ V, nabla.form V e x = 0) :
    QuotientLineConnection.IsParallelOn nabla V e.sectionValue := by
  intro W e' x hxW hxV v
  have he : e.sectionValue x ≠ 0 := by
    intro hz
    have h := e.normalized x hxV
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hg : e'.coefficient e.sectionValue x ≠ 0 := by
    simpa only [QuotientLineConnection.HolomorphicFrame.coefficient, dite_eq_left hxW,
      ne_eq, LinearEquiv.map_eq_zero_iff] using he
  have h := congrArg (fun A : TangentSpace (realModel d) x →L[ℝ] ℂ ↦ A v)
    (nabla.gauge W V e' e x hxW hxV)
  rw [hzero x hxV] at h
  simp only [zero_apply, add_apply, smul_apply, smul_eq_mul] at h
  have hz : QuotientLineConnection.realDifferential (e'.coefficient e.sectionValue) x v +
      e'.coefficient e.sectionValue x * nabla.form W e' x v = 0 := by
    have hh := congrArg (fun z : ℂ ↦ e'.coefficient e.sectionValue x * z) h
    field_simp at hh
    linear_combination -hh
  simp only [QuotientLineConnection.covariantDerivative, hz, map_zero]

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
