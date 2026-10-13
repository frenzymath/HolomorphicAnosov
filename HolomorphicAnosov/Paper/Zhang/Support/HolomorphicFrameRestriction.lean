import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

/-! Restriction of holomorphic quotient frames and their connection forms. (Zhang, eqs. (3), (5), p.
4, Lemma 2.4, p. 7; Demailly, V §11, p. 267) -/
noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

/-- A holomorphic quotient frame restricts to a smaller open set with the same section and
connection form there. (Zhang, eqs. (3), (5), p. 4, Lemma 2.4, p. 7; Demailly, V §11, p. 267) -/
theorem holomorphic_frame_restriction
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (nabla : QuotientLineConnection.Connection U)
    {V W : Opens X} (e : QuotientLineConnection.HolomorphicFrame U V)
    (hWV : (W : Set X) ⊆ V) :
    ∃ eW : QuotientLineConnection.HolomorphicFrame U W,
      eW.sectionValue = e.sectionValue ∧
      ∀ x ∈ W, nabla.form W eW x = nabla.form V e x := by
  let eW : QuotientLineConnection.HolomorphicFrame U W := {
    sectionValue := e.sectionValue
    holomorphic := by
      intro x hx
      obtain ⟨O, v, hopen, hxO, hOV, hv, heq⟩ := e.holomorphic x (hWV hx)
      exact ⟨O ∩ W, v, hopen.inter W.isOpen, ⟨hxO, hx⟩,
        inter_subset_right, hv.mono inter_subset_left, fun y hy ↦ heq y hy.1⟩
    coordinate := fun x hx ↦ e.coordinate x (hWV hx)
    normalized := fun x hx ↦ e.normalized x (hWV hx) }
  refine ⟨eW, rfl, ?_⟩
  intro x hx
  have heq : e.coefficient eW.sectionValue =ᶠ[nhds x] (fun _ ↦ (1 : ℂ)) := by
    filter_upwards [W.isOpen.mem_nhds hx] with y hy
    unfold QuotientLineConnection.HolomorphicFrame.coefficient
    have hyv : y ∈ V := hWV hy
    rw [dite_eq_left hyv]
    exact e.normalized y (hWV hy)
  have hd : QuotientLineConnection.realDifferential (d := d) (e.coefficient eW.sectionValue) x = 0 := by
    unfold QuotientLineConnection.realDifferential
    rw [heq.mfderiv_eq, mfderiv_const]
    simp
  rw [nabla.gauge V W e eW x (hWV hx) hx, hd]
  ext v
  simp

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
