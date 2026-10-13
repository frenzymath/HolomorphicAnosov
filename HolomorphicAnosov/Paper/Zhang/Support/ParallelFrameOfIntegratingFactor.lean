import HolomorphicAnosov.Paper.Zhang.Support.HolomorphicSectionSmul
import HolomorphicAnosov.Paper.Zhang.Support.ParallelOfZeroFrameForm

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

/-- A nowhere-zero holomorphic integrating factor satisfying `dg = -gA` rescales a holomorphic
quotient frame to a parallel holomorphic frame. (Zhang, Lemma 2.4, p. 7, eq. (5), p. 4) -/
theorem exists_parallel_frame_of_integrating_factor
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (nabla : QuotientLineConnection.Connection U)
    {V : Opens X} (e : QuotientLineConnection.HolomorphicFrame U V)
    (g : X → ℂ) (hg : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ g V)
    (hgzero : ∀ x ∈ V, g x ≠ 0)
    (hdg : ∀ x ∈ V, QuotientLineConnection.realDifferential (d := d) g x =
      -(g x) • nabla.form V e x) :
    ∃ e' : QuotientLineConnection.HolomorphicFrame U V,
      e'.sectionValue = (fun x ↦ g x • e.sectionValue x) ∧
      (∀ x ∈ V, nabla.form V e' x = 0) ∧
      QuotientLineConnection.IsParallelOn nabla V e'.sectionValue := by
  classical
  let e' : QuotientLineConnection.HolomorphicFrame U V := {
    sectionValue := fun x ↦ g x • e.sectionValue x
    holomorphic := holomorphic_section_smul e.sectionValue e.holomorphic g hg
    coordinate := fun x hx ↦ (e.coordinate x hx).trans
      (LinearEquiv.smulOfNeZero ℂ ℂ (g x)⁻¹ (inv_ne_zero (hgzero x hx)))
    normalized := by
      intro x hx
      simp [LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit, e.normalized x hx,
        hgzero x hx] }
  have hzero : ∀ x ∈ V, nabla.form V e' x = 0 := by
    intro x hx
    have hc : e.coefficient e'.sectionValue =ᶠ[nhds x] g := by
      filter_upwards [V.isOpen.mem_nhds hx] with y hy
      unfold QuotientLineConnection.HolomorphicFrame.coefficient
      rw [dite_eq_left (show y ∈ V from hy)]
      change e.coordinate y _ (g y • e.sectionValue y) = g y
      rw [map_smul, e.normalized y hy, smul_eq_mul, mul_one]
    have hd : QuotientLineConnection.realDifferential (e.coefficient e'.sectionValue) x =
        QuotientLineConnection.realDifferential (d := d) g x := by
      unfold QuotientLineConnection.realDifferential
      rw [hc.eq_of_nhds, hc.mfderiv_eq]
      rfl
    rw [nabla.gauge V V e e' x hx hx, hc.eq_of_nhds, hd, hdg x hx]
    ext v
    simp [smul_smul, hgzero x hx]
  exact ⟨e', rfl, hzero, parallel_of_zero_frame_form nabla e' hzero⟩

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
