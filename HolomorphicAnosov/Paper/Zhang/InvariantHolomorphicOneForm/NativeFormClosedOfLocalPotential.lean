import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.LocallyExactCovectorClosedAt
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeScalarDifferentialPullback

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang

attribute [local instance] complex_isManifold_real
universe u

/-- A one-form locally equal to the differential of a holomorphic potential is closed in every real
chart. (Demailly, I §3.C, (3.17); Zhang, Lemma 4.2) -/
theorem native_form_closed_of_local_potential
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (θ : ∀ y : X, TangentSpace (complexModel d) y →L[ℂ] ℂ)
    (hlocal : ∀ y, ∃ (O : Set X) (t : X → ℂ), IsOpen O ∧ y ∈ O ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t O ∧
      ∀ w ∈ O, θ w = transverseScalarDifferential (d := d) t w) :
    ∀ x : X, ∀ z ∈ (chartAt (ComplexModel d) x).target,
      extDeriv (fun w : ComplexModel d ↦
        ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel d) ℂ (0 : Fin 1)
          (((θ ((chartAt (ComplexModel d) x).symm w)).comp
            (mfderiv 𝓘(ℂ, ComplexModel d) (complexModel d)
              (chartAt (ComplexModel d) x).symm w)).restrictScalars ℝ)) z = 0 := by
  intro x z hz
  let c := chartAt (ComplexModel d) x
  obtain ⟨O, t, hO, hyO, ht, hθ⟩ := hlocal (c.symm z)
  have hc : ContMDiffAt 𝓘(ℂ, ComplexModel d) (complexModel d) ∞ c.symm z :=
    (contMDiffOn_chart_symm (I := complexModel d) (x := x) z hz).contMDiffAt
      (c.open_target.mem_nhds hz)
  have hg : ContDiffAt ℂ ∞ (t ∘ c.symm) z :=
    (((ht (c.symm z) hyO).contMDiffAt (hO.mem_nhds hyO)).comp z hc).contDiffAt
  apply locally_exact_covector_closed_at (t ∘ c.symm) _ z (hg.restrict_scalars ℝ)
  have hpre : ∀ᶠ w in 𝓝 z, c.symm w ∈ O := hc.continuousAt (hO.mem_nhds hyO)
  filter_upwards [c.open_target.mem_nhds hz, hpre] with w hw hwO
  have hcw : ContMDiffAt 𝓘(ℂ, ComplexModel d) (complexModel d) ∞ c.symm w :=
    (contMDiffOn_chart_symm (I := complexModel d) (x := x) w hw).contMDiffAt
      (c.open_target.mem_nhds hw)
  have htw := (ht _ hwO).contMDiffAt (hO.mem_nhds hwO)
  have hgw : ContDiffAt ℂ ∞ (t ∘ c.symm) w := (htw.comp w hcw).contDiffAt
  rw [hθ _ hwO]
  rw [native_scalar_differential_pullback t c.symm w
    (htw.mdifferentiableAt (by simp)) (hcw.mdifferentiableAt (by simp))]
  exact (hgw.differentiableAt (by simp) |>.fderiv_restrictScalars ℝ).symm


end HolomorphicAnosov.Paper.Zhang
