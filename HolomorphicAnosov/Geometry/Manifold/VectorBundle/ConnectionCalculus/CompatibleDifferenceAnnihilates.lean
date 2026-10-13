import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.SmoothTangentFieldOfHolomorphic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The difference of two compatible quotient-line connections annihilates the holomorphic subbundle (Zhang, §2.1, Definition 2.1 and equation (6), pp.4–5; Demailly, V §2, p.255). -/
theorem compatible_difference_annihilates
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)} {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P)
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V))
    (D D' : QuotientLineConnection.Connection P)
    (hD : QuotientLineConnection.IsCompatible D)
    (hD' : QuotientLineConnection.IsCompatible D')
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hα : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (x : X), x ∈ V → D'.form V e x = D.form V e x + α x)
    (x : X) (v : TangentSpace (complexModel d) x) (hv : v ∈ P x) :
    α x (complexTangentToReal d x v) = 0 := by
  classical
  obtain ⟨O, u, hxO, hu, hspan⟩ := hP x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (by rwa [hspan x hxO])
  let Y : (y : X) → TangentSpace (complexModel d) y := fun y ↦ ∑ i, c i • u i y
  have hY : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun y ↦ (⟨y, Y y⟩ : TangentBundle (complexModel d) X)) O := by
    exact ContMDiffOn.sum_section (fun i _ ↦ (hu.2.1 i).const_smul_section (a := c i))
  have hYP : ∀ y ∈ O, Y y ∈ P y := by
    intro y hy
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    rw [← hspan y hy]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨V, hxV, ⟨e⟩⟩ := hcover x
  obtain ⟨B, T, hB, hxB, hBV, hT, hTe⟩ := e.holomorphic x hxV
  let W : Opens X := ⟨O ∩ B, hu.1.inter hB⟩
  have hWV : (W : Set X) ⊆ V := fun y hy ↦ hBV hy.2
  let eW : QuotientLineConnection.HolomorphicFrame P W := {
    sectionValue := e.sectionValue
    holomorphic := by
      intro y hy
      obtain ⟨A, Z, hA, hyA, hAV, hZ, hZe⟩ := e.holomorphic y (hWV hy)
      exact ⟨A ∩ W, Z, hA.inter W.isOpen, ⟨hyA, hy⟩, inter_subset_right,
        hZ.mono inter_subset_left, fun z hz ↦ hZe z hz.1⟩
    coordinate := fun y hy ↦ e.coordinate y (hWV hy)
    normalized := fun y hy ↦ e.normalized y (hWV hy) }
  have hxW : x ∈ W := ⟨hxO, hxB⟩
  have hYr : QuotientLineConnection.IsSmoothTangentField W Y := (smoothTangentField_of_holomorphic hu.1 hY).mono inter_subset_left
  have hTr : QuotientLineConnection.IsSmoothTangentField W T := (smoothTangentField_of_holomorphic hB hT).mono inter_subset_right
  have hb := (hD.2 W eW Y T hYr hTr (fun y hy ↦ hYP y hy.1) x hxW).trans
    (hD'.2 W eW Y T hYr hTr (fun y hy ↦ hYP y hy.1) x hxW).symm
  have hcoeff : eW.coefficient (fun y ↦ QuotientLineConnection.projection P y (T y)) x = 1 := by
    simp only [QuotientLineConnection.HolomorphicFrame.coefficient, dite_eq_left hxW]
    change e.coordinate x (hWV hxW) (QuotientLineConnection.projection P x (T x)) = 1
    rw [hTe x hxB, e.normalized]
  apply_fun eW.coordinate x hxW at hb
  simp only [map_smul, map_sub, QuotientLineConnection.covariantDerivative,
    LinearEquiv.apply_symm_apply, smul_eq_mul, hcoeff, one_mul,
    hD.1 W eW x hxW (Y x), hD'.1 W eW x hxW (Y x)] at hb
  have heq : D.form W eW x (complexTangentToReal d x (Y x)) =
      D'.form W eW x (complexTangentToReal d x (Y x)) := by
    linear_combination (norm := (ring_nf; simp [Complex.I_sq])) hb
  have hyx : Y x = v := hc
  rw [hyx, hα W eW x hxW, add_apply] at heq
  exact (add_eq_left.mp heq.symm)

end HolomorphicAnosov.ConnectionCalculus
