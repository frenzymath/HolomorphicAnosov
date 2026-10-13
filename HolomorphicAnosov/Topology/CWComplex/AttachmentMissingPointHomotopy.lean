import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import HolomorphicAnosov.Topology.CWComplex.RelativeSmoothApproximationOffClosed
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Order.ProjIcc

namespace HolomorphicAnosov.HatcherAttachedCell

open Set Metric
open scoped Topology _root_.Topology ContDiff Manifold

/-- The local missed-point construction in Bredon, Topology and Geometry,
IV.11.2, p.207, using II.11.7, pp.96–97.

Extend the cube map to Euclidean space by coordinatewise clamping. On the
open inverse image of the attached cell take its coordinate map. Smooth it
relative to the complement of the inverse image of the open unit chart ball.
The closed unit chart ball is compact and closed in the target, so this
relative homotopy is stationary on a neighborhood of every point outside
the open-cell inverse image. Extending by the original map is therefore
jointly continuous. The smooth image on the modified region has dimension
less than k; choose a missed point in the unit chart ball. The stationary
part also avoids this point. Finally restrict the homotopy to the cube.
The open-cell smoothing and locally stationary extension follow Bredon's
written proof. His statement assumes a disk boundary mapped into the old
space. The arbitrary-cube formulation here additionally uses coordinate
clamping, so this node retains its agent provenance for that adaptation. -/
theorem attachment_missing_point_homotopy
    {Z : Type*} [TopologicalSpace Z] [T2Space Z] {n k : ℕ}
    (cell : Attachment Z k) (f : C(Cube n, Z)) (hnk : n < k) :
    ∃ (g : C(Cube n, Z)) (p : Z), p ∉ cell.oldSpace ∧
      (∀ x, g x ≠ p) ∧
      Nonempty (ContinuousMap.HomotopyRel f g (f ⁻¹' cell.oldSpace)) := by
  classical
  let D := Fin n → ℝ
  let F := EuclideanSpace ℝ (Fin k)
  let e : C(F, Z) := ⟨fun y ↦ (cell.coordinates y).val,
    continuous_subtype_val.comp cell.coordinates.continuous⟩
  have heinj : Function.Injective e := Subtype.val_injective.comp cell.coordinates.injective
  let ρ : C(D, Cube n) := ⟨fun x i ↦ Set.projIcc 0 1 (by norm_num) (x i),
    continuous_pi fun i ↦ (continuous_projIcc (h := by norm_num)).comp (continuous_apply i)⟩
  let ext : C(D, Z) := f.comp ρ
  have hext : ∀ x : Cube n, ext (cubeCoordinates x) = f x := by
    intro x
    have hρ : ρ (cubeCoordinates x) = x := by
      funext i
      exact Set.projIcc_of_mem (by norm_num) (x i).property
    exact congrArg f hρ
  let U : TopologicalSpace.Opens D :=
    ⟨ext ⁻¹' cell.oldSpaceᶜ, cell.cell_open.preimage ext.continuous⟩
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let q : C(U, F) := ⟨fun x ↦ cell.coordinates.symm ⟨ext x, x.property⟩,
    cell.coordinates.symm.continuous.comp
      ((ext.continuous.comp continuous_subtype_val).subtype_mk fun x ↦ x.property)⟩
  have heq : ∀ x : U, e (q x) = ext x := by
    intro x
    exact congrArg Subtype.val (cell.coordinates.apply_symm_apply ⟨ext x, x.property⟩)
  let B : Set U := (q ⁻¹' Metric.ball 0 1)ᶜ
  have hB : IsClosed B := (Metric.isOpen_ball.preimage q.continuous).isClosed_compl
  obtain ⟨g, hg, H, _⟩ := relative_smooth_approximation_off_closed
    (E := D) B hB q 1 (by norm_num)
  let K : Set Z := e '' Metric.closedBall 0 1
  have hK : IsClosed K := ((isCompact_closedBall (0 : F) 1).image e.continuous).isClosed
  let V : Set D := ext ⁻¹' (e '' Metric.ball 0 1)
  have hVU : V ⊆ U := by
    rintro x ⟨y, _, hy⟩
    change ext x ∉ cell.oldSpace
    rw [← hy]
    exact (cell.coordinates y).property
  have hVB : ∀ x (hx : x ∈ V), (⟨x, hVU hx⟩ : U) ∉ B := by
    intro x hx
    obtain ⟨y, hy, hexy⟩ := hx
    have hq : q ⟨x, hVU ⟨y, hy, hexy⟩⟩ = y := heinj ((heq _).trans hexy.symm)
    simpa [B, hq] using hy
  let s : D → F := fun x ↦ if hx : x ∈ U then g ⟨x, hx⟩ else 0
  have hsU : ∀ x : U, s x = g x := by
    intro x
    simp [s, x.property]
  have hdiff : DifferentiableOn ℝ s V := by
    intro x hx
    have hsmooth : ContMDiffAt 𝓘(ℝ, D) 𝓘(ℝ, F) ∞ g (⟨x, hVU hx⟩ : U) :=
      (hg _ (hVB x hx)).contMDiffAt (hB.isOpen_compl.mem_nhds (hVB x hx))
    have hequal : (fun y : U ↦ s y) = g := funext hsU
    rw [← hequal] at hsmooth
    have hfull := contMDiffAt_subtype_iff.mp hsmooth
    exact (hfull.contDiffAt.differentiableAt (by simp)).differentiableWithinAt
  have hdim : dimH V < Module.finrank ℝ F := by
    calc
      dimH V ≤ dimH (Set.univ : Set D) := dimH_mono (subset_univ _)
      _ = Module.finrank ℝ D := Real.dimH_univ_eq_finrank D
      _ < Module.finrank ℝ F := by exact_mod_cast (show Module.finrank ℝ D <
        Module.finrank ℝ F by simpa [D, F] using hnk)
  obtain ⟨p, hpavoid, hp⟩ := (hdiff.dense_compl_image_of_dimH_lt_finrank hdim).exists_mem_open
    (Metric.isOpen_ball (x := (0 : F)) (ε := 1)) ⟨0, by simp⟩
  let h : unitInterval × D → Z := fun z ↦
    if hz : z.2 ∈ U then e (H (z.1, ⟨z.2, hz⟩)) else ext z.2
  have hU : ∀ t (x : U), h (t, x) = e (H (t, x)) := by
    intro t x
    simp [h, x.property]
  have hfix : ∀ t x, ext x ∉ K → h (t, x) = ext x := by
    intro t x hx
    by_cases hxU : x ∈ U
    · rw [hU t ⟨x, hxU⟩]
      have hxB : (⟨x, hxU⟩ : U) ∈ B := by
        intro hqball
        apply hx
        exact ⟨q ⟨x, hxU⟩, Metric.ball_subset_closedBall hqball, heq _⟩
      rw [H.eq_fst t hxB, heq]
    · simp [h, hxU]
  have hcontU : ContinuousOn h (Prod.snd ⁻¹' (U : Set D)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hf : (fun z : Prod.snd ⁻¹' (U : Set D) ↦ h z) =
        (fun z ↦ e (H (z.val.1, (⟨z.val.2, z.property⟩ : U)))) := by
      funext z
      simpa only [Prod.eta] using hU z.val.1 (⟨z.val.2, z.property⟩ : U)
    change Continuous (fun z : Prod.snd ⁻¹' (U : Set D) ↦ h z.val)
    rw [hf]
    exact e.continuous.comp (H.continuous.comp (by fun_prop))
  have hcont : Continuous h := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hzU : z.2 ∈ U
    · exact hcontU.continuousAt ((U.isOpen.preimage continuous_snd).mem_nhds hzU)
    · have hzK : ext z.2 ∉ K := by
        rintro ⟨y, _, hy⟩
        apply hzU
        change ext z.2 ∉ cell.oldSpace
        rw [← hy]
        exact (cell.coordinates y).property
      apply (ext.continuous.comp continuous_snd).continuousAt.congr_of_eventuallyEq
      filter_upwards [((hK.preimage ext.continuous).isOpen_compl.preimage
        continuous_snd).mem_nhds hzK] with w hw
      exact hfix w.1 w.2 hw
  have hzero : ∀ x, h (0, x) = ext x := by
    intro x
    by_cases hxU : x ∈ U
    · rw [hU 0 ⟨x, hxU⟩, H.apply_zero, heq]
    · simp [h, hxU]
  have hav : ∀ x, h (1, x) ≠ e p := by
    intro x hx
    by_cases hxU : x ∈ U
    · rw [hU 1 ⟨x, hxU⟩, H.apply_one] at hx
      have hgxp : g ⟨x, hxU⟩ = p := heinj hx
      by_cases hxV : x ∈ V
      · apply hpavoid
        exact ⟨x, hxV, (hsU ⟨x, hxU⟩).trans hgxp⟩
      · have hxB : (⟨x, hxU⟩ : U) ∈ B := by
          intro hqball
          exact hxV ⟨q ⟨x, hxU⟩, hqball, heq _⟩
        have hgp : q ⟨x, hxU⟩ = p := (H.fst_eq_snd hxB).trans hgxp
        apply hxB
        change q ⟨x, hxU⟩ ∈ Metric.ball 0 1
        rwa [hgp]
    · have hepx : ext x = e p := by simpa [h, hxU] using hx
      apply hxU
      change ext x ∉ cell.oldSpace
      rw [hepx]
      exact (cell.coordinates p).property
  let hc : C(unitInterval × Cube n, Z) := ⟨fun z ↦ h (z.1, cubeCoordinates z.2),
    hcont.comp (by unfold cubeCoordinates; fun_prop)⟩
  let result : C(Cube n, Z) := ⟨fun x ↦ hc (1, x),
    hc.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨result, e p, (cell.coordinates p).property, fun x ↦ hav _, ⟨?_⟩⟩
  exact {
    toContinuousMap := hc
    map_zero_left := fun x ↦ (hzero _).trans (hext x)
    map_one_left := fun _ ↦ rfl
    prop' := fun t x hx ↦ by
      have hxU : cubeCoordinates x ∉ U := by
        change ¬ ext (cubeCoordinates x) ∉ cell.oldSpace
        simpa [hext] using hx
      change h (t, cubeCoordinates x) = f x
      simp [h, hxU, hext] }

end HolomorphicAnosov.HatcherAttachedCell
