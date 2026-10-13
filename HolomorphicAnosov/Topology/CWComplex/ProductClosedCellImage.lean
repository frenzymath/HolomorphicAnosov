import HolomorphicAnosov.Topology.CWComplex.NativeDiskIntervalHomeomorph
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.UnitInterval

open Set _root_.Topology
namespace HolomorphicAnosov.Topology

/-- Closed-cell images of endpoint and prism characteristic maps have the
source product forms required by the interval-product construction.

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Theorem 2.2.2(ii),
p.58. The endpoint and prism closed cells are products of the original closed
cell with the interval zero-cell or one-cell. This lemma isolates the native
maximum-norm coordinate calculation from the construction of the product CW
structure.

Proof: use the displayed endpoint/prism formulas on the closed native disk.
For a forward image, the head coordinates remain in the original closed disk.
Conversely, for a point in an original closed-cell product, append the affine
last coordinate `2*t-1` and use the native disk–interval homeomorphism to obtain
a closed-disk preimage. The endpoint case is the same argument with a fixed
second coordinate. No regularity, injectivity, finiteness, or product CW
instance is assumed. -/
theorem endpoint_closed_image
    {X : Type*} [TopologicalSpace X] [CWComplex (univ : Set X)]
    (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d)
    (t : unitInterval)
    (e : PartialEquiv (Fin d → ℝ) (X × unitInterval))
    (hformula : ∀ z ∈ Metric.closedBall (0 : Fin d → ℝ) 1,
      e z = (RelCWComplex.map (C := (univ : Set X)) d i z, t)) :
    e '' Metric.closedBall (0 : Fin d → ℝ) 1 =
      (CWComplex.closedCell (C := (univ : Set X)) d i).prod {t} := by
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hm : RelCWComplex.map (C := (univ : Set X)) d i z ∈
        CWComplex.closedCell (C := (univ : Set X)) d i := ⟨z, hz, rfl⟩
    have hp : e z ∈ (CWComplex.closedCell (C := (univ : Set X)) d i).prod {t} := by
      rw [hformula z hz]
      exact ⟨hm, mem_singleton _⟩
    exact hzy ▸ hp
  · intro hy
    have hx : y.1 ∈ CWComplex.closedCell (C := (univ : Set X)) d i := hy.1
    have ht : y.2 ∈ ({t} : Set unitInterval) := hy.2
    have hex : ∃ z, z ∈ Metric.closedBall (0 : Fin d → ℝ) 1 ∧
        RelCWComplex.map (C := (univ : Set X)) d i z = y.1 := hx
    obtain ⟨z, hz, hzx⟩ := hex
    refine ⟨z, hz, ?_⟩
    rw [hformula z hz]
    apply Prod.ext
    · exact hzx
    · exact (mem_singleton_iff.mp ht).symm

theorem prism_closed_image
    {X : Type*} [TopologicalSpace X] [CWComplex (univ : Set X)]
    (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d)
    (e : PartialEquiv (Fin (d + 1) → ℝ) (X × unitInterval))
    (hformula : ∀ w ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) 1,
      (e w).1 = RelCWComplex.map (C := (univ : Set X)) d i
          (fun j ↦ w j.castSucc) ∧
      ((e w).2 : ℝ) = (w (Fin.last d) + 1) / 2) :
    e '' Metric.closedBall (0 : Fin (d + 1) → ℝ) 1 =
      (CWComplex.closedCell (C := (univ : Set X)) d i).prod univ := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hformula w hw with ⟨hfirst, htime⟩
    have hhead : (fun j ↦ w j.castSucc) ∈ Metric.closedBall (0 : Fin d → ℝ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mpr
      intro j
      exact (norm_le_pi_norm w j.castSucc).trans (by simpa [Metric.mem_closedBall, dist_zero_right] using hw)
    exact ⟨⟨(fun j ↦ w j.castSucc), hhead, hfirst.symm⟩, mem_univ _⟩
  · intro hy
    have hx : y.1 ∈ CWComplex.closedCell (C := (univ : Set X)) d i := hy.1
    have ht : y.2 ∈ (univ : Set unitInterval) := hy.2
    have hex : ∃ z, z ∈ Metric.closedBall (0 : Fin d → ℝ) 1 ∧
        RelCWComplex.map (C := (univ : Set X)) d i z = y.1 := hx
    obtain ⟨z, hz, hzx⟩ := hex
    obtain ⟨q, hhead, htime, hsymm⟩ := native_disk_interval_homeomorph d
    let w := q.symm (⟨z, hz⟩, y.2)
    have hw : (w : Fin (d + 1) → ℝ) ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) 1 := w.property
    refine ⟨w, hw, ?_⟩
    rcases hformula w hw with ⟨hfirst, hlast⟩
    have hsplit : (fun j ↦ w.1 j.castSucc) = z := by
      funext j
      rw [← hhead w j]
      simp only [w, q.apply_symm_apply]
    apply Prod.ext
    · exact hfirst.trans (by rw [hsplit]; exact hzx)
    · apply Subtype.ext
      rw [hlast]
      have hs := congrFun (hsymm ⟨z, hz⟩ y.2) (Fin.last d)
      simp only [Fin.snoc_last] at hs
      rw [hs]
      ring

end HolomorphicAnosov.Topology

