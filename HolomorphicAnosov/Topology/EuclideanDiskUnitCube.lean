import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UnitInterval

/-!
# The Euclidean closed disk and the unit cube

Source: Bredon, *Topology and Geometry* (1993), Chapter I Section 16,
Propositions 16.2–16.3 and Theorem 16.4, pp.56–57. The radial extension of the
boundary-normalization homeomorphism, specialized to the centered cube, gives the
Euclidean/sup-norm comparison. Coordinate affine rescaling then gives the unit cube.
DAG node: `topo.euclidean_closed_disk_unit_cube_homeomorphism`.
-/

open Metric Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- The closed Euclidean unit disk is homeomorphic to the unit cube by radial comparison
followed by coordinate affine rescaling, in every dimension including zero.

Source: Bredon, *Topology and Geometry* (1993), Chapter I Section 16,
Propositions 16.2–16.3 and Theorem 16.4, pp.56–57. Hatcher, *Algebraic Topology*,
Standard Notations p.xii and the proof of Proposition 2B.1(a), p.169, give the disk/cube
conventions and consumer but omit the proof.

Natural-language proof:

For `k = 0`, both spaces are singletons, so their unique maps form a homeomorphism.
The coordinate formula has no coordinates to check. No maximum over an empty index
set or normalization of a nonzero vector is needed.

For `k > 0`, write `N₂(x)` for the Euclidean norm and `N∞(x)` for the maximum of the
absolute coordinates. Both are continuous, and `N∞ ≤ N₂ ≤ √k N∞`, by comparison of
coordinate squares. The centered cube `C = [-1,1]^k` is closed and convex, contains
the open Euclidean unit ball, and lies in the closed Euclidean ball of radius `√k`.
Finite-dimensional properness and closed-subset compactness make it compact. Its
boundary is precisely `N∞ = 1`: strict coordinate inequalities give interior
neighborhoods, and a coordinate equal to either endpoint admits outward perturbations.

Every ray of Euclidean unit direction `u` meets the boundary uniquely at `u/N∞(u)`.
The denominator is positive since `u ≠ 0`, and positive homogeneity proves both
existence and uniqueness. Thus Bredon's boundary normalization `y ↦ y/N₂(y)` is a
continuous bijection from the compact cube boundary to the Hausdorff Euclidean sphere,
with inverse `u ↦ u/N∞(u)`. The compact-to-Hausdorff criterion makes it a homeomorphism.

Extend this boundary homeomorphism radially as in Theorem 16.4: send zero to zero,
and send a nonzero disk vector `x` to `N₂(x) f⁻¹(x/N₂(x))`. Substituting the boundary
inverse yields `H(x) = (N₂(x)/N∞(x)) x`. It sends the radial segment `r u` to
`r f⁻¹(u)`. For nonzero `y ∈ C`, the vector `(N∞(y)/N₂(y)) y` lies in the disk and
maps to `y`. The radius is recovered as `N∞(H(x))` and the direction by boundary
normalization, giving injectivity. Only zero maps to zero.

Off zero, continuity follows by composition of the norm, normalization, boundary
inverse and scalar multiplication. At zero, `N₂(H(x)) ≤ √k N₂(x)` proves continuity.
The disk is compact and the cube Hausdorff, so this continuous bijection has continuous
inverse, given by zero at zero and `(N∞(y)/N₂(y)) y` elsewhere.

Finally rescale coordinates by `A(y)(i) = (y(i)+1)/2`, with inverse `2z(i)-1`.
Coordinate inequalities make both maps well-defined; affine identities prove their
inverse laws, and coordinatewise continuity proves continuity in the product and
subtype topologies. Compose `A` with `H`. Boundary coordinates reach the endpoints
zero or one; no boundary points are removed. For `k = 1` the two-point boundary is
included. In the displayed formula, real division sends `0/0` to zero, so at the
origin the formula records the midpoint of the cube without a separate branch.

The disk norm is the Euclidean `L²` norm. The norm of the plain coordinate function
in the denominator is the finite-product maximum norm, used only in the radial map.
-/
theorem euclidean_closed_disk_unit_cube_homeomorphism (k : ℕ) :
    ∃ e : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) ≃ₜ (Fin k → unitInterval),
      ∀ (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)) (i : Fin k),
        (e x i : ℝ) = (‖x.val‖ / ‖fun j : Fin k ↦ x.val j‖ * x.val i + 1) / 2 := by
  let E := EuclideanSpace ℝ (Fin k)
  let F := Fin k → ℝ
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k ↦ ℝ)
  let S : Set E := closedBall 0 1
  let T : Set E := L ⁻¹' closedBall 0 1
  have hSc : Convex ℝ S := convex_closedBall _ _
  have hS₀ : S ∈ 𝓝 0 := closedBall_mem_nhds _ zero_lt_one
  have hSb : Bornology.IsVonNBounded ℝ S := NormedSpace.isVonNBounded_closedBall _ _ _
  have hTc : Convex ℝ T := (convex_closedBall (0 : F) 1).linear_preimage L.toLinearMap
  have hT₀ : T ∈ 𝓝 0 := L.continuous.continuousAt.preimage_mem_nhds
    (by simpa using closedBall_mem_nhds (0 : F) zero_lt_one)
  have hTb : Bornology.IsVonNBounded ℝ T := by
    have h := (NormedSpace.isVonNBounded_closedBall ℝ F 1).image L.symm.toContinuousLinearMap
    apply h.subset
    intro x hx
    exact ⟨L x, hx, L.symm_apply_apply x⟩
  have hSg (x : E) : gauge S x = ‖x‖ := by
    rw [show S = closedBall (0 : E) 1 by rfl, gauge_closedBall zero_le_one, div_one]
  have hTg (x : E) : gauge T x = ‖L x‖ := by
    have h : gauge T x = gauge (closedBall (0 : F) 1) (L x) := by
      simp only [gauge_def']
      congr 1
    rw [h, gauge_closedBall zero_le_one, div_one]
  let H := gaugeRescaleHomeomorph S T hSc hS₀ hSb hTc hT₀ hTb
  have hH (x : E) : H x = (‖x‖ / ‖L x‖) • x := by
    change gaugeRescale S T x = _
    rw [gaugeRescale_def, hSg, hTg]
  have hmem (x : E) : x ∈ S ↔ H x ∈ T := by
    have hg := gauge_gaugeRescale S (absorbent_nhds_zero hT₀) hTb x
    change gauge T (H x) = gauge S x at hg
    rw [hTg, hSg] at hg
    simp only [S, T, mem_preimage, mem_closedBall, dist_zero_right]
    rw [hg]
  let Hs : S ≃ₜ T := H.subtype hmem
  let Lt : T ≃ₜ closedBall (0 : F) 1 := L.toHomeomorph.subtype (fun _ ↦ Iff.rfl)
  let C : closedBall (0 : F) 1 ≃ₜ (Fin k → unitInterval) :=
    { toFun := fun y i ↦ ⟨(y.val i + 1) / 2, by
        have hy0 : ‖y.val‖ ≤ 1 := by
          have hy' := y.property
          change dist y.val (0 : F) ≤ 1 at hy'
          rw [dist_zero_right] at hy'
          exact hy'
        have hy : ‖y.val i‖ ≤ 1 := (norm_le_pi_norm y.val i).trans hy0
        rw [Real.norm_eq_abs, abs_le] at hy
        constructor <;> linarith⟩
      invFun := fun z ↦ ⟨fun i ↦ 2 * (z i : ℝ) - 1, by
        simp only [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one,
          Real.norm_eq_abs, abs_le]
        intro i
        have hz := (z i).property
        constructor <;> linarith [hz.1, hz.2]⟩
      left_inv := by intro y; ext i; dsimp; ring
      right_inv := by intro z; ext i; dsimp; ring
      continuous_toFun := by
        apply continuous_pi
        intro i
        apply Continuous.subtype_mk
        exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const }
  refine ⟨(Hs.trans Lt).trans C, ?_⟩
  intro x i
  change ((L (H x.val)) i + 1) / 2 = _
  rw [hH, map_smul]
  rfl

end HolomorphicAnosov

