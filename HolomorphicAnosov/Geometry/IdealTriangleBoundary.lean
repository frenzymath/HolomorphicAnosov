import HolomorphicAnosov.Geometry.IdealTriangleReflectionData
import Mathlib.Tactic.FunProp
import Mathlib.Order.Filter.Finite

/-! This file describes the boundary decomposition of the finite ideal-triangle carrier into its interior and side loci. (Epstein–Petronio, Def. 2.1) -/

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.IdealDiskTriangle

lemma continuous_sideEquation (p q : ℂ) : Continuous (sideEquation p q) := by
  unfold sideEquation
  split_ifs <;> fun_prop

/-- The finite triangle carrier is closed relative to the disk. (Epstein–Petronio, Def. 2.1) -/
theorem isClosed_triangle_in_disk (V : Finset ℂ) :
    IsClosed {z : disk | z.val ∈ triangle V} := by
  simp only [triangle, Set.mem_ofPred_eq, Subtype.property, true_and, Set.ofPred_forall]
  refine isClosed_iInter fun p ↦ isClosed_iInter fun hp ↦
    isClosed_iInter fun q ↦ isClosed_iInter fun hq ↦
    isClosed_iInter fun r ↦ isClosed_iInter fun hr ↦
    isClosed_iInter fun hpq ↦ isClosed_iInter fun hqr ↦ isClosed_iInter fun hrp ↦ ?_
  exact isClosed_le continuous_const
    (((continuous_sideEquation p q).comp continuous_subtype_val).mul_const _)

/-- A point satisfying the finite triangle inequalities that lies on none of its side zero loci lies in its topological interior. (Epstein–Petronio, Def. 2.1) -/
theorem mem_openTriangle_of_not_mem_sides {V : Finset ℂ} {z : ℂ}
    (hz : z ∈ triangle V)
    (hs : ¬ ∃ p ∈ V, ∃ q ∈ V, p ≠ q ∧ z ∈ openSide p q) :
    z ∈ openTriangle V := by
  classical
  have hD : ∀ᶠ w in 𝓝 z, w ∈ disk :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hz.1
  have hP : ∀ᶠ w in 𝓝 z, ∀ p q r : V,
      p.val ≠ q.val → q.val ≠ r.val → r.val ≠ p.val →
        0 ≤ sideEquation p.val q.val w * sideEquation p.val q.val r.val := by
    apply eventually_all.mpr
    intro p
    apply eventually_all.mpr
    intro q
    apply eventually_all.mpr
    intro r
    by_cases hpq : p.val = q.val
    · exact Filter.Eventually.of_forall (by simp [hpq])
    by_cases hqr : q.val = r.val
    · exact Filter.Eventually.of_forall (by simp [hqr])
    by_cases hrp : r.val = p.val
    · exact Filter.Eventually.of_forall (by simp [hrp])
    by_cases hr : sideEquation p.val q.val r.val = 0
    · exact Filter.Eventually.of_forall (by simp [hr])
    have hzside : sideEquation p.val q.val z ≠ 0 := by
      intro heq
      exact hs ⟨p.val, p.property, q.val, q.property, hpq, hz.1, heq⟩
    have hpos : 0 < sideEquation p.val q.val z * sideEquation p.val q.val r.val :=
      lt_of_le_of_ne (hz.2 p.val p.property q.val q.property r.val r.property hpq hqr hrp)
        (Ne.symm (mul_ne_zero hzside hr))
    have hnear : ∀ᶠ w in 𝓝 z,
        0 < sideEquation p.val q.val w * sideEquation p.val q.val r.val :=
      (isOpen_lt continuous_const ((continuous_sideEquation p.val q.val).mul_const _)).mem_nhds
        hpos
    exact hnear.mono fun w hw _ _ _ ↦ hw.le
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hD, hP] with w hw hPw
  exact ⟨hw, fun p hp q hq r hr ↦ hPw ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩⟩

/-- Every point of the finite triangle carrier is interior or belongs to one of its side zero loci. (Epstein–Petronio, Def. 2.1) -/
theorem triangle_subset_openTriangle_union_sides (V : Finset ℂ) :
    triangle V ⊆ openTriangle V ∪
      {z | ∃ p ∈ V, ∃ q ∈ V, p ≠ q ∧ z ∈ openSide p q} := by
  intro z hz
  by_cases hs : ∃ p ∈ V, ∃ q ∈ V, p ≠ q ∧ z ∈ openSide p q
  · exact Or.inr hs
  · exact Or.inl (mem_openTriangle_of_not_mem_sides hz hs)

end HolomorphicAnosov.IdealDiskTriangle
