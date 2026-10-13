import HolomorphicAnosov.Geometry.IdealTriangleKleinBarycenterG6
import HolomorphicAnosov.Geometry.IdealTriangleBoundary

open Set Filter
open scoped Topology _root_.Topology
noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle

/-- The explicitly defined carrier of every actual ideal triangle has nonempty interior. (Epstein–Petronio, Def. 2.1) -/
theorem normalized_triangle_carrier_nonempty_g6 (A : VertexTriple) :
    (openTriangle A.val).Nonempty := by
  classical
  obtain ⟨z, hz, t, ht, heq⟩ := ideal_triangle_klein_barycenter_g6 A
  refine ⟨z, ?_⟩
  have hD : ∀ᶠ u in 𝓝 z, u ∈ disk :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hz
  have hP : ∀ᶠ u in 𝓝 z, ∀ p q r : A.val,
      p.val ≠ q.val → q.val ≠ r.val → r.val ≠ p.val →
        0 ≤ sideEquation p.val q.val u * sideEquation p.val q.val r.val := by
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
    have he := heq p p.property q q.property r r.property hpq hqr hrp
    have hpos : 0 < sideEquation p.val q.val z * sideEquation p.val q.val r.val := by
      rw [he]
      have hsq := sq_pos_of_ne_zero hr
      nlinarith
    have hnear : ∀ᶠ u in 𝓝 z,
        0 < sideEquation p.val q.val u * sideEquation p.val q.val r.val :=
      (isOpen_lt continuous_const ((continuous_sideEquation p.val q.val).mul_const _)).mem_nhds hpos
    exact hnear.mono fun u hu _ _ _ ↦ hu.le
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hD,hP] with u hu hPu
  exact ⟨hu, fun p hp q hq r hr ↦ hPu ⟨p,hp⟩ ⟨q,hq⟩ ⟨r,hr⟩⟩

end HolomorphicAnosov.IdealDiskTriangle
