import HolomorphicAnosov.Topology.CairnsGapNullFamily
import HolomorphicAnosov.Topology.CairnsGapRefinementCoordinates
import Mathlib.Topology.Order.IsLUB

namespace HolomorphicAnosov.Topology.Plane.CairnsCircleGap
open Set Filter
open scoped _root_.Topology

/-- A nonempty residual family of a closed contact set has a longest proper
angular gap. Source: Cairns (1951), §4(C), p.865. Choose gap lengths tending
to their supremum and a convergent subsequence of principal starting angles.
The limiting endpoints remain contacts by closedness. Every strictly interior
point of their limiting angular interval belongs to all sufficiently late
gaps and therefore avoids the contact set. The limiting length cannot be a
full turn: that would leave only one possible contact, whereas any existing
proper gap has two distinct endpoint contacts. The limiting proper gap thus
realizes the supremum, which is also the literal mesh with zero inserted. -/
theorem mesh_attained_of_closed (S : Set Circle) (hS : IsClosed S)
    (hex : ∃ g : CairnsCircleGap, g.IsGapOf S) :
    ∃ g : CairnsCircleGap, g.IsGapOf S ∧ g.normalizedLength = mesh S := by
  classical
  obtain ⟨g₀,hg₀⟩ := hex
  have hturn : 0 < 2 * Real.pi := by positivity
  let J := normalizedLength '' {g | g.IsGapOf S}
  have hJne : J.Nonempty := ⟨g₀.normalizedLength,g₀,hg₀,rfl⟩
  have hJbound : BddAbove J := by
    refine ⟨1,?_⟩
    rintro x ⟨g,hg,rfl⟩
    exact ((div_lt_one hturn).mpr g.shorter_than_turn).le
  let L := sSup J
  have hLpos : 0 < L := lt_of_lt_of_le
    (div_pos (sub_pos.mpr g₀.start_lt_stop) hturn)
    (le_csSup hJbound (show g₀.normalizedLength ∈ J from ⟨g₀,hg₀,rfl⟩))
  have hLle : L ≤ 1 := by
    apply csSup_le hJne
    rintro x ⟨g,hg,rfl⟩
    exact ((div_lt_one hturn).mpr g.shorter_than_turn).le
  obtain ⟨v,hvmono,hvlim,hv⟩ := exists_seq_tendsto_sSup hJne hJbound
  choose g hg hgv using hv
  let a : ℕ → ℝ := fun n ↦ ((g n).first : ℂ).arg
  let b : ℕ → ℝ := fun n ↦ a n + ((g n).stop - (g n).start)
  obtain ⟨r,hr,k,hk,halim⟩ := isCompact_Icc.tendsto_subseq
    (fun n ↦ show a n ∈ Icc (-Real.pi) Real.pi from
      ⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩)
  have hlength : Tendsto (fun n ↦ (g n).stop - (g n).start) atTop (nhds ((2 * Real.pi) * L)) := by
    have hh := hvlim.const_mul (2 * Real.pi)
    convert hh using 1
    funext n
    rw [← hgv n]
    dsimp only [normalizedLength]
    exact (mul_div_cancel₀ _ hturn.ne').symm
  have hblim : Tendsto (b ∘ k) atTop (nhds (r + (2 * Real.pi) * L)) :=
    halim.add (hlength.comp hk.tendsto_atTop)
  have hlast (n : ℕ) : Circle.exp (b n) = (g n).last := by
    change Circle.exp (a n + ((g n).stop - (g n).start)) = _
    rw [Circle.exp_add, Circle.exp_arg]
    change Circle.exp (g n).start * Circle.exp ((g n).stop - (g n).start) = _
    rw [← Circle.exp_add]
    congr 1
    ring
  have hrS : Circle.exp r ∈ S := hS.mem_of_tendsto (Circle.exp.continuous.tendsto r |>.comp halim)
    (Eventually.of_forall (fun n ↦ by simpa [a] using (hg (k n)).1))
  have hbS : Circle.exp (r + (2 * Real.pi) * L) ∈ S :=
    hS.mem_of_tendsto (Circle.exp.continuous.tendsto _ |>.comp hblim)
      (Eventually.of_forall (fun n ↦ by simpa only [Function.comp_apply,hlast] using (hg (k n)).2.1))
  have havoid : Circle.exp '' Ioo r (r + (2 * Real.pi) * L) ⊆ Sᶜ := by
    rintro z ⟨θ,hθ,rfl⟩
    obtain ⟨n,hnlo,hnhi⟩ := ((halim.eventually_lt_const hθ.1).and
      (hblim.eventually_const_lt hθ.2)).exists
    have hz : Circle.exp θ ∈ (g (k n)).openArc := by
      rw [← principal_interval_image]
      exact ⟨θ,⟨hnlo,hnhi⟩,rfl⟩
    obtain ⟨x,hx,hcomp⟩ := (hg (k n)).2.2
    apply connectedComponentIn_subset Sᶜ x
    rwa [hcomp]
  have hLlt : L < 1 := by
    by_contra hh
    have hLone : L = 1 := le_antisymm hLle (le_of_not_gt hh)
    rw [hLone,mul_one] at havoid
    have hsingleton (z : Circle) (hz : z ∈ S) : z = Circle.exp r := by
      have hcover : Circle.exp '' Icc r (r + 2 * Real.pi) = univ := by
        rw [Circle.periodic_exp.image_Icc hturn]
        exact Circle.exp_surjective.range_eq
      obtain ⟨θ,hθ,hθz⟩ := (show z ∈ Circle.exp '' Icc r (r + 2 * Real.pi) from hcover ▸ mem_univ z)
      by_cases hlo : r = θ
      · exact hθz.symm.trans (congrArg Circle.exp hlo.symm)
      by_cases hhi : θ = r + 2 * Real.pi
      · exact hθz.symm.trans ((congrArg Circle.exp hhi).trans (Circle.periodic_exp r))
      · exact (havoid ⟨θ,⟨lt_of_le_of_ne hθ.1 hlo,lt_of_le_of_ne hθ.2 hhi⟩,hθz⟩ hz).elim
    have hends : g₀.first = g₀.last := (hsingleton _ hg₀.1).trans (hsingleton _ hg₀.2.1).symm
    have hh := Circle.exp_injOn_Icc g₀.shorter_than_turn
      (show g₀.start ∈ Icc g₀.start g₀.stop from ⟨le_rfl,g₀.start_lt_stop.le⟩)
      (show g₀.stop ∈ Icc g₀.start g₀.stop from ⟨g₀.start_lt_stop.le,le_rfl⟩) hends
    exact g₀.start_lt_stop.ne hh
  let G : CairnsCircleGap := {
    start := r
    stop := r + (2 * Real.pi) * L
    start_lt_stop := by nlinarith
    shorter_than_turn := by nlinarith }
  refine ⟨G,G.isGapOf_of_endpoints S hrS hbS havoid,?_⟩
  have hmesh : mesh S = L := by
    unfold mesh
    rw [csSup_insert hJbound hJne]
    exact max_eq_right hLpos.le
  rw [hmesh]
  change (r + (2 * Real.pi) * L - r) / (2 * Real.pi) = L
  field_simp
  ring

end HolomorphicAnosov.Topology.Plane.CairnsCircleGap
