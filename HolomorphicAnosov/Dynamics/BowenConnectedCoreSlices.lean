import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Tactic

open Set
open scoped _root_.Topology

namespace HolomorphicAnosov.Dynamics.Bowen
universe u

/-- Reverse the time direction of the same contracting canonical coordinates.
The bracket swaps its arguments and the product chart swaps its factors. -/
def CompactLocalProductData.reverse
    {M : Type*} [MetricSpace M] [CompactSpace M]
    {f : M ≃ₜ M} {γ lam : ℝ} (H : CompactLocalProductData f γ lam) :
    CompactLocalProductData f.symm γ lam where
  gamma_pos := H.gamma_pos
  lambda_pos := H.lambda_pos
  lambda_lt_one := H.lambda_lt_one
  stable_contraction := H.unstable_contraction
  unstable_contraction := H.stable_contraction
  closeRadius := H.closeRadius
  closeRadius_pos := H.closeRadius_pos
  bracket x y := H.bracket y x
  bracket_mem := fun x y hxy ↦ by
    obtain ⟨hs,hu⟩ := H.bracket_mem y x (dist_comm x y ▸ hxy)
    exact ⟨hu,hs⟩
  bracket_unique := fun x y z hxy hz ↦ H.bracket_unique y x z (dist_comm x y ▸ hxy) ⟨hz.2,hz.1⟩
  bracket_continuous := H.bracket_continuous.comp (continuous_swap.continuousOn)
    (fun z hz ↦ by change dist z.2 z.1 ≤ H.closeRadius; exact dist_comm z.1 z.2 ▸ hz)
  product_chart := by
    intro x
    obtain ⟨ρ,hρ,hργ,hρε,hchart⟩ := H.product_chart x
    refine ⟨ρ,hρ,hργ,hρε,?_⟩
    intro U V hU hV hoU hoV
    obtain ⟨ho,Q,hQ⟩ := hchart V U hV hU hoV hoU
    have heq : image2 (fun x y ↦ H.bracket y x) U V = image2 H.bracket V U := by
      ext z
      constructor <;> rintro ⟨a,ha,b,hb,he⟩ <;> exact ⟨b,hb,a,ha,he⟩
    refine ⟨heq.symm ▸ ho, ?_⟩
    let R := (Homeomorph.prodComm _ _).trans Q
    let J := Homeomorph.setCongr heq.symm
    refine ⟨R.trans J, ?_⟩
    intro p
    exact hQ (p.2,p.1)

/-- Small stable orbit pairs in a canonical product neighborhood lie on one
connected small product slice. Source: Bowen (1970), Fact 1 pp.726–727 and
Lemmas 7–8 pp.728–729. Choose a connected open stable factor and a small
unstable factor whose bracket image remains in a prescribed ball. The
unstable coordinates of two sufficiently close forward orbits have close
forward iterates by stable contraction and close inverse iterates because
both are in the small unstable factor. Bracket uniqueness on the diagonal
makes these coordinates equal. Varying the stable coordinate in the fixed
connected factor then gives the desired slice. -/
theorem CompactLocalProductData.local_stable_connected_slice
    {M : Type u} [MetricSpace M] [CompactSpace M]
    {f : M ≃ₜ M} {γ lam : ℝ} (H : CompactLocalProductData f γ lam)
    (x : M) (η : ℝ) (hη : 0 < η)
    (hlocal : ∃ ρ : ℝ, 0 < ρ ∧
      LocallyConnectedSpace {s : relativeClosedStablePlaque f γ x // dist s.val x < ρ}) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ p ∈ O, ∀ y ∈ O, y ∈ relativeClosedStablePlaque f δ p →
        ∃ (X : Type u) (_ : TopologicalSpace X) (_ : LocallyConnectedSpace X)
          (_ : ConnectedSpace X) (q : X → M), Continuous q ∧
          p ∈ range q ∧ y ∈ range q ∧
          ∀ z, q z ∈ relativeClosedStablePlaque f γ p ∧ dist (q z) p < η := by
  classical
  have hselfS (p : M) : p ∈ relativeClosedStablePlaque f γ p := by
    intro n; simpa using H.gamma_pos.le
  have hselfU (p : M) : p ∈ relativeClosedUnstablePlaque f γ p := by
    intro n; simpa using H.gamma_pos.le
  have hdiag : H.bracket x x = x :=
    (H.bracket_unique x x x (by simpa using H.closeRadius_pos.le) ⟨hselfS x, hselfU x⟩).symm
  let c := min η γ / 20
  have hc : 0 < c := div_pos (lt_min hη H.gamma_pos) (by norm_num)
  have hcη : c ≤ η / 20 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hcγ : c ≤ γ / 20 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hbc : ContinuousAt (fun z : M × M ↦ H.bracket z.1 z.2) (x, x) := by
    apply H.bracket_continuous.continuousAt
    apply Filter.mem_of_superset
      ((isOpen_lt continuous_dist continuous_const).mem_nhds (by simpa using H.closeRadius_pos))
    intro z hz
    exact (show dist z.1 z.2 < H.closeRadius from hz).le
  obtain ⟨b, hb, hnear⟩ := Metric.continuousAt_iff.mp hbc c hc
  obtain ⟨ρp, hρp, hρpγ, hρpε, hprod⟩ := H.product_chart x
  obtain ⟨ρl, hρl, hlocal⟩ := hlocal
  let ρ := min (min ρp ρl) (min b c) / 2
  have hρ : 0 < ρ := half_pos (lt_min (lt_min hρp hρl) (lt_min hb hc))
  have hρp' : ρ < ρp := (half_lt_self (lt_min (lt_min hρp hρl) (lt_min hb hc))).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hρl' : ρ < ρl := (half_lt_self (lt_min (lt_min hρp hρl) (lt_min hb hc))).trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  have hρb : ρ < b := (half_lt_self (lt_min (lt_min hρp hρl) (lt_min hb hc))).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hρc : ρ < c := (half_lt_self (lt_min (lt_min hρp hρl) (lt_min hb hc))).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  let KS := relativeClosedStablePlaque f γ x
  let KU := relativeClosedUnstablePlaque f γ x
  let AS := {s : KS // dist s.val x < ρl}
  have : LocallyConnectedSpace AS := hlocal
  let sx : AS := ⟨⟨x, hselfS x⟩, by simpa using hρl⟩
  have hsnear : {s : AS | dist s.val.val x < ρ} ∈ 𝓝 sx := by
    exact (isOpen_lt ((continuous_subtype_val.comp continuous_subtype_val).dist continuous_const)
      continuous_const).mem_nhds (by simpa [sx] using hρ)
  obtain ⟨V, hVsub, hVopen, hxV, hVconn⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance sx _ hsnear
  let VS : Set KS := Subtype.val '' V
  have hVS : IsOpen VS :=
    (isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const).isOpenMap_subtype_val _ hVopen
  let U : Set M := KU ∩ Metric.ball x ρ
  let S : Set M := Subtype.val '' VS
  have hUS : U ⊆ relativeClosedUnstablePlaque f ρp x := by
    intro u hu n
    have hh := H.unstable_contraction x u x hu.1 (hselfU x) n
    have hp := pow_le_one₀ (n := n) H.lambda_pos.le H.lambda_lt_one.le
    exact hh.trans ((mul_le_of_le_one_left (dist_nonneg) hp).trans (hu.2.le.trans hρp'.le))
  have hSS : S ⊆ relativeClosedStablePlaque f ρp x := by
    rintro _ ⟨s, ⟨t, ht, rfl⟩, rfl⟩ n
    have hh := H.stable_contraction x t.val.val x t.val.property (hselfS x) n
    exact hh.trans ((mul_le_of_le_one_left (dist_nonneg) (pow_le_one₀ (n := n) H.lambda_pos.le H.lambda_lt_one.le)).trans
      ((hVsub ht).le.trans hρp'.le))
  have hUopen : IsOpen {u : KU | (u : M) ∈ U} := by
    have heq : {u : KU | (u : M) ∈ U} = {u : KU | dist u.val x < ρ} := by
      ext u; simp only [U, mem_ofPred_eq, mem_inter_iff, Metric.mem_ball, u.property, true_and]
    rw [heq]
    exact isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
  have hSopen : IsOpen {s : KS | (s : M) ∈ S} := by
    have heq : {s : KS | (s : M) ∈ S} = VS := by
      ext s; exact Subtype.val_injective.mem_set_image
    rw [heq]
    exact hVS
  obtain ⟨hO, HP, hHP⟩ := hprod U S hUS hSS hUopen hSopen
  let O := image2 H.bracket U S
  have hxU : x ∈ U := ⟨hselfU x, by simpa using hρ⟩
  have hxS : x ∈ S := ⟨⟨x, hselfS x⟩, ⟨sx, hxV, rfl⟩, rfl⟩
  have hxO : x ∈ O := ⟨x, hxU, x, hxS, hdiag⟩
  have hSc (s : M) (hs : s ∈ S) : dist s x < ρ := by
    obtain ⟨s, ⟨t, ht, rfl⟩, rfl⟩ := hs
    exact hVsub ht
  have hclose (u : M) (hu : u ∈ U) (s : M) (hs : s ∈ S) : dist u s ≤ H.closeRadius := by
    have ht := (dist_triangle u x s).trans_lt (add_lt_add hu.2 (by simpa only [dist_comm] using hSc s hs))
    linarith
  have hOc (z : M) (hz : z ∈ O) : dist z x < c := by
    obtain ⟨u, hu, s, hs, rfl⟩ := hz
    have hh := hnear (show dist (u,s) (x,x) < b by
      rw [Prod.dist_eq]; exact max_lt (hu.2.trans hρb) ((hSc s hs).trans hρb))
    simpa only [hdiag] using hh
  refine ⟨O, hO, hxO, c, hc, ?_⟩
  intro p hp y hy hys
  obtain ⟨u, hu, s, hs, hpus⟩ := hp
  obtain ⟨u', hu', s', hs', hyus⟩ := hy
  have hpmem : p ∈ relativeClosedStablePlaque f γ u := by
    rw [← hpus]; exact (H.bracket_mem u s (hclose u hu s hs)).1
  have hymem : y ∈ relativeClosedStablePlaque f γ u' := by
    rw [← hyus]; exact (H.bracket_mem u' s' (hclose u' hu' s' hs')).1
  have hpc : dist p x < c := hOc p ⟨u, hu, s, hs, hpus⟩
  have hyc : dist y x < c := hOc y ⟨u', hu', s', hs', hyus⟩
  have huu : u' = u := by
    have hforward : u' ∈ relativeClosedStablePlaque f γ u := by
      intro n
      have h1 := H.stable_contraction u' u' y (hselfS u') hymem n
      have h2 := H.stable_contraction u p u hpmem (hselfS u) n
      have hpow := pow_le_one₀ (n := n) H.lambda_pos.le H.lambda_lt_one.le
      have h1' := h1.trans (mul_le_of_le_one_left dist_nonneg hpow)
      have h2' := h2.trans (mul_le_of_le_one_left dist_nonneg hpow)
      have htr := dist_triangle ((f : M → M)^[n] u') ((f : M → M)^[n] y) ((f : M → M)^[n] u)
      have htr2 := dist_triangle ((f : M → M)^[n] y) ((f : M → M)^[n] p) ((f : M → M)^[n] u)
      have hu'y := dist_triangle u' x y
      have hpu := dist_triangle p x u
      have hu0 : dist u x < ρ := hu.2; have hu0' : dist u' x < ρ := hu'.2
      rw [dist_comm x y] at hu'y
      rw [dist_comm x u] at hpu
      have hysn := hys n
      linarith
    have hbackward : u' ∈ relativeClosedUnstablePlaque f γ u := by
      intro n
      have hh := H.unstable_contraction x u' u hu'.1 hu.1 n
      have hp := pow_le_one₀ (n := n) H.lambda_pos.le H.lambda_lt_one.le
      have hle := hh.trans (mul_le_of_le_one_left dist_nonneg hp)
      have ht := dist_triangle u' x u
      rw [dist_comm x u] at ht
      have hu0 : dist u x < ρ := hu.2; have hu0' : dist u' x < ρ := hu'.2
      linarith
    exact (H.bracket_unique u u u' (by simpa using H.closeRadius_pos.le) ⟨hforward,hbackward⟩).trans
      (H.bracket_unique u u u (by simpa using H.closeRadius_pos.le) ⟨hselfS u,hselfU u⟩).symm
  subst u'
  let q : V → M := fun t ↦ H.bracket u t.val.val.val
  have hq : Continuous q := H.bracket_continuous.comp_continuous
    (continuous_const.prodMk (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
    (fun t ↦ hclose u hu _ ⟨t.val.val, ⟨t.val,t.property,rfl⟩,rfl⟩)
  have : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  have : LocallyConnectedSpace V := hVopen.isOpenEmbedding_subtypeVal.locallyConnectedSpace
  refine ⟨↥V, inferInstance, inferInstance, inferInstance, q, hq, ?_, ?_, ?_⟩
  · obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hs
    exact ⟨⟨t, ht⟩, hpus⟩
  · obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hs'
    exact ⟨⟨t, ht⟩, hyus⟩
  · intro t
    have hts : t.val.val.val ∈ S := ⟨t.val.val, ⟨t.val,t.property,rfl⟩,rfl⟩
    have hqc : dist (q t) x < c := hOc _ ⟨u,hu,t.val.val.val,hts,rfl⟩
    have hqp : dist (q t) p < 2 * c := by
      have ht := dist_triangle (q t) x p
      rw [dist_comm x p] at ht
      linarith
    refine ⟨?_, by linarith⟩
    intro n
    have hqmem := (H.bracket_mem u t.val.val.val (hclose u hu _ hts)).1
    have hh := H.stable_contraction u (q t) p hqmem hpmem n
    exact hh.trans ((mul_le_of_le_one_left dist_nonneg
      (pow_le_one₀ (n := n) H.lambda_pos.le H.lambda_lt_one.le)).trans (by linarith))

end HolomorphicAnosov.Dynamics.Bowen
