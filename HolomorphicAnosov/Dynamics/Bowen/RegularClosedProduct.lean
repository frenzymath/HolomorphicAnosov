import HolomorphicAnosov.Dynamics.Bowen.PlaqueRebase
import HolomorphicAnosov.Dynamics.Bowen.ProductChart
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Defs

/-! The regular-closed product and its plaque sections from Bowen's Lemma 10. -/

/-- Bowen (1970), Fact 1 pp. 726--727: the closed forward orbit plaque. -/
private def stablePlaque {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (δ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f ^ n) y) ((f ^ n) x) ≤ δ}

/-- Bowen (1970), Fact 1 pp. 726--727: the closed backward orbit plaque. -/
private def unstablePlaque {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (δ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f.symm ^ n) y) ((f.symm ^ n) x) ≤ δ}

/-- Bowen (1970), Lemma 10 p. 730: the set of brackets of pairs of factor points. -/
private def bracketImage {X : Type*} (b : X → X → X) (C D : Set X) : Set X :=
  {z | ∃ c ∈ C, ∃ d ∈ D, b c d = z}

/-- Bowen (1970), Lemmas 9--10 pp. 729--730: interior in the full plaque subtype. -/
private def relativeInterior {X : Type*} [TopologicalSpace X] (S C : Set X) : Set X :=
  (Subtype.val : S → X) '' interior ((Subtype.val : S → X) ⁻¹' C)

/-- Bowen (1970), Lemma 10 p. 730: frontier in the full plaque subtype. -/
private def relativeFrontier {X : Type*} [TopologicalSpace X] (S C : Set X) : Set X :=
  (Subtype.val : S → X) '' frontier ((Subtype.val : S → X) ⁻¹' C)

open Set Topology

namespace BowenRegularClosedPreparation

/-- Natural powers of the original homeomorphism are its function iterates. -/
theorem pow_apply_iterate {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) (x : X) : (f ^ n) x = (f : X → X)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa only [pow_succ, Homeomorph.mul_apply,
      Function.iterate_succ_apply] using ih (f x)

/-- Orbit plaques are closed, including at their boundary. -/
theorem isClosed_stable {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (δ : ℝ) (x : X) :
    IsClosed (stablePlaque f δ x) := by
  simp only [stablePlaque, ofPred_forall]
  exact isClosed_iInter fun n ↦ isClosed_le
    ((f ^ n).continuous.dist continuous_const) continuous_const

/-- The zeroth orbit condition controls the original distance. -/
theorem dist_le_of_mem {X : Type*} [MetricSpace X] (f : X ≃ₜ X) {δ : ℝ} {x y : X}
    (hy : y ∈ stablePlaque f δ x) : dist y x ≤ δ := by
  simpa using hy 0

/-- Smaller orbit plaques sit in larger ones. -/
theorem plaque_mono {X : Type*} [MetricSpace X] (f : X ≃ₜ X) {δ γ : ℝ}
    (hδ : δ ≤ γ) (x : X) : stablePlaque f δ x ⊆ stablePlaque f γ x :=
  fun _ hy n ↦ (hy n).trans hδ

/-- Every point belongs to its own nonnegative-radius plaque. -/
theorem self_mem {X : Type*} [MetricSpace X] (f : X ≃ₜ X) {δ : ℝ} (hδ : 0 ≤ δ)
    (x : X) : x ∈ stablePlaque f δ x := by
  intro n
  simpa using hδ

/-- Two simultaneous orbit-distance bounds add by the triangle inequality. -/
theorem plaque_triangle {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    {a b c : X} {r s : ℝ} (hab : a ∈ stablePlaque f r b)
    (hbc : b ∈ stablePlaque f s c) : a ∈ stablePlaque f (r + s) c := by
  intro n
  exact (dist_triangle _ _ _).trans (add_le_add (hab n) (hbc n))

/-- The orbit-distance condition is symmetric. -/
theorem plaque_symm {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    {a b : X} {r : ℝ} (hab : a ∈ stablePlaque f r b) :
    b ∈ stablePlaque f r a := by
  intro n
  simpa only [dist_comm] using hab n

/-- Intersection uniqueness only at the diagonal already separates simultaneous plaques. -/
theorem diagonal_separation {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    {γ ε : ℝ} (b : X → X → X) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hu : ∀ a z, dist a a ≤ ε → z ∈ stablePlaque f γ a →
      z ∈ unstablePlaque f γ a → z = b a a)
    {a z : X} (hs : z ∈ stablePlaque f γ a) (ht : z ∈ unstablePlaque f γ a) :
    z = a := by
  have hz := hu a z (by simpa using hε) hs ht
  have ha := hu a a (by simpa using hε) (self_mem f hγ a) (self_mem f.symm hγ a)
  exact hz.trans ha.symm

/-- Product brackets absorb their crossed factor coordinates. The proof uses only the
small-plaque orbit bounds and diagonal uniqueness, so no unstated bracket-domain cap is needed. -/
theorem absorption {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    {γ ε δ σ : ℝ} (b : X → X → X) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hu : ∀ a z, dist a a ≤ ε → z ∈ stablePlaque f γ a →
      z ∈ unstablePlaque f γ a → z = b a a)
    (hmargin : 2 * δ + σ ≤ γ)
    {c₁ c₂ d₁ d₂ : X}
    (h11 : b c₁ d₁ ∈ stablePlaque f δ c₁ ∩ unstablePlaque f δ d₁)
    (h22 : b c₂ d₂ ∈ stablePlaque f δ c₂ ∩ unstablePlaque f δ d₂)
    (h12 : b c₁ d₂ ∈ stablePlaque f δ c₁ ∩ unstablePlaque f δ d₂)
    (houter : b (b c₁ d₁) (b c₂ d₂) ∈
      stablePlaque f σ (b c₁ d₁) ∩ unstablePlaque f σ (b c₂ d₂)) :
    b (b c₁ d₁) (b c₂ d₂) = b c₁ d₂ := by
  apply (diagonal_separation f b hγ hε hu
    (plaque_mono f (by linarith : δ + δ + σ ≤ γ) _
      (plaque_triangle f (plaque_triangle f h12.1 (plaque_symm f h11.1))
        (plaque_symm f houter.1)))
    (plaque_mono f.symm (by linarith : δ + δ + σ ≤ γ) _
      (plaque_triangle f.symm
        (plaque_triangle f.symm h12.2 (plaque_symm f.symm h22.2))
        (plaque_symm f.symm houter.2)))).symm

/-- Contracting plaques give a bounded orbit-distance estimate from the zeroth distance. -/
theorem contraction_bound {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    {lam γ r : ℝ} (hlam : 0 ≤ lam ∧ lam ≤ 1)
    (hc : ∀ a y z n, y ∈ stablePlaque f γ a → z ∈ stablePlaque f γ a →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    {a y z : X} (hy : y ∈ stablePlaque f γ a) (hz : z ∈ stablePlaque f γ a)
    (hd : dist y z ≤ r) : y ∈ stablePlaque f r z := by
  intro n
  exact (hc a y z n hy hz).trans
    ((mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.1 hlam.2)).trans hd)

/-- A plaque point is unchanged when bracketed with its base in the complementary direction. -/
theorem unstable_bracket_self {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    {lam γ ε σ : ℝ} (b : X → X → X) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hlam : 0 ≤ lam ∧ lam ≤ 1)
    (hu : ∀ a z, dist a a ≤ ε → z ∈ stablePlaque f γ a →
      z ∈ unstablePlaque f γ a → z = b a a)
    (hc : ∀ a y z n, y ∈ unstablePlaque f γ a → z ∈ unstablePlaque f γ a →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    {a q : X} (ha : a ∈ unstablePlaque f γ q) (hσ : σ ≤ γ)
    (hb : b a q ∈ stablePlaque f σ a ∩ unstablePlaque f σ q)
    (hd : dist a q + σ ≤ γ) : b a q = a := by
  refine diagonal_separation f b hγ hε hu (plaque_mono f hσ a hb.1) ?_
  apply contraction_bound f.symm hlam hc (plaque_mono f.symm hσ q hb.2) ha
  calc
    dist (b a q) a ≤ dist (b a q) q + dist q a := dist_triangle _ _ _
    _ ≤ σ + dist a q := by
      rw [dist_comm q a]
      exact add_le_add (dist_le_of_mem f.symm hb.2) le_rfl
    _ ≤ γ := by linarith

/-- Regular closure pulls back under a continuous open map. -/
theorem regular_preimage {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {g : Y → Z} (hg : Continuous g) (ho : IsOpenMap g) {C : Set Z}
    (hC : C = closure (interior C)) :
    g ⁻¹' C = closure (interior (g ⁻¹' C)) := by
  conv_lhs => rw [hC]
  rw [ho.preimage_closure_eq_closure_preimage hg,
    ho.preimage_interior_eq_interior_preimage hg]

/-- A regular-closed compact set remains regular closed under a continuous open map
into a Hausdorff space. This is the chart-transport step in Bowen's Lemma 10. -/
theorem regular_image {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space Z] {g : Y → Z} (hg : Continuous g) (ho : IsOpenMap g) {C : Set Y}
    (hC : C = closure (interior C)) (hc : IsCompact C) :
    g '' C = closure (interior (g '' C)) := by
  apply Subset.antisymm
  · calc
      g '' C = g '' closure (interior C) := congrArg _ hC
      _ ⊆ closure (g '' interior C) := image_closure_subset_closure_image hg
      _ ⊆ closure (interior (g '' C)) := closure_mono (ho.image_interior_subset C)
  · exact closure_minimal interior_subset (hc.image hg).isClosed

/-- Product regular-closure follows directly from the native product identities. -/
theorem regular_product {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {C : Set Y} {D : Set Z} (hC : C = closure (interior C))
    (hD : D = closure (interior D)) :
    C ×ˢ D = closure (interior (C ×ˢ D)) := by
  rw [interior_prod_eq, closure_prod_eq, ← hC, ← hD]

/-- Interior in a full plaque can be read at its literal subtype point. -/
theorem mem_relativeInterior {X : Type*} [TopologicalSpace X] (S C : Set X)
    (x : X) (hx : x ∈ S) :
    x ∈ relativeInterior S C ↔ (⟨x,hx⟩ : S) ∈ interior (Subtype.val ⁻¹' C) := by
  constructor
  · rintro ⟨z,hz,hzx⟩
    have heq : z = ⟨x,hx⟩ := Subtype.ext hzx
    simpa only [heq] using hz
  · intro hx'
    exact ⟨⟨x,hx⟩,hx',rfl⟩

/-- A relative-open rebase chart transports the full-plaque interior at every point
of a factor. No equality of the two ambient plaques is asserted. -/
theorem rebase_interior {X : Type*} [TopologicalSpace X]
    (S T U C : Set X) (g : X → X) (hU : U ⊆ S) (hC : C ⊆ U)
    (himg : g '' U ⊆ T)
    (hUopen : IsOpen ((Subtype.val : S → X) ⁻¹' U))
    (hBopen : IsOpen ((Subtype.val : T → X) ⁻¹' (g '' U)))
    (h : Homeomorph {s : S // (s:X)∈U} {t : T // (t:X)∈g '' U})
    (hf : ∀s,(h s).val.val = g s.val.val) (c : X) (hc : c∈C) :
    g c ∈ relativeInterior T (g '' C) ↔ c ∈ relativeInterior S C := by
  let c' : {s : S // (s:X)∈U} := ⟨⟨c,hU (hC hc)⟩,hC hc⟩
  let F : {s : S // (s:X)∈U} → T := Subtype.val ∘ h
  let Cp : Set {s : S // (s:X)∈U} := {s | s.val.val∈C}
  have heq : F '' Cp = (Subtype.val : T → X) ⁻¹' (g '' C) := by
    ext t
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨s.val.val,hs,(hf s).symm⟩
    · rintro ⟨s,hs,hst⟩
      let s' : {s : S // (s:X)∈U} := ⟨⟨s,hU (hC hs)⟩,hC hs⟩
      refine ⟨s',hs,?_⟩
      apply Subtype.ext
      exact (hf s').trans hst
  have hFc : F c' = ⟨g c,himg ⟨c,hC hc,rfl⟩⟩ := Subtype.ext (hf c')
  have hFcont : Continuous F := continuous_subtype_val.comp h.continuous
  have hFopen : IsOpenMap F := hBopen.isOpenMap_subtype_val.comp h.isOpenMap
  have hFinj : Function.Injective F := Subtype.val_injective.comp h.injective
  rw [mem_relativeInterior T (g '' C) (g c) (himg ⟨c,hC hc,rfl⟩),
      mem_relativeInterior S C c (hU (hC hc)), ← hFc, ← heq]
  change c'∈F ⁻¹' interior (F '' Cp) ↔ c'.val∈interior (Subtype.val ⁻¹' C)
  rw [hFopen.preimage_interior_eq_interior_preimage hFcont,
    Set.preimage_image_eq _ hFinj]
  have hlocal := hUopen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
    continuous_subtype_val ((Subtype.val : S → X) ⁻¹' C)
  exact (Set.ext_iff.mp hlocal c').symm

/-- The full-plaque interior is equivalent to a literal ambient-ball condition. -/
theorem relativeInterior_ball {X : Type*} [MetricSpace X] (S C : Set X)
    (x : X) (hx : x∈S) :
    x∈relativeInterior S C ↔ ∃r>0,∀y∈S,dist y x<r → y∈C := by
  rw [mem_relativeInterior S C x hx, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  constructor
  · rintro ⟨r,hr,hball⟩
    refine ⟨r,hr,?_⟩
    intro y hy hd
    exact hball (Metric.mem_ball.mpr hd : (⟨y,hy⟩:S)∈Metric.ball ⟨x,hx⟩ r)
  · rintro ⟨r,hr,hball⟩
    refine ⟨r,hr,?_⟩
    intro y hy
    exact hball y.val y.property (Metric.mem_ball.mp hy)

/-- Two full plaques agreeing in one ambient neighborhood have the same relative
interior test there. Only local agreement is used, not global plaque equality. -/
theorem relativeInterior_local {X : Type*} [MetricSpace X] (S T C : Set X)
    (x : X) (hxS : x∈S) (hxT : x∈T) {η : ℝ} (hη : 0<η)
    (hloc : ∀y,dist y x<η → (y∈S ↔ y∈T)) :
    x∈relativeInterior S C ↔ x∈relativeInterior T C := by
  rw [relativeInterior_ball S C x hxS, relativeInterior_ball T C x hxT]
  constructor
  · rintro ⟨r,hr,hb⟩
    refine ⟨min r η,lt_min hr hη,?_⟩
    intro y hy hd
    exact hb y ((hloc y (hd.trans_le (min_le_right _ _))).mpr hy)
      (hd.trans_le (min_le_left _ _))
  · rintro ⟨r,hr,hb⟩
    refine ⟨min r η,lt_min hr hη,?_⟩
    intro y hy hd
    exact hb y ((hloc y (hd.trans_le (min_le_right _ _))).mp hy)
      (hd.trans_le (min_le_left _ _))

/-- Contracting orbit plaques centered at two nearby points agree locally around
one center. The radius margin is strict, including at slice-frontier points. -/
theorem plaque_local_agreement {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    {lam γ δ η : ℝ} (hlam : 0≤lam ∧ lam≤1)
    (hc : ∀ a y z n, y∈stablePlaque f γ a → z∈stablePlaque f γ a →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hγ : 0≤γ) (hδ : δ≤γ) (hη : η+δ≤γ) {q d : X}
    (hqd : q∈stablePlaque f δ d) :
    ∀t,dist t q<η → (t∈stablePlaque f γ q ↔ t∈stablePlaque f γ d) := by
  have hqdγ := plaque_mono f hδ d hqd
  have hδnonneg : 0 ≤ δ := dist_nonneg.trans (dist_le_of_mem f hqd)
  intro t ht
  constructor
  · intro htq
    apply plaque_mono f hη d
    apply plaque_triangle f
      (contraction_bound f hlam hc htq (self_mem f hγ q) ht.le)
      (contraction_bound f hlam hc hqdγ (self_mem f hγ d) (dist_le_of_mem f hqd))
  · intro htd
    exact contraction_bound f hlam hc htd hqdγ (ht.le.trans (by linarith))

/-- For a closed factor contained in its full plaque, its relative frontier is
exactly that factor minus its full-plaque relative interior. -/
theorem relativeFrontier_closed {X : Type*} [TopologicalSpace X]
    (S C : Set X) (hCS : C⊆S)
    (hcl : IsClosed ((Subtype.val : S → X) ⁻¹' C)) (c : X) :
    c∈relativeFrontier S C ↔ c∈C ∧ c∉relativeInterior S C := by
  constructor
  · rintro ⟨u,hu,rfl⟩
    rw [frontier, hcl.closure_eq] at hu
    refine ⟨hu.1,?_⟩
    rw [mem_relativeInterior S C u.val u.property]
    exact hu.2
  · rintro ⟨hc,hni⟩
    refine ⟨⟨c,hCS hc⟩,?_,rfl⟩
    rw [frontier,hcl.closure_eq]
    exact ⟨hc,(mem_relativeInterior S C c (hCS hc)).not.mp hni⟩

/-- A full-plaque relative interior stays inside both the plaque and the factor. -/
theorem relativeInterior_subset {X : Type*} [TopologicalSpace X] (S C : Set X) :
    relativeInterior S C ⊆ S ∩ C := by
  rintro _ ⟨z,hz,rfl⟩
  exact ⟨z.property,(interior_subset hz : z ∈ (Subtype.val : S → X) ⁻¹' C)⟩

/-- The pullback of the included full-plaque interior is the literal subtype interior. -/
theorem preimage_relativeInterior {X : Type*} [TopologicalSpace X] (S C : Set X) :
    (Subtype.val : S → X) ⁻¹' relativeInterior S C =
      interior ((Subtype.val : S → X) ⁻¹' C) := by
  exact Set.preimage_image_eq _ Subtype.val_injective

end BowenRegularClosedPreparation

/--
Source: R. Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970), Lemma 10,
printed pp. 729--730. Choose `r` with `α₄ < r < α₂`, and put
`U = W^u_γ(x) ∩ B_r(x)` and `V = W^s_γ(x) ∩ B_r(x)`. Fact 1 and contraction put
these open relative plaque neighborhoods inside the `α₂` plaques. The guarded
product chart is a homeomorphism `U × V → [U,V]`; restricting it to `C × D` and
using compactness proves that `A = [C,D]` is nonempty compact, hence closed in `X`.

For `a=[c₁,d₁]` and `b=[c₂,d₂]`, each bracket coordinate is within `α₃/3` of
its corresponding factor and each factor is within `α₄` of `x`.  Triangle
inequalities at every iterate put the relevant candidates in common strict `γ`
plaques, so Fact 1 uniqueness gives the absorption identity `[a,b]=[c₁,d₂]`.
Thus `A` is bracket closed, and `dist a b ≤ 2α₃/3 + 2α₄ < α₃`.  The product
identities `closure (C × D) = closure C × closure D` and
`interior (C × D) = interior C × interior D`, transported by the chart, give
`A = closure (interior A)` and identify `interior A` with the product of the
relative factor interiors.

For `q=[c₀,d₀]`, absorption gives `A ∩ W^u_γ(q) = [C,q]` and, dually,
`A ∩ W^s_γ(q) = [q,D]`.  Apply the plaque-rebase homeomorphism to the map
`c ↦ [c,d₀]` on a relative open neighborhood of `C` in the `α₂` plaque; it
identifies the full-plaque interior of `C` with that of `[C,d₀]`.  Every point
of this slice is within `α₃/3` of `d₀` by the modulus and the `α₄` factor guard.
Choose `η > 0` with `3(α₃/3)+η < γ`.  If `t` lies in the `η`-ball around a
slice point, contraction in the two plaques shows
`t ∈ W^u_γ(q)` iff `t ∈ W^u_γ(d₀)`, so the two full-plaque subspace topologies
agree locally, including at boundary points.  Hence a slice point is in the
stable boundary exactly when `c₀` is in the relative frontier of `C`; the stable
argument is dual.  The frontier formula for a product of regular-closed factors
then gives the stated two images and their union.  This is the source proof;
lower Fact 1 and Lean formalization obligations remain separate nodes.
-/
theorem dynamics_bowen_fact1_regular_closed_product_g6
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X ≃ₜ X) (lam γ ε : ℝ) (bracket : X → X → X)
    (εmod : ℝ → ℝ) (α : Fin 5 → ℝ) (x : X)
    (hlam : 0 < lam ∧ lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hfact_s : ∀ a y z n, y ∈ stablePlaque f γ a → z ∈ stablePlaque f γ a →
      dist ((f ^ n) y) ((f ^ n) z) ≤ lam ^ n * dist y z)
    (hfact_u : ∀ a y z n, y ∈ unstablePlaque f γ a → z ∈ unstablePlaque f γ a →
      dist ((f.symm ^ n) y) ((f.symm ^ n) z) ≤ lam ^ n * dist y z)
    (hbracket_mem : ∀ a b, dist a b ≤ ε →
      bracket a b ∈ stablePlaque f γ a ∩ unstablePlaque f γ b)
    (hbracket_unique : ∀ a b z, dist a b ≤ ε →
      z ∈ stablePlaque f γ a → z ∈ unstablePlaque f γ b → z = bracket a b)
    (hbracket_cont : ContinuousOn (fun p : X × X => bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ ∧
      ∀ a b, dist a b ≤ εmod δ →
        bracket a b ∈ stablePlaque f δ a ∩ unstablePlaque f δ b)
    (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαstrict : ∀ i : Fin 4, α i.succ < α i.castSucc)
    (hαrec : ∀ i : Fin 4, α i.succ <
      (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hαmargin : ∀ i : Fin 4, ∀ a b, dist a b ≤ α i.succ →
      dist (f a) (f b) < α i.castSucc ∧
        dist (f.symm a) (f.symm b) < α i.castSucc)
    (C D : Set X) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hCcompact : IsCompact C) (hDcompact : IsCompact D)
    (hCguard : C ⊆ unstablePlaque f (α 4) x)
    (hDguard : D ⊆ stablePlaque f (α 4) x)
    (hCreg : (Subtype.val : unstablePlaque f γ x → X) ⁻¹' C =
      closure (interior ((Subtype.val : unstablePlaque f γ x → X) ⁻¹' C)))
    (hDreg : (Subtype.val : stablePlaque f γ x → X) ⁻¹' D =
      closure (interior ((Subtype.val : stablePlaque f γ x → X) ⁻¹' D))) :
    let A := bracketImage bracket C D
    let boundaryS := {q ∈ A | q ∉
      relativeInterior (unstablePlaque f γ q) (A ∩ unstablePlaque f γ q)}
    let boundaryU := {q ∈ A | q ∉
      relativeInterior (stablePlaque f γ q) (A ∩ stablePlaque f γ q)}
    A.Nonempty ∧ IsCompact A ∧
      (∀ a ∈ A, ∀ b ∈ A, bracket a b ∈ A) ∧
      Metric.diam A ≤ α 3 ∧ A = closure (interior A) ∧
      (∀ q ∈ A, A ∩ unstablePlaque f γ q = bracketImage bracket C {q}) ∧
      (∀ q ∈ A, A ∩ stablePlaque f γ q = bracketImage bracket {q} D) ∧
      boundaryS = bracketImage bracket (relativeFrontier (unstablePlaque f γ x) C) D ∧
      boundaryU = bracketImage bracket C (relativeFrontier (stablePlaque f γ x) D) ∧
      frontier A = boundaryS ∪ boundaryU := by
  classical
  open BowenRegularClosedPreparation in
  have hdiag : ∀ a z, dist a a ≤ ε → z ∈ stablePlaque f γ a →
      z ∈ unstablePlaque f γ a → z = bracket a a := by
    intro a z ha hs hu
    exact hbracket_unique a a z ha hs hu
  have h01 := hαstrict 0
  have h12 := hαstrict 1
  have h23 := hαstrict 2
  have h34 := hαstrict 3
  have hr2 := hαrec 2
  have hr3 := hαrec 3
  change α 1 < α 0 at h01
  change α 2 < α 1 at h12
  change α 3 < α 2 at h23
  change α 4 < α 3 at h34
  change α 3 < (1 / 3 : ℝ) * min (α 2 / 3) (εmod (α 2 / 3)) at hr2
  change α 4 < (1 / 3 : ℝ) * min (α 3 / 3) (εmod (α 3 / 3)) at hr3
  have hp2 := hαpos 2
  have hp3 := hαpos 3
  have hp4 := hαpos 4
  have hδ : 0 < α 3 / 3 := by positivity
  have hδγ : α 3 / 3 ≤ γ / 3 := by rw [← hα0]; linarith
  have hδγ' : α 3 / 3 ≤ γ := by linarith
  have hσ : 0 < α 2 / 3 := by positivity
  have hσγ : α 2 / 3 ≤ γ := by rw [← hα0]; linarith
  have hsmall3 : 3 * α 4 < min (α 3 / 3) (εmod (α 3 / 3)) := by
    linarith
  have hsmall2 : 3 * α 3 < min (α 2 / 3) (εmod (α 2 / 3)) := by
    linarith
  have hm4 : 3 * α 4 < α 3 / 3 := hsmall3.trans_le (min_le_left _ _)
  have he4 : 3 * α 4 < εmod (α 3 / 3) := hsmall3.trans_le (min_le_right _ _)
  have hm3 : 3 * α 3 < α 2 / 3 := hsmall2.trans_le (min_le_left _ _)
  have he3 : 3 * α 3 < εmod (α 2 / 3) := hsmall2.trans_le (min_le_right _ _)
  have hcd : ∀ c ∈ C, ∀ d ∈ D, dist c d ≤ 2 * α 4 := by
    intro c hc d hd
    have hc0 := BowenRegularClosedPreparation.dist_le_of_mem f.symm (hCguard hc)
    have hd0 := BowenRegularClosedPreparation.dist_le_of_mem f (hDguard hd)
    calc
      dist c d ≤ dist c x + dist x d := dist_triangle _ _ _
      _ ≤ 2 * α 4 := by rw [dist_comm x d]; linarith
  have hpair : ∀ c ∈ C, ∀ d ∈ D, bracket c d ∈
      stablePlaque f (α 3 / 3) c ∩ unstablePlaque f (α 3 / 3) d := by
    intro c hc d hd
    exact (hmod _ hδ hδγ').2 c d ((hcd c hc d hd).trans (by linarith))
  have hdA : ∀ a ∈ bracketImage bracket C D, ∀ b ∈ bracketImage bracket C D,
      dist a b ≤ 2 * (α 3 / 3) + 2 * α 4 := by
    rintro a ⟨c₁, hc₁, d₁, hd₁, rfl⟩ b ⟨c₂, hc₂, d₂, hd₂, rfl⟩
    have h1 := BowenRegularClosedPreparation.dist_le_of_mem f (hpair _ hc₁ _ hd₁).1
    have h2 := BowenRegularClosedPreparation.dist_le_of_mem f (hpair _ hc₂ _ hd₂).1
    have hc₁0 := BowenRegularClosedPreparation.dist_le_of_mem f.symm (hCguard hc₁)
    have hc₂0 := BowenRegularClosedPreparation.dist_le_of_mem f.symm (hCguard hc₂)
    have hcc := dist_triangle c₁ x c₂
    rw [dist_comm x c₂] at hcc
    have hd := dist_triangle (bracket c₁ d₁) c₁ (bracket c₂ d₂)
    have hd' := dist_triangle c₁ c₂ (bracket c₂ d₂)
    rw [dist_comm c₂ (bracket c₂ d₂)] at hd'
    linarith
  have hAclosed : ∀ a ∈ bracketImage bracket C D,
      ∀ b ∈ bracketImage bracket C D, bracket a b ∈ bracketImage bracket C D := by
    rintro a ha b hb
    obtain ⟨c₁, hc₁, d₁, hd₁, rfl⟩ := ha
    obtain ⟨c₂, hc₂, d₂, hd₂, rfl⟩ := hb
    refine ⟨c₁, hc₁, d₂, hd₂, ?_⟩
    apply (BowenRegularClosedPreparation.absorption f bracket hγ.le hε.le hdiag
      (by rw [← hα0]; linarith : 2 * (α 3 / 3) + α 2 / 3 ≤ γ)
      (hpair _ hc₁ _ hd₁) (hpair _ hc₂ _ hd₂) (hpair _ hc₁ _ hd₂) ?_).symm
    exact (hmod _ hσ hσγ).2 _ _ ((hdA _ ⟨_, hc₁, _, hd₁, rfl⟩
      _ ⟨_, hc₂, _, hd₂, rfl⟩).trans (by linarith))
  have hne : (bracketImage bracket C D).Nonempty := by
    obtain ⟨c,hc⟩ := hCne
    obtain ⟨d,hd⟩ := hDne
    exact ⟨bracket c d,c,hc,d,hd,rfl⟩
  have hdiam : Metric.diam (bracketImage bracket C D) ≤ α 3 := by
    apply Metric.diam_le_of_forall_dist_le (hαpos 3).le
    intro a ha b hb
    exact (hdA a ha b hb).trans (by linarith)
  have hprod := HolomorphicAnosov.Bowen.bowen_fact1_product_chart_g6
    f lam γ ε hlam.1 hlam.2 hγ hε α εmod
    (fun δ hδ hδγ ↦ (hmod δ hδ hδγ).1) hα0 hαpos hαrec hαmargin bracket
    (by
      intro a y z n hy hz
      rw [← BowenRegularClosedPreparation.pow_apply_iterate,
          ← BowenRegularClosedPreparation.pow_apply_iterate]
      exact hfact_s a y z n
        (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
          BowenRegularClosedPreparation.pow_apply_iterate]; exact hy k)
        (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
          BowenRegularClosedPreparation.pow_apply_iterate]; exact hz k))
    (by
      intro a y z n hy hz
      rw [← BowenRegularClosedPreparation.pow_apply_iterate,
          ← BowenRegularClosedPreparation.pow_apply_iterate]
      exact hfact_u a y z n
        (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
          BowenRegularClosedPreparation.pow_apply_iterate]; exact hy k)
        (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
          BowenRegularClosedPreparation.pow_apply_iterate]; exact hz k))
    (by
      intro a b hab
      obtain ⟨hs,hu⟩ := hbracket_mem a b hab
      refine ⟨bracket a b, ⟨?_,?_⟩, ?_⟩
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hs n
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hu n
      · intro z hz
        exact hbracket_unique a b z hab
          (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
            BowenRegularClosedPreparation.pow_apply_iterate]; exact hz.1 k)
          (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
            BowenRegularClosedPreparation.pow_apply_iterate]; exact hz.2 k))
    (by
      intro a b hab
      constructor
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
          (hbracket_mem a b hab).1 n
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
          (hbracket_mem a b hab).2 n)
    hbracket_cont
    (by
      intro δ hδ hδγ a b hab
      constructor
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
          ((hmod δ hδ hδγ).2 a b hab).1 n
      · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
          ((hmod δ hδ hδγ).2 a b hab).2 n)
  have hcompact : IsCompact (bracketImage bracket C D) := by
    have hp := (hCcompact.prod hDcompact).image_of_continuousOn
      ((hprod.1 _ hδ hδγ).mono (by
        rintro ⟨c,d⟩ ⟨hc,hd⟩
        exact (hcd _ hc _ hd).trans (by linarith)))
    convert hp using 1
    ext z
    simp only [bracketImage, mem_ofPred_eq, mem_image, mem_prod]
    constructor
    · rintro ⟨c,hc,d,hd,hz⟩
      exact ⟨(c,d),⟨hc,hd⟩,hz⟩
    · rintro ⟨⟨c,d⟩,⟨hc,hd⟩,hz⟩
      exact ⟨c,hc,d,hd,hz⟩
  let r : ℝ := (α 4 + α 2) / 2
  have hr4 : α 4 < r := by dsimp [r]; linarith
  have hr2 : r < α 2 := by dsimp [r]; linarith
  let U := unstablePlaque f γ x ∩ Metric.ball x r
  let V := stablePlaque f γ x ∩ Metric.ball x r
  have hUguard : U ⊆ unstablePlaque f (α 2) x := by
    rintro y ⟨hy,hyd⟩
    exact BowenRegularClosedPreparation.contraction_bound f.symm
      ⟨hlam.1.le,hlam.2.le⟩ hfact_u hy
      (BowenRegularClosedPreparation.self_mem f.symm hγ.le x)
      (le_of_lt ((Metric.mem_ball.mp hyd).trans hr2))
  have hVguard : V ⊆ stablePlaque f (α 2) x := by
    rintro y ⟨hy,hyd⟩
    exact BowenRegularClosedPreparation.contraction_bound f
      ⟨hlam.1.le,hlam.2.le⟩ hfact_s hy
      (BowenRegularClosedPreparation.self_mem f hγ.le x)
      (le_of_lt ((Metric.mem_ball.mp hyd).trans hr2))
  have hCU : C ⊆ U := by
    intro c hc
    exact ⟨BowenRegularClosedPreparation.plaque_mono f.symm (by rw [←hα0]; linarith)
      x (hCguard hc), Metric.mem_ball.mpr
        ((BowenRegularClosedPreparation.dist_le_of_mem f.symm (hCguard hc)).trans_lt hr4)⟩
  have hDV : D ⊆ V := by
    intro d hd
    exact ⟨BowenRegularClosedPreparation.plaque_mono f (by rw [←hα0]; linarith)
      x (hDguard hd), Metric.mem_ball.mpr
        ((BowenRegularClosedPreparation.dist_le_of_mem f (hDguard hd)).trans_lt hr4)⟩
  have hchart := hprod.2 x U V
    (by intro y hy n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate]
          using hUguard hy n)
    (by intro y hy n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate]
          using hVguard hy n)
    (by
      change IsOpen {u : {y | ∀n:ℕ,dist ((f.symm:X→X)^[n] y)
        ((f.symm:X→X)^[n] x) ≤ γ} | (u:X)∈U}
      have heq : {u : {y | ∀n:ℕ,dist ((f.symm:X→X)^[n] y)
        ((f.symm:X→X)^[n] x) ≤ γ} | (u:X)∈U} = Subtype.val ⁻¹' Metric.ball x r := by
        ext u
        simp only [U, mem_inter_iff, mem_preimage, mem_ofPred_eq]
        exact and_iff_right (by intro n; simpa only
          [BowenRegularClosedPreparation.pow_apply_iterate] using u.property n)
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val)
    (by
      change IsOpen {v : {y | ∀n:ℕ,dist ((f:X→X)^[n] y)
        ((f:X→X)^[n] x) ≤ γ} | (v:X)∈V}
      have heq : {v : {y | ∀n:ℕ,dist ((f:X→X)^[n] y)
        ((f:X→X)^[n] x) ≤ γ} | (v:X)∈V} = Subtype.val ⁻¹' Metric.ball x r := by
        ext v
        simp only [V, mem_inter_iff, mem_preimage, mem_ofPred_eq]
        exact and_iff_right (by intro n; simpa only
          [BowenRegularClosedPreparation.pow_apply_iterate] using v.property n)
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val)
  change IsOpen (bracketImage bracket U V) ∧
    ∃ h : Homeomorph
      ({u : {y | ∀n:ℕ,dist ((f.symm:X→X)^[n] y) ((f.symm:X→X)^[n] x) ≤ γ} // (u:X)∈U} ×
       {v : {y | ∀n:ℕ,dist ((f:X→X)^[n] y) ((f:X→X)^[n] x) ≤ γ} // (v:X)∈V})
      (bracketImage bracket U V),
      (∀p,(h p:X)=bracket p.1.val.val p.2.val.val) ∧
      (∀z,(h.symm z).1.val.val=bracket z x ∧
        (h.symm z).2.val.val=bracket x z) at hchart
  have hst : {y : X | ∀n : ℕ, dist ((f.symm : X → X)^[n] y)
      ((f.symm : X → X)^[n] x) ≤ γ} = unstablePlaque f γ x := by
    ext y
    simp only [unstablePlaque, BowenRegularClosedPreparation.pow_apply_iterate]
  have hss : {y : X | ∀n : ℕ, dist ((f : X → X)^[n] y)
      ((f : X → X)^[n] x) ≤ γ} = stablePlaque f γ x := by
    ext y
    simp only [stablePlaque, BowenRegularClosedPreparation.pow_apply_iterate]
  rw [hst, hss] at hchart
  change IsOpen (bracketImage bracket U V) ∧
    ∃ h : Homeomorph
      ({u : unstablePlaque f γ x // (u:X)∈U} × {v : stablePlaque f γ x // (v:X)∈V})
      (bracketImage bracket U V),
      (∀p,(h p:X)=bracket p.1.val.val p.2.val.val) ∧
      (∀z,(h.symm z).1.val.val=bracket z x ∧
        (h.symm z).2.val.val=bracket x z) at hchart
  obtain ⟨hUVopen,chart,hchart,hchartinv⟩ := hchart
  have hUopen : IsOpen {u : unstablePlaque f γ x | (u:X)∈U} := by
    have heq : {u : unstablePlaque f γ x | (u:X)∈U} =
        Subtype.val ⁻¹' Metric.ball x r := by
      ext u
      exact and_iff_right u.property
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hVopen : IsOpen {v : stablePlaque f γ x | (v:X)∈V} := by
    have heq : {v : stablePlaque f γ x | (v:X)∈V} =
        Subtype.val ⁻¹' Metric.ball x r := by
      ext v
      exact and_iff_right v.property
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  let Cu : Set {u : unstablePlaque f γ x // (u:X)∈U} :=
    {u | (u.val:X)∈C}
  let Dv : Set {v : stablePlaque f γ x // (v:X)∈V} :=
    {v | (v.val:X)∈D}
  have hCureg : Cu = closure (interior Cu) :=
    BowenRegularClosedPreparation.regular_preimage continuous_subtype_val
      hUopen.isOpenMap_subtype_val hCreg
  have hDvreg : Dv = closure (interior Dv) :=
    BowenRegularClosedPreparation.regular_preimage continuous_subtype_val
      hVopen.isOpenMap_subtype_val hDreg
  let chartMap := (Subtype.val : bracketImage bracket U V → X) ∘ chart
  have hchartcont : Continuous chartMap := continuous_subtype_val.comp chart.continuous
  have hchartopen : IsOpenMap chartMap :=
    hUVopen.isOpenMap_subtype_val.comp chart.isOpenMap
  have himage : chartMap '' (Cu ×ˢ Dv) = bracketImage bracket C D := by
    ext z
    constructor
    · rintro ⟨⟨c,d⟩,⟨hc,hd⟩,rfl⟩
      exact ⟨c.val.val,hc,d.val.val,hd,(hchart (c,d)).symm⟩
    · rintro ⟨c,hc,d,hd,rfl⟩
      let c' : {u : unstablePlaque f γ x // (u:X)∈U} := ⟨⟨c,(hCU hc).1⟩,hCU hc⟩
      let d' : {v : stablePlaque f γ x // (v:X)∈V} := ⟨⟨d,(hDV hd).1⟩,hDV hd⟩
      exact ⟨(c',d'),⟨hc,hd⟩,hchart (c',d')⟩
  have hcp : IsCompact (Cu ×ˢ Dv) := by
    apply (IsEmbedding.subtypeVal.comp chart.isEmbedding).isCompact_iff.mpr
    rw [himage]
    exact hcompact
  have hregular : bracketImage bracket C D = closure (interior (bracketImage bracket C D)) := by
    rw [←himage]
    exact BowenRegularClosedPreparation.regular_image hchartcont hchartopen
      (BowenRegularClosedPreparation.regular_product hCureg hDvreg) hcp
  have hcx : ∀c∈C, bracket c x = c := by
    intro c hc
    have hd := BowenRegularClosedPreparation.dist_le_of_mem f.symm (hCguard hc)
    have hm := (hmod _ hδ hδγ').2 c x (hd.trans (by linarith))
    exact BowenRegularClosedPreparation.unstable_bracket_self f bracket hγ.le hε.le
      ⟨hlam.1.le,hlam.2.le⟩ hdiag hfact_u
      (BowenRegularClosedPreparation.plaque_mono f.symm
        (by rw [←hα0]; linarith) x (hCguard hc)) hδγ' hm (by linarith)
  have hxd : ∀d∈D, bracket x d = d := by
    intro d hd
    have hh := BowenRegularClosedPreparation.dist_le_of_mem f (hDguard hd)
    have hm := (hmod _ hδ hδγ').2 x d (by rw [dist_comm]; exact hh.trans (by linarith))
    apply BowenRegularClosedPreparation.diagonal_separation f bracket hγ.le hε.le hdiag
    · apply BowenRegularClosedPreparation.contraction_bound f
        ⟨hlam.1.le,hlam.2.le⟩ hfact_s
        (BowenRegularClosedPreparation.plaque_mono f hδγ' x hm.1)
        (BowenRegularClosedPreparation.plaque_mono f
          (by rw [←hα0]; linarith) x (hDguard hd))
      have hd' := dist_triangle (bracket x d) x d
      have h1 := BowenRegularClosedPreparation.dist_le_of_mem f hm.1
      rw [dist_comm x d] at hd'
      linarith
    · exact BowenRegularClosedPreparation.plaque_mono f.symm hδγ' d hm.2
  have hcq : ∀ c∈C, ∀c₀∈C, ∀d₀∈D,
      bracket c (bracket c₀ d₀) = bracket c d₀ := by
    intro c hc c₀ hc₀ d₀ hd₀
    have hcxpair := (hmod _ hδ hδγ').2 c x
      ((BowenRegularClosedPreparation.dist_le_of_mem f.symm (hCguard hc)).trans
        (by linarith))
    have hdist : dist c (bracket c₀ d₀) ≤ 2 * α 4 + α 3 / 3 := by
      have hh := dist_triangle c c₀ (bracket c₀ d₀)
      have h1 := dist_triangle c x c₀
      have h2 := BowenRegularClosedPreparation.dist_le_of_mem f.symm (hCguard hc)
      have h3 := BowenRegularClosedPreparation.dist_le_of_mem f.symm (hCguard hc₀)
      have h4 := BowenRegularClosedPreparation.dist_le_of_mem f (hpair _ hc₀ _ hd₀).1
      rw [dist_comm x c₀] at h1
      rw [dist_comm c₀ (bracket c₀ d₀)] at hh
      linarith
    have houter := (hmod _ hσ hσγ).2 c (bracket c₀ d₀) (hdist.trans (by linarith))
    have hab := BowenRegularClosedPreparation.absorption f bracket hγ.le hε.le hdiag
      (by rw [←hα0]; linarith : 2*(α 3/3)+α 2/3≤γ)
      hcxpair (hpair _ hc₀ _ hd₀) (hpair _ hc _ hd₀)
      (by simpa only [hcx c hc] using houter)
    simpa only [hcx c hc] using hab
  have hqd : ∀ c₀∈C, ∀d₀∈D, ∀d∈D,
      bracket (bracket c₀ d₀) d = bracket c₀ d := by
    intro c₀ hc₀ d₀ hd₀ d hd
    have hxdpair := (hmod _ hδ hδγ').2 x d (by
      rw [dist_comm]
      exact (BowenRegularClosedPreparation.dist_le_of_mem f (hDguard hd)).trans
        (by linarith))
    have hdist : dist (bracket c₀ d₀) d ≤ 2 * α 4 + α 3 / 3 := by
      have hh := dist_triangle (bracket c₀ d₀) d₀ d
      have h1 := dist_triangle d₀ x d
      have h2 := BowenRegularClosedPreparation.dist_le_of_mem f (hDguard hd₀)
      have h3 := BowenRegularClosedPreparation.dist_le_of_mem f (hDguard hd)
      have h4 := BowenRegularClosedPreparation.dist_le_of_mem f.symm (hpair _ hc₀ _ hd₀).2
      rw [dist_comm x d] at h1
      linarith
    have houter := (hmod _ hσ hσγ).2 (bracket c₀ d₀) d (hdist.trans (by linarith))
    have hab := BowenRegularClosedPreparation.absorption f bracket hγ.le hε.le hdiag
      (by rw [←hα0]; linarith : 2*(α 3/3)+α 2/3≤γ)
      (hpair _ hc₀ _ hd₀) hxdpair (hpair _ hc₀ _ hd)
      (by simpa only [hxd d hd] using houter)
    simpa only [hxd d hd] using hab
  have huslice : ∀ q∈bracketImage bracket C D,
      bracketImage bracket C D ∩ unstablePlaque f γ q = bracketImage bracket C {q} := by
    rintro q ⟨c₀,hc₀,d₀,hd₀,rfl⟩
    ext a
    constructor
    · rintro ⟨⟨c,hc,d,hd,rfl⟩,ha⟩
      have hstable : bracket c d₀ ∈ stablePlaque f γ (bracket c d) :=
        BowenRegularClosedPreparation.plaque_mono f (by linarith : α 3/3+α 3/3≤γ) _
          (BowenRegularClosedPreparation.plaque_triangle f
            (hpair _ hc _ hd₀).1 (BowenRegularClosedPreparation.plaque_symm f
              (hpair _ hc _ hd).1))
      have hq : bracket c d₀ ∈ unstablePlaque f (α 3/3+α 3/3) (bracket c₀ d₀) :=
        BowenRegularClosedPreparation.plaque_triangle f.symm
          (hpair _ hc _ hd₀).2 (BowenRegularClosedPreparation.plaque_symm f.symm
            (hpair _ hc₀ _ hd₀).2)
      have haq := BowenRegularClosedPreparation.contraction_bound f.symm
        ⟨hlam.1.le,hlam.2.le⟩ hfact_u ha
        (BowenRegularClosedPreparation.self_mem f.symm hγ.le (bracket c₀ d₀))
        ((hdA _ ⟨_,hc,_,hd,rfl⟩ _ ⟨_,hc₀,_,hd₀,rfl⟩).trans (by linarith :
          2*(α 3/3)+2*α 4≤α 3))
      have hunstable : bracket c d₀ ∈ unstablePlaque f γ (bracket c d) :=
        BowenRegularClosedPreparation.plaque_mono f.symm
          (by linarith : α 3/3+α 3/3+α 3≤γ) _
          (BowenRegularClosedPreparation.plaque_triangle f.symm hq
            (BowenRegularClosedPreparation.plaque_symm f.symm haq))
      have heq := BowenRegularClosedPreparation.diagonal_separation f bracket
        hγ.le hε.le hdiag hstable hunstable
      exact ⟨c,hc,bracket c₀ d₀,rfl,(hcq c hc c₀ hc₀ d₀ hd₀).trans heq⟩
    · rintro ⟨c,hc,d,hd,rfl⟩
      have hd' : d = bracket c₀ d₀ := hd
      subst d
      rw [hcq c hc c₀ hc₀ d₀ hd₀]
      exact ⟨⟨c,hc,d₀,hd₀,rfl⟩,
        BowenRegularClosedPreparation.plaque_mono f.symm (by linarith : α 3/3+α 3/3≤γ) _
          (BowenRegularClosedPreparation.plaque_triangle f.symm
            (hpair _ hc _ hd₀).2 (BowenRegularClosedPreparation.plaque_symm f.symm
              (hpair _ hc₀ _ hd₀).2))⟩
  have hsslice : ∀ q∈bracketImage bracket C D,
      bracketImage bracket C D ∩ stablePlaque f γ q = bracketImage bracket {q} D := by
    rintro q ⟨c₀,hc₀,d₀,hd₀,rfl⟩
    ext a
    constructor
    · rintro ⟨⟨c,hc,d,hd,rfl⟩,ha⟩
      have hu : bracket c₀ d ∈ unstablePlaque f γ (bracket c d) :=
        BowenRegularClosedPreparation.plaque_mono f.symm (by linarith : α 3/3+α 3/3≤γ) _
          (BowenRegularClosedPreparation.plaque_triangle f.symm
            (hpair _ hc₀ _ hd).2 (BowenRegularClosedPreparation.plaque_symm f.symm
              (hpair _ hc _ hd).2))
      have hq : bracket c₀ d ∈ stablePlaque f (α 3/3+α 3/3) (bracket c₀ d₀) :=
        BowenRegularClosedPreparation.plaque_triangle f
          (hpair _ hc₀ _ hd).1 (BowenRegularClosedPreparation.plaque_symm f
            (hpair _ hc₀ _ hd₀).1)
      have haq := BowenRegularClosedPreparation.contraction_bound f
        ⟨hlam.1.le,hlam.2.le⟩ hfact_s ha
        (BowenRegularClosedPreparation.self_mem f hγ.le (bracket c₀ d₀))
        ((hdA _ ⟨_,hc,_,hd,rfl⟩ _ ⟨_,hc₀,_,hd₀,rfl⟩).trans (by linarith :
          2*(α 3/3)+2*α 4≤α 3))
      have hs : bracket c₀ d ∈ stablePlaque f γ (bracket c d) :=
        BowenRegularClosedPreparation.plaque_mono f
          (by linarith : α 3/3+α 3/3+α 3≤γ) _
          (BowenRegularClosedPreparation.plaque_triangle f hq
            (BowenRegularClosedPreparation.plaque_symm f haq))
      have heq := BowenRegularClosedPreparation.diagonal_separation f bracket
        hγ.le hε.le hdiag hs hu
      exact ⟨bracket c₀ d₀,rfl,d,hd,(hqd c₀ hc₀ d₀ hd₀ d hd).trans heq⟩
    · rintro ⟨c,hc,d,hd,rfl⟩
      have hc' : c = bracket c₀ d₀ := hc
      subst c
      rw [hqd c₀ hc₀ d₀ hd₀ d hd]
      exact ⟨⟨c₀,hc₀,d,hd,rfl⟩,
        BowenRegularClosedPreparation.plaque_mono f (by linarith : α 3/3+α 3/3≤γ) _
          (BowenRegularClosedPreparation.plaque_triangle f
            (hpair _ hc₀ _ hd).1 (BowenRegularClosedPreparation.plaque_symm f
              (hpair _ hc₀ _ hd₀).1))⟩
  have hrebase : ∀y,dist x y≤α 3 →
      (∀U : Set X,U⊆unstablePlaque f (α 2) x →
        IsOpen ((Subtype.val : unstablePlaque f γ x → X) ⁻¹' U) →
        let B := (fun u ↦ bracket u y) '' U
        B⊆unstablePlaque f γ y ∧
        IsOpen ((Subtype.val : unstablePlaque f γ y → X) ⁻¹' B) ∧
        ∃h : Homeomorph {u : unstablePlaque f γ x // (u:X)∈U}
          {w : unstablePlaque f γ y // (w:X)∈B},
          (∀u,(h u).val.val=bracket u.val.val y) ∧
          (∀w,(h.symm w).val.val=bracket w.val.val x)) ∧
      (∀V : Set X,V⊆stablePlaque f (α 2) x →
        IsOpen ((Subtype.val : stablePlaque f γ x → X) ⁻¹' V) →
        let B := (fun v ↦ bracket y v) '' V
        B⊆stablePlaque f γ y ∧
        IsOpen ((Subtype.val : stablePlaque f γ y → X) ⁻¹' B) ∧
        ∃h : Homeomorph {v : stablePlaque f γ x // (v:X)∈V}
          {w : stablePlaque f γ y // (w:X)∈B},
          (∀v,(h v).val.val=bracket y v.val.val) ∧
          (∀w,(h.symm w).val.val=bracket x w.val.val)) := by
    intro y hxy
    have hh := HolomorphicAnosov.Bowen.bowen_fact1_plaque_rebase_g6
      f lam γ ε hlam.1 hlam.2 hγ hε α εmod
      (fun δ hδ hδγ ↦ (hmod δ hδ hδγ).1) hα0 hαpos hαrec hαmargin bracket
      (by
        intro a y z n hy hz
        rw [← BowenRegularClosedPreparation.pow_apply_iterate,
            ← BowenRegularClosedPreparation.pow_apply_iterate]
        exact hfact_s a y z n
          (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
            BowenRegularClosedPreparation.pow_apply_iterate]; exact hy k)
          (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
            BowenRegularClosedPreparation.pow_apply_iterate]; exact hz k))
      (by
        intro a y z n hy hz
        rw [← BowenRegularClosedPreparation.pow_apply_iterate,
            ← BowenRegularClosedPreparation.pow_apply_iterate]
        exact hfact_u a y z n
          (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
            BowenRegularClosedPreparation.pow_apply_iterate]; exact hy k)
          (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
            BowenRegularClosedPreparation.pow_apply_iterate]; exact hz k))
      (by
        intro a b hab
        obtain ⟨hs,hu⟩ := hbracket_mem a b hab
        refine ⟨bracket a b, ⟨?_,?_⟩, ?_⟩
        · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hs n
        · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using hu n
        · intro z hz
          exact hbracket_unique a b z hab
            (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
              BowenRegularClosedPreparation.pow_apply_iterate]; exact hz.1 k)
            (fun k ↦ by rw [BowenRegularClosedPreparation.pow_apply_iterate,
              BowenRegularClosedPreparation.pow_apply_iterate]; exact hz.2 k))
      (by
        intro a b hab
        constructor
        · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
            (hbracket_mem a b hab).1 n
        · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
            (hbracket_mem a b hab).2 n)
      hbracket_cont
      (by
        intro δ hδ hδγ a b hab
        constructor
        · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
            ((hmod δ hδ hδγ).2 a b hab).1 n
        · intro n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate] using
            ((hmod δ hδ hδγ).2 a b hab).2 n) x y hxy
    change
      (∀U : Set X,U⊆{z | ∀n : ℕ,dist ((f.symm:X→X)^[n] z) ((f.symm:X→X)^[n] x)≤α 2} →
        IsOpen {u : {z | ∀n : ℕ,dist ((f.symm:X→X)^[n] z) ((f.symm:X→X)^[n] x)≤γ} | (u:X)∈U} →
        let B := (fun u ↦ bracket u y) '' U
        B⊆{z | ∀n : ℕ,dist ((f.symm:X→X)^[n] z) ((f.symm:X→X)^[n] y)≤γ} ∧
        IsOpen {w : {z | ∀n : ℕ,dist ((f.symm:X→X)^[n] z) ((f.symm:X→X)^[n] y)≤γ} | (w:X)∈B} ∧
        ∃h : Homeomorph
          {u : {z | ∀n : ℕ,dist ((f.symm:X→X)^[n] z) ((f.symm:X→X)^[n] x)≤γ} // (u:X)∈U}
          {w : {z | ∀n : ℕ,dist ((f.symm:X→X)^[n] z) ((f.symm:X→X)^[n] y)≤γ} // (w:X)∈B},
          (∀u,(h u).val.val=bracket u.val.val y) ∧
          (∀w,(h.symm w).val.val=bracket w.val.val x)) ∧
      (∀V : Set X,V⊆{z | ∀n : ℕ,dist ((f:X→X)^[n] z) ((f:X→X)^[n] x)≤α 2} →
        IsOpen {v : {z | ∀n : ℕ,dist ((f:X→X)^[n] z) ((f:X→X)^[n] x)≤γ} | (v:X)∈V} →
        let B := (fun v ↦ bracket y v) '' V
        B⊆{z | ∀n : ℕ,dist ((f:X→X)^[n] z) ((f:X→X)^[n] y)≤γ} ∧
        IsOpen {w : {z | ∀n : ℕ,dist ((f:X→X)^[n] z) ((f:X→X)^[n] y)≤γ} | (w:X)∈B} ∧
        ∃h : Homeomorph
          {v : {z | ∀n : ℕ,dist ((f:X→X)^[n] z) ((f:X→X)^[n] x)≤γ} // (v:X)∈V}
          {w : {z | ∀n : ℕ,dist ((f:X→X)^[n] z) ((f:X→X)^[n] y)≤γ} // (w:X)∈B},
          (∀v,(h v).val.val=bracket y v.val.val) ∧
          (∀w,(h.symm w).val.val=bracket x w.val.val)) at hh
    have hsE : ∀a δ,{z : X | ∀n : ℕ,dist ((f:X→X)^[n] z) ((f:X→X)^[n] a)≤δ} =
        stablePlaque f δ a := by
      intro a δ; ext z; simp only [stablePlaque,BowenRegularClosedPreparation.pow_apply_iterate]
    have huE : ∀a δ,{z : X | ∀n : ℕ,dist ((f.symm:X→X)^[n] z) ((f.symm:X→X)^[n] a)≤δ} =
        unstablePlaque f δ a := by
      intro a δ; ext z; simp only [unstablePlaque,BowenRegularClosedPreparation.pow_apply_iterate]
    rw [huE x γ, hsE x γ, huE y γ, hsE y γ,
      huE x (α 2), hsE x (α 2)] at hh
    exact hh
  have himgu : ∀c₀∈C,∀d₀∈D,
      bracketImage bracket C D ∩ unstablePlaque f γ (bracket c₀ d₀) =
        (fun c ↦ bracket c d₀) '' C := by
    intro c₀ hc₀ d₀ hd₀
    rw [huslice _ ⟨c₀,hc₀,d₀,hd₀,rfl⟩]
    ext z
    constructor
    · rintro ⟨c,hc,q,hq,rfl⟩
      subst q
      exact ⟨c,hc,(hcq c hc c₀ hc₀ d₀ hd₀).symm⟩
    · rintro ⟨c,hc,rfl⟩
      exact ⟨c,hc,bracket c₀ d₀,rfl,hcq c hc c₀ hc₀ d₀ hd₀⟩
  have himgs : ∀c₀∈C,∀d₀∈D,
      bracketImage bracket C D ∩ stablePlaque f γ (bracket c₀ d₀) =
        (fun d ↦ bracket c₀ d) '' D := by
    intro c₀ hc₀ d₀ hd₀
    rw [hsslice _ ⟨c₀,hc₀,d₀,hd₀,rfl⟩]
    ext z
    constructor
    · rintro ⟨q,hq,d,hd,rfl⟩
      subst q
      exact ⟨d,hd,(hqd c₀ hc₀ d₀ hd₀ d hd).symm⟩
    · rintro ⟨d,hd,rfl⟩
      exact ⟨bracket c₀ d₀,rfl,d,hd,hqd c₀ hc₀ d₀ hd₀ d hd⟩
  have huInterior : ∀c∈C,∀d∈D,
      bracket c d∈relativeInterior (unstablePlaque f γ (bracket c d))
        (bracketImage bracket C D ∩ unstablePlaque f γ (bracket c d)) ↔
        c∈relativeInterior (unstablePlaque f γ x) C := by
    intro c hc d hd
    have hdr : dist x d ≤ α 3 := by
      rw [dist_comm]
      exact (BowenRegularClosedPreparation.dist_le_of_mem f (hDguard hd)).trans h34.le
    obtain ⟨hBguard,hBopen,rb,hrb,hrbinv⟩ := (hrebase d hdr).1 U hUguard hUopen
    have ht := BowenRegularClosedPreparation.rebase_interior
      (unstablePlaque f γ x) (unstablePlaque f γ d) U C (fun c ↦ bracket c d)
      (fun _ hu ↦ hu.1) hCU hBguard hUopen hBopen rb hrb c hc
    rw [himgu c hc d hd]
    have hqd := (hpair _ hc _ hd).2
    have hη : 0<(γ-α 3/3)/2 := by linarith
    have hloc := BowenRegularClosedPreparation.plaque_local_agreement f.symm
      ⟨hlam.1.le,hlam.2.le⟩ hfact_u hγ.le hδγ'
      (by linarith : (γ-α 3/3)/2+α 3/3≤γ) hqd
    have hi := BowenRegularClosedPreparation.relativeInterior_local
      (unstablePlaque f γ (bracket c d)) (unstablePlaque f γ d)
      ((fun c ↦ bracket c d) '' C) (bracket c d)
      (BowenRegularClosedPreparation.self_mem f.symm hγ.le _)
      (BowenRegularClosedPreparation.plaque_mono f.symm hδγ' d hqd) hη hloc
    exact hi.trans ht
  have hsInterior : ∀c∈C,∀d∈D,
      bracket c d∈relativeInterior (stablePlaque f γ (bracket c d))
        (bracketImage bracket C D ∩ stablePlaque f γ (bracket c d)) ↔
        d∈relativeInterior (stablePlaque f γ x) D := by
    intro c hc d hd
    have hcr : dist x c ≤ α 3 := by
      rw [dist_comm]
      exact (BowenRegularClosedPreparation.dist_le_of_mem f.symm (hCguard hc)).trans h34.le
    obtain ⟨hBguard,hBopen,rb,hrb,hrbinv⟩ := (hrebase c hcr).2 V hVguard hVopen
    have ht := BowenRegularClosedPreparation.rebase_interior
      (stablePlaque f γ x) (stablePlaque f γ c) V D (fun d ↦ bracket c d)
      (fun _ hv ↦ hv.1) hDV hBguard hVopen hBopen rb hrb d hd
    rw [himgs c hc d hd]
    have hqc := (hpair _ hc _ hd).1
    have hη : 0<(γ-α 3/3)/2 := by linarith
    have hloc := BowenRegularClosedPreparation.plaque_local_agreement f
      ⟨hlam.1.le,hlam.2.le⟩ hfact_s hγ.le hδγ'
      (by linarith : (γ-α 3/3)/2+α 3/3≤γ) hqc
    have hi := BowenRegularClosedPreparation.relativeInterior_local
      (stablePlaque f γ (bracket c d)) (stablePlaque f γ c)
      ((fun d ↦ bracket c d) '' D) (bracket c d)
      (BowenRegularClosedPreparation.self_mem f hγ.le _)
      (BowenRegularClosedPreparation.plaque_mono f hδγ' c hqc) hη hloc
    exact hi.trans ht
  have hCplaque : C⊆unstablePlaque f γ x := fun _ hc ↦ (hCU hc).1
  have hDplaque : D⊆stablePlaque f γ x := fun _ hd ↦ (hDV hd).1
  have hCfront := BowenRegularClosedPreparation.relativeFrontier_closed
    (unstablePlaque f γ x) C hCplaque
    (hCcompact.isClosed.preimage continuous_subtype_val)
  have hDfront := BowenRegularClosedPreparation.relativeFrontier_closed
    (stablePlaque f γ x) D hDplaque
    (hDcompact.isClosed.preimage continuous_subtype_val)
  have hboundaryS : {q∈bracketImage bracket C D | q∉relativeInterior
      (unstablePlaque f γ q) (bracketImage bracket C D ∩ unstablePlaque f γ q)} =
      bracketImage bracket (relativeFrontier (unstablePlaque f γ x) C) D := by
    ext q
    constructor
    · rintro ⟨⟨c,hc,d,hd,rfl⟩,hq⟩
      exact ⟨c,(hCfront c).mpr ⟨hc,(huInterior c hc d hd).not.mp hq⟩,d,hd,rfl⟩
    · rintro ⟨c,hc,d,hd,rfl⟩
      obtain ⟨hc,hni⟩ := (hCfront c).mp hc
      exact ⟨⟨c,hc,d,hd,rfl⟩,(huInterior c hc d hd).not.mpr hni⟩
  have hboundaryU : {q∈bracketImage bracket C D | q∉relativeInterior
      (stablePlaque f γ q) (bracketImage bracket C D ∩ stablePlaque f γ q)} =
      bracketImage bracket C (relativeFrontier (stablePlaque f γ x) D) := by
    ext q
    constructor
    · rintro ⟨⟨c,hc,d,hd,rfl⟩,hq⟩
      exact ⟨c,hc,d,(hDfront d).mpr ⟨hd,(hsInterior c hc d hd).not.mp hq⟩,rfl⟩
    · rintro ⟨c,hc,d,hd,rfl⟩
      obtain ⟨hd,hni⟩ := (hDfront d).mp hd
      exact ⟨⟨c,hc,d,hd,rfl⟩,(hsInterior c hc d hd).not.mpr hni⟩
  have hinterior : ∀q∈bracketImage bracket C D,
      q∈interior (bracketImage bracket C D) ↔
        q∈relativeInterior (unstablePlaque f γ q)
          (bracketImage bracket C D ∩ unstablePlaque f γ q) ∧
        q∈relativeInterior (stablePlaque f γ q)
          (bracketImage bracket C D ∩ stablePlaque f γ q) := by
    intro q hq
    constructor
    · intro hi
      obtain ⟨η,hη,hηA⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
      constructor
      · rw [BowenRegularClosedPreparation.relativeInterior_ball (unstablePlaque f γ q) _ q
          (BowenRegularClosedPreparation.self_mem f.symm hγ.le q)]
        exact ⟨η,hη,fun z hz hd ↦ ⟨hηA (Metric.mem_ball.mpr hd),hz⟩⟩
      · rw [BowenRegularClosedPreparation.relativeInterior_ball _ _ q
          (BowenRegularClosedPreparation.self_mem f hγ.le q)]
        exact ⟨η,hη,fun z hz hd ↦ ⟨hηA (Metric.mem_ball.mpr hd),hz⟩⟩
    · rintro ⟨hiu,his⟩
      let Uq := relativeInterior (unstablePlaque f γ q)
        (bracketImage bracket C D ∩ unstablePlaque f γ q) ∩ Metric.ball q (α 2)
      let Vq := relativeInterior (stablePlaque f γ q)
        (bracketImage bracket C D ∩ stablePlaque f γ q) ∩ Metric.ball q (α 2)
      have hUq : Uq⊆unstablePlaque f (α 2) q := by
        intro y hy
        have hs := (BowenRegularClosedPreparation.relativeInterior_subset _ _ hy.1).1
        exact BowenRegularClosedPreparation.contraction_bound f.symm
          ⟨hlam.1.le,hlam.2.le⟩ hfact_u hs
          (BowenRegularClosedPreparation.self_mem f.symm hγ.le q)
          (Metric.mem_ball.mp hy.2).le
      have hVq : Vq⊆stablePlaque f (α 2) q := by
        intro y hy
        have hs := (BowenRegularClosedPreparation.relativeInterior_subset _ _ hy.1).1
        exact BowenRegularClosedPreparation.contraction_bound f
          ⟨hlam.1.le,hlam.2.le⟩ hfact_s hs
          (BowenRegularClosedPreparation.self_mem f hγ.le q)
          (Metric.mem_ball.mp hy.2).le
      have hoUq : IsOpen ((Subtype.val : unstablePlaque f γ q → X) ⁻¹' Uq) := by
        dsimp only [Uq]
        rw [Set.preimage_inter,BowenRegularClosedPreparation.preimage_relativeInterior]
        exact isOpen_interior.inter (Metric.isOpen_ball.preimage continuous_subtype_val)
      have hoVq : IsOpen ((Subtype.val : stablePlaque f γ q → X) ⁻¹' Vq) := by
        dsimp only [Vq]
        rw [Set.preimage_inter,BowenRegularClosedPreparation.preimage_relativeInterior]
        exact isOpen_interior.inter (Metric.isOpen_ball.preimage continuous_subtype_val)
      have huEq : {y : X | ∀n : ℕ, dist ((f.symm : X→X)^[n] y)
          ((f.symm : X→X)^[n] q)≤γ} = unstablePlaque f γ q := by
        ext y; simp only [unstablePlaque,BowenRegularClosedPreparation.pow_apply_iterate]
      have hsEq : {y : X | ∀n : ℕ, dist ((f : X→X)^[n] y)
          ((f : X→X)^[n] q)≤γ} = stablePlaque f γ q := by
        ext y; simp only [stablePlaque,BowenRegularClosedPreparation.pow_apply_iterate]
      have hpc := hprod.2 q Uq Vq
        (by intro y hy n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate]
              using hUq hy n)
        (by intro y hy n; simpa only [BowenRegularClosedPreparation.pow_apply_iterate]
              using hVq hy n)
        (by
          change IsOpen {u : {y : X | ∀n : ℕ,dist ((f.symm:X→X)^[n] y)
            ((f.symm:X→X)^[n] q)≤γ} | (u:X)∈Uq}
          rw [huEq]
          exact hoUq)
        (by
          change IsOpen {v : {y : X | ∀n : ℕ,dist ((f:X→X)^[n] y)
            ((f:X→X)^[n] q)≤γ} | (v:X)∈Vq}
          rw [hsEq]
          exact hoVq)
      have hqU : q∈Uq := ⟨hiu,Metric.mem_ball.mpr (by simpa using hp2)⟩
      have hqV : q∈Vq := ⟨his,Metric.mem_ball.mpr (by simpa using hp2)⟩
      have hbqq : bracket q q=q :=
        (hbracket_unique q q q (by simpa using hε.le)
          (BowenRegularClosedPreparation.self_mem f hγ.le q)
          (BowenRegularClosedPreparation.self_mem f.symm hγ.le q)).symm
      have hqO : q∈bracketImage bracket Uq Vq := ⟨q,hqU,q,hqV,hbqq⟩
      have hOA : bracketImage bracket Uq Vq ⊆ bracketImage bracket C D := by
        rintro z ⟨u,hu,v,hv,rfl⟩
        exact hAclosed u ((BowenRegularClosedPreparation.relativeInterior_subset _ _ hu.1).2).1
          v ((BowenRegularClosedPreparation.relativeInterior_subset _ _ hv.1).2).1
      exact mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hpc.1.mem_nhds hqO) hOA)
  refine ⟨hne,hcompact,hAclosed,hdiam,hregular,huslice,hsslice,hboundaryS,hboundaryU,?_⟩
  ext q
  rw [frontier,hcompact.isClosed.closure_eq]
  change (q∈bracketImage bracket C D ∧ q∉interior (bracketImage bracket C D)) ↔
    (q∈bracketImage bracket C D ∧ q∉relativeInterior (unstablePlaque f γ q)
      (bracketImage bracket C D ∩ unstablePlaque f γ q)) ∨
    (q∈bracketImage bracket C D ∧ q∉relativeInterior (stablePlaque f γ q)
      (bracketImage bracket C D ∩ stablePlaque f γ q))
  by_cases hq : q∈bracketImage bracket C D
  · rw [hinterior q hq]
    tauto
  · tauto


