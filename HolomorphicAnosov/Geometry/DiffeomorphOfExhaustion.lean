import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Analysis.Complex.ConnectedCurveHolomorphicIdentity

/-! Compatible smooth coordinate maps on increasing open domains exhausting both manifolds glue to a
diffeomorphism. Holomorphic compatibility can be obtained from agreement of germs. (Zhang, Lemma
2.7, p.9, Eq. (18)) -/

open Set Filter
open scoped Manifold ContDiff Topology

namespace HolomorphicAnosov

/-- Compatible partial diffeomorphisms with increasing sources and targets covering both manifolds
glue to a diffeomorphism. (Zhang, Lemma 2.7, p.9, Eq. (18)) -/
theorem diffeomorph_of_exhaustion
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N] (k : ℕ∞ω)
    (e : ℕ → OpenPartialHomeomorph M N)
    (hsource : Monotone fun n ↦ (e n).source)
    (hcompat : ∀ m n, m ≤ n → EqOn (e n) (e m) (e m).source)
    (hcover : ∀ x, ∃ n, x ∈ (e n).source)
    (hcover' : ∀ y, ∃ n, y ∈ (e n).target)
    (hsmooth : ∀ n, ContMDiffOn I J k (e n) (e n).source)
    (hsmooth' : ∀ n, ContMDiffOn J I k (e n).symm (e n).target) :
    ∃ φ : Diffeomorph I J M N k, ∀ n, EqOn φ (e n) (e n).source := by
  classical
  have htarget : Monotone fun n ↦ (e n).target := by
    intro m n hmn y hy
    have hx := (e m).map_target hy
    have heq := hcompat m n hmn hx
    rw [(e m).right_inv hy] at heq
    exact heq ▸ (e n).map_source (hsource hmn hx)
  have hinv : ∀ m n, m ≤ n → EqOn (e n).symm (e m).symm (e m).target := by
    intro m n hmn y hy
    apply (e n).injOn ((e n).map_target (htarget hmn hy))
      (hsource hmn ((e m).map_target hy))
    rw [(e n).right_inv (htarget hmn hy), hcompat m n hmn ((e m).map_target hy),
      (e m).right_inv hy]
  let F : M → N := fun x ↦ e (Classical.choose (hcover x)) x
  let G : N → M := fun y ↦ (e (Classical.choose (hcover' y))).symm y
  have hF : ∀ n, EqOn F (e n) (e n).source := by
    intro n x hx
    let m := Classical.choose (hcover x)
    have hm : x ∈ (e m).source := Classical.choose_spec (hcover x)
    exact (hcompat m (max m n) (le_max_left _ _) hm).symm.trans
      (hcompat n (max m n) (le_max_right _ _) hx)
  have hG : ∀ n, EqOn G (e n).symm (e n).target := by
    intro n y hy
    let m := Classical.choose (hcover' y)
    have hm : y ∈ (e m).target := Classical.choose_spec (hcover' y)
    exact (hinv m (max m n) (le_max_left _ _) hm).symm.trans
      (hinv n (max m n) (le_max_right _ _) hy)
  refine ⟨{
    toEquiv := {
      toFun := F
      invFun := G
      left_inv := ?_
      right_inv := ?_ }
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }, hF⟩
  · intro x
    obtain ⟨n, hn⟩ := hcover x
    rw [hF n hn, hG n ((e n).map_source hn), (e n).left_inv hn]
  · intro y
    obtain ⟨n, hn⟩ := hcover' y
    rw [hG n hn, hF n ((e n).map_target hn), (e n).right_inv hn]
  · intro x
    obtain ⟨n, hn⟩ := hcover x
    apply ((hsmooth n x hn).contMDiffAt ((e n).open_source.mem_nhds hn)).congr_of_eventuallyEq
    exact Filter.eventuallyEq_of_mem ((e n).open_source.mem_nhds hn) (hF n)
  · intro y
    obtain ⟨n, hn⟩ := hcover' y
    apply ((hsmooth' n y hn).contMDiffAt ((e n).open_target.mem_nhds hn)).congr_of_eventuallyEq
    exact Filter.eventuallyEq_of_mem ((e n).open_target.mem_nhds hn) (hG n)

/-- Holomorphic maps into a complex line agree on a connected open set if their germs agree at one
point. (Zhang, Lemma 2.7) -/
theorem line_holomorphic_eqOn_of_germ
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 1) M]
    [IsManifold (complexModel 1) ∞ M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : E ≃L[ℂ] ComplexModel 1)
    (f g : M → E) {W : Set M} (hW : IsOpen W) (hconnected : IsPreconnected W)
    {x : M} (hx : x ∈ W)
    (hf : ContMDiffOn (complexModel 1) 𝓘(ℂ, E) ∞ f W)
    (hg : ContMDiffOn (complexModel 1) 𝓘(ℂ, E) ∞ g W)
    (heq : f =ᶠ[𝓝 x] g) : EqOn f g W := by
  let U : TopologicalSpace.Opens M := ⟨W, hW⟩
  let xU : U := ⟨x, hx⟩
  let : ConnectedSpace U := Subtype.connectedSpace ⟨⟨x, hx⟩, hconnected⟩
  have hcf : ContMDiff (complexModel 1) (complexModel 1) ∞
      (fun p : U ↦ c (f p)) := by
    intro p
    apply (contMDiffAt_subtype_iff (f := fun q ↦ c (f q))).mpr
    exact c.contDiff.contMDiff.contMDiffAt.comp _
      ((hf p p.property).contMDiffAt (hW.mem_nhds p.property))
  have hcg : ContMDiff (complexModel 1) (complexModel 1) ∞
      (fun p : U ↦ c (g p)) := by
    intro p
    apply (contMDiffAt_subtype_iff (f := fun q ↦ c (g q))).mpr
    exact c.contDiff.contMDiff.contMDiffAt.comp _
      ((hg p p.property).contMDiffAt (hW.mem_nhds p.property))
  have hlocal : (fun p : U ↦ c (f p)) =ᶠ[𝓝 xU] (fun p : U ↦ c (g p)) :=
    (show Tendsto (Subtype.val : U → M) (𝓝 xU) (𝓝 x) from
      continuous_subtype_val.continuousAt.tendsto).eventually
        (heq.mono (fun p hp ↦ congrArg c hp))
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.mp hlocal
  have h := Ghys.connected_curve_holomorphic_eq_of_open_germ
    _ _ hcf hcg V hVo ⟨xU, hxV⟩ hV
  exact fun p hp ↦ c.injective (congrFun h (⟨p, hp⟩ : U))

/-- Holomorphic chart exhaustions on curves glue to a biholomorphism when their germs agree at a
common center and their sources are connected. (Zhang, Lemma 2.7, p.9) -/
theorem biholomorph_of_exhaustion_of_germs
    {M N : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 1) M]
    [IsManifold (complexModel 1) ∞ M]
    [TopologicalSpace N] [T2Space N] [ChartedSpace (ComplexModel 1) N]
    [IsManifold (complexModel 1) ∞ N]
    (e : ℕ → OpenPartialHomeomorph M N) (x : M)
    (hx : x ∈ (e 0).source)
    (hsource : Monotone fun n ↦ (e n).source)
    (hconnected : ∀ n, IsPreconnected (e n).source)
    (hgerm : ∀ n, (e n : M → N) =ᶠ[𝓝 x] e 0)
    (hcover : ∀ p, ∃ n, p ∈ (e n).source)
    (hcover' : ∀ y, ∃ n, y ∈ (e n).target)
    (hsmooth : ∀ n, ContMDiffOn (complexModel 1) (complexModel 1) ∞
      (e n) (e n).source)
    (hsmooth' : ∀ n, ContMDiffOn (complexModel 1) (complexModel 1) ∞
      (e n).symm (e n).target) :
    ∃ φ : Diffeomorph (complexModel 1) (complexModel 1) M N ∞,
      ∀ n, EqOn φ (e n) (e n).source := by
  apply diffeomorph_of_exhaustion (complexModel 1) (complexModel 1) ∞ e hsource
    _ hcover hcover' hsmooth hsmooth'
  intro m n hmn
  let U : TopologicalSpace.Opens M := ⟨(e m).source, (e m).open_source⟩
  have hxU : x ∈ U := hsource (Nat.zero_le m) hx
  let xU : U := ⟨x, hxU⟩
  have : ConnectedSpace U := Subtype.connectedSpace ⟨⟨x, hxU⟩, hconnected m⟩
  have hn : ContMDiff (complexModel 1) (complexModel 1) ∞
      (fun p : U ↦ e n p) := by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact (hsmooth n p (hsource hmn p.property)).contMDiffAt
      ((e n).open_source.mem_nhds (hsource hmn p.property))
  have hm : ContMDiff (complexModel 1) (complexModel 1) ∞
      (fun p : U ↦ e m p) := by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact (hsmooth m p p.property).contMDiffAt ((e m).open_source.mem_nhds p.property)
  have hnm : (fun p : U ↦ e n p) =ᶠ[𝓝 xU] (fun p : U ↦ e m p) :=
    (show Tendsto (Subtype.val : U → M) (𝓝 xU) (𝓝 x) from
      continuous_subtype_val.continuousAt.tendsto).eventually ((hgerm n).trans (hgerm m).symm)
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.mp hnm
  have heq := Ghys.connected_curve_holomorphic_eq_of_open_germ
    (fun p : U ↦ e n p) (fun p : U ↦ e m p) hn hm V hVo ⟨xU, hxV⟩ hV
  intro p hp
  exact congrFun heq (⟨p, hp⟩ : U)

/-- Holomorphic chart exhaustions with connected sources and agreeing germs at a common center glue
to a biholomorphism onto a fixed complex line. -/
theorem line_biholomorph_of_exhaustion_of_germs
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel 1) M]
    [IsManifold (complexModel 1) ∞ M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : E ≃L[ℂ] ComplexModel 1)
    (e : ℕ → OpenPartialHomeomorph M E) (x : M)
    (hx : x ∈ (e 0).source)
    (hsource : Monotone fun n ↦ (e n).source)
    (hconnected : ∀ n, IsPreconnected (e n).source)
    (hgerm : ∀ n, (e n : M → E) =ᶠ[𝓝 x] e 0)
    (hcover : ∀ p, ∃ n, p ∈ (e n).source)
    (hcover' : ∀ y, ∃ n, y ∈ (e n).target)
    (hsmooth : ∀ n, ContMDiffOn (complexModel 1) 𝓘(ℂ, E) ∞ (e n) (e n).source)
    (hsmooth' : ∀ n, ContMDiffOn 𝓘(ℂ, E) (complexModel 1) ∞ (e n).symm (e n).target) :
    ∃ φ : Diffeomorph (complexModel 1) 𝓘(ℂ, E) M E ∞,
      ∀ n, EqOn φ (e n) (e n).source := by
  let e' := fun n ↦ (e n).transHomeomorph c.toHomeomorph
  have hgerm' : ∀ n, (e' n : M → ComplexModel 1) =ᶠ[𝓝 x] e' 0 := by
    intro n
    exact (hgerm n).mono (fun p hp ↦ congrArg c hp)
  have hcover'' : ∀ y, ∃ n, y ∈ (e' n).target := by
    intro y
    exact hcover' (c.symm y)
  have hsmooth'' : ∀ n, ContMDiffOn (complexModel 1) (complexModel 1) ∞
      (e' n) (e' n).source := fun n ↦ c.contDiff.contMDiff.comp_contMDiffOn (hsmooth n)
  have hinverse : ∀ n, ContMDiffOn (complexModel 1) (complexModel 1) ∞
      (e' n).symm (e' n).target := fun n ↦
    (hsmooth' n).comp c.symm.contDiff.contMDiff.contMDiffOn (fun _ hy ↦ hy)
  obtain ⟨φ, hφ⟩ := biholomorph_of_exhaustion_of_germs e' x hx hsource hconnected
    hgerm' hcover hcover'' hsmooth'' hinverse
  refine ⟨φ.trans c.symm.toDiffeomorph, ?_⟩
  intro n p hp
  change c.symm (φ p) = e n p
  rw [hφ n hp]
  exact c.symm_apply_apply _

end HolomorphicAnosov
