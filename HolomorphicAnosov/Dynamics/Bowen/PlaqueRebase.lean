import HolomorphicAnosov.Dynamics.Bowen.ProductChart

/-!
# Rebase a relative open local plaque

Source: Rufus Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
Fact 1 p.727, Lemma 5 and descending scales p.728, Lemma 8 p.729.
The receiving set retains the full receiving plaque's native subspace topology.
The source and receiving maps are the same original modulus-defined bracket.
-/

namespace HolomorphicAnosov.Bowen

/-- Bowen Fact 1 p.727: stable plaque defined by all original forward iterates. -/
private def rebaseStable {X : Type*} [MetricSpace X]
    (f : X ≃ₜ X) (δ : ℝ) (x : X) : Set X :=
  {z | ∀ n : ℕ, dist ((f : X → X)^[n] z) ((f : X → X)^[n] x) ≤ δ}

/-- Bowen Fact 1 p.727: unstable plaque defined by all original inverse iterates. -/
private def rebaseUnstable {X : Type*} [MetricSpace X]
    (f : X ≃ₜ X) (δ : ℝ) (x : X) : Set X :=
  {z | ∀ n : ℕ, dist ((f.symm : X → X)^[n] z) ((f.symm : X → X)^[n] x) ≤ δ}

/-- Plaque rebase, including the stable dual and empty source factors.

Source: Bowen, Lemma 8 p.729. The product-chart input is
`bowen_fact1_product_chart_g6`, whose hypotheses are precisely the original
Fact 1, positive moduli and scale hypotheses displayed here. The bracket is
a total Lean function with only its original ε-domain and modulus domains
constrained; no continuity, geometric meaning or extension condition is
imposed on its values outside those domains. The source and receiving types
below are subtypes of their FULL γ-plaques, with the inherited native
subspace topologies. No initial-ε cap or receiving-domain assumption is added.

Complete natural-language proof:

1. Set z=[x,y]. Since dist(x,y)≤α₃<εmod(α₂/3), the modulus gives
z∈Wˢ_(α₂/3)(x)∩Wᵘ_(α₂/3)(y). Choose r with α₂/3<r<α₂ and let
V=Wˢ_γ(x)∩{v:dist(v,x)<r}. Contraction inside Wˢ_γ(x) puts V in
Wˢ_α₂(x). V is relatively open in the full γ-stable plaque and contains z.
The product chart gives an ambient open O=[U,V] and a homeomorphism
Φ:U×V→O with Φ(u,v)=[u,v] and inverse ([w,x],[x,w]). Both factor
subspaces keep their native topology. This is Bowen's actual chosen stable
collar, rather than an additional open-domain hypothesis.

2. For u∈U, dist(u,y)≤α₂+α₃<εmod(α₁/3), so s=[u,y] is defined
and belongs to Wˢ_(α₁/3)(u)∩Wᵘ_(α₁/3)(y). Likewise t=[u,z] is
in Wˢ_(α₁/3)(u)∩Wᵘ_(α₁/3)(z), since u,z are in the α₂ plaques
about x and 2α₂<εmod(α₁/3). The backward triangle bound α₁/3+α₂/3<γ
puts t in Wᵘ_γ(y). To compare s,t, their forward iterate distances are
at most 2α₁/3<γ. Their initial distance has this same bound, and they are
both in Wᵘ_γ(y); pairwise unstable contraction therefore bounds every
backward distance by lam^n(2α₁/3)<γ. Thus t lies in both γ-plaques
about s. The diagonal Fact 1 uniqueness at (s,s) yields t=s. This uses
only diagonal uniqueness, not uniqueness of an arbitrary far-apart
γ-stable/γ-unstable intersection. Consequently [U,y]⊆O∩Wᵘ_γ(y).

3. Conversely, let w=[u,v]∈O∩Wᵘ_γ(y). The same product-domain modulus
puts w∈Wˢ_(α₁/3)(u). Compare it with s=[u,y] from step 2. Forward
pair distances are bounded by 2α₁/3; both points lie in Wᵘ_γ(y), so
pairwise contraction gives the same backward bound. Diagonal uniqueness
again gives w=s. No unstable relation between the arbitrary stable factor
v and y is required. Hence [U,y]=O∩Wᵘ_γ(y), proving openness in the
FULL receiving plaque with its original subspace topology.

4. The forward map is u↦(u,z)↦Φ(u,z), with target restricted to
[U,y]=[U,z]. It is continuous. The inverse is pr₁∘Φ⁻¹ restricted to
this receiving slice, so it is continuous and equals w↦[w,x]. The product
chart inverse identities yield [[u,y],x]=u and [[w,x],y]=w on the
actual indicated domains. These maps give the required homeomorphism.
The same argument with f replaced by f.symm and bracket arguments exchanged
proves the stable map v↦[y,v], whose inverse is w↦[x,w]. If either
source factor is empty its image is empty, the receiving open set is empty,
and the unique maps between the empty subtypes are inverse continuous maps.
Nothing requires x=y or excludes frontier points of a relatively open plaque.
-/
theorem bowen_fact1_plaque_rebase_g6
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X ≃ₜ X) (lam γ ε : ℝ)
    (hlam : 0 < lam) (hlam1 : lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (α : Fin 5 → ℝ) (εmod : ℝ → ℝ)
    (hεmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ)
    (hα0 : α 0 = γ) (hαpos : ∀ i, 0 < α i)
    (hαscale : ∀ i : Fin 4,
      α i.succ < (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hsmall : ∀ i : Fin 4, ∀ a b : X,
      dist a b ≤ α i.succ →
        dist (f a) (f b) < α i.castSucc ∧ dist (f.symm a) (f.symm b) < α i.castSucc)
    (bracket : X → X → X)
    (hcontract_s : ∀ (x a b : X) (n : ℕ),
      a ∈ rebaseStable f γ x → b ∈ rebaseStable f γ x →
      dist ((f : X → X)^[n] a) ((f : X → X)^[n] b) ≤ lam ^ n * dist a b)
    (hcontract_u : ∀ (x a b : X) (n : ℕ),
      a ∈ rebaseUnstable f γ x → b ∈ rebaseUnstable f γ x →
      dist ((f.symm : X → X)^[n] a) ((f.symm : X → X)^[n] b) ≤ lam ^ n * dist a b)
    (hunique : ∀ a b : X, dist a b ≤ ε →
      ∃! z, z ∈ rebaseStable f γ a ∧ z ∈ rebaseUnstable f γ b)
    (hbracket_mem : ∀ a b : X, dist a b ≤ ε →
      bracket a b ∈ rebaseStable f γ a ∧ bracket a b ∈ rebaseUnstable f γ b)
    (hbracket_cont : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmodulus : ∀ δ, 0 < δ → δ ≤ γ → ∀ a b : X,
      dist a b ≤ εmod δ →
      bracket a b ∈ rebaseStable f δ a ∧ bracket a b ∈ rebaseUnstable f δ b)
    (x y : X) (hxy : dist x y ≤ α 3) :
    (∀ U : Set X, U ⊆ rebaseUnstable f (α 2) x →
      IsOpen {u : rebaseUnstable f γ x | (u : X) ∈ U} →
      let B := (fun u : X ↦ bracket u y) '' U
      B ⊆ rebaseUnstable f γ y ∧
      IsOpen {w : rebaseUnstable f γ y | (w : X) ∈ B} ∧
      ∃ h : Homeomorph
          {u : rebaseUnstable f γ x // (u : X) ∈ U}
          {w : rebaseUnstable f γ y // (w : X) ∈ B},
        (∀ u, (h u : X) = bracket (u : X) y) ∧
        (∀ w, (h.symm w : X) = bracket (w : X) x)) ∧
    (∀ V : Set X, V ⊆ rebaseStable f (α 2) x →
      IsOpen {v : rebaseStable f γ x | (v : X) ∈ V} →
      let B := (fun v : X ↦ bracket y v) '' V
      B ⊆ rebaseStable f γ y ∧
      IsOpen {w : rebaseStable f γ y | (w : X) ∈ B} ∧
      ∃ h : Homeomorph
          {v : rebaseStable f γ x // (v : X) ∈ V}
          {w : rebaseStable f γ y // (w : X) ∈ B},
        (∀ v, (h v : X) = bracket y (v : X)) ∧
        (∀ w, (h.symm w : X) = bracket x (w : X))) := by
  have hscale1 : 3 * α 2 < εmod (α 1 / 3) := by
    have h := lt_of_lt_of_le (hαscale 1)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
    norm_num at h ⊢
    linarith
  have hscale0 : α 1 < γ / 9 := by
    have h := lt_of_lt_of_le (hαscale 0)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, hα0] at h
    linarith
  have hscale2 : α 3 < α 2 / 9 := by
    have h := lt_of_lt_of_le (hαscale 2)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
    norm_num at h ⊢
    linarith
  have hβpos : 0 < α 1 / 3 := by linarith [hαpos 1]
  have hβγ : α 1 / 3 ≤ γ := by linarith [hscale0]
  have hβγ3 : α 1 / 3 ≤ γ / 3 := by linarith [hscale0]
  have hscale0b : α 1 < εmod (γ / 3) / 3 := by
    have h := lt_of_lt_of_le (hαscale 0)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, hα0] at h
    linarith
  have hscale1a : α 2 < α 1 / 9 := by
    have h := lt_of_lt_of_le (hαscale 1)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
    norm_num at h ⊢
    linarith
  have hscale2b : 3 * α 3 < εmod (α 2 / 3) := by
    have h := lt_of_lt_of_le (hαscale 2)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
    norm_num at h ⊢
    linarith
  have hchart := bowen_fact1_product_chart_g6 f lam γ ε hlam hlam1 hγ hε α εmod
    hεmod hα0 hαpos hαscale hsmall bracket hcontract_s hcontract_u hunique
    hbracket_mem hbracket_cont hmodulus
  constructor
  · intro U hU hUopen
    have hdist (u : X) (hu : u ∈ U) : dist u y ≤ εmod (α 1 / 3) := by
      have hu0 : dist u x ≤ α 2 := by
        simpa only [Function.iterate_zero, id_eq] using hU hu 0
      calc
        dist u y ≤ dist u x + dist x y := dist_triangle _ _ _
        _ ≤ α 2 + α 3 := add_le_add hu0 hxy
        _ ≤ εmod (α 1 / 3) := by linarith [hαpos 2]
    have hm (u : X) (hu : u ∈ U) :=
      hmodulus (α 1 / 3) hβpos hβγ u y (hdist u hu)
    have hB : (fun u : X ↦ bracket u y) '' U ⊆ rebaseUnstable f γ y := by
      rintro w ⟨u, hu, rfl⟩ n
      exact ((hm u hu).2 n).trans hβγ
    refine ⟨hB, ?_⟩
    let z := bracket x y
    have hz : z ∈ rebaseStable f (α 2 / 3) x ∧
        z ∈ rebaseUnstable f (α 2 / 3) y := by
      apply hmodulus (α 2 / 3) (by linarith [hαpos 2]) (by linarith) x y
      exact hxy.trans (by linarith [hαpos 3])
    let V : Set X := {v | v ∈ rebaseStable f γ x ∧ dist v x < 2 * α 2 / 3}
    have hV : V ⊆ rebaseStable f (α 2) x := by
      intro v hv n
      calc
        dist ((f : X → X)^[n] v) ((f : X → X)^[n] x) ≤
            lam ^ n * dist v x := hcontract_s x v x n hv.1 (fun _ ↦ by simpa using hγ.le)
        _ ≤ dist v x := mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.le hlam1.le)
        _ ≤ α 2 := by linarith [hv.2, hαpos 2]
    have hVopen : IsOpen {v : rebaseStable f γ x | (v : X) ∈ V} := by
      have heq : {v : rebaseStable f γ x | (v : X) ∈ V} =
          {v : rebaseStable f γ x | dist (v : X) x < 2 * α 2 / 3} := by
        ext v
        exact and_iff_right v.property
      rw [heq]
      exact isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
    have hzV : z ∈ V := by
      refine ⟨fun n ↦ (hz.1 n).trans (by linarith), ?_⟩
      have hz0 : dist z x ≤ α 2 / 3 := by simpa using hz.1 0
      linarith [hαpos 2]
    let O : Set X := {w | ∃ u ∈ U, ∃ v ∈ V, bracket u v = w}
    obtain ⟨hO, Φ, hΦ, hΦinv⟩ := hchart.2 x U V hU hV hUopen hVopen
    have hproduct (u v : X) (hu : u ∈ U) (hv : v ∈ V) :
        bracket u v ∈ rebaseStable f (α 1 / 3) u ∧
        bracket u v ∈ rebaseUnstable f (α 1 / 3) v := by
      apply hmodulus (α 1 / 3) hβpos hβγ
      calc
        dist u v ≤ dist u x + dist x v := dist_triangle _ _ _
        _ ≤ α 2 + α 2 := add_le_add
          (by simpa using hU hu 0)
          (by simpa only [Function.iterate_zero, id_eq, dist_comm] using hV hv 0)
        _ ≤ εmod (α 1 / 3) := by linarith [hαpos 2]
    have hshift (u : X) (hu : u ∈ U) : bracket u z = bracket u y := by
      have ht := hproduct u z hu hzV
      have htu : bracket u z ∈ rebaseUnstable f γ y := by
        intro n
        calc
          dist ((f.symm : X → X)^[n] (bracket u z)) ((f.symm : X → X)^[n] y) ≤
              dist ((f.symm : X → X)^[n] (bracket u z)) ((f.symm : X → X)^[n] z) +
              dist ((f.symm : X → X)^[n] z) ((f.symm : X → X)^[n] y) := dist_triangle _ _ _
          _ ≤ α 1 / 3 + α 2 / 3 := add_le_add (ht.2 n) (hz.2 n)
          _ ≤ γ := by linarith
      have hforward (n : ℕ) :
          dist ((f : X → X)^[n] (bracket u z)) ((f : X → X)^[n] (bracket u y)) ≤
            2 * (α 1 / 3) := by
        calc
          _ ≤ dist ((f : X → X)^[n] (bracket u z)) ((f : X → X)^[n] u) +
            dist ((f : X → X)^[n] u) ((f : X → X)^[n] (bracket u y)) := dist_triangle _ _ _
          _ ≤ α 1 / 3 + α 1 / 3 := add_le_add (ht.1 n)
            (by simpa only [dist_comm] using (hm u hu).1 n)
          _ = _ := by ring
      apply (hunique (bracket u y) (bracket u y) (by simpa using hε.le)).unique
      · constructor
        · intro n
          exact (hforward n).trans (by linarith)
        · intro n
          calc
            _ ≤ lam ^ n * dist (bracket u z) (bracket u y) :=
              hcontract_u y _ _ n htu (hB ⟨u, hu, rfl⟩)
            _ ≤ dist (bracket u z) (bracket u y) :=
              mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.le hlam1.le)
            _ ≤ 2 * (α 1 / 3) := by simpa using hforward 0
            _ ≤ γ := by linarith
      · exact ⟨fun _ ↦ by simpa using hγ.le, fun _ ↦ by simpa using hγ.le⟩
    have hqO (u v : X) (hu : u ∈ U) (hv : v ∈ V) :
        dist (bracket u v) x < εmod (γ / 3) := by
      have ht := hproduct u v hu hv
      calc
        dist (bracket u v) x ≤ dist (bracket u v) u + dist u x := dist_triangle _ _ _
        _ ≤ α 1 / 3 + α 2 := add_le_add
          (by simpa only [Function.iterate_zero, id_eq] using ht.1 0)
          (by simpa only [Function.iterate_zero, id_eq] using hU hu 0)
        _ < εmod (γ / 3) := by linarith [hscale0b, hscale1a]
    have hBO : ∀ w : X, w ∈ (fun u : X ↦ bracket u y) '' U ↔
        w ∈ O ∧ w ∈ rebaseUnstable f γ y := by
      intro w
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨u, hu, z, hzV, hshift u hu⟩, hB ⟨u, hu, rfl⟩⟩
      · rintro ⟨⟨u, hu, v, hv, rfl⟩, hw⟩
        refine ⟨u, hu, ?_⟩
        have ht := hproduct u v hu hv
        have hforward (n : ℕ) :
            dist ((f : X → X)^[n] (bracket u y)) ((f : X → X)^[n] (bracket u v)) ≤
              2 * (α 1 / 3) := by
          calc
            _ ≤ dist ((f : X → X)^[n] (bracket u y)) ((f : X → X)^[n] u) +
              dist ((f : X → X)^[n] u) ((f : X → X)^[n] (bracket u v)) := dist_triangle _ _ _
            _ ≤ α 1 / 3 + α 1 / 3 := add_le_add ((hm u hu).1 n)
              (by simpa only [dist_comm] using ht.1 n)
            _ = _ := by ring
        apply (hunique (bracket u v) (bracket u v) (by simpa using hε.le)).unique
        · constructor
          · intro n
            exact (hforward n).trans (by linarith)
          · intro n
            calc
              _ ≤ lam ^ n * dist (bracket u y) (bracket u v) :=
                hcontract_u y _ _ n (hB ⟨u, hu, rfl⟩) hw
              _ ≤ dist (bracket u y) (bracket u v) :=
                mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.le hlam1.le)
              _ ≤ 2 * (α 1 / 3) := by simpa using hforward 0
              _ ≤ γ := by linarith
        · exact ⟨fun _ ↦ by simpa using hγ.le, fun _ ↦ by simpa using hγ.le⟩
    have hopen : IsOpen {w : rebaseUnstable f γ y |
        (w : X) ∈ (fun u : X ↦ bracket u y) '' U} := by
      have heq : {w : rebaseUnstable f γ y |
          (w : X) ∈ (fun u : X ↦ bracket u y) '' U} =
          {w : rebaseUnstable f γ y | (w : X) ∈ O} := by
        ext w
        exact (hBO w).trans (and_iff_left w.property)
      rw [heq]
      exact hO.preimage continuous_subtype_val
    refine ⟨hopen, ?_⟩
    let A := {u : rebaseUnstable f γ x // (u : X) ∈ U}
    let C := {w : rebaseUnstable f γ y // (w : X) ∈ (fun u : X ↦ bracket u y) '' U}
    let F : A → C := fun u =>
      ⟨⟨bracket (u : X) y, hB ⟨u, u.property, rfl⟩⟩, ⟨u, u.property, rfl⟩⟩
    let toO : C → O := fun w ↦ ⟨w, ((hBO (w : X)).mp w.property).1⟩
    let G : C → A := fun w ↦ (Φ.symm (toO w)).1
    have hFcont : Continuous F := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (hchart.1 (α 1 / 3) hβpos hβγ3).comp_continuous
        ((continuous_subtype_val.comp continuous_subtype_val).prodMk continuous_const)
        (fun u ↦ hdist (u : X) u.property)
    have hGcont : Continuous G := by
      have htoO : Continuous toO :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      exact continuous_fst.comp (Φ.symm.continuous.comp htoO)
    let zV : {v : rebaseStable f γ x // (v : X) ∈ V} := ⟨⟨z, hzV.1⟩, hzV⟩
    have hFG : ∀ u : A, G (F u) = u := by
      intro u
      have heq : toO (F u) = Φ (u, zV) := by
        apply Subtype.ext
        exact (hΦ (u, zV)).trans (hshift (u : X) u.property) |>.symm
      change (Φ.symm (toO (F u))).1 = u
      rw [heq, Φ.symm_apply_apply]
    have hFGprime : ∀ w : C, F (G w) = w := by
      intro w
      obtain ⟨u, hu, heq⟩ := w.property
      have huγ : u ∈ rebaseUnstable f γ x :=
        fun n ↦ (hU hu n).trans (by linarith)
      let ua : A := ⟨⟨u, huγ⟩, hu⟩
      have hw : F ua = w := by
        apply Subtype.ext
        apply Subtype.ext
        exact heq
      rw [← hw, hFG]
    let H : A ≃ₜ C :=
      { toFun := F
        invFun := G
        left_inv := hFG
        right_inv := hFGprime
        continuous_toFun := hFcont
        continuous_invFun := hGcont }
    refine ⟨H, ?_, ?_⟩
    · intro u
      rfl
    · intro w
      exact (hΦinv (toO w)).1
  · have huniqueDual : ∀ a b : X, dist a b ≤ ε →
        ∃! z, z ∈ rebaseStable f.symm γ a ∧ z ∈ rebaseUnstable f.symm γ b := by
      intro a b hab
      obtain ⟨z, hz, huniq⟩ := hunique b a (by simpa only [dist_comm] using hab)
      exact ⟨z, ⟨hz.2, hz.1⟩, fun w hw ↦ huniq w ⟨hw.2, hw.1⟩⟩
    have hmodulusDual : ∀ δ, 0 < δ → δ ≤ γ → ∀ a b : X,
        dist a b ≤ εmod δ →
        bracket b a ∈ rebaseStable f.symm δ a ∧
        bracket b a ∈ rebaseUnstable f.symm δ b := by
      intro δ hδ hδγ a b hab
      exact (hmodulus δ hδ hδγ b a (by simpa only [dist_comm] using hab)).symm
    have hbracketDual : ∀ a b : X, dist a b ≤ ε →
        bracket b a ∈ rebaseStable f.symm γ a ∧
        bracket b a ∈ rebaseUnstable f.symm γ b := by
      intro a b hab
      exact (hbracket_mem b a (by simpa only [dist_comm] using hab)).symm
    have hcontDual : ContinuousOn (fun p : X × X ↦ bracket p.2 p.1)
        {p | dist p.1 p.2 ≤ ε} := by
      exact hbracket_cont.comp continuous_swap.continuousOn
        (fun p hp ↦ by
          change dist p.1 p.2 ≤ ε at hp
          change dist p.2 p.1 ≤ ε
          simpa only [dist_comm] using hp)
    have hchart := bowen_fact1_product_chart_g6 f.symm lam γ ε hlam hlam1 hγ hε α εmod
      hεmod hα0 hαpos hαscale (fun i a b hab ↦ (hsmall i a b hab).symm)
      (fun a b ↦ bracket b a) hcontract_u hcontract_s huniqueDual
      hbracketDual hcontDual hmodulusDual

    intro U hU hUopen
    have hdist (u : X) (hu : u ∈ U) : dist u y ≤ εmod (α 1 / 3) := by
      have hu0 : dist u x ≤ α 2 := by
        simpa only [Function.iterate_zero, id_eq] using hU hu 0
      calc
        dist u y ≤ dist u x + dist x y := dist_triangle _ _ _
        _ ≤ α 2 + α 3 := add_le_add hu0 hxy
        _ ≤ εmod (α 1 / 3) := by linarith [hαpos 2]
    have hm (u : X) (hu : u ∈ U) :=
      hmodulusDual (α 1 / 3) hβpos hβγ u y (hdist u hu)
    have hB : (fun u : X ↦ bracket y u) '' U ⊆ rebaseStable f γ y := by
      rintro w ⟨u, hu, rfl⟩ n
      exact ((hm u hu).2 n).trans hβγ
    refine ⟨hB, ?_⟩
    let z := bracket y x
    have hz : z ∈ rebaseUnstable f (α 2 / 3) x ∧
        z ∈ rebaseStable f (α 2 / 3) y := by
      apply hmodulusDual (α 2 / 3) (by linarith [hαpos 2]) (by linarith) x y
      exact hxy.trans (by linarith [hαpos 3])
    let V : Set X := {v | v ∈ rebaseUnstable f γ x ∧ dist v x < 2 * α 2 / 3}
    have hV : V ⊆ rebaseUnstable f (α 2) x := by
      intro v hv n
      calc
        dist ((f.symm : X → X)^[n] v) ((f.symm : X → X)^[n] x) ≤
            lam ^ n * dist v x := hcontract_u x v x n hv.1 (fun _ ↦ by simpa using hγ.le)
        _ ≤ dist v x := mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.le hlam1.le)
        _ ≤ α 2 := by linarith [hv.2, hαpos 2]
    have hVopen : IsOpen {v : rebaseUnstable f γ x | (v : X) ∈ V} := by
      have heq : {v : rebaseUnstable f γ x | (v : X) ∈ V} =
          {v : rebaseUnstable f γ x | dist (v : X) x < 2 * α 2 / 3} := by
        ext v
        exact and_iff_right v.property
      rw [heq]
      exact isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
    have hzV : z ∈ V := by
      refine ⟨fun n ↦ (hz.1 n).trans (by linarith), ?_⟩
      have hz0 : dist z x ≤ α 2 / 3 := by simpa using hz.1 0
      linarith [hαpos 2]
    let O : Set X := {w | ∃ u ∈ U, ∃ v ∈ V, bracket v u = w}
    obtain ⟨hO, Φ, hΦ, hΦinv⟩ := hchart.2 x U V hU hV hUopen hVopen
    have hproduct (u v : X) (hu : u ∈ U) (hv : v ∈ V) :
        bracket v u ∈ rebaseUnstable f (α 1 / 3) u ∧
        bracket v u ∈ rebaseStable f (α 1 / 3) v := by
      apply hmodulusDual (α 1 / 3) hβpos hβγ
      calc
        dist u v ≤ dist u x + dist x v := dist_triangle _ _ _
        _ ≤ α 2 + α 2 := add_le_add
          (by simpa using hU hu 0)
          (by simpa only [Function.iterate_zero, id_eq, dist_comm] using hV hv 0)
        _ ≤ εmod (α 1 / 3) := by linarith [hαpos 2]
    have hshift (u : X) (hu : u ∈ U) : bracket z u = bracket y u := by
      have ht := hproduct u z hu hzV
      have htu : bracket z u ∈ rebaseStable f γ y := by
        intro n
        calc
          dist ((f : X → X)^[n] (bracket z u)) ((f : X → X)^[n] y) ≤
              dist ((f : X → X)^[n] (bracket z u)) ((f : X → X)^[n] z) +
              dist ((f : X → X)^[n] z) ((f : X → X)^[n] y) := dist_triangle _ _ _
          _ ≤ α 1 / 3 + α 2 / 3 := add_le_add (ht.2 n) (hz.2 n)
          _ ≤ γ := by linarith
      have hforward (n : ℕ) :
          dist ((f.symm : X → X)^[n] (bracket z u)) ((f.symm : X → X)^[n] (bracket y u)) ≤
            2 * (α 1 / 3) := by
        calc
          _ ≤ dist ((f.symm : X → X)^[n] (bracket z u)) ((f.symm : X → X)^[n] u) +
            dist ((f.symm : X → X)^[n] u) ((f.symm : X → X)^[n] (bracket y u)) := dist_triangle _ _ _
          _ ≤ α 1 / 3 + α 1 / 3 := add_le_add (ht.1 n)
            (by simpa only [dist_comm] using (hm u hu).1 n)
          _ = _ := by ring
      apply (huniqueDual (bracket y u) (bracket y u) (by simpa using hε.le)).unique
      · constructor
        · intro n
          exact (hforward n).trans (by linarith)
        · intro n
          calc
            _ ≤ lam ^ n * dist (bracket z u) (bracket y u) :=
              hcontract_s y _ _ n htu (hB ⟨u, hu, rfl⟩)
            _ ≤ dist (bracket z u) (bracket y u) :=
              mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.le hlam1.le)
            _ ≤ 2 * (α 1 / 3) := by simpa using hforward 0
            _ ≤ γ := by linarith
      · exact ⟨fun _ ↦ by simpa using hγ.le, fun _ ↦ by simpa using hγ.le⟩
    have hBO : ∀ w : X, w ∈ (fun u : X ↦ bracket y u) '' U ↔
        w ∈ O ∧ w ∈ rebaseStable f γ y := by
      intro w
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨u, hu, z, hzV, hshift u hu⟩, hB ⟨u, hu, rfl⟩⟩
      · rintro ⟨⟨u, hu, v, hv, rfl⟩, hw⟩
        refine ⟨u, hu, ?_⟩
        have ht := hproduct u v hu hv
        have hforward (n : ℕ) :
            dist ((f.symm : X → X)^[n] (bracket y u)) ((f.symm : X → X)^[n] (bracket v u)) ≤
              2 * (α 1 / 3) := by
          calc
            _ ≤ dist ((f.symm : X → X)^[n] (bracket y u)) ((f.symm : X → X)^[n] u) +
              dist ((f.symm : X → X)^[n] u) ((f.symm : X → X)^[n] (bracket v u)) := dist_triangle _ _ _
            _ ≤ α 1 / 3 + α 1 / 3 := add_le_add ((hm u hu).1 n)
              (by simpa only [dist_comm] using ht.1 n)
            _ = _ := by ring
        apply (huniqueDual (bracket v u) (bracket v u) (by simpa using hε.le)).unique
        · constructor
          · intro n
            exact (hforward n).trans (by linarith)
          · intro n
            calc
              _ ≤ lam ^ n * dist (bracket y u) (bracket v u) :=
                hcontract_s y _ _ n (hB ⟨u, hu, rfl⟩) hw
              _ ≤ dist (bracket y u) (bracket v u) :=
                mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hlam.le hlam1.le)
              _ ≤ 2 * (α 1 / 3) := by simpa using hforward 0
              _ ≤ γ := by linarith
        · exact ⟨fun _ ↦ by simpa using hγ.le, fun _ ↦ by simpa using hγ.le⟩
    have hopen : IsOpen {w : rebaseStable f γ y |
        (w : X) ∈ (fun u : X ↦ bracket y u) '' U} := by
      have heq : {w : rebaseStable f γ y |
          (w : X) ∈ (fun u : X ↦ bracket y u) '' U} =
          {w : rebaseStable f γ y | (w : X) ∈ O} := by
        ext w
        exact (hBO w).trans (and_iff_left w.property)
      rw [heq]
      exact hO.preimage continuous_subtype_val
    refine ⟨hopen, ?_⟩
    let A := {u : rebaseStable f γ x // (u : X) ∈ U}
    let C := {w : rebaseStable f γ y // (w : X) ∈ (fun u : X ↦ bracket y u) '' U}
    let F : A → C := fun u =>
      ⟨⟨bracket y (u : X), hB ⟨u, u.property, rfl⟩⟩, ⟨u, u.property, rfl⟩⟩
    let toO : C → O := fun w ↦ ⟨w, ((hBO (w : X)).mp w.property).1⟩
    let G : C → A := fun w ↦ (Φ.symm (toO w)).1
    have hFcont : Continuous F := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (hchart.1 (α 1 / 3) hβpos hβγ3).comp_continuous
        ((continuous_subtype_val.comp continuous_subtype_val).prodMk continuous_const)
        (fun u ↦ hdist (u : X) u.property)
    have hGcont : Continuous G := by
      have htoO : Continuous toO :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      exact continuous_fst.comp (Φ.symm.continuous.comp htoO)
    let zV : {v : rebaseUnstable f γ x // (v : X) ∈ V} := ⟨⟨z, hzV.1⟩, hzV⟩
    have hFG : ∀ u : A, G (F u) = u := by
      intro u
      have heq : toO (F u) = Φ (u, zV) := by
        apply Subtype.ext
        exact (hΦ (u, zV)).trans (hshift (u : X) u.property) |>.symm
      change (Φ.symm (toO (F u))).1 = u
      rw [heq, Φ.symm_apply_apply]
    have hFGprime : ∀ w : C, F (G w) = w := by
      intro w
      obtain ⟨u, hu, heq⟩ := w.property
      have huγ : u ∈ rebaseStable f γ x :=
        fun n ↦ (hU hu n).trans (by linarith)
      let ua : A := ⟨⟨u, huγ⟩, hu⟩
      have hw : F ua = w := by
        apply Subtype.ext
        apply Subtype.ext
        exact heq
      rw [← hw, hFG]
    let H : A ≃ₜ C :=
      { toFun := F
        invFun := G
        left_inv := hFG
        right_inv := hFGprime
        continuous_toFun := hFcont
        continuous_invFun := hGcont }
    refine ⟨H, ?_, ?_⟩
    · intro u
      rfl
    · intro w
      exact (hΦinv (toO w)).1

end HolomorphicAnosov.Bowen
