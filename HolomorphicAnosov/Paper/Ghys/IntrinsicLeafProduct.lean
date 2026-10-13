import HolomorphicAnosov.Paper.Ghys.UniqueLeafProductEquiv
import HolomorphicAnosov.Paper.Ghys.ProductHomeomorphOfContinuousRetraction
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.PathConnected

/-! This module constructs a global product from complete intrinsic leaf coordinates. (Ghys, Thm. B) -/

noncomputable section
open Filter Set Topology _root_.Topology
universe u v w a l
namespace HolomorphicAnosov.Ghys

/-- A continuous developing map with complete intrinsic leaf coordinates gives a global product when local product charts are compatible with the developing map. (Ghys, Thm. B) -/
theorem product_homeomorph_of_intrinsic_leaf_coordinates
    {E : Type u} {V : Type v} {Z : Type w} {A : Type a} [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace Z]
    (D : E → Z) (hD : Continuous D) (R : E → E → Prop) (z₀ : Z)
    (O : A → Set E) (W : A → Set Z) (H : ∀ a, (V × W a) ≃ₜ O a)
    (hO : ∀ a, IsOpen (O a)) (hW : ∀ a, IsOpen (W a))
    (hcover : ∀ e : E, ∃ a, e ∈ O a)
    (hcoord : ∀ a r z, D (H a (r, z)).val = z.val)
    (hplaque : ∀ a (e : O a) (z : W a),
      Relation.EqvGen R e.val (H a (((H a).symm e).1, z)).val)
    (L : E → Type l) [∀ e, TopologicalSpace (L e)] [∀ e, PathConnectedSpace (L e)]
    (lift : ∀ e, L e → E) (hlift : ∀ e, Continuous (lift e))
    (coordinate : ∀ e, L e ≃ Z)
    (hrange : ∀ e, Set.range (lift e) = {y | Relation.EqvGen R e y})
    (hleafcoord : ∀ e x, coordinate e x = D (lift e x)) :
    ∃ B : ({e : E // D e = z₀} × Z) ≃ₜ E,
      ∀ r z, D (B (r, z)) = z := by
  have product_chart_coordinate_motion
      {E : Type u} {V : Type v} {Z : Type w} [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace Z]
      (O : Set E) (H : (V × Z) ≃ₜ O) :
      Continuous (fun q : O × Z => H ((H.symm q.1).1, q.2)) := by
    exact H.continuous.comp
      (((H.symm.continuous.comp continuous_fst).fst).prodMk continuous_snd)
  have product_chart_motion_ambient
      {E : Type u} {V : Type v} {Z : Type w} [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace Z]
      (D : E → Z) (R : E → E → Prop)
      (O : Set E) (W : Set Z) (H : (V × W) ≃ₜ O)
      (hcoord : ∀ r z, D (H (r, z)).val = z.val)
      (hplaque : ∀ (e : O) (z : W),
        Relation.EqvGen R e.val (H ((H.symm e).1, z)).val) :
      ∃ m : E × Z → E, ContinuousOn m (O ×ˢ W) ∧
        Set.MapsTo m (O ×ˢ W) O ∧
        ∀ q ∈ O ×ˢ W, Relation.EqvGen R q.1 (m q) ∧ D (m q) = q.2 := by
    classical
    let m : E × Z → E := fun q ↦
      if h : q ∈ O ×ˢ W then
        (H ((H.symm ⟨q.1, h.1⟩).1, ⟨q.2, h.2⟩)).val
      else q.1
    have hformula (q : E × Z) (hq : q ∈ O ×ˢ W) :
        m q = (H ((H.symm ⟨q.1, hq.1⟩).1, ⟨q.2, hq.2⟩)).val := by
      simp only [m, dite_eq_left hq]
    refine ⟨m, ?_, ?_, ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      let Q : (O ×ˢ W : Set (E × Z)) → O × W := fun q ↦
        (⟨q.val.1, q.property.1⟩, ⟨q.val.2, q.property.2⟩)
      have hQ : Continuous Q :=
        (continuous_subtype_val.fst.subtype_mk _).prodMk
          (continuous_subtype_val.snd.subtype_mk _)
      have hc := (continuous_subtype_val.comp (product_chart_coordinate_motion O H)).comp hQ
      exact hc.congr (fun q ↦ (hformula q.val q.property).symm)
    · intro q hq
      rw [hformula q hq]
      exact (H ((H.symm ⟨q.1, hq.1⟩).1, ⟨q.2, hq.2⟩)).property
    · intro q hq
      rw [hformula q hq]
      exact ⟨hplaque ⟨q.1, hq.1⟩ ⟨q.2, hq.2⟩, hcoord _ _⟩
  have exists_open_guarded_continuation
      {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
      (f : X → Y) (g : Y → Z) (s : Set X) (t : Set Y) (x : X)
      (hs : IsOpen s) (ht : IsOpen t) (hxs : x ∈ s) (hfx : f x ∈ t)
      (hf : ContinuousOn f s) (hg : ContinuousOn g t) :
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ s ∧
        Set.MapsTo f U t ∧ ContinuousOn (g ∘ f) U := by
    have hsn := hs.mem_nhds hxs
    have hpre : f ⁻¹' t ∈ 𝓝 x := (hf.continuousAt hsn) (ht.mem_nhds hfx)
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp (Filter.inter_mem hsn hpre)
    have hUs : U ⊆ s := fun y hy ↦ (hUsub hy).1
    have hmap : Set.MapsTo f U t := fun y hy ↦ (hUsub hy).2
    exact ⟨U, hUopen, hxU, hUs, hmap, hg.comp (hf.mono hUs) hmap⟩
  have exists_open_guarded_finite_chain
      {X : Type u} [TopologicalSpace X] (F f : ℕ → X → X) (S : ℕ → Set X)
      (x : X) (hzero : F 0 = id) (hstep : ∀ i, F (i + 1) = f i ∘ F i) (n : ℕ) :
      (∀ i, i ≤ n → IsOpen (S i)) →
      (∀ i, i ≤ n → F i x ∈ S i) →
      (∀ i, i < n → ContinuousOn (f i) (S i)) →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ i, i ≤ n → ContinuousOn (F i) U ∧ Set.MapsTo (F i) U (S i) := by
    induction n with
    | zero =>
        intro hs hx hf
        refine ⟨S 0, hs 0 le_rfl, ?_, ?_⟩
        · simpa only [hzero, id_eq] using hx 0 le_rfl
        · intro i hi
          have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
          subst i
          rw [hzero]
          exact ⟨continuous_id.continuousOn, fun y hy ↦ hy⟩
    | succ n ih =>
        intro hs hx hf
        obtain ⟨V, hVo, hxV, hV⟩ := ih
          (fun i hi ↦ hs i (Nat.le_trans hi (Nat.le_succ n)))
          (fun i hi ↦ hx i (Nat.le_trans hi (Nat.le_succ n)))
          (fun i hi ↦ hf i (Nat.lt_trans hi (Nat.lt_succ_self n)))
        have hn : ContinuousOn (F (n + 1)) V := by
          rw [hstep n]
          exact (hf n (Nat.lt_succ_self n)).comp (hV n le_rfl).1 (hV n le_rfl).2
        obtain ⟨U, hUo, hxU, hUV, hmap, _⟩ :=
          exists_open_guarded_continuation (F (n + 1)) id V (S (n + 1)) x
            hVo (hs _ le_rfl) hxV (hx _ le_rfl) hn continuous_id.continuousOn
        refine ⟨U, hUo, hxU, ?_⟩
        intro i hi
        rcases Nat.eq_or_lt_of_le hi with rfl | hi
        · exact ⟨hn.mono hUV, hmap⟩
        · have hprev := hV i (Nat.le_of_lt_succ hi)
          exact ⟨hprev.1.mono hUV, fun y hy ↦ hprev.2 (hUV hy)⟩
  have leaf_selector_continuous_after_finite_chain
      {E : Type u} {Z : Type w} [TopologicalSpace E] [TopologicalSpace Z]
      (D : E → Z) (R : E → E → Prop) (P : E → Z → E)
      (hP : ∀ e z, Relation.EqvGen R e (P e z) ∧ D (P e z) = z)
      (hinj : ∀ e, Set.InjOn D {y : E | Relation.EqvGen R e y})
      (F f : ℕ → E → E) (S : ℕ → Set E) (x : E) (n : ℕ)
      (hzero : F 0 = id) (hstep : ∀ i, F (i + 1) = f i ∘ F i)
      (hs : ∀ i, i ≤ n → IsOpen (S i))
      (hx : ∀ i, i ≤ n → F i x ∈ S i)
      (hf : ∀ i, i < n → ContinuousOn (f i) (S i))
      (hrel : ∀ i, i < n → ∀ e ∈ S i, Relation.EqvGen R e (f i e))
      (W : Set Z) (m : E × Z → E)
      (hm : ContinuousOn m ((S n) ×ˢ W))
      (hmrel : ∀ e ∈ S n, ∀ z ∈ W, Relation.EqvGen R e (m (e, z)))
      (hmcoord : ∀ e ∈ S n, ∀ z ∈ W, D (m (e, z)) = z) :
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
        ContinuousOn (fun q : E × Z ↦ P q.1 q.2) (U ×ˢ W) := by
    obtain ⟨U, hUo, hxU, hguard⟩ :=
      exists_open_guarded_finite_chain F f S x hzero hstep n hs hx hf
    have hchain (i : ℕ) (hi : i ≤ n) (e : E) (he : e ∈ U) :
        Relation.EqvGen R e (F i e) := by
      induction i with
      | zero => simpa only [hzero, id_eq] using (Relation.EqvGen.refl e : Relation.EqvGen R e e)
      | succ i ih =>
          have hil : i < n := Nat.lt_of_succ_le hi
          have hip : i ≤ n := Nat.le_of_lt hil
          rw [hstep i, Function.comp_apply]
          exact Relation.EqvGen.trans _ _ _ (ih hip)
            (hrel i hil (F i e) ((hguard i hip).2 he))
    have hpair : ContinuousOn (fun q : E × Z ↦ (F n q.1, q.2)) (U ×ˢ W) :=
      ((hguard n le_rfl).1.comp continuous_fst.continuousOn
        (fun _ hq ↦ hq.1)).prodMk continuous_snd.continuousOn
    have hmap : Set.MapsTo (fun q : E × Z ↦ (F n q.1, q.2)) (U ×ˢ W) ((S n) ×ˢ W) :=
      fun _ hq ↦ ⟨(hguard n le_rfl).2 hq.1, hq.2⟩
    refine ⟨U, hUo, hxU, (hm.comp hpair hmap).congr ?_⟩
    intro q hq
    have heS := (hguard n le_rfl).2 hq.1
    exact hinj q.1 (hP q.1 q.2).1
      (Relation.EqvGen.trans _ _ _ (hchain n le_rfl q.1 hq.1)
        (hmrel _ heS _ hq.2))
      ((hP q.1 q.2).2.trans (hmcoord _ heS _ hq.2).symm)
  have leaf_selector_continuousAt_of_chart_chain
      {E : Type u} {V : Type v} {Z : Type w} [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace Z]
      (D : E → Z) (R : E → E → Prop) (P : E → Z → E)
      (hP : ∀ e z, Relation.EqvGen R e (P e z) ∧ D (P e z) = z)
      (hinj : ∀ e, Set.InjOn D {y : E | Relation.EqvGen R e y})
      (F f : ℕ → E → E) (S : ℕ → Set E) (x : E) (n : ℕ)
      (hzero : F 0 = id) (hstep : ∀ i, F (i + 1) = f i ∘ F i)
      (hs : ∀ i, i ≤ n → IsOpen (S i))
      (hx : ∀ i, i ≤ n → F i x ∈ S i)
      (hf : ∀ i, i < n → ContinuousOn (f i) (S i))
      (hrel : ∀ i, i < n → ∀ e ∈ S i, Relation.EqvGen R e (f i e))
      (W : Set Z) (hW : IsOpen W) (z : Z) (hz : z ∈ W)
      (H : (V × W) ≃ₜ S n)
      (hcoord : ∀ r w, D (H (r, w)).val = w.val)
      (hplaque : ∀ (e : S n) (w : W),
        Relation.EqvGen R e.val (H ((H.symm e).1, w)).val) :
      ContinuousAt (fun q : E × Z ↦ P q.1 q.2) (x, z) := by
    obtain ⟨m, hm, _, hspec⟩ := product_chart_motion_ambient D R (S n) W H hcoord hplaque
    obtain ⟨U, hUo, hxU, hcont⟩ :=
      leaf_selector_continuous_after_finite_chain D R P hP hinj F f S x n
        hzero hstep hs hx hf hrel W m hm
        (fun e he w hw ↦ (hspec (e, w) ⟨he, hw⟩).1)
        (fun e he w hw ↦ (hspec (e, w) ⟨he, hw⟩).2)
    exact hcont.continuousAt ((hUo.prod hW).mem_nhds ⟨hxU, hz⟩)
  have product_homeomorph_of_continuous_leaf_selector
      {E : Type u} {Z : Type w} [TopologicalSpace E] [TopologicalSpace Z]
      (R : Setoid E) (D : E → Z) (hD : Continuous D) (z₀ : Z)
      (P : E → Z → E)
      (hP : ∀ e z, R.r e (P e z) ∧ D (P e z) = z)
      (hinj : ∀ e, Set.InjOn D {y : E | R.r e y})
      (hc : Continuous (fun q : E × Z ↦ P q.1 q.2)) :
      ∃ B : ({e : E // D e = z₀} × Z) ≃ₜ E,
        ∀ r z, D (B (r, z)) = z := by
    have hu : ∀ e z, ∃! y, R.r e y ∧ D y = z := by
      intro e z
      refine ⟨P e z, hP e z, ?_⟩
      intro y hy
      exact hinj e hy.1 (hP e z).1 (hy.2.trans (hP e z).2.symm)
    obtain ⟨B, hcoord, hrel, _⟩ := product_equiv_of_unique_leaf_intersections R D z₀ hu
    have hforward : (fun q : {e : E // D e = z₀} × Z ↦ P q.1.val q.2) = B := by
      funext q
      exact hinj q.1.val (hP q.1.val q.2).1 (hrel q.1 q.2)
        ((hP q.1.val q.2).2.trans (hcoord q.1 q.2).symm)
    have hB : Continuous B := by
      rw [← hforward]
      exact hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hr : Continuous (fun e ↦ (B.symm e).1) := by
      have hfirst : (fun e ↦ (B.symm e).1) =
          (fun e ↦ (⟨P e z₀, (hP e z₀).2⟩ : {e : E // D e = z₀})) := by
        funext e
        apply Subtype.ext
        have hleaf : R.r (B.symm e).1.val e := by
          simpa only [Prod.mk.eta, B.apply_symm_apply] using
            hrel (B.symm e).1 (B.symm e).2
        exact hinj e (R.symm hleaf) (hP e z₀).1
          ((B.symm e).1.property.trans (hP e z₀).2.symm)
      rw [hfirst]
      exact (hc.comp (continuous_id.prodMk continuous_const)).subtype_mk _
    obtain ⟨H, _, hH⟩ := product_homeomorph_of_continuous_retraction D hD z₀ B hcoord hB hr
    exact ⟨H, hH⟩
  have guarded_chain_from_developing_charts
      {E : Type u} {V : Type v} {Z : Type w} [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace Z]
      (D : E → Z) (R : E → E → Prop)
      (hinj : ∀ e, Set.InjOn D {y : E | Relation.EqvGen R e y})
      (S : ℕ → Set E) (W : ℕ → Set Z) (H : ∀ i, (V × W i) ≃ₜ S i)
      (hcoord : ∀ i r z, D (H i (r, z)).val = z.val)
      (hplaque : ∀ i (e : S i) (z : W i),
        Relation.EqvGen R e.val (H i (((H i).symm e).1, z)).val)
      (c : ℕ → E) (n : ℕ)
      (hs : ∀ i, i ≤ n → IsOpen (S i))
      (hc : ∀ i, i ≤ n → c i ∈ S i)
      (hw : ∀ i, i < n → D (c (i + 1)) ∈ W i)
      (hnext : ∀ i, i < n → Relation.EqvGen R (c i) (c (i + 1))) :
      ∃ (f F : ℕ → E → E) (U : Set E),
        F 0 = id ∧ (∀ i, F (i + 1) = f i ∘ F i) ∧
        (∀ i, i ≤ n → F i (c 0) = c i) ∧
        (∀ i, i < n → ContinuousOn (f i) (S i)) ∧
        (∀ i, i < n → ∀ e ∈ S i, Relation.EqvGen R e (f i e)) ∧
        IsOpen U ∧ c 0 ∈ U ∧
        ∀ i, i ≤ n → ContinuousOn (F i) U ∧ Set.MapsTo (F i) U (S i) := by
    classical
    have hm : ∀ i, ∃ m : E × Z → E, ContinuousOn m (S i ×ˢ W i) ∧
        Set.MapsTo m (S i ×ˢ W i) (S i) ∧
        ∀ q ∈ S i ×ˢ W i, Relation.EqvGen R q.1 (m q) ∧ D (m q) = q.2 :=
      fun i ↦ product_chart_motion_ambient D R (S i) (W i) (H i) (hcoord i) (hplaque i)
    choose m hmcont hmmap hmspec using hm
    let f : ℕ → E → E := fun i e ↦ m i (e, D (c (i + 1)))
    let F : ℕ → E → E := Nat.rec id (fun i g ↦ f i ∘ g)
    have hzero : F 0 = id := rfl
    have hstep (i : ℕ) : F (i + 1) = f i ∘ F i := rfl
    have hf (i : ℕ) (hi : i < n) : ContinuousOn (f i) (S i) := by
      exact (hmcont i).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun e he ↦ ⟨he, hw i hi⟩)
    have hrel (i : ℕ) (hi : i < n) (e : E) (he : e ∈ S i) :
        Relation.EqvGen R e (f i e) := (hmspec i (e, D (c (i + 1))) ⟨he, hw i hi⟩).1
    have hcenter (i : ℕ) (hi : i ≤ n) : F i (c 0) = c i := by
      induction i with
      | zero => rfl
      | succ i ih =>
          have hil : i < n := Nat.lt_of_succ_le hi
          have hip : i ≤ n := Nat.le_of_lt hil
          rw [hstep, Function.comp_apply, ih hip]
          exact hinj (c i) (hrel i hil (c i) (hc i hip)) (hnext i hil)
            (hmspec i (c i, D (c (i + 1))) ⟨hc i hip, hw i hil⟩).2
    obtain ⟨U, hU, hxU, hguard⟩ := exists_open_guarded_finite_chain F f S (c 0)
      hzero hstep n hs (fun i hi ↦ hcenter i hi ▸ hc i hi) hf
    exact ⟨f, F, U, hzero, hstep, hcenter, hf, hrel, hU, hxU, hguard⟩
  have leaf_selector_continuousAt_of_developing_charts
      {E : Type u} {V : Type v} {Z : Type w} [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace Z]
      (D : E → Z) (R : E → E → Prop) (P : E → Z → E)
      (hP : ∀ e z, Relation.EqvGen R e (P e z) ∧ D (P e z) = z)
      (hinj : ∀ e, Set.InjOn D {y : E | Relation.EqvGen R e y})
      (S : ℕ → Set E) (W : ℕ → Set Z) (H : ∀ i, (V × W i) ≃ₜ S i)
      (hcoord : ∀ i r z, D (H i (r, z)).val = z.val)
      (hplaque : ∀ i (e : S i) (z : W i),
        Relation.EqvGen R e.val (H i (((H i).symm e).1, z)).val)
      (c : ℕ → E) (n : ℕ)
      (hs : ∀ i, i ≤ n → IsOpen (S i))
      (hc : ∀ i, i ≤ n → c i ∈ S i)
      (hw : ∀ i, i < n → D (c (i + 1)) ∈ W i)
      (hnext : ∀ i, i < n → Relation.EqvGen R (c i) (c (i + 1)))
      (hW : IsOpen (W n)) (z : Z) (hz : z ∈ W n) :
      ContinuousAt (fun q : E × Z ↦ P q.1 q.2) (c 0, z) := by
    obtain ⟨f, F, U, hzero, hstep, hcenter, hf, hrel, _⟩ :=
      guarded_chain_from_developing_charts D R hinj S W H hcoord hplaque c n hs hc hw hnext
    exact leaf_selector_continuousAt_of_chart_chain D R P hP hinj F f S (c 0) n
      hzero hstep hs (fun i hi ↦ hcenter i hi ▸ hc i hi) hf hrel
      (W n) hW z hz (H n) (hcoord n) (hplaque n)
  have developing_chart_chain_of_leaf_path
      {E : Type u} {V : Type v} {Z : Type w} {A : Type a} [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace Z]
      (D : E → Z) (R : E → E → Prop)
      (O : A → Set E) (W : A → Set Z) (H : ∀ a, (V × W a) ≃ₜ O a)
      (hO : ∀ a, IsOpen (O a))
      (hcoord : ∀ a r z, D (H a (r, z)).val = z.val)
      (x y : E) (γ : Path x y)
      (hcover : ∀ t : unitInterval, ∃ a, γ t ∈ O a)
      (hleaf : ∀ t : unitInterval, Relation.EqvGen R x (γ t)) :
      ∃ (n : ℕ) (c : ℕ → E) (a : ℕ → A),
        c 0 = x ∧ c n = y ∧
        (∀ i, IsOpen (O (a i))) ∧
        ∀ i, c i ∈ O (a i) ∧ c (i + 1) ∈ O (a i) ∧
          D (c (i + 1)) ∈ W (a i) ∧ Relation.EqvGen R (c i) (c (i + 1)) := by
    classical
    obtain ⟨t, ht0, htmono, ⟨n, htn⟩, hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval
        (fun a ↦ (hO a).preimage γ.continuous)
        (fun s _ ↦ Set.mem_iUnion.mpr (hcover s))
    choose a ha using hsub
    let c : ℕ → E := fun i ↦ γ (t i)
    have hleft (i : ℕ) : c i ∈ O (a i) :=
      ha i ⟨le_rfl, htmono (Nat.le_succ i)⟩
    have hright (i : ℕ) : c (i + 1) ∈ O (a i) :=
      ha i ⟨htmono (Nat.le_succ i), le_rfl⟩
    refine ⟨n, c, a, ?_, ?_, fun i ↦ hO (a i), fun i ↦ ?_⟩
    · simpa only [c, ht0] using γ.source
    · simpa only [c, htn n le_rfl] using γ.target
    · refine ⟨hleft i, hright i, ?_, ?_⟩
      · let e : O (a i) := ⟨c (i + 1), hright i⟩
        have hc := hcoord (a i) (((H (a i)).symm e).1) (((H (a i)).symm e).2)
        have heq : D (c (i + 1)) = (((H (a i)).symm e).2).val := by
          simpa only [Prod.mk.eta, Homeomorph.apply_symm_apply] using hc
        rw [heq]
        exact (((H (a i)).symm e).2).property
      · exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (hleaf (t i))) (hleaf (t (i + 1)))
  have leaf_selector_continuousAt_of_leaf_path
      {E : Type u} {V : Type v} {Z : Type w} {A : Type a} [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace Z]
      (D : E → Z) (R : E → E → Prop) (P : E → Z → E)
      (hP : ∀ e z, Relation.EqvGen R e (P e z) ∧ D (P e z) = z)
      (hinj : ∀ e, Set.InjOn D {y : E | Relation.EqvGen R e y})
      (O : A → Set E) (W : A → Set Z) (H : ∀ a, (V × W a) ≃ₜ O a)
      (hO : ∀ a, IsOpen (O a)) (hW : ∀ a, IsOpen (W a))
      (hcoord : ∀ a r z, D (H a (r, z)).val = z.val)
      (hplaque : ∀ a (e : O a) (z : W a),
        Relation.EqvGen R e.val (H a (((H a).symm e).1, z)).val)
      (x y : E) (z : Z) (hyz : D y = z) (γ : Path x y)
      (hcover : ∀ t : unitInterval, ∃ a, γ t ∈ O a)
      (hleaf : ∀ t : unitInterval, Relation.EqvGen R x (γ t)) :
      ContinuousAt (fun q : E × Z ↦ P q.1 q.2) (x, z) := by
    obtain ⟨n, c, a, hc0, hcn, hs, hchain⟩ :=
      developing_chart_chain_of_leaf_path D R O W H hO hcoord x y γ hcover hleaf
    have hz : z ∈ W (a n) := by
      let e : O (a n) := ⟨c n, (hchain n).1⟩
      have heq : D (c n) = (((H (a n)).symm e).2).val := by
        simpa only [Prod.mk.eta, Homeomorph.apply_symm_apply] using
          hcoord (a n) (((H (a n)).symm e).1) (((H (a n)).symm e).2)
      have hmem : D (c n) ∈ W (a n) := heq ▸ (((H (a n)).symm e).2).property
      simpa only [hcn, hyz] using hmem
    have hcont := leaf_selector_continuousAt_of_developing_charts D R P hP hinj
      (fun i ↦ O (a i)) (fun i ↦ W (a i)) (fun i ↦ H (a i))
      (fun i ↦ hcoord (a i)) (fun i ↦ hplaque (a i)) c n
      (fun i _ ↦ hs i) (fun i _ ↦ (hchain i).1)
      (fun i _ ↦ (hchain i).2.2.1) (fun i _ ↦ (hchain i).2.2.2)
      (hW (a n)) z hz
    simpa only [hc0] using hcont
  have leaf_selector_continuous_of_intrinsic_leaf_lifts
      {E : Type u} {V : Type v} {Z : Type w} {A : Type a} [TopologicalSpace E] [TopologicalSpace V] [TopologicalSpace Z]
      (D : E → Z) (R : E → E → Prop) (P : E → Z → E)
      (hP : ∀ e z, Relation.EqvGen R e (P e z) ∧ D (P e z) = z)
      (hinj : ∀ e, Set.InjOn D {y : E | Relation.EqvGen R e y})
      (O : A → Set E) (W : A → Set Z) (H : ∀ a, (V × W a) ≃ₜ O a)
      (hO : ∀ a, IsOpen (O a)) (hW : ∀ a, IsOpen (W a))
      (hcover : ∀ e : E, ∃ a, e ∈ O a)
      (hcoord : ∀ a r z, D (H a (r, z)).val = z.val)
      (hplaque : ∀ a (e : O a) (z : W a),
        Relation.EqvGen R e.val (H a (((H a).symm e).1, z)).val)
      (L : E → Type l) [∀ e, TopologicalSpace (L e)] [∀ e, PathConnectedSpace (L e)]
      (lift : ∀ e, L e → E) (hlift : ∀ e, Continuous (lift e))
      (hrange : ∀ e, Set.range (lift e) = {y | Relation.EqvGen R e y}) :
      Continuous (fun q : E × Z ↦ P q.1 q.2) := by
    rw [continuous_iff_continuousAt]
    intro q
    have hx : q.1 ∈ Set.range (lift q.1) := by
      rw [hrange q.1]
      exact Relation.EqvGen.refl q.1
    have hy : P q.1 q.2 ∈ Set.range (lift q.1) := by
      rw [hrange q.1]
      exact (hP q.1 q.2).1
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    let γ : Path q.1 (P q.1 q.2) :=
      ((PathConnectedSpace.somePath a b).map (hlift q.1)).cast ha.symm hb.symm
    have hleaf (t : unitInterval) : Relation.EqvGen R q.1 (γ t) := by
      have hmem : γ t ∈ Set.range (lift q.1) :=
        ⟨(PathConnectedSpace.somePath a b) t, rfl⟩
      rw [hrange q.1] at hmem
      exact hmem
    exact leaf_selector_continuousAt_of_leaf_path D R P hP hinj O W H hO hW hcoord hplaque
      q.1 (P q.1 q.2) q.2 (hP q.1 q.2).2 γ (fun t ↦ hcover (γ t)) hleaf
  have unique_fibre_intersection_of_leaf_coordinate
      {E : Type u} {L : Type l} {Z : Type w} (D : E → Z) (R : E → E → Prop) (e : E)
      (lift : L → E) (coordinate : L ≃ Z)
      (hrange : Set.range lift = {y : E | Relation.EqvGen R e y})
      (hcoord : ∀ x, coordinate x = D (lift x)) (z : Z) :
      ∃! y : E, Relation.EqvGen R e y ∧ D y = z := by
    let x := coordinate.symm z
    have hx : D (lift x) = z :=
      (hcoord x).symm.trans (coordinate.apply_symm_apply z)
    refine ⟨lift x, ⟨?_, hx⟩, ?_⟩
    · have hm : lift x ∈ Set.range lift := Set.mem_range_self x
      rwa [hrange] at hm
    · intro y hy
      have hyrange : y ∈ Set.range lift := hrange.symm ▸ hy.1
      obtain ⟨x', rfl⟩ := hyrange
      apply congrArg lift
      apply coordinate.injective
      exact (hcoord x').trans (hy.2.trans ((hcoord x).trans hx).symm)

  let P : E → Z → E := fun e z ↦ lift e ((coordinate e).symm z)
  have hP (e : E) (z : Z) : Relation.EqvGen R e (P e z) ∧ D (P e z) = z := by
    constructor
    · have hm : P e z ∈ Set.range (lift e) := ⟨(coordinate e).symm z, rfl⟩
      rw [hrange e] at hm
      exact hm
    · exact (hleafcoord e ((coordinate e).symm z)).symm.trans
        ((coordinate e).apply_symm_apply z)
  have hinj (e : E) : Set.InjOn D {y : E | Relation.EqvGen R e y} := by
    intro y hy y' hy' heq
    obtain ⟨w, hw, huniq⟩ := unique_fibre_intersection_of_leaf_coordinate
      D R e (lift e) (coordinate e) (hrange e) (hleafcoord e) (D y)
    exact (huniq y ⟨hy, rfl⟩).trans (huniq y' ⟨hy', heq.symm⟩).symm
  have hcont := leaf_selector_continuous_of_intrinsic_leaf_lifts D R P hP hinj
    O W H hO hW hcover hcoord hplaque L lift hlift hrange
  let S : Setoid E :=
    { r := Relation.EqvGen R
      iseqv := ⟨Relation.EqvGen.refl,
        fun h ↦ Relation.EqvGen.symm _ _ h,
        fun h h' ↦ Relation.EqvGen.trans _ _ _ h h'⟩ }
  exact product_homeomorph_of_continuous_leaf_selector S D hD z₀ P hP hinj hcont

end HolomorphicAnosov.Ghys
