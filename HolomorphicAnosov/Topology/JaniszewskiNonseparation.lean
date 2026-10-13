import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Piecewise
import HolomorphicAnosov.Topology.FrontierConnectedComponentIn
import HolomorphicAnosov.Topology.OnePointFiniteChart
import HolomorphicAnosov.Analysis.Complex.ContinuousLogarithmOnComponents
import HolomorphicAnosov.Analysis.Complex.ContinuousLogarithmGluing
import HolomorphicAnosov.Topology.OnePointMarkedChart
import HolomorphicAnosov.Topology.ConnectedComplementComponent
import HolomorphicAnosov.Topology.CompactComplementComponentPath
import HolomorphicAnosov.Topology.JaniszewskiNeighborhoods
import HolomorphicAnosov.Topology.OnePointComplexLocallyPathConnected
import HolomorphicAnosov.Topology.OnePointCompactComplement
import HolomorphicAnosov.Topology.PlaneDomainConnectedComplement

/-!
# Janiszewski nonseparation for sphere and plane continua

The Riemann sphere is Mathlib's native one-point compactification `OnePoint ℂ`, following the
existing project convention. The plane specialization uses the usual topology on `ℂ` itself.
Same-component assertions use genuine `connectedComponentIn` membership. No local connectedness
of the compact sets, Jordan-curve hypothesis, arc assumption, or finite decomposition is imposed.

Source: John B. Conway, Functions of One Complex Variable II, GTM159, Springer1995, Chapter14 Lemma5.4, printed p.49 (PDF64), complete written human proof; supporting Chapter13 Corollary1.6 and Proposition1.7 printed p.4 (PDF19), and Proposition1.1 pp.1–2/Separation Theorem1.5 p.3. Local literature/conway-functions-one-complex-variable-II-1995.pdf. The two named open source prerequisites remain unproved; no transitive foundation closure is claimed.
DAG node: `topo.conway_janiszewski_nonseparation`.
-/

open Set

namespace HolomorphicAnosov.Topology

/-- Janiszewski's nonseparation theorem for compact continua in the Riemann sphere.

`IsConnected (A₁ ∩ A₂)` states both connectedness and nonemptiness of the intersection.
Consequently the nonemptiness included in `IsConnected A₁` and `IsConnected A₂` imposes no
additional restriction. Both marked points explicitly avoid the union; the component assertions
therefore select genuine, nonempty components. Singleton continua and coincident marked points
are allowed. Continua containing infinity are allowed. If the union exhausts the sphere, there
are no marked points satisfying the hypotheses.

Source: John B. Conway, Functions of One Complex Variable II, GTM159, Springer1995, Chapter14 Lemma5.4, printed p.49 (PDF64), complete written human proof; supporting Chapter13 Corollary1.6 and Proposition1.7 printed p.4 (PDF19), and Proposition1.1 pp.1–2/Separation Theorem1.5 p.3. Local literature/conway-functions-one-complex-variable-II-1995.pdf. The two named open source prerequisites remain unproved; no transitive foundation closure is claimed.

Complete natural-language proof of the DAG node:

J1:
If x=y, component reflexivity gives the conclusion. Otherwise apply the two-marked-point normalization theorem to the sphere points x,y. Its first homeomorphism sends y to infinity and its extended translation sends the finite image of x to zero. Both original compact continua avoid y, so their images avoid infinity and identify, through the finite chart, with compact plane continua. Homeomorphisms preserve intersections, connectedness, and the two complement-component hypotheses. It suffices to connect zero and infinity outside the image union.

J2:
For j=1,2, the sphere component of the complement of Aj containing0 and∞ is open and path connected: reachable points by paths form a relatively open and relatively closed subset, using small coordinate balls. Choose paths γj from0 to∞ missing Aj. Their images are compact connected. Since A1∩A2 misses both paths and is connected, it lies in one component G of the sphere minus γ1∪γ2. G is a plane open connected set, because∞ is on both paths. The sets Aj\G are compact and disjoint, since their intersection would lie in A1∩A2⊂G. Choose disjoint open V1,V2 containing them and missing γ1,γ2 respectively; the positive distance between the relevant disjoint compact sets gives these neighborhoods. Put U=G∪V1∪V2; it contains A1∪A2 and avoids0 and∞.

J3:
Every component of a path complement has connected sphere complement by the connected-complement component theorem. Each is a nonempty proper open sphere domain, so the Conway criterion makes it simply connected. The componentwise continuous logarithm theorem supplies branches for the normalized chart coordinate on each path complement. Holomorphicity of these logarithms is unnecessary for the exponential-lift winding convention.

J4:
On the connected common domain G, the two continuous logarithm branches differ by one constant integer multiple of 2πi. Subtract that constant from one branch so that they agree on G. The gluing theorem pastes the first branch on V1, the adjusted second branch on V2, and their common branch on G; V1 and V2 are disjoint, so all overlaps agree. In the normalized finite chart this gives a continuous logarithm L on a neighborhood of the compact union K, with exp(L(z))=z.

J5:
Let R be the component of ℂ minus K containing zero. If R were bounded, its frontier would lie in K. Restrict L to K and extend this continuous complex-valued function to all ℂ by the complex Tietze theorem. Paste exp of the extension on R with the identity outside R. The values agree on the frontier because exp(L(z))=z on K, so the pasted map f is continuous. It never vanishes: its inner values are exponentials and its outer values are nonzero since zero belongs to R. The exponential covering over the contractible plane therefore supplies a continuous global logarithm g of f. Choose a circle of positive radius enclosing the bounded set R. On this circle f is the identity. Uniqueness of exponential lifts identifies g along its standard once-around parametrization with g at the initial point plus 2πit. The parametrization has equal endpoints, while that lift has endpoint difference 2πi, a contradiction. Hence R is unbounded.

J6:
Unboundedness puts infinity in the closure of the sphere image of R: otherwise that image has closure avoiding infinity, whose finite preimage is compact and bounds R. Adjoining infinity to the image of the connected set R thus gives a connected subset of the sphere complement of K containing zero and infinity. They are in the same complement component. Undo the marked-point normalization to obtain the sphere conclusion. This final argument uses exponential covering and Tietze extension and does not use Jordan separation or any arc-access construction.

JP:
Embed the compact plane continua into OnePoint complex space. Continuous injective images preserve the individual component memberships, connectedness and intersection. Apply the sphere theorem. The compact-complement component comparison reflects the resulting component membership back to the plane.
-/
theorem janiszewski_nonseparation_sphere
    (A₁ A₂ : Set (OnePoint ℂ))
    (hcompact₁ : IsCompact A₁) (hcompact₂ : IsCompact A₂)
    (_hconnected₁ : IsConnected A₁) (_hconnected₂ : IsConnected A₂)
    (hintersection : IsConnected (A₁ ∩ A₂))
    (x y : OnePoint ℂ)
    (hx : x ∉ A₁ ∪ A₂) (hy : y ∉ A₁ ∪ A₂)
    (hcomponent₁ : y ∈ connectedComponentIn A₁ᶜ x)
    (hcomponent₂ : y ∈ connectedComponentIn A₂ᶜ x) :
    y ∈ connectedComponentIn (A₁ ∪ A₂)ᶜ x := by
  classical
  by_cases hxy : x = y
  · subst y
    exact mem_connectedComponentIn hx
  by_cases hsubset₁ : A₁ ⊆ A₂
  · simpa only [Set.union_eq_right.mpr hsubset₁] using hcomponent₂
  by_cases hsubset₂ : A₂ ⊆ A₁
  · simpa only [Set.union_eq_left.mpr hsubset₂] using hcomponent₁
  -- Conway 14.5.4: choose the two paths in the original individual complements.
  have hjoined (A : Set (OnePoint ℂ)) (hA : IsCompact A) (hxA : x ∉ A)
      (hxyA : y ∈ connectedComponentIn Aᶜ x) : JoinedIn Aᶜ x y :=
    joinedIn_compl_of_compact_component A hA x y hxA hxyA
  obtain ⟨γ₁, hγ₁⟩ := hjoined A₁ hcompact₁ (fun h ↦ hx (Or.inl h)) hcomponent₁
  obtain ⟨γ₂, hγ₂⟩ := hjoined A₂ hcompact₂ (fun h ↦ hx (Or.inr h)) hcomponent₂
  have havoid₁ : Disjoint A₁ (Set.range γ₁) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨t, rfl⟩
    exact hγ₁ t hz
  have havoid₂ : Disjoint A₂ (Set.range γ₂) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨t, rfl⟩
    exact hγ₂ t hz
  obtain ⟨a, ha, V₁, V₂, hGopen, hGconnected, hinterG, hV₁open, hV₂open,
      hVdisjoint, hrem₁, hrem₂, hV₁avoid, hV₂avoid, hcover, havoid⟩ :=
    janiszewski_neighborhoods A₁ A₂ (Set.range γ₁) (Set.range γ₂)
      hcompact₁ hcompact₂ hintersection (isCompact_range γ₁.continuous).isClosed
        (isCompact_range γ₂.continuous).isClosed havoid₁ havoid₂
  let T := Set.range γ₁ ∪ Set.range γ₂
  have hcomplement₁ (z : OnePoint ℂ) :
      IsConnected (connectedComponentIn (Set.range γ₁)ᶜ z)ᶜ :=
    connected_complement_component (isCompact_range γ₁.continuous).isClosed
      (isConnected_range γ₁.continuous) z
  have hcomplement₂ (z : OnePoint ℂ) :
      IsConnected (connectedComponentIn (Set.range γ₂)ᶜ z)ᶜ :=
    connected_complement_component (isCompact_range γ₂.continuous).isClosed
      (isConnected_range γ₂.continuous) z
  -- Conway J3: the components are proper open sphere domains with connected
  -- complements, so the connected-complement criterion applies before charting.
  have hsimple₁ (z : OnePoint ℂ) (hz : z ∉ Set.range γ₁) :
      IsSimplyConnected (connectedComponentIn (Set.range γ₁)ᶜ z) := by
    apply (conway_plane_domain_connected_complement_criterion _
      ⟨z, mem_connectedComponentIn hz⟩ ?_
      (isCompact_range γ₁.continuous).isClosed.isOpen_compl.connectedComponentIn
      (isConnected_connectedComponentIn_iff.mpr hz)).mpr (hcomplement₁ z)
    intro heq
    have hxmem : x ∈ connectedComponentIn (Set.range γ₁)ᶜ z :=
      heq.symm ▸ Set.mem_univ x
    exact (connectedComponentIn_subset (Set.range γ₁)ᶜ z hxmem) ⟨0, γ₁.source⟩
  have hsimple₂ (z : OnePoint ℂ) (hz : z ∉ Set.range γ₂) :
      IsSimplyConnected (connectedComponentIn (Set.range γ₂)ᶜ z) := by
    apply (conway_plane_domain_connected_complement_criterion _
      ⟨z, mem_connectedComponentIn hz⟩ ?_
      (isCompact_range γ₂.continuous).isClosed.isOpen_compl.connectedComponentIn
      (isConnected_connectedComponentIn_iff.mpr hz)).mpr (hcomplement₂ z)
    intro heq
    have hxmem : x ∈ connectedComponentIn (Set.range γ₂)ᶜ z :=
      heq.symm ▸ Set.mem_univ x
    exact (connectedComponentIn_subset (Set.range γ₂)ᶜ z hxmem) ⟨0, γ₂.source⟩
  -- The component branches glue on Conway's neighborhood because its two open
  -- pieces intersect exactly in G. The normalized chart below supplies g.
  have hlog_neighborhood (g : OnePoint ℂ → ℂ)
      (hg₁ : ContinuousOn g (Set.range γ₁)ᶜ)
      (hg₂ : ContinuousOn g (Set.range γ₂)ᶜ)
      (hg0 : ∀ z ∈ (Set.range γ₁ ∩ Set.range γ₂)ᶜ, g z ≠ 0) :
      ∃ L : OnePoint ℂ → ℂ,
        ContinuousOn L (connectedComponentIn Tᶜ a ∪ V₁ ∪ V₂) ∧
        EqOn (Complex.exp ∘ L) g (connectedComponentIn Tᶜ a ∪ V₁ ∪ V₂) := by
    obtain ⟨L₁, hL₁, he₁⟩ :=
      Analysis.Complex.continuous_logarithm_of_simplyConnected_components
        (isCompact_range γ₁.continuous).isClosed.isOpen_compl hsimple₁ hg₁
        (fun z hz ↦ hg0 z (fun h ↦ hz h.1))
    obtain ⟨L₂, hL₂, he₂⟩ :=
      Analysis.Complex.continuous_logarithm_of_simplyConnected_components
        (isCompact_range γ₂.continuous).isClosed.isOpen_compl hsimple₂ hg₂
        (fun z hz ↦ hg0 z (fun h ↦ hz h.2))
    have hsub₁ : connectedComponentIn Tᶜ a ∪ V₁ ⊆ (Set.range γ₁)ᶜ := by
      rintro z (hz | hz)
      · exact fun h ↦ connectedComponentIn_subset Tᶜ a hz (Or.inl h)
      · exact hV₁avoid hz
    have hsub₂ : connectedComponentIn Tᶜ a ∪ V₂ ⊆ (Set.range γ₂)ᶜ := by
      rintro z (hz | hz)
      · exact fun h ↦ connectedComponentIn_subset Tᶜ a hz (Or.inr h)
      · exact hV₂avoid hz
    have hinter : (connectedComponentIn Tᶜ a ∪ V₁) ∩
        (connectedComponentIn Tᶜ a ∪ V₂) = connectedComponentIn Tᶜ a := by
      ext z
      constructor
      · rintro ⟨hz | hz, hz' | hz'⟩
        · exact hz
        · exact hz
        · exact hz'
        · exact (Set.disjoint_left.mp hVdisjoint hz hz').elim
      · exact fun hz ↦ ⟨Or.inl hz, Or.inl hz⟩
    have hc : IsConnected ((connectedComponentIn Tᶜ a ∪ V₁) ∩
        (connectedComponentIn Tᶜ a ∪ V₂)) := by
      rw [hinter]
      exact hGconnected
    obtain ⟨L, hLc, hLe⟩ := Analysis.Complex.continuous_logarithm_on_union
      (hGopen.union hV₁open) (hGopen.union hV₂open) hc
      (hL₁.mono hsub₁) (he₁.mono hsub₁) (hL₂.mono hsub₂) (he₂.mono hsub₂)
    have hsub : connectedComponentIn Tᶜ a ∪ V₁ ∪ V₂ ⊆
        (connectedComponentIn Tᶜ a ∪ V₁) ∪ (connectedComponentIn Tᶜ a ∪ V₂) := by
      rintro z (hz | hz)
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz)
    exact ⟨L, hLc.mono hsub, hLe.mono hsub⟩
  -- Conway J1 normalization is available as an explicit sphere homeomorphism.
  have hnormalized : ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ,
      e x = OnePoint.some 0 ∧ e y = OnePoint.infty :=
    onePoint_homeomorph_send_two_points_to_zero_infty x y hxy
  obtain ⟨enorm, hnormx, hnormy⟩ := hnormalized
  obtain ⟨gchart, hgchart, hgzero, hgcoord⟩ :=
    onePoint_finite_chart x y enorm hnormx hnormy
  have hgcont₁ : ContinuousOn gchart (Set.range γ₁)ᶜ :=
    hgchart.mono (by
      intro z hz hzy
      apply hz
      exact ⟨1, γ₁.target.trans hzy.symm⟩)
  have hgcont₂ : ContinuousOn gchart (Set.range γ₂)ᶜ :=
    hgchart.mono (by
      intro z hz hzy
      apply hz
      exact ⟨1, γ₂.target.trans hzy.symm⟩)
  have hgnonzero : ∀ z ∈ (Set.range γ₁ ∩ Set.range γ₂)ᶜ, gchart z ≠ 0 := by
    intro z hz hg
    have hzy : z ≠ y := by
      intro heq
      exact hz ⟨⟨1, γ₁.target.trans heq.symm⟩, ⟨1, γ₂.target.trans heq.symm⟩⟩
    have hzx := (hgzero z hzy).mp hg
    exact hz ⟨⟨0, γ₁.source.trans hzx.symm⟩, ⟨0, γ₂.source.trans hzx.symm⟩⟩
  obtain ⟨L, hLcontinuous, hLexp⟩ :=
    hlog_neighborhood gchart hgcont₁ hgcont₂ hgnonzero
  let N := connectedComponentIn Tᶜ a ∪ V₁ ∪ V₂
  have hNopen : IsOpen N := (hGopen.union hV₁open).union hV₂open
  have hNy : ∀ z ∈ N, z ≠ y := by
    intro z hz heq
    exact havoid hz ⟨⟨1, γ₁.target.trans heq.symm⟩, ⟨1, γ₂.target.trans heq.symm⟩⟩
  let U : Set ℂ := OnePoint.some ⁻¹' (enorm '' N)
  let K : Set ℂ := gchart '' (A₁ ∪ A₂)
  have hUopen : IsOpen U := (enorm.isOpenMap N hNopen).preimage OnePoint.continuous_coe
  have hKcompact : IsCompact K :=
    (hcompact₁.union hcompact₂).image_of_continuousOn (hgchart.mono (by
      intro z hz hzy
      exact hy (hzy ▸ hz)))
  have hKU : K ⊆ U := by
    rintro w ⟨z, hz, rfl⟩
    change OnePoint.some (gchart z) ∈ enorm '' N
    rw [hgcoord z (hNy z (hcover hz))]
    exact ⟨z, hcover hz, rfl⟩
  let j : ℂ → OnePoint ℂ := enorm.symm ∘ OnePoint.some
  have hjcont : Continuous j := enorm.symm.continuous.comp OnePoint.continuous_coe
  have hjN : MapsTo j U N := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := hz
    change enorm.symm (OnePoint.some z) ∈ N
    rw [← heq, enorm.symm_apply_apply]
    exact hw
  let Lplane : ℂ → ℂ := L ∘ j
  have hLplane : ContinuousOn Lplane U := hLcontinuous.comp hjcont.continuousOn hjN
  have hLplane_exp : EqOn (Complex.exp ∘ Lplane) id U := by
    intro z hz
    change Complex.exp (L (j z)) = z
    calc
      Complex.exp (L (j z)) = gchart (j z) := hLexp (hjN hz)
      _ = z := ?_
    apply OnePoint.coe_injective
    rw [hgcoord (j z) (hNy _ (hjN hz))]
    exact enorm.apply_symm_apply _
  have hUzero : (0 : ℂ) ∉ U := by
    intro hz
    exact Complex.exp_ne_zero (Lplane 0) (hLplane_exp hz)
  have hKzero : (0 : ℂ) ∉ K := fun hz ↦ hUzero (hKU hz)
  let R := connectedComponentIn Kᶜ (0 : ℂ)
  have hzeroR : (0 : ℂ) ∈ R := mem_connectedComponentIn hKzero
  have hRc : R ⊆ Kᶜ := connectedComponentIn_subset _ _
  have hRconn : IsConnected R := isConnected_connectedComponentIn_iff.mpr hKzero
  have hunbounded : ¬ Bornology.IsBounded R := by
    intro hRb
    have hfront : frontier R ⊆ K := by
      simpa only [compl_compl] using
        frontier_connectedComponentIn_subset_compl hKcompact.isClosed.isOpen_compl 0
    let l : C(K, ℂ) := ⟨fun z ↦ Lplane z, (hLplane.mono hKU).domRestrict⟩
    obtain ⟨F, hF⟩ := l.exists_extension'
      hKcompact.isClosed.isClosedEmbedding_subtypeVal
    have hFexp (z : ℂ) (hz : z ∈ K) : Complex.exp (F z) = z := by
      have heq : F z = l ⟨z, hz⟩ := congrFun hF ⟨z, hz⟩
      rw [heq]
      exact hLplane_exp (hKU hz)
    let f : ℂ → ℂ := R.piecewise (fun z ↦ Complex.exp (F z)) id
    have hf : Continuous f := Continuous.piecewise (fun z hz ↦ hFexp z (hfront hz))
      (Complex.continuous_exp.comp F.continuous) continuous_id
    have hf0 : ∀ z, f z ≠ 0 := by
      intro z
      by_cases hz : z ∈ R
      · simp [f, hz]
      · simp only [f, Set.piecewise_eq_of_notMem R _ _ hz, id_eq]
        intro heq
        exact hz (heq ▸ hzeroR)
    let f' : C(ℂ, {z : ℂ // z ≠ 0}) := ⟨fun z ↦ ⟨f z, hf0 z⟩, hf.subtype_mk _⟩
    obtain ⟨g, hg, _⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
      f' 0 (F 0) (by apply Subtype.ext; change Complex.exp (F 0) = f 0; simp [f, hzeroR])
    have hgf (z : ℂ) : Complex.exp (g z) = f z :=
      congrArg Subtype.val (congrFun hg.2 z)
    obtain ⟨C, hC⟩ := hRb.subset_closedBall 0
    let r := max C 0 + 1
    have hr : 0 < r := by dsimp [r]; linarith [le_max_right C 0]
    have hCr : C < r := by dsimp [r]; linarith [le_max_left C 0]
    let τ : ℂ := 2 * Real.pi * Complex.I
    let p : unitInterval → ℂ := fun t ↦ (r : ℂ) * Complex.exp (τ * (t : ℝ))
    have hp : Continuous p := by fun_prop
    have hnorm (t : unitInterval) : ‖p t‖ = r := by
      simp [p, Complex.norm_exp, τ, abs_of_pos hr]
    have hpout (t : unitInterval) : p t ∉ R := by
      intro ht
      have ht' : ‖p t‖ ≤ C := by simpa using hC ht
      rw [hnorm] at ht'
      exact (not_le_of_gt hCr) ht'
    have hgp (t : unitInterval) :
        Complex.exp (g (p t)) = (r : ℂ) * Complex.exp (τ * (t : ℝ)) := by
      rw [hgf]
      exact Set.piecewise_eq_of_notMem R _ _ (hpout t)
    have hp01 : p 0 = p 1 := by simp [p, τ]
    let k : unitInterval → ℂ := fun t ↦ g (p 0) + τ * (t : ℝ)
    have hk : Continuous k := by fun_prop
    have hgk : (fun t ↦ g (p t)) = k := by
      refine Complex.isCoveringMap_exp.eq_of_comp_eq (g.continuous.comp hp) hk ?_ 0 ?_
      · funext t
        apply Subtype.ext
        change Complex.exp (g (p t)) = Complex.exp (k t)
        rw [hgp]
        dsimp [k]
        rw [Complex.exp_add, hgp 0]
        simp
      · simp [k]
    have hτ : τ = 0 := by
      have heq := congrFun hgk 1
      simp only [k, Set.Icc.coe_one, Complex.ofReal_one, mul_one] at heq
      rw [← hp01] at heq
      exact add_eq_left.mp heq.symm
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) hτ
  let Rs : Set (OnePoint ℂ) := insert OnePoint.infty (OnePoint.some '' R)
  have hinftyCl : (OnePoint.infty : OnePoint ℂ) ∈ closure (OnePoint.some '' R) := by
    by_contra hn
    have hc := ((OnePoint.isClosed_iff_of_notMem hn).mp isClosed_closure).2
    exact hunbounded (hc.isBounded.subset (fun z hz ↦ subset_closure ⟨z, hz, rfl⟩))
  have hRsconn : IsConnected Rs :=
    (hRconn.image _ OnePoint.continuous_coe.continuousOn).subset_closure
      (subset_insert _ _) (insert_subset hinftyCl subset_closure)
  have hRsK : Rs ⊆ (OnePoint.some '' K)ᶜ := by
    intro z hz
    rcases hz with hz | ⟨w, hw, rfl⟩
    · subst z
      exact OnePoint.infty_notMem_image_coe
    · rintro ⟨v, hv, heq⟩
      exact hRc hw (OnePoint.coe_injective heq ▸ hv)
  have hfinal : OnePoint.infty ∈
      connectedComponentIn (OnePoint.some '' K)ᶜ (OnePoint.some 0) :=
    hRsconn.isPreconnected.subset_connectedComponentIn
      (show OnePoint.some 0 ∈ Rs from Or.inr ⟨0, hzeroR, rfl⟩) hRsK
      (show OnePoint.infty ∈ Rs from Or.inl rfl)
  have himage : enorm '' (A₁ ∪ A₂) = OnePoint.some '' K := by
    rw [show K = gchart '' (A₁ ∪ A₂) from rfl, ← Set.image_comp]
    apply Set.image_congr
    intro z hz
    exact (hgcoord z (hNy _ (hcover hz))).symm
  have hcomp := enorm.image_connectedComponentIn
    (show x ∈ (A₁ ∪ A₂)ᶜ from hx)
  rw [enorm.image_compl, himage, hnormx] at hcomp
  rw [← hcomp, ← hnormy] at hfinal
  exact enorm.injective.mem_set_image.mp hfinal


/-- Janiszewski's nonseparation theorem for compact plane continua, with all component
assertions taken in the plane. Singleton continua and coincident marked points are allowed.

Source: John B. Conway, Functions of One Complex Variable II, GTM159, Springer1995, Chapter14 Lemma5.4, printed p.49 (PDF64), complete written human proof; supporting Chapter13 Corollary1.6 and Proposition1.7 printed p.4 (PDF19), and Proposition1.1 pp.1–2/Separation Theorem1.5 p.3. Local literature/conway-functions-one-complex-variable-II-1995.pdf. The two named open source prerequisites remain unproved; no transitive foundation closure is claimed.

Complete natural-language proof of the DAG node:

J1:
If x=y, component reflexivity gives the conclusion. Otherwise apply the two-marked-point normalization theorem to the sphere points x,y. Its first homeomorphism sends y to infinity and its extended translation sends the finite image of x to zero. Both original compact continua avoid y, so their images avoid infinity and identify, through the finite chart, with compact plane continua. Homeomorphisms preserve intersections, connectedness, and the two complement-component hypotheses. It suffices to connect zero and infinity outside the image union.

J2:
For j=1,2, the sphere component of the complement of Aj containing0 and∞ is open and path connected: reachable points by paths form a relatively open and relatively closed subset, using small coordinate balls. Choose paths γj from0 to∞ missing Aj. Their images are compact connected. Since A1∩A2 misses both paths and is connected, it lies in one component G of the sphere minus γ1∪γ2. G is a plane open connected set, because∞ is on both paths. The sets Aj\G are compact and disjoint, since their intersection would lie in A1∩A2⊂G. Choose disjoint open V1,V2 containing them and missing γ1,γ2 respectively; the positive distance between the relevant disjoint compact sets gives these neighborhoods. Put U=G∪V1∪V2; it contains A1∪A2 and avoids0 and∞.

J3:
Every component of a path complement has connected sphere complement by the connected-complement component theorem. Each is a nonempty proper open sphere domain, so the Conway criterion makes it simply connected. The componentwise continuous logarithm theorem supplies branches for the normalized chart coordinate on each path complement. Holomorphicity of these logarithms is unnecessary for the exponential-lift winding convention.

J4:
On the connected common domain G, the two continuous logarithm branches differ by one constant integer multiple of 2πi. Subtract that constant from one branch so that they agree on G. The gluing theorem pastes the first branch on V1, the adjusted second branch on V2, and their common branch on G; V1 and V2 are disjoint, so all overlaps agree. In the normalized finite chart this gives a continuous logarithm L on a neighborhood of the compact union K, with exp(L(z))=z.

J5:
Let R be the component of ℂ minus K containing zero. If R were bounded, its frontier would lie in K. Restrict L to K and extend this continuous complex-valued function to all ℂ by the complex Tietze theorem. Paste exp of the extension on R with the identity outside R. The values agree on the frontier because exp(L(z))=z on K, so the pasted map f is continuous. It never vanishes: its inner values are exponentials and its outer values are nonzero since zero belongs to R. The exponential covering over the contractible plane therefore supplies a continuous global logarithm g of f. Choose a circle of positive radius enclosing the bounded set R. On this circle f is the identity. Uniqueness of exponential lifts identifies g along its standard once-around parametrization with g at the initial point plus 2πit. The parametrization has equal endpoints, while that lift has endpoint difference 2πi, a contradiction. Hence R is unbounded.

J6:
Unboundedness puts infinity in the closure of the sphere image of R: otherwise that image has closure avoiding infinity, whose finite preimage is compact and bounds R. Adjoining infinity to the image of the connected set R thus gives a connected subset of the sphere complement of K containing zero and infinity. They are in the same complement component. Undo the marked-point normalization to obtain the sphere conclusion. This final argument uses exponential covering and Tietze extension and does not use Jordan separation or any arc-access construction.

JP:
Embed the compact plane continua into OnePoint complex space. Continuous injective images preserve the individual component memberships, connectedness and intersection. Apply the sphere theorem. The compact-complement component comparison reflects the resulting component membership back to the plane.
-/
theorem janiszewski_nonseparation_plane
    (A₁ A₂ : Set ℂ)
    (hcompact₁ : IsCompact A₁) (hcompact₂ : IsCompact A₂)
    (hconnected₁ : IsConnected A₁) (hconnected₂ : IsConnected A₂)
    (hintersection : IsConnected (A₁ ∩ A₂))
    (x y : ℂ)
    (hx : x ∉ A₁ ∪ A₂) (hy : y ∉ A₁ ∪ A₂)
    (hcomponent₁ : y ∈ connectedComponentIn A₁ᶜ x)
    (hcomponent₂ : y ∈ connectedComponentIn A₂ᶜ x) :
    y ∈ connectedComponentIn (A₁ ∪ A₂)ᶜ x := by
  let f : ℂ → OnePoint ℂ := (↑)
  have hcont : Continuous f := OnePoint.continuous_coe
  have himg (A : Set ℂ) (hxA : x ∉ A)
      (hxyA : y ∈ connectedComponentIn Aᶜ x) :
      f y ∈ connectedComponentIn (f '' A)ᶜ (f x) := by
    apply connectedComponentIn_mono (f x) (show f '' Aᶜ ⊆ (f '' A)ᶜ from ?_)
      (hcont.continuousOn.mapsTo_connectedComponentIn hxA hxyA)
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    exact hz (OnePoint.coe_injective heq ▸ hw)
  have hinter : f '' (A₁ ∩ A₂) = f '' A₁ ∩ f '' A₂ :=
    Set.image_inter OnePoint.coe_injective
  have hs := janiszewski_nonseparation_sphere
    (f '' A₁) (f '' A₂) (hcompact₁.image hcont) (hcompact₂.image hcont)
    (hconnected₁.image f hcont.continuousOn) (hconnected₂.image f hcont.continuousOn)
    (hinter ▸ hintersection.image f hcont.continuousOn) (f x) (f y)
    (by simpa [f] using hx) (by simpa [f] using hy)
    (himg A₁ (fun h ↦ hx (Or.inl h)) hcomponent₁)
    (himg A₂ (fun h ↦ hx (Or.inr h)) hcomponent₂)
  apply onePoint_complex_complement_component (hcompact₁.union hcompact₂) hx hy
  simpa only [image_union] using hs

end HolomorphicAnosov.Topology

