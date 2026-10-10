import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedCollapse
import YesMetaZFC.SetTheory.Notation

/-! # 有界超幂池的精确有界编码

节点的反向完备性直接量化支撑和代表，再要求原节点集中的实际有序对。
因此原池的全部条款都有 Δ₀ 编码，不缩小代表或节点的数学范围。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def eb_pool_m {d} (ω κ L X B J K P G A : Term d) : Formula 1 d := set[d] ⟪
  ⌜J⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜P⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜G⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜A⌝ₛ ∈ ⌜X⌝ₛ ∧
  ⌜FilterZF.source_m⌝ₚ(⌜X⌝ₛ, ⌜K⌝ₛ, ⌜P⌝ₛ) ∧ ⌜G⌝ₛ ⊆ ⌜X⌝ₛ ∧
  (∀ f ∈ ⌜X⌝ₛ, f ∈ ⌜G⌝ₛ ↔ ∀ p ∈ f, ∃ s ∈ ⌜K⌝ₛ, ∃ x ∈ ⌜B⌝ₛ, ⌜kpair0_m⌝ₚ(p, s, x)) ∧
  (∀ u ∈ ⌜A⌝ₛ, ⌜eb_node_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜K⌝ₛ, ⌜B⌝ₛ, ⌜J⌝ₛ, ⌜G⌝ₛ, ⌜P⌝ₛ, u)) ∧
  (∀ a ∈ ⌜J⌝ₛ, ∀ f ∈ ⌜G⌝ₛ, ∀ n ∈ ⌜ω⌝ₛ, ∀ D ∈ ⌜P⌝ₛ,
    ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, a) ∧ ⌜eb_space_m⌝ₚ(⌜κ⌝ₛ, ⌜K⌝ₛ, n, D) ∧ ⌜fn0_m⌝ₚ(D, ⌜B⌝ₛ, f) →
      ∃ u ∈ ⌜A⌝ₛ, ⌜kpair0_m⌝ₚ(u, a, f))⟫
derive_free_closed eb_pool_m

theorem eb_pool_delta_l {d} (ω κ L X B J K P G A : Term d) : (eb_pool_m ω κ L X B J K P G A).IsDelta0 := by
  unfold eb_pool_m
  repeat first
    | exact FilterZF.source_delta_l .. | exact eb_node_delta_l .. | exact eb_space_delta_l ..
    | exact fn0_delta_l .. | exact kpair0_delta_l .. | exact .mem .. | exact .atom ..
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.forallMem
    | apply Formula.IsDelta0.existsMem | apply Formula.IsDelta0.iff
    | apply Formula.IsDelta0.imp

theorem eb_pool_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω κ L X B J K P G A : Term d) :
    Formula.satisfies ρ (eb_pool_m ω κ L X B J K P G A) ↔
      Eb_pool_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (B.eval ρ) (J.eval ρ) (K.eval ρ) (P.eval ρ) (G.eval ρ) (A.eval ρ) := by
  simp only [eb_pool_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, FilterZF.source_sat_l,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, kpair0_sat_l hKP.1,
    eb_node_sat_l hKP.1, fn0_sat_l hKP.1, eb_space_sat_l hKP.1, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hj, hp, hg, ha, subsets, sub, graphs, nodes, total⟩
    refine ⟨hj, hp, hg, ha, subsets, fun f => ⟨fun hf => ⟨sub f hf, (graphs f (sub f hf)).mp hf⟩,
      fun ⟨hf, hs⟩ => (graphs f hf).mpr hs⟩, fun u => ⟨nodes u, ?_⟩⟩
    rintro ⟨a, ha, f, hf, pair, n, hn, D, hd, fn, space, gf⟩
    obtain ⟨v, hv, code⟩ := total a ha f hf n hn D hd ⟨fn, space, gf⟩
    exact kpair_unique_l M hKP.1 code pair ▸ hv
  · intro h
    refine ⟨h.indices, h.powers, h.functions, h.carrier, h.subsets, fun f hf => ((h.graphs f).mp hf).1,
      fun f hf => (h.graphs f).trans (and_iff_right hf), fun u hu => (h.nodes u).mp hu, ?_⟩
    intro a ha f hf n hn D hd spec
    obtain ⟨u, pair⟩ := (kp_pair_l hKP).total a f
    exact ⟨u, (h.nodes u).mpr ⟨a, ha, f, hf, pair, n, hn, D, hd, spec⟩, pair⟩

def ep_indices0_m {d} (ω L H J : Term d) : Formula 1 d := .conj (Formula.subset J H)
  (Formula.forallMem H (.iff (.mem .newest J.weaken) (ei_m ω.weaken L.weaken .newest)))
derive_free_closed ep_indices0_m

theorem ep_indices0_delta_l {d} (ω L H J : Term d) : (ep_indices0_m ω L H J).IsDelta0 :=
  .conj (.atom ..) (.forallMem _ (.iff (.mem ..) (ei_delta_l ..)))

theorem ep_indices0_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω L H J : Term d)
    (seq : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (L.eval ρ) (H.eval ρ)) :
    Formula.satisfies ρ (ep_indices0_m ω L H J) ↔ ∀ a, M.mem a (J.eval ρ) ↔ Ei_d (ω.eval ρ) (L.eval ρ) a := by
  have mem a (h : Ei_d (ω.eval ρ) (L.eval ρ) a) : M.mem a (H.eval ρ) := by
    obtain ⟨n, hn, fn, _⟩ := h
    exact (seq a).mpr ⟨n, hn, fn0_function_l hKP fn⟩
  simp only [ep_indices0_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    ei_sat_l hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨sub, h⟩ a => ⟨fun ha => (h a (sub a ha)).mp ha, fun ha => (h a (mem a ha)).mpr ha⟩,
    fun h => ⟨fun a ha => mem a ((h a).mp ha), fun a _ => h a⟩⟩

def eb_collapse_m {d} (ω κ L K X B F A Q Y e H : Term d) : Formula 1 d := set[d] ⟪
  ∃ J ∈ ⌜X⌝ₛ, ∃ P ∈ ⌜X⌝ₛ, ∃ G ∈ ⌜X⌝ₛ, ∃ U ∈ ⌜X⌝ₛ, ∃ R ∈ ⌜X⌝ₛ,
    ⌜eb_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜B⌝ₛ, J, ⌜K⌝ₛ, P, G, ⌜A⌝ₛ) ∧
    ⌜ep_indices0_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜H⌝ₛ, J) ∧ ⌜Q⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜e⌝ₛ ∈ ⌜X⌝ₛ ∧
    ⌜rd_graph_m .range⌝ₚ(⌜F⌝ₛ, ⌜F⌝ₛ, ⌜F⌝ₛ, U) ∧ ⌜rd_graph_m .mem⌝ₚ(⌜B⌝ₛ, ⌜B⌝ₛ, ⌜B⌝ₛ, R) ∧
    (∀ p ∈ ⌜Q⌝ₛ, ∃ u ∈ ⌜A⌝ₛ, ∃ v ∈ ⌜A⌝ₛ, ⌜kpair0_m⌝ₚ(p, u, v)) ∧
    (∀ u ∈ ⌜A⌝ₛ, ∀ v ∈ ⌜A⌝ₛ, ⌜rd_entry0_m⌝ₚ(u, v, ⌜Q⌝ₛ) ↔
      ⌜eb_link_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜B⌝ₛ, J, ⌜K⌝ₛ, U, R, ⌜F⌝ₛ, G, u, v)) ∧
    ⌜wc_map_m⌝ₚ(⌜A⌝ₛ, ⌜Q⌝ₛ, ⌜Y⌝ₛ, ⌜e⌝ₛ) ∧
    (∀ u ∈ ⌜A⌝ₛ, ∀ v ∈ ⌜A⌝ₛ, ∀ x ∈ ⌜Y⌝ₛ, ∀ y ∈ ⌜Y⌝ₛ,
      ⌜rd_entry0_m⌝ₚ(u, x, ⌜e⌝ₛ) → ⌜rd_entry0_m⌝ₚ(v, y, ⌜e⌝ₛ) → (⌜rd_entry0_m⌝ₚ(u, v, ⌜Q⌝ₛ) ↔ x ∈ y))⟫
derive_free_closed eb_collapse_m

theorem eb_collapse_delta_l {d} (ω κ L K X B F A Q Y e H : Term d) :
    (eb_collapse_m ω κ L K X B F A Q Y e H).IsDelta0 := by
  unfold eb_collapse_m
  repeat first
    | exact eb_pool_delta_l .. | exact ep_indices0_delta_l .. | exact rd_graph_delta_l ..
    | exact eb_link_delta_l .. | exact wc_map_delta_l .. | exact rd_entry0_delta_l ..
    | exact kpair0_delta_l .. | exact .mem ..
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.forallMem
    | apply Formula.IsDelta0.existsMem | apply Formula.IsDelta0.iff
    | apply Formula.IsDelta0.imp

theorem eb_collapse_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω κ L K X B F A Q Y e H : Term d)
    (seq : Fseq_space_d (kp_pair_l hKP) (ω.eval ρ) (L.eval ρ) (H.eval ρ)) :
    Formula.satisfies ρ (eb_collapse_m ω κ L K X B F A Q Y e H) ↔
      Eb_collapse_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (X.eval ρ) (B.eval ρ) (F.eval ρ)
        (A.eval ρ) (Q.eval ρ) (Y.eval ρ) (e.eval ρ) := by
  have indices (J P G U R : M.Domain) :
      Formula.satisfies (((((ρ.push J).push P).push G).push U).push R)
        (ep_indices0_m ω.weaken.weaken.weaken.weaken.weaken L.weaken.weaken.weaken.weaken.weaken
          H.weaken.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken.weaken) ↔
        ∀ a, M.mem a J ↔ Ei_d (ω.eval ρ) (L.eval ρ) a := by
    simpa only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using
      (ep_indices0_sat_l hKP (((((ρ.push J).push P).push G).push U).push R)
        ω.weaken.weaken.weaken.weaken.weaken L.weaken.weaken.weaken.weaken.weaken
        H.weaken.weaken.weaken.weaken.weaken Term.newest.weaken.weaken.weaken.weaken
        (by simpa only [Definitional.Term.eval_weaken] using seq))
  simp only [eb_collapse_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    eb_pool_sat_l hKP, indices, Formula.satisfies_mem_iff,
    rd_graph_sat_l hKP, Formula.satisfies_forallMem_iff, kpair0_sat_l hKP.1,
    Formula.satisfies_iff_iff, rd_entry0_sat_l hKP.1, eb_link_sat_l hKP.1, wc_map_sat_l hKP.1,
    Formula.satisfies_imp_iff, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨J, _, P, _, G, _, U, hU, R, hR, pool, indices, hQ, he, range, rel, shape, edges, wc, member⟩
    refine ⟨J, P, G, U, R, pool, indices, hU, hR, hQ, he, range, rel, shape, ?_, wc, ?_⟩
    · intro u v
      refine ⟨fun h => ?_, fun ⟨hu, hv, h⟩ => (edges u hu v hv).mpr h⟩
      obtain ⟨p, pair, hp⟩ := h
      obtain ⟨a, ha, b, hb, code⟩ := shape p hp
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M code pair
      exact ⟨ha, hb, (edges a ha b hb).mp ⟨p, pair, hp⟩⟩
    · intro u v x y hu hv
      exact member u (wc.function.bound_l hu).1 v (wc.function.bound_l hv).1
        x (wc.function.bound_l hu).2 y (wc.function.bound_l hv).2 hu hv
  · rintro ⟨J, P, G, U, R, pool, indices, hU, hR, hQ, he, range, rel, shape, edges, wc, member⟩
    exact ⟨J, pool.indices, P, pool.powers, G, pool.functions, U, hU, R, hR, pool, indices, hQ, he,
      range, rel, shape, fun u hu v hv => (edges u v).trans ⟨fun h => h.2.2, fun h => ⟨hu, hv, h⟩⟩,
      wc, fun u _ v _ x _ y _ => member u v x y⟩

end YesMetaZFC.SetTheory.LargeCardinal
