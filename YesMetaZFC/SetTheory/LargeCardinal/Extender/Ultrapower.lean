import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative
import YesMetaZFC.Model.SetTheory.DirectedSystem.Isomorphism
import YesMetaZFC.Model.SetTheory.Embedding.Range
import YesMetaZFC.Model.SetTheory.Internal.Extensionality
import YesMetaZFC.Model.SetTheory.Relations.Collapse
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceFormula

/-! # 全分量图的代表读取及恒等、复合律 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem ep_representatives_l (hE : Extensional M) {ω κ L X R F a c C S B : M.Domain}
    (hF : Em_source_d ω κ L X F) (hm : Ep_component_d I ω κ L X R F a c)
    (hc : Smdl_d I c C S) (hB : M.mem B C) : ∃ n, M.mem n ω ∧ Fn0_d n L a ∧
      (∃ f, M.mem f B) ∧ ∀ f, M.mem f B → M.mem f X ∧ Ep_fun_d κ X n f := by
  obtain ⟨n, D, U, G, p, C', S', hn, ha, hD, haU, hG, hp⟩ := hm
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hp.code hc
  have hu := (hF.at_l hE haU ha hD).base
  obtain ⟨f, hf⟩ := (hp.map.range B).mp hB
  refine ⟨n, hn, ha, ⟨f, hp.map.representative_l I hu hf⟩, fun g hg => ?_⟩
  have hgp := hp.map.member_l I hE hu hB hg
  have hgG := hp.map.projection.input_mem_of_pairMember hgp
  exact ⟨((hG g).mp hgG).1, D, hD, ((hG g).mp hgG).2⟩

theorem ep_relation_l (hE : Extensional M) {ω κ L X R F a c C S B D U f g : M.Domain}
    (hF : Em_source_d ω κ L X F) (hm : Ep_component_d I ω κ L X R F a c)
    (hc : Smdl_d I c C S) (hB : M.mem B C) (hD : M.mem D C) (hf : M.mem f B) (hg : M.mem g D)
    (haU : Rd_entry_d a U F) : M.PairMember I B D S ↔ Rp_rel_d I X U R f g := by
  obtain ⟨n, E, V, G, p, C', S', _, ha, hE', haV, _, hp⟩ := hm
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hp.code hc
  have eu := hF.function a V U haV haU
  subst V
  have hu := (hF.at_l hE haU ha hE').base
  exact hp.relation f g B D (hp.map.member_l I hE hu hB hf) (hp.map.member_l I hE hu hD hg)

theorem ep_arrow_id_l (hZF : M.Models ZF) {ω κ L X R F a c C S B : M.Domain}
    (hF : Em_source_d ω κ L X F) (ha : Ei_d ω L a) (hm : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c)
    (hc : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C S) (hB : M.mem B C) : Ep_arrow_d ω κ L X a a B B := by
  obtain ⟨_, _, _, inj⟩ := ha
  obtain ⟨n, hn, hna, ⟨f, hf⟩, functions⟩ := ep_representatives_l _ hZF.1 hF hm hc hB
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF hna ⟨fn0_function_l (ZF.modelsKP hZF) hna, inj⟩ (fun i _ hi => ⟨i, hi⟩)
  have idq i j (hij : Rd_entry_d i j q) : i = j := by
    obtain ⟨x, _, hix⟩ := hna.2.1 i (hq.bound_l hij).1
    exact inj i j x hix ((hqa.value_l hq hna hij).mp hix)
  exact ⟨n, n, q, f, f, hn, hn, hq, hna, hqa, hf, hf, ep_pull_id_l hZF.1 (functions f hf).2 idq⟩

theorem ep_arrow_comp_l (hZF : M.Models ZF) {ω κ K L X R F a b c v w B T C V x y z : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (hco : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F)
    (hc : Ei_d ω L c)
    (hbM : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F b v)
    (hcM : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F c w)
    (hB : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) v B T)
    (hC : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) w C V)
    (hy : M.mem y B) (hz : M.mem z C) (hxy : Ep_arrow_d ω κ L X a b x y) (hyz : Ep_arrow_d ω κ L X b c y z) :
    Ep_arrow_d ω κ L X a c x z := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_, _, _, inj⟩ := hc
  obtain ⟨m, n, q, f, g, hm, hn, hq, hnb, hqa, hf, hg, hfg⟩ := hxy
  have edge := hyz
  obtain ⟨n', l, r, _, _, _, hl, hr, hlc, hrb, _⟩ := hyz
  have en := hrb.1.domain_eq_l hZF.1 hnb
  subst n'
  obtain ⟨j, B', T', C', V', hb, hc, _, _, _, spec, any⟩ := ep_map_l hZF h hF hco hn hl hr hlc inj hrb hbM hcM
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hb hB
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hc hC
  obtain ⟨g', hg', hgg'⟩ := any y z ((spec y z).mpr ⟨hy, hz, edge⟩) g hg
  obtain ⟨s, hs⟩ := cp0_exists_l (ZF.modelsKP hZF) hq hr
  exact ⟨m, l, s, f, g', hm, hl, hs.1, hlc, Cp0_d.assoc_l hr hq hs hlc hrb hqa,
    hf, hg', ep_pull_comp_l (ZF.modelsKP hZF) hq hr hs hfg hgg'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部源分量的带标号并及其实际过渡关系 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_at_d (Z a B : M.Domain) : Prop := ∃ c C S, Rd_entry_d a c Z ∧ KPair_d M c C S ∧ M.mem B C
def ep_at_m {d} (Z a B : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (rd_entry_m a.weaken.weaken.weaken (.bound 2) Z.weaken.weaken.weaken)
    (.conj (kpair_m (.bound 2) (.bound 1) .newest) (.mem B.weaken.weaken.weaken (.bound 1))))))
derive_free_closed ep_at_m
theorem ep_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Z a B : Term d) :
    Formula.satisfies ρ (ep_at_m Z a B) ↔ Ep_at_d (Z.eval ρ) (a.eval ρ) (B.eval ρ) := by
  simp only [ep_at_m, Ep_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, kpair_sat_l M hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

def Ep_rel_d (Z a B D : M.Domain) : Prop := ∃ c C S, Rd_entry_d a c Z ∧ KPair_d M c C S ∧ Rd_entry_d B D S
def ep_rel_m {d} (Z a B D : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (rd_entry_m a.weaken.weaken.weaken (.bound 2) Z.weaken.weaken.weaken)
    (.conj (kpair_m (.bound 2) (.bound 1) .newest) (rd_entry_m B.weaken.weaken.weaken D.weaken.weaken.weaken .newest)))))
derive_free_closed ep_rel_m
theorem ep_rel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Z a B D : Term d) :
    Formula.satisfies ρ (ep_rel_m Z a B D) ↔ Ep_rel_d (Z.eval ρ) (a.eval ρ) (B.eval ρ) (D.eval ρ) := by
  simp only [ep_rel_m, Ep_rel_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, kpair_sat_l M hE, Definitional.Term.eval_weaken]; rfl

theorem ep_at_read_l {J Q Z a c C S B : M.Domain} (hz : Fn0_d J Q Z)
    (hac : Rd_entry_d a c Z) (hc : KPair_d M c C S) : Ep_at_d Z a B ↔ M.mem B C := by
  refine ⟨fun ⟨d, D, T, had, hd, hB⟩ => ?_, fun hB => ⟨c, C, S, hac, hc, hB⟩⟩
  have e := hz.2.2 a (hz.bound_l hac).1 d (hz.bound_l had).2 c (hz.bound_l hac).2 had hac
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M (e ▸ hd) hc
  exact hB

theorem ep_rel_read_l {J Q Z a c C S B D : M.Domain} (hz : Fn0_d J Q Z)
    (hac : Rd_entry_d a c Z) (hc : KPair_d M c C S) : Ep_rel_d Z a B D ↔ Rd_entry_d B D S := by
  refine ⟨fun ⟨d, E, T, had, hd, hBD⟩ => ?_, fun hBD => ⟨c, C, S, hac, hc, hBD⟩⟩
  have e := hz.2.2 a (hz.bound_l hac).1 d (hz.bound_l had).2 c (hz.bound_l hac).2 had hac
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M (e ▸ hd) hc
  exact hBD

theorem ep_at_model_l (hZF : M.Models ZF) {ω κ L X R F Z a B : M.Domain}
    (models : ∀ a c, Rd_entry_d a c Z → Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c)
    (hB : Ep_at_d Z a B) : ∃ c C S, Rd_entry_d a c Z ∧
      Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c ∧
      Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C S ∧ M.mem B C := by
  obtain ⟨c, C, S, hac, hc, hB⟩ := hB
  have hm := models a c hac
  obtain ⟨_, _, _, _, _, C', S', _, _, _, _, _, hp⟩ := hm
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hc hp.code.1
  exact ⟨c, C, S, hac, models a c hac, hp.code, hB⟩

structure Eg_graph_d (ω κ L X J O Z A p T S : M.Domain) : Prop where
  order : Di_order_d J O
  order_spec : ∀ a b, Rd_entry_d a b O ↔ M.mem a J ∧ M.mem b J ∧ ∃ q, Ei_map_d ω L a b q
  projection : Fn0_d A J p
  indices : ∀ a, M.mem a J ↔ Ei_d ω L a
  codes : ∃ Q, Fn0_d J Q Z
  nodes : ∀ u, M.mem u A ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z a B
  index : ∀ u a B, KPair_d M u a B → (Rd_entry_d u a p ↔ M.mem u A)
  arrows : ∀ u v, Rd_entry_d u v T ↔ M.mem u A ∧ M.mem v A ∧
    ∃ a b B C, KPair_d M u a B ∧ KPair_d M v b C ∧ Ep_arrow_d ω κ L X a b B C
  relations : ∀ u v, Rd_entry_d u v S ↔ M.mem u A ∧ M.mem v A ∧
    ∃ a B C, KPair_d M u a B ∧ KPair_d M v a C ∧ Ep_rel_d Z a B C

structure Ep_graph_d (I : kpair_convention_l.Interpretation M) (ω κ L X R F J O Z A p T S : M.Domain) : Prop
    extends Eg_graph_d ω κ L X J O Z A p T S where
  components : ∀ a c, Rd_entry_d a c Z → Ep_component_d I ω κ L X R F a c

def Ep_lift_d (ω κ L X a b B C : M.Domain) : Prop := ∀ f, M.mem f B → ∃ m n q g,
  M.mem m ω ∧ M.mem n ω ∧ Fn0_d m n q ∧ Fn0_d n L b ∧ Cp0_d m n L q b a ∧
    M.mem g C ∧ Ep_pull_d κ X m n q f g

def Eg_transition_d (I : kpair_convention_l.Interpretation M) (ω κ L X O Z : M.Domain) : Prop :=
  ∀ a b, Rd_entry_d a b O → ∃ j c C V d D W,
    Rd_entry_d a c Z ∧ Rd_entry_d b d Z ∧ Smdl_d I c C V ∧ Smdl_d I d D W ∧
      Smap_d I ω c d C D j ∧
      (∀ B E, Rd_entry_d B E j ↔ M.mem B C ∧ M.mem E D ∧ Ep_arrow_d ω κ L X a b B E) ∧
      ∀ B E, Rd_entry_d B E j → Ep_lift_d ω κ L X a b B E

structure Ep_system_d (I : kpair_convention_l.Interpretation M) (ω κ L X R F J O Z A p T S : M.Domain) : Prop
    extends Ep_graph_d I ω κ L X R F J O Z A p T S where
  diagram : Di_system_d J O A p T S
  representatives : ∀ u v a b B C, KPair_d M u a B → KPair_d M v b C → Rd_entry_d u v T →
    Ep_lift_d ω κ L X a b B C

variable {I : kpair_convention_l.Interpretation M} {ω κ L X R F J O Z A p T S : M.Domain}

theorem Eg_graph_d.at_l (h : Eg_graph_d ω κ L X J O Z A p T S)
    {u a B} (hu : M.mem u A) (hc : KPair_d M u a B) : Ep_at_d Z a B := by
  obtain ⟨b, C, hc', hb⟩ := (h.nodes u).mp hu
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hc hc'
  exact hb

theorem Eg_graph_d.label_l (h : Eg_graph_d ω κ L X J O Z A p T S)
    {u a} (hua : Rd_entry_d u a p) : ∃ B, KPair_d M u a B ∧ Ep_at_d Z a B := by
  obtain ⟨b, B, hu, hat⟩ := (h.nodes u).mp (h.projection.bound_l hua).1
  have hub := (h.index u b B hu).mpr (h.projection.bound_l hua).1
  have e := h.projection.2.2 u (h.projection.bound_l hua).1 b (h.projection.bound_l hub).2
    a (h.projection.bound_l hua).2 hub hua
  exact ⟨B, e ▸ hu, e ▸ hat⟩

theorem Eg_graph_d.arrow_l (h : Eg_graph_d ω κ L X J O Z A p T S)
    {u v a b B C} (hu : KPair_d M u a B) (hv : KPair_d M v b C) :
    Rd_entry_d u v T ↔ M.mem u A ∧ M.mem v A ∧ Ep_arrow_d ω κ L X a b B C := by
  refine (h.arrows u v).trans ⟨?_, fun ⟨huA, hvA, hab⟩ => ⟨huA, hvA, a, b, B, C, hu, hv, hab⟩⟩
  rintro ⟨huA, hvA, a', b', B', C', hu', hv', hab⟩
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu'
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
  exact ⟨huA, hvA, hab⟩

theorem Eg_graph_d.relation_l (h : Eg_graph_d ω κ L X J O Z A p T S)
    {u v a B C} (hu : KPair_d M u a B) (hv : KPair_d M v a C) :
    Rd_entry_d u v S ↔ M.mem u A ∧ M.mem v A ∧ Ep_rel_d Z a B C := by
  refine (h.relations u v).trans ⟨?_, fun ⟨huA, hvA, hab⟩ => ⟨huA, hvA, a, B, C, hu, hv, hab⟩⟩
  rintro ⟨huA, hvA, a', B', C', hu', hv', hab⟩
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu'
  obtain ⟨_, rfl⟩ := kpair_injective_l M hv hv'
  exact ⟨huA, hvA, hab⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部有限支撑分量及映射的集合装配

类都是源函数集合的子集，因此整个带标号并有统一的幂集界。源模型图、标签图、
过渡图与分量关系一次实际生成，索引包含全部内部有限单射支撑。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem eg_graphs_l (hZF : M.Models ZF) {ω κ L X J O Z Q : M.Domain}
    (ho : Di_order_d J O)
    (os : ∀ a b, Rd_entry_d a b O ↔ M.mem a J ∧ M.mem b J ∧ ∃ q, Ei_map_d ω L a b q)
    (hj : ∀ a, M.mem a J ↔ Ei_d ω L a) (hz : Fn0_d J Q Z) :
    ∃ A p T S, Eg_graph_d ω κ L X J O Z A p T S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q₁, h₁⟩ := KP.exists_union (ZF.modelsKP hZF) Q
  obtain ⟨Q₂, h₂⟩ := KP.exists_union (ZF.modelsKP hZF) Q₁
  obtain ⟨P, hP⟩ := KP.exists_union (ZF.modelsKP hZF) Q₂
  have bound a B (hat : Ep_at_d Z a B) : M.mem a J ∧ M.mem B P := by
    obtain ⟨c, C, S, hac, ⟨s, t, hs, _, pair⟩, hB⟩ := hat
    have hCQ := (h₂ C).mpr ⟨s, (h₁ s).mpr ⟨c, (hz.bound_l hac).2, (pair s).mpr (Or.inl rfl)⟩, (hs C).mpr rfl⟩
    exact ⟨(hz.bound_l hac).1, (hP B).mpr ⟨C, hCQ, hB⟩⟩
  obtain ⟨W, hW⟩ := ZF.exists_cartesianProduct hZF I J P
  let φ : UnarySchema 1 := { body := .existsE (.existsE (.conj (kpair_m (.bound 2) (.bound 1) .newest)
    (ep_at_m (.bound 3) (.bound 1) .newest))) }
  obtain ⟨A, ha⟩ := ZF.separation_exists_d hZF φ ⟨fun _ => Z, fun _ => Z⟩ W
  have node u : M.mem u A ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z a B := by
    have sat : φ.denote ⟨fun _ => Z, fun _ => Z⟩ u ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z a B := by
      simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        kpair_sat_l M hZF.1, ep_at_sat_l hZF.1]; rfl
    refine (ha u).trans ((and_congr_right fun _ => sat).trans ⟨And.right, fun ⟨a, B, hu, hat⟩ => ?_⟩)
    exact ⟨(hW u).mpr ⟨a, (bound a B hat).1, B, (bound a B hat).2, hu⟩, a, B, hu, hat⟩
  let ψ : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) (.bound 1) .newest) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => Z⟩
  have sat u a : ψ.denote ρ u a ↔ ∃ B, KPair_d M u a B := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  obtain ⟨p, hp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ ρ (source := A) (target := J)
    (fun u hu => by
      obtain ⟨a, B, hu, _⟩ := (node u).mp hu
      exact ⟨a, (sat u a).mpr ⟨B, hu⟩⟩)
    (fun u _ a b ha hb => by
      obtain ⟨B, hu⟩ := (sat u a).mp ha
      obtain ⟨C, hv⟩ := (sat u b).mp hb
      exact (kpair_injective_l M hu hv).1)
    (fun u a hu hat => by
      obtain ⟨b, B, hb, hatB⟩ := (node u).mp hu
      obtain ⟨C, hc⟩ := (sat u a).mp hat
      exact (kpair_injective_l M hb hc).1 ▸ (bound b B hatB).1)
  have index u a B (hu : KPair_d M u a B) : Rd_entry_d u a p ↔ M.mem u A :=
    ⟨hp.input_mem_of_pairMember, fun huA => (ps u a).mpr ⟨huA, (sat u a).mpr ⟨B, hu⟩⟩⟩
  let η := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push κ).push L).push X
  let transition : BinarySchema 4 := { body := .existsE (.existsE (.existsE (.existsE (.conj
    (kpair_m (.bound 5) (.bound 3) (.bound 1)) (.conj (kpair_m (.bound 4) (.bound 2) .newest)
      (ep_arrow_m (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 3) (.bound 2) (.bound 1) .newest)))))) }
  obtain ⟨T, _, ts⟩ := ZF.exists_setRelationOn_of_denote hZF I transition η A
  have arrows u v : Rd_entry_d u v T ↔ M.mem u A ∧ M.mem v A ∧
      ∃ a b B C, KPair_d M u a B ∧ KPair_d M v b C ∧ Ep_arrow_d ω κ L X a b B C := by
    simpa only [transition, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, ep_arrow_sat_l hZF.1] using! ts u v
  let relation : BinarySchema 1 := { body := .existsE (.existsE (.existsE (.conj
    (kpair_m (.bound 4) (.bound 2) (.bound 1)) (.conj (kpair_m (.bound 3) (.bound 2) .newest)
      (ep_rel_m (.bound 5) (.bound 2) (.bound 1) .newest))))) }
  obtain ⟨S, _, ss⟩ := ZF.exists_setRelationOn_of_denote hZF I relation ⟨fun _ => Z, fun _ => Z⟩ A
  have relations u v : Rd_entry_d u v S ↔ M.mem u A ∧ M.mem v A ∧
      ∃ a B C, KPair_d M u a B ∧ KPair_d M v a C ∧ Ep_rel_d Z a B C := by
    simpa only [relation, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, ep_rel_sat_l hZF.1] using! ss u v
  exact ⟨A, p, T, S, ho, os, fn0_of_function_l (ZF.modelsKP hZF) hp, hj, ⟨Q, hz⟩, node, index, arrows, relations⟩

/-- 传递源直接调用与原关系源共用的图装配。 -/
theorem ep_graphs_l (hZF : M.Models ZF) {ω κ K L X R F : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    : ∃ J O Z A p T S,
      Ep_graph_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S := by
  obtain ⟨J, O, hj, ho, os⟩ := ei_order_l hZF h.omega
  obtain ⟨Z, Q, hz, models⟩ := ep_components_l hZF h hF (fun a ha => ((hj a).mp ha).elim fun n hn => ⟨n, hn.1, hn.2.1⟩) R
  obtain ⟨A, p, T, S, graph⟩ := eg_graphs_l hZF (κ := κ) (X := X) ho os hj hz
  exact ⟨J, O, Z, A, p, T, S, graph, models⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑测度族的完整定向系统

对已经统一生成的真实图逐项核验函子律。所有过渡图同时作用于同一批规范
源分量；证明保留模型内部任意有限长度及全部坐标排列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Eg_graph_d.system_l (hZF : M.Models ZF) {ω κ L X J O Z A p T S : M.Domain}
    (hω : M.IsOmega ω) (h : Eg_graph_d ω κ L X J O Z A p T S)
    (reps : ∀ a B, Ep_at_d Z a B → ∃ n, M.mem n ω ∧ Fn0_d n L a ∧
      (∃ f, M.mem f B) ∧ ∀ f, M.mem f B → Ep_fun_d κ X n f)
    (transition : Eg_transition_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X O Z) :
    Di_system_d J O A p T S ∧ ∀ u v a b B C,
      KPair_d M u a B → KPair_d M v b C → Rd_entry_d u v T → Ep_lift_d ω κ L X a b B C := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hz⟩ := h.codes
  have label u a (hua : Rd_entry_d u a p) : ∃ B, KPair_d M u a B ∧ Ep_at_d Z a B := by
    obtain ⟨b, B, hu, hat⟩ := (h.nodes u).mp (h.projection.bound_l hua).1
    have hub := (h.index u b B hu).mpr (h.projection.bound_l hua).1
    have e := (fn0_function_l (ZF.modelsKP hZF) h.projection).1.2 u b a hub hua
    exact ⟨B, e ▸ hu, e ▸ hat⟩
  have node a B (hat : Ep_at_d Z a B) : ∃ u, M.mem u A ∧ KPair_d M u a B ∧ Rd_entry_d u a p := by
    obtain ⟨u, hu⟩ := I.total a B
    have huA := (h.nodes u).mpr ⟨a, B, hu, hat⟩
    exact ⟨u, huA, hu, (h.index u a B hu).mpr huA⟩
  have bounds u v (huv : Rd_entry_d u v T) : M.mem u A ∧ M.mem v A :=
    ⟨((h.arrows u v).mp huv).1, ((h.arrows u v).mp huv).2.1⟩
  have forward u v a b (hua : Rd_entry_d u a p) (hvb : Rd_entry_d v b p) (huv : Rd_entry_d u v T) : Rd_entry_d a b O := by
    obtain ⟨B, hu, _⟩ := label u a hua
    obtain ⟨C, hv, _⟩ := label v b hvb
    obtain ⟨m, n, q, _, _, hm, hn, hq, hb, hqa, _⟩ := ((h.arrow_l hu hv).mp huv).2.2
    exact (h.order_spec a b).mpr ⟨(h.projection.bound_l hua).2, (h.projection.bound_l hvb).2,
      q, m, n, hm, hn, hq, hb, hqa⟩
  have maps a b (hab : Rd_entry_d a b O) : ∃ j c C V d D W,
      Rd_entry_d a c Z ∧ Rd_entry_d b d Z ∧ Smdl_d I c C V ∧ Smdl_d I d D W ∧
      M.IsSetInjectionFromTo I j C D ∧
      (∀ B E B' E', Rd_entry_d B B' j → Rd_entry_d E E' j → (Rd_entry_d B E V ↔ Rd_entry_d B' E' W)) ∧
      (∀ B E, Rd_entry_d B E j ↔ M.mem B C ∧ M.mem E D ∧ Ep_arrow_d ω κ L X a b B E) ∧
      ∀ B E, Rd_entry_d B E j → Ep_lift_d ω κ L X a b B E := by
    obtain ⟨j, c, C, V, d, D, W, hac, hbd, hc, hd, elem, spec, lift⟩ := transition a b hab
    exact ⟨j, c, C, V, d, D, W, hac, hbd, hc, hd, elem.1,
      fun B E B' E' hb he => elem.relation_l I hZF hω hc hd hb he, spec, lift⟩
  refine ⟨⟨h.order, h.projection, bounds, forward, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu
    obtain ⟨a, B, huB, hat⟩ := (h.nodes u).mp hu
    obtain ⟨n, hn, hna, ⟨f, hf⟩, fs⟩ := reps a B hat
    obtain ⟨_, _, _, ha⟩ := (h.indices a).mp (h.projection.bound_l ((h.index u a B huB).mpr hu)).2
    obtain ⟨r, hr, hra⟩ := ec_factor_l hZF hna ⟨fn0_function_l (ZF.modelsKP hZF) hna, ha⟩ (fun i _ hi => ⟨i, hi⟩)
    have fixed i j (hij : Rd_entry_d i j r) : i = j := by
      obtain ⟨x, _, hix⟩ := hna.2.1 i (hr.bound_l hij).1
      exact ha i j x hix ((hra.value_l hr hna hij).mp hix)
    exact (h.arrow_l huB huB).mpr ⟨hu, hu, n, n, r, f, f, hn, hn, hr, hna, hra,
      hf, hf, ep_pull_id_l hZF.1 (fs f hf) fixed⟩
  · intro u v w huv hvw
    obtain ⟨a, B, hu, _⟩ := (h.nodes u).mp (bounds u v huv).1
    obtain ⟨b, C, hv, hvC⟩ := (h.nodes v).mp (bounds u v huv).2
    obtain ⟨c, D, hw, hwD⟩ := (h.nodes w).mp (bounds v w hvw).2
    have hvb := (h.index v b C hv).mpr (bounds u v huv).2
    have hwc := (h.index w c D hw).mpr (bounds v w hvw).2
    obtain ⟨j, c₀, C₀, V, c₁, C₁, W, hbc, hcc, mc₀, mc₁, _, _, spec, lift⟩ :=
      maps b c (forward v w b c hvb hwc hvw)
    have hCD := (spec C D).mpr ⟨(ep_at_read_l hz hbc mc₀.1).mp hvC,
      (ep_at_read_l hz hcc mc₁.1).mp hwD, ((h.arrow_l hv hw).mp hvw).2.2⟩
    obtain ⟨m, n, r, f, g, hm, hn, hr, hnb, hra, hf, hg, pull⟩ := ((h.arrow_l hu hv).mp huv).2.2
    obtain ⟨n', l, t, g', _, hl, ht, hlc, htb, hg', pull'⟩ := lift C D hCD g hg
    have eq := htb.1.domain_eq_l hZF.1 hnb
    subst n'
    obtain ⟨s, hs⟩ := cp0_exists_l (ZF.modelsKP hZF) hr ht
    exact (h.arrow_l hu hw).mpr ⟨(bounds u v huv).1, (bounds v w hvw).2, m, l, s, f, g',
      hm, hl, hs.1, hlc, Cp0_d.assoc_l ht hr hs hlc htb hra, hf, hg',
      ep_pull_comp_l (ZF.modelsKP hZF) hr ht hs pull pull'⟩
  · intro u a b hua hab
    obtain ⟨B, hu, hat⟩ := label u a hua
    obtain ⟨j, c, C, V, d, D, W, hac, hbd, hc, hd, hj, _, spec, _⟩ := maps a b hab
    have hBC := (ep_at_read_l hz hac hc.1).mp hat
    obtain ⟨E, hED, hBE⟩ := hj.1.2.2 B hBC
    obtain ⟨v, hvA, hv, hvb⟩ := node b E ⟨d, D, W, hbd, hd.1, hED⟩
    exact ⟨v, hvb, (h.arrow_l hu hv).mpr ⟨(h.projection.bound_l hua).1, hvA, ((spec B E).mp hBE).2.2⟩⟩
  · intro u v w b hvb hwb huv huw
    obtain ⟨a, _, hua⟩ := h.projection.2.1 u (bounds u v huv).1
    obtain ⟨B, hu, huB⟩ := label u a hua
    obtain ⟨C, hv, hvC⟩ := label v b hvb
    obtain ⟨D, hw, hwD⟩ := label w b hwb
    obtain ⟨j, c, E, V, d, G, W, hac, hbd, hc, hd, hj, _, spec, _⟩ := maps a b (forward u v a b hua hvb huv)
    have hBE := (ep_at_read_l hz hac hc.1).mp huB
    have hCG := (ep_at_read_l hz hbd hd.1).mp hvC
    have hDG := (ep_at_read_l hz hbd hd.1).mp hwD
    have e := hj.1.1.2 B C D ((spec B C).mpr ⟨hBE, hCG, ((h.arrow_l hu hv).mp huv).2.2⟩)
      ((spec B D).mpr ⟨hBE, hDG, ((h.arrow_l hu hw).mp huw).2.2⟩)
    exact kpair_unique_l M hZF.1 (e ▸ hv) hw
  · intro u v w a hua hva huw hvw
    obtain ⟨b, _, hwb⟩ := h.projection.2.1 w (bounds u w huw).2
    obtain ⟨B, hu, huB⟩ := label u a hua
    obtain ⟨C, hv, hvC⟩ := label v a hva
    obtain ⟨D, hw, hwD⟩ := label w b hwb
    obtain ⟨j, c, E, V, d, G, W, hac, hbd, hc, hd, hj, _, spec, _⟩ := maps a b (forward u w a b hua hwb huw)
    have hBE := (ep_at_read_l hz hac hc.1).mp huB
    have hCE := (ep_at_read_l hz hac hc.1).mp hvC
    have hDG := (ep_at_read_l hz hbd hd.1).mp hwD
    have e := hj.2 B C D ((spec B D).mpr ⟨hBE, hDG, ((h.arrow_l hu hw).mp huw).2.2⟩)
      ((spec C D).mpr ⟨hCE, hDG, ((h.arrow_l hv hw).mp hvw).2.2⟩)
    exact kpair_unique_l M hZF.1 (e ▸ hu) hv
  · intro u v huv
    obtain ⟨huA, hvA, a, B, C, hu, hv, _⟩ := (h.relations u v).mp huv
    exact ⟨a, (h.index u a B hu).mpr huA, (h.index v a C hv).mpr hvA⟩
  · intro u v a w z b hua hva hwb hzb huw hvz
    obtain ⟨B, hu, huB⟩ := label u a hua
    obtain ⟨C, hv, hvC⟩ := label v a hva
    obtain ⟨D, hw, hwD⟩ := label w b hwb
    obtain ⟨E, he, hzE⟩ := label z b hzb
    obtain ⟨j, c, G, V, d, H, W, hac, hbd, hc, hd, hj, rel, spec, _⟩ := maps a b (forward u w a b hua hwb huw)
    have hBG := (ep_at_read_l hz hac hc.1).mp huB
    have hCG := (ep_at_read_l hz hac hc.1).mp hvC
    have hDH := (ep_at_read_l hz hbd hd.1).mp hwD
    have hEH := (ep_at_read_l hz hbd hd.1).mp hzE
    have old : Rd_entry_d u v S ↔ Rd_entry_d B C V := (h.relation_l hu hv).trans
      ⟨fun hh => (ep_rel_read_l hz hac hc.1).mp hh.2.2, fun hh =>
        ⟨(h.projection.bound_l hua).1, (h.projection.bound_l hva).1, (ep_rel_read_l hz hac hc.1).mpr hh⟩⟩
    have new : Rd_entry_d w z S ↔ Rd_entry_d D E W := (h.relation_l hw he).trans
      ⟨fun hh => (ep_rel_read_l hz hbd hd.1).mp hh.2.2, fun hh =>
        ⟨(h.projection.bound_l hwb).1, (h.projection.bound_l hzb).1, (ep_rel_read_l hz hbd hd.1).mpr hh⟩⟩
    exact old.trans ((rel B C D E ((spec B D).mpr ⟨hBG, hDH, ((h.arrow_l hu hw).mp huw).2.2⟩)
      ((spec C E).mpr ⟨hCG, hEH, ((h.arrow_l hv he).mp hvz).2.2⟩)).trans new.symm)
  · intro u v a b B C hu hv huv
    have huA := (bounds u v huv).1
    have hvA := (bounds u v huv).2
    obtain ⟨j, c, E, V, d, G, W, hac, hbd, hc, hd, _, _, spec, lifts⟩ := maps a b
      (forward u v a b ((h.index u a B hu).mpr huA) ((h.index v b C hv).mpr hvA) huv)
    exact lifts B C ((spec B C).mpr ⟨(ep_at_read_l hz hac hc.1).mp (h.at_l huA hu),
      (ep_at_read_l hz hbd hd.1).mp (h.at_l hvA hv), ((h.arrow_l hu hv).mp huv).2.2⟩)

theorem Ep_graph_d.transition_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S : M.Domain}
    (h : Ep_graph_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F) :
    Eg_transition_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X O Z := by
  obtain ⟨_, hz⟩ := h.codes
  intro a b hab
  obtain ⟨ha, hb, q, m, n, hm, hn, hq, hnb, hqa⟩ := (h.order_spec a b).mp hab
  obtain ⟨c, _, hac⟩ := hz.2.1 a ha
  obtain ⟨d, _, hbd⟩ := hz.2.1 b hb
  obtain ⟨_, _, _, inj⟩ := (h.indices b).mp hb
  obtain ⟨j, C, V, D, W, hc, hd, _, elem, _, spec, any⟩ := ep_map_l hZF source hF coherent hm hn hq hnb inj hqa
    (h.components a c hac) (h.components b d hbd)
  exact ⟨j, c, C, V, d, D, W, hac, hbd, hc, hd, elem, spec, fun B E hBE f hf =>
    (any B E hBE f hf).elim fun g hg => ⟨m, n, q, g, hm, hn, hq, hnb, hqa, hg⟩⟩

theorem Ep_graph_d.system_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F)
    (h : Ep_graph_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S) :
    Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S := by
  obtain ⟨diagram, lifts⟩ := h.toEg_graph_d.system_l hZF source.omega (fun a B hat => by
    obtain ⟨c, C, V, _, component, model, hB⟩ := ep_at_model_l hZF h.components hat
    obtain ⟨n, hn, ha, point, functions⟩ := ep_representatives_l _ hZF.1 hF component model hB
    exact ⟨n, hn, ha, point, fun f hf => (functions f hf).2⟩) (h.transition_l hZF source hF coherent)
  exact ⟨h, diagram, lifts⟩

theorem ep_system_exists_l (hZF : M.Models ZF) {ω κ K L X R F : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (hc : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F)
    : ∃ J O Z A p T S,
      Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S := by
  obtain ⟨J, O, Z, A, p, T, S, hg⟩ := ep_graphs_l hZF h hF
  exact ⟨J, O, Z, A, p, T, S, hg.system_l hZF h hF hc⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一有限支撑超幂中的代表元计算

直接以商投影读取 [a,f]，给出实际代表的存在、同分量原子方程及坐标
拉回不变性。这些计算不预设原派生嵌入或超幂良基性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_repr_d (q a f E : M.Domain) : Prop :=
  ∃ u B, KPair_d M u a B ∧ M.mem f B ∧ Rd_entry_d u E q

def ep_repr_m {d} (q a f E : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (kpair_m (.bound 1) a.weaken.weaken .newest)
    (.conj (.mem f.weaken.weaken .newest) (rd_entry_m (.bound 1) E.weaken.weaken q.weaken.weaken))))
derive_free_closed ep_repr_m

theorem ep_repr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (q a f E : Term d) :
    Formula.satisfies ρ (ep_repr_m q a f E) ↔ Ep_repr_d (q.eval ρ) (a.eval ρ) (f.eval ρ) (E.eval ρ) := by
  simp only [ep_repr_m, Ep_repr_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, Formula.satisfies_mem_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

variable (hZF : M.Models ZF) {ω κ L X R F J O Z A p T S q C W : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_repr_d.index_l (h : Ep_system_d I ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C W) {a f E} (he : Ep_repr_d q a f E) : M.mem a J := by
  obtain ⟨u, B, hu, _, huE⟩ := he
  exact (h.projection.bound_l ((h.index u a B hu).mpr (limit.projection.bound_l huE).1)).2

theorem ep_repr_exists_l (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {n D a f : M.Domain} (haJ : M.mem a J) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D)
    (hfX : M.mem f X) (hf : Fn0_d D X f) : ∃ E, M.mem E C ∧ Ep_repr_d q a f E := by
  obtain ⟨_, hz⟩ := h.codes
  have models := h.components
  obtain ⟨b, _, hab⟩ := hz.2.1 a haJ
  obtain ⟨m, D', U, G, r, H, V, _, ha', hD', haU, hG, model⟩ := models a b hab
  have en := ha'.domain_eq_l hZF.1 ha
  subst m
  have eD := hZF.1.eq_of_same_members D' D (fun s => (hD' s).trans (hD s).symm)
  subst D'
  obtain ⟨B, hBH, hfB⟩ := model.map.projection.2.2 f ((hG f).mpr ⟨hfX, hf⟩)
  obtain ⟨u, hu⟩ := (I).total a B
  have huA := (h.nodes u).mpr ⟨a, B, hu, b, H, V, hab, model.code.1, hBH⟩
  obtain ⟨E, hEC, huE⟩ := limit.projection.2.1 u huA
  exact ⟨E, hEC, u, B, hu, model.map.representative_l I (family.at_l hZF.1 haU ha hD).base hfB, huE⟩

/-- 极限的每个元素都有实际源内代表。 -/
theorem ep_repr_surjective_l (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {E : M.Domain} (hEC : M.mem E C) : ∃ n a D f, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧
      Ep_space_d κ n D ∧ M.mem f X ∧ Fn0_d D X f ∧ Ep_repr_d q a f E := by
  obtain ⟨u, huE⟩ := (limit.range E).mp hEC
  have huA := (limit.projection.bound_l huE).1
  obtain ⟨a, B, hu, _, _, _, _, _, _⟩ := (h.nodes u).mp huA
  have models := h.components
  obtain ⟨_, _, _, _, component, model, hB⟩ := ep_at_model_l hZF models (h.toEp_graph_d.at_l huA hu)
  obtain ⟨n, hn, ha, ⟨f, hfB⟩, reps⟩ := ep_representatives_l I hZF.1 family component model hB
  obtain ⟨hfX, D, hD, hf⟩ := reps f hfB
  exact ⟨n, a, D, f, hn, (h.projection.bound_l ((h.index u a B hu).mpr huA)).2,
    ha, hD, hfX, hf, u, B, hu, hfB, huE⟩

/-- 代表所属的实际源和内部有限定义域，可由商证书直接读回。 -/
theorem Ep_repr_d.source_l (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {a f E : M.Domain} (he : Ep_repr_d q a f E) : M.mem f X ∧ ∃ n, M.mem n ω ∧ Fn0_d n L a ∧ Ep_fun_d κ X n f := by
  obtain ⟨u, B, hu, hf, huE⟩ := he
  have models := h.components
  obtain ⟨_, _, _, _, component, model, hB⟩ := ep_at_model_l hZF models
    (h.toEp_graph_d.at_l (limit.projection.bound_l huE).1 hu)
  obtain ⟨n, hn, ha, _, reps⟩ := ep_representatives_l I hZF.1 family component model hB
  exact ⟨(reps f hf).1, n, hn, ha, (reps f hf).2⟩

/-- 固定分量中，极限上的等号和隶属恰好由原代表的测度一关系判定。 -/
theorem ep_repr_atoms_l (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {a f g E H U : M.Domain} (haU : Rd_entry_d a U F) (he : Ep_repr_d q a f E) (hh : Ep_repr_d q a g H) :
    (E = H ↔ Rp_eq_d X U f g) ∧ (Rd_entry_d E H W ↔ Rp_rel_d I X U R f g) := by
  obtain ⟨u, B, hu, hf, huE⟩ := he
  obtain ⟨v, D, hv, hg, hvH⟩ := hh
  have huA := (limit.projection.bound_l huE).1
  have hvA := (limit.projection.bound_l hvH).1
  have hua := (h.index u a B hu).mpr huA
  have hva := (h.index v a D hv).mpr hvA
  obtain ⟨_, hz⟩ := h.codes
  have models := h.components
  obtain ⟨b, Q, V, hab, component, model, hBQ⟩ := ep_at_model_l hZF models (h.toEp_graph_d.at_l huA hu)
  have hDQ := (ep_at_read_l hz hab model.1).mp (h.toEp_graph_d.at_l hvA hv)
  have relation := ep_relation_l I hZF.1 family component model hBQ hDQ hf hg haU
  have rel := (limit.relation u v E H huE hvH).trans
    (h.diagram.rel_at_l hua hva (h.diagram.identity u huA) (h.diagram.identity v hvA))
  have same : u = v ↔ B = D := ⟨fun e => ((kpair_injective_l M (e ▸ hu) hv).2),
    fun e => kpair_unique_l M hZF.1 (e ▸ hu) hv⟩
  obtain ⟨n, Q₀, V₀, G, r, Q', S', _, ha, hQ₀, haV, _, md⟩ := component
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I md.code model
  have ev := family.function a V₀ U haV haU
  subst V₀
  have ultra := (family.at_l hZF.1 haU ha hQ₀).base
  refine ⟨(limit.kernel u v E H huE hvH).trans ((h.diagram.eq_at_l hua hva).trans
    (same.trans (rp_kernel_l I hZF.1 ultra md.map (md.map.member_l I hZF.1 ultra hBQ hf)
      (md.map.member_l I hZF.1 ultra hDQ hg)))), rel.trans ?_⟩
  exact (h.toEp_graph_d.relation_l hu hv).trans
    ((and_congr_right fun _ => and_congr_right fun _ => ep_rel_read_l hz hab model.1).trans
      (Iff.trans ⟨And.right ∘ And.right, fun hr => ⟨huA, hvA, hr⟩⟩ relation))

theorem ep_repr_pull_l
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {m n a b r f g E H : M.Domain} (hm : M.mem m ω) (hn : M.mem n ω)
    (hr : Fn0_d m n r) (hb : Fn0_d n L b) (hra : Cp0_d m n L r b a)
    (pull : Ep_pull_d κ X m n r f g) (he : Ep_repr_d q a f E) (hh : Ep_repr_d q b g H) : E = H := by
  obtain ⟨u, B, hu, hf, huE⟩ := he
  obtain ⟨v, D, hv, hg, hvH⟩ := hh
  exact limit.commute_l h.diagram ((h.toEp_graph_d.arrow_l hu hv).mpr
    ⟨(limit.projection.bound_l huE).1, (limit.projection.bound_l hvH).1,
      m, n, r, f, g, hm, hn, hr, hb, hra, hf, hg, pull⟩) huE hvH

/-- 实际构造拉回代表，并保留它在同一极限中的值。 -/
theorem ep_repr_reindex_l {R₀ : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R₀) (family : Em_source_d ω κ L X F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {n m a b D E r f B : M.Domain} (hn : M.mem n ω) (hm : M.mem m ω)
    (hr : Fn0_d n m r) (hbJ : M.mem b J) (hb : Fn0_d m L b) (hra : Cp0_d n m L r b a)
    (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E) (hfX : M.mem f X) (hf : Fn0_d D X f)
    (value : Ep_repr_d q a f B) : ∃ g, M.mem g X ∧ Fn0_d E X g ∧
      Ep_pull_d κ X n m r f g ∧ Ep_repr_d q b g B := by
  obtain ⟨t, htX, ht, ts⟩ := source.projection_l hZF hn hm hr hD hE
  obtain ⟨c, code⟩ := source.code
  obtain ⟨g, hg, comp⟩ := sc_compose_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hm hE) (source.space_mem_l hZF hn hD) htX hfX ht hf
  have pull := ep_pull_of_comp_l hD hE ht hf ts comp
  obtain ⟨H, _, hh⟩ := ep_repr_exists_l hZF family h limit hbJ hb hE hg.1 comp.1
  exact ⟨g, hg.1, comp.1, pull, (ep_repr_pull_l hZF h limit hn hm hr hb hra pull value hh).symm ▸ hh⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 源包含诱导实际超幂的关系嵌入

同一支撑、同一代表在两个商中读取；函数值域的包含保持等价核及隶属关系。
不要求小源初等包含于大源。该构造用于辨认严格秩段超幂的实际像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_inclusion_l {ω κ L X R Y S F c d
    J O Z A p T V q C W J' O' Z' A' p' T' V' q' C' W' : M.Domain}
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (inside : M.MemberSubset X Y)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ L Y F)
    (h : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (h' : Ep_system_d I ω κ L Y S F J' O' Z' A' p' T' V') (limit' : Di_limit_d A' p' T' V' q' C' W') :
    ∃ g, M.IsSetInjectionFromTo I g C C' ∧
      (∀ E H E' H', Rd_entry_d E E' g → Rd_entry_d H H' g → (Rd_entry_d E H W ↔ Rd_entry_d E' H' W')) ∧
      ∀ a f E E', Ep_repr_d q a f E → (Rd_entry_d E E' g ↔ Ep_repr_d q' a f E') := by
  have lift u a B f (hu : M.mem u A) (pair : KPair_d M u a B) (hf : M.mem f B) :
      ∃ E, M.mem E C' ∧ Ep_repr_d q' a f E := by
    obtain ⟨H, _, huH⟩ := limit.projection.2.1 u hu
    have old : Ep_repr_d q a f H := ⟨u, B, pair, hf, huH⟩
    obtain ⟨hfX, n, hno, ha, D, hd, fn⟩ := old.source_l hZF family h limit
    exact ep_repr_exists_l hZF family' h' limit' ((h'.indices a).mpr ((h.indices a).mp (old.index_l hZF h limit)))
      ha hd (inside f hfX) (fn.mono_target_l inside)
  have atoms a f g E H E' H' U (haU : Rd_entry_d a U F)
      (fe : Ep_repr_d q a f E) (gh : Ep_repr_d q a g H)
      (fe' : Ep_repr_d q' a f E') (gh' : Ep_repr_d q' a g H') :
      (E = H ↔ E' = H') ∧ (Rd_entry_d E H W ↔ Rd_entry_d E' H' W') := by
    obtain ⟨_, _, _, _, D, _, ff⟩ := fe.source_l hZF family h limit
    obtain ⟨_, _, _, _, D', _, gf⟩ := gh.source_l hZF family h limit
    have eq : Rp_eq_d X U f g ↔ Rp_eq_d Y U f g := by
      constructor <;> rintro ⟨B, hB, eq⟩ <;> refine ⟨B, hB, fun s hs => ?_⟩
      · obtain ⟨x, hx, hf, hg⟩ := eq s hs
        exact ⟨x, inside x hx, hf, hg⟩
      · obtain ⟨x, _, hf, hg⟩ := eq s hs
        exact ⟨x, (ff.bound_l hf).2, hf, hg⟩
    have rel : Rp_rel_d I X U R f g ↔ Rp_rel_d I Y U S f g := by
      constructor <;> rintro ⟨B, hB, rel⟩ <;> refine ⟨B, hB, fun s hs => ?_⟩
      · obtain ⟨x, hx, y, hy, hf, hg, hxy⟩ := rel s hs
        exact ⟨x, inside x hx, y, inside y hy, hf, hg,
          (hn.2 x y).mpr ⟨inside x hx, inside y hy, ((hm.2 x y).mp hxy).2.2⟩⟩
      · obtain ⟨x, _, y, _, hf, hg, hxy⟩ := rel s hs
        exact ⟨x, (ff.bound_l hf).2, y, (gf.bound_l hg).2, hf, hg,
          (hm.2 x y).mpr ⟨(ff.bound_l hf).2, (gf.bound_l hg).2, ((hn.2 x y).mp hxy).2.2⟩⟩
    have left := ep_repr_atoms_l hZF family h limit haU fe gh
    have right := ep_repr_atoms_l hZF family' h' limit' haU fe' gh'
    exact ⟨left.1.trans (eq.trans right.1.symm), left.2.trans (rel.trans right.2.symm)⟩
  let ρ : Env M 1 := ⟨fun _ => q', fun _ => q'⟩
  let φ : BinarySchema 1 := { body := .existsE (.existsE (.existsE
    (.conj (kpair_m (.bound 4) (.bound 2) (.bound 1))
      (.conj (.mem .newest (.bound 1)) (ep_repr_m (.bound 5) (.bound 2) .newest (.bound 3)))))) }
  have sat u E : φ.denote ρ u E ↔ ∃ a B f, KPair_d M u a B ∧ M.mem f B ∧ Ep_repr_d q' a f E := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, Formula.satisfies_mem_iff, ep_repr_sat_l hZF.1]; rfl
  have unique u (hu : M.mem u A) E H (he : φ.denote ρ u E) (hh : φ.denote ρ u H) : E = H := by
    obtain ⟨a, B, f, pair, hf, fe⟩ := (sat u E).mp he
    obtain ⟨a', B', g, pair', hg, gh⟩ := (sat u H).mp hh
    obtain ⟨ea, eb⟩ := kpair_injective_l M pair' pair
    subst a' B'
    obtain ⟨E₀, _, huE⟩ := limit.projection.2.1 u hu
    have fv : Ep_repr_d q a f E₀ := ⟨u, B, pair, hf, huE⟩
    obtain ⟨_, n, hno, ha, _⟩ := fv.source_l hZF family h limit
    obtain ⟨U, haU⟩ := family.total n a hno ha
    exact (atoms a f g E₀ E₀ E H U haU fv ⟨u, B, pair, hg, huE⟩ fe gh).1.mp rfl
  obtain ⟨t, ht, ts⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := A) (target := C')
    (fun u hu => by
      obtain ⟨a, B, pair, hat⟩ := (h.nodes u).mp hu
      have models := h.components
      obtain ⟨_, _, _, _, comp, model, hb⟩ := ep_at_model_l hZF models hat
      obtain ⟨_, _, _, ⟨f, hf⟩, _⟩ := ep_representatives_l I hZF.1 family comp model hb
      obtain ⟨E, _, he⟩ := lift u a B f hu pair hf
      exact ⟨E, (sat u E).mpr ⟨a, B, f, pair, hf, he⟩⟩)
    unique (fun u E _ he => by
      obtain ⟨_, _, _, _, _, v, _, _, _, hv⟩ := (sat u E).mp he
      exact (limit'.projection.bound_l hv).2)
  have spec u E := (ts u E).trans (and_congr_right fun _ => sat u E)
  have any u a B f E (pair : KPair_d M u a B) (hf : M.mem f B) (huE : Rd_entry_d u E t) : Ep_repr_d q' a f E := by
    obtain ⟨H, _, fh⟩ := lift u a B f (ht.input_mem_of_pairMember huE) pair hf
    have hH := (ts u H).mpr ⟨ht.input_mem_of_pairMember huE, (sat u H).mpr ⟨a, B, f, pair, hf, fh⟩⟩
    exact ht.1.2 u H E hH huE ▸ fh
  have comm u v E H (edge : Rd_entry_d u v T) (huE : Rd_entry_d u E t) (hvH : Rd_entry_d v H t) : E = H := by
    obtain ⟨_, a, B, f, pair, hf, fe⟩ := (spec u E).mp huE
    obtain ⟨b, D, pair', _⟩ := (h.nodes v).mp (ht.input_mem_of_pairMember hvH)
    obtain ⟨m, n, r, g, hm, hn, hr, hb, hra, hg, pull⟩ := h.representatives u v a b B D pair pair' edge f hf
    exact ep_repr_pull_l hZF h' limit' hm hn hr hb hra (pull.mono_l inside) fe (any v b D g H pair' hg hvH)
  have fiber u v a E H (hua : Rd_entry_d u a p) (hva : Rd_entry_d v a p)
      (huE : Rd_entry_d u E t) (hvH : Rd_entry_d v H t) :
      (u = v ↔ E = H) ∧ (Rd_entry_d u v V ↔ Rd_entry_d E H W') := by
    obtain ⟨B, pair, _⟩ := h.toEp_graph_d.label_l hua
    obtain ⟨D, pair', _⟩ := h.toEp_graph_d.label_l hva
    obtain ⟨_, a₀, B₀, f, pair₀, hf, fe⟩ := (spec u E).mp huE
    obtain ⟨ea, eb⟩ := kpair_injective_l M pair₀ pair
    subst a₀ B₀
    obtain ⟨_, a₁, D₀, g, pair₁, hg, gh⟩ := (spec v H).mp hvH
    obtain ⟨ea, ed⟩ := kpair_injective_l M pair₁ pair'
    subst a₁ D₀
    obtain ⟨E₀, _, hu₀⟩ := limit.projection.2.1 u (ht.input_mem_of_pairMember huE)
    obtain ⟨H₀, _, hv₀⟩ := limit.projection.2.1 v (ht.input_mem_of_pairMember hvH)
    have fv : Ep_repr_d q a f E₀ := ⟨u, B, pair, hf, hu₀⟩
    obtain ⟨_, n, hno, ha, _⟩ := fv.source_l hZF family h limit
    obtain ⟨U, haU⟩ := family.total n a hno ha
    have compare := atoms a f g E₀ H₀ E H U haU fv ⟨v, D, pair', hg, hv₀⟩ fe gh
    exact ⟨((limit.kernel u v E₀ H₀ hu₀ hv₀).trans (h.diagram.eq_at_l hua hva)).symm.trans compare.1,
      ((limit.relation u v E₀ H₀ hu₀ hv₀).trans (h.diagram.rel_at_l hua hva
        (h.diagram.identity u (ht.input_mem_of_pairMember huE)) (h.diagram.identity v (ht.input_mem_of_pairMember hvH)))).symm.trans compare.2⟩
  obtain ⟨g, hg, gs, rel, _⟩ := di_factor_embedding_l hZF h.diagram limit
    (fn0_of_function_l (ZF.modelsKP hZF) ht) comm fiber
  refine ⟨g, hg, rel, fun a f E E' old => ?_⟩
  obtain ⟨u, B, pair, hf, huE⟩ := old
  constructor
  · intro hEE
    obtain ⟨H, _, huH⟩ := ht.2.2 u (limit.projection.bound_l huE).1
    exact hg.1.1.2 E H E' (gs u E H huE huH) hEE ▸ any u a B f H pair hf huH
  · intro value
    exact gs u E E' huE ((spec u E').mpr ⟨(limit.projection.bound_l huE).1, a, B, f, pair, hf, value⟩)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 分量类结构与带标签分量的实际同构

去掉支撑标签给出双射，逆图由集合逆关系构造。两个方向均保持全部内部码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_tag_l (hZF : M.Models ZF) {ω J Z A p S a c C V d Y W : M.Domain}
    (hω : M.IsOmega ω) (codes : ∃ Q, Fn0_d J Q Z)
    (nodes : ∀ u, M.mem u A ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z a B)
    (index : ∀ u a B, KPair_d M u a B → (Rd_entry_d u a p ↔ M.mem u A))
    (label : ∀ {u a}, Rd_entry_d u a p → ∃ B, KPair_d M u a B ∧ Ep_at_d Z a B)
    (relation : ∀ {u v a B C}, KPair_d M u a B → KPair_d M v a C →
      (Rd_entry_d u v S ↔ M.mem u A ∧ M.mem v A ∧ Ep_rel_d Z a B C))
    (stage : Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p S a d Y W)
    (hac : Rd_entry_d a c Z) (hm : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V) :
    ∃ e u, Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω d c Y C e ∧
      Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d C Y u ∧
      (∀ x B, Rd_entry_d x B e ↔ M.mem x Y ∧ KPair_d M x a B) ∧
      ∀ B x, Rd_entry_d B x u ↔ M.mem x Y ∧ KPair_d M x a B := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hz⟩ := codes
  let φ : BinarySchema 1 := { body := kpair_m (.bound 1) (.bound 2) .newest }
  let ρ : Env M 1 := ⟨fun _ => a, fun _ => a⟩
  have sat x B : φ.denote ρ x B ↔ KPair_d M x a B := kpair_sat_l M hZF.1 _ _ _ _
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := C)
    (fun x hx => by
      obtain ⟨B, hp, _⟩ := label (((stage.2.1 x).mp hx).2)
      exact ⟨B, (sat x B).mpr hp⟩)
    (fun x _ B D hb hd => (kpair_injective_l M ((sat x B).mp hb) ((sat x D).mp hd)).2)
    (fun x B hx hb => by
      obtain ⟨a', B', pair, hat⟩ := (nodes x).mp (((stage.2.1 x).mp hx).1)
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M ((sat x B).mp hb) pair
      exact (ep_at_read_l hz hac hm.1).mp hat)
  have spec x B : Rd_entry_d x B e ↔ M.mem x Y ∧ KPair_d M x a B :=
    (es x B).trans (and_congr_right fun _ => sat x B)
  have bij : M.IsSetBijectionFromTo I e Y C := by
    refine ⟨⟨he, fun x y B hx hy => I.unique (((spec x B).mp hx).2) (((spec y B).mp hy).2)⟩, fun B hb => ?_⟩
    obtain ⟨x, hp⟩ := I.total a B
    have hxA := (nodes x).mpr ⟨a, B, hp, c, C, V, hac, hm.1, hb⟩
    have hxY := (stage.2.1 x).mpr ⟨hxA, (index x a B hp).mpr hxA⟩
    exact ⟨x, hxY, (spec x B).mpr ⟨hxY, hp⟩⟩
  have rel x y B D (hx : Rd_entry_d x B e) (hy : Rd_entry_d y D e) : Rd_entry_d x y W ↔ Rd_entry_d B D V := by
    obtain ⟨hxY, hpx⟩ := (spec x B).mp hx
    obtain ⟨hyY, hpy⟩ := (spec y D).mp hy
    have hxA := ((stage.2.1 x).mp hxY).1
    have hyA := ((stage.2.1 y).mp hyY).1
    have localW : Rd_entry_d x y W ↔ Rd_entry_d x y S := (stage.2.2 x y).trans
      ⟨And.right ∘ And.right, fun hr => ⟨hxY, hyY, hr⟩⟩
    have localS : Rd_entry_d x y S ↔ Ep_rel_d Z a B D := (relation hpx hpy).trans
      ⟨And.right ∘ And.right, fun hr => ⟨hxA, hyA, hr⟩⟩
    exact localW.trans (localS.trans (ep_rel_read_l hz hac hm.1))
  obtain ⟨u, hu, us⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  exact ⟨e, u, smap_of_iso_l I hZF hω stage.1 hm bij rel,
    smap_of_iso_l I hZF hω hm stage.1 hu (fun B D x y hx hy =>
      (rel x y B D ((us B x).mp hx) ((us D y).mp hy)).symm), spec,
    fun B x => (us B x).trans (spec x B)⟩

section RelationChange
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 更换关系后复用原标签双射，仅需 ZF。 -/
theorem ep_tag_change_l {ω κ L X R F J O Z D p T V V' q C W a b H U e U' d Q S v : M.Domain}
    (hω : M.IsOmega ω) (system : Ep_system_d I ω κ L X R F J O Z D p T V)
    (changed : Di_system_d J O D p T V') (limit : Di_limit_d D p T V' q C W)
    (stage : Di_stage_d I D p V' a d Q S) (hab : Rd_entry_d a b Z)
    (old : Smdl_d I b H U) (new : Smdl_d I e H U')
    (vr : ∀ E H x y, Rd_entry_d E x v → Rd_entry_d H y v → (Rd_entry_d E H U' ↔ Rd_entry_d x y W))
    (vs : ∀ E E', Rd_entry_d E E' v ↔ M.mem E H ∧ ∃ u, KPair_d M u a E ∧ Rd_entry_d u E' q) :
    ∃ t s, Smap_d I ω d e Q H t ∧ Smap_d I ω e d H Q s ∧
      (∀ x E, Rd_entry_d x E t ↔ M.mem x Q ∧ KPair_d M x a E) ∧
      ∀ E x, Rd_entry_d E x s ↔ M.mem x Q ∧ KPair_d M x a E := by
  obtain ⟨x, hx⟩ := stage.1.2.1
  obtain ⟨d₀, Q₀, S₀, st⟩ := di_stage_exists_l hZF system.diagram (((stage.2.1 x).mp hx).2)
  have eq := hZF.1.eq_of_same_members Q₀ Q (fun x => (st.2.1 x).trans (stage.2.1 x).symm)
  subst Q₀
  obtain ⟨t, s, ht, hs, ts, ss⟩ := ep_tag_l hZF hω system.codes system.nodes system.index
    system.toEg_graph_d.label_l system.toEg_graph_d.relation_l st hab old
  have bt : M.IsSetBijectionFromTo I t Q H := ⟨ht.1, fun E hE => by
    obtain ⟨x, hx, hEx⟩ := hs.1.1.2.2 E hE
    exact ⟨x, hx, (ts x E).mpr ((ss E x).mp hEx)⟩⟩
  have bs : M.IsSetBijectionFromTo I s H Q := ⟨hs.1, fun x hx => by
    obtain ⟨E, hE, hxE⟩ := ht.1.1.2.2 x hx
    exact ⟨E, hE, (ss E x).mpr ((ts x E).mp hxE)⟩⟩
  obtain ⟨r, hr, rs, rr⟩ := di_projection_l hZF changed limit stage
  have rel x y E H (hxE : Rd_entry_d x E t) (hyH : Rd_entry_d y H t) : Rd_entry_d x y S ↔ Rd_entry_d E H U' := by
    obtain ⟨u, _, hxu⟩ := hr.1.2.2 x (ht.1.1.input_mem_of_pairMember hxE)
    obtain ⟨w, _, hyw⟩ := hr.1.2.2 y (ht.1.1.input_mem_of_pairMember hyH)
    exact (rr x y u w hxu hyw).trans (vr E H u w
      ((vs E u).mpr ⟨ht.1.1.output_mem_of_pairMember hxE, x, ((ts x E).mp hxE).2, ((rs x u).mp hxu).2⟩)
      ((vs H w).mpr ⟨ht.1.1.output_mem_of_pairMember hyH, y, ((ts y H).mp hyH).2, ((rs y w).mp hyw).2⟩)).symm
  exact ⟨t, s, smap_of_iso_l I hZF hω stage.1 new bt rel,
    smap_of_iso_l I hZF hω new stage.1 bs (fun E H x y hx hy =>
      (rel x y E H ((ts x E).mpr ((ss E x).mp hx)) ((ts y H).mpr ((ss H y).mp hy))).symm), ts, ss⟩

end RelationChange

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑源系统的完整内部初等性

先在既有过渡图上识别源内部初等映射，再用标签同构接入通用定向极限定理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Eg_graph_d.elementary_l (hZF : M.Models ZF) {ω κ L X J O Z A p T S : M.Domain}
    (hω : M.IsOmega ω) (h : Eg_graph_d ω κ L X J O Z A p T S)
    (transition : Eg_transition_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X O Z) :
    Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨_, hz⟩ := h.codes
  intro a b c Y V d W U stage₀ stage₁ hab
  obtain ⟨j, c₀, C₀, S₀, c₁, C₁, S₁, hac, hbd, hc₀, hc₁, elem, spec, _⟩ := transition a b hab
  obtain ⟨e, _, he, _, es, _⟩ := ep_tag_l hZF hω h.codes h.nodes h.index h.label_l h.relation_l stage₀ hac hc₀
  obtain ⟨_, u, _, hu, _, us⟩ := ep_tag_l hZF hω h.codes h.nodes h.index h.label_l h.relation_l stage₁ hbd hc₁
  obtain ⟨v, hv, vs⟩ := smap_comp_l I hZF he elem
  obtain ⟨w, hw, ws⟩ := smap_comp_l I hZF hv hu
  refine ⟨w, hw, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨hxY, D, hxD, hDy⟩ := (ws x y).mp hxy
    obtain ⟨_, B, hxB, hBD⟩ := (vs x D).mp hxD
    obtain ⟨_, hpx⟩ := (es x B).mp hxB
    obtain ⟨hyW, hpy⟩ := (us D y).mp hDy
    exact ⟨hxY, hyW, (h.arrow_l hpx hpy).mpr ⟨((stage₀.2.1 x).mp hxY).1,
      ((stage₁.2.1 y).mp hyW).1, ((spec B D).mp hBD).2.2⟩⟩
  · rintro ⟨hxY, hyW, hxy⟩
    obtain ⟨B, hpx, hat⟩ := h.label_l (((stage₀.2.1 x).mp hxY).2)
    obtain ⟨D, hpy, hbt⟩ := h.label_l (((stage₁.2.1 y).mp hyW).2)
    have hBD := (spec B D).mpr ⟨(ep_at_read_l hz hac hc₀.1).mp hat,
      (ep_at_read_l hz hbd hc₁.1).mp hbt, ((h.arrow_l hpx hpy).mp hxy).2.2⟩
    exact (ws x y).mpr ⟨hxY, D, (vs x D).mpr ⟨hxY, B, (es x B).mpr ⟨hxY, hpx⟩, hBD⟩,
      (us D y).mpr ⟨hyW, hpy⟩⟩

theorem Ep_graph_d.elementary_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S : M.Domain}
    (h : Ep_graph_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F) :
    Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S :=
  h.toEg_graph_d.elementary_l hZF source.omega (h.transition_l hZF source hF coherent)

/-- 原分量类结构到实际极限的完整内部初等嵌入，并保留精确的带标签代表方程。 -/
theorem ep_stage_embedding_l (hZF : M.Models ZF) {ω κ L X J O Z A p T S q c C V a d D W : M.Domain}
    (hω : M.IsOmega ω) (h : Eg_graph_d ω κ L X J O Z A p T S)
    (diagram : Di_system_d J O A p T S)
    (limit : Di_limit_d A p T S q C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V)
    (had : Rd_entry_d a d Z) (stage : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) d D W) :
    ∃ j, Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω d c D C j ∧
      ∀ B E, Rd_entry_d B E j ↔ M.mem B D ∧ ∃ u, KPair_d M u a B ∧ Rd_entry_d u E q := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, hB⟩ := stage.2.1
  obtain ⟨u, hu⟩ := I.total a B
  have huA := (h.nodes u).mpr ⟨a, B, hu, d, D, W, had, stage.1, hB⟩
  obtain ⟨d', D', W', ht⟩ := di_stage_exists_l hZF diagram ((h.index u a B hu).mpr huA)
  obtain ⟨_, e, _, he, _, es⟩ := ep_tag_l hZF hω h.codes h.nodes h.index h.label_l h.relation_l ht had stage
  obtain ⟨k, hk, ks⟩ := di_elementary_limit_l hZF hω diagram limit elementary ht model
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF he hk
  refine ⟨j, hj, fun B E => (js B E).trans (and_congr_right fun hB => ?_)⟩
  apply exists_congr
  intro u
  refine ⟨fun ⟨hBu, huE⟩ => ⟨((es B u).mp hBu).2, ((ks u E).mp huE).2⟩, fun ⟨hu, huE⟩ => ?_⟩
  have huA := (h.nodes u).mpr ⟨a, B, hu, d, D, W, had, stage.1, hB⟩
  have huD := (ht.2.1 u).mpr ⟨huA, (h.index u a B hu).mpr huA⟩
  exact ⟨(es B u).mpr ⟨huD, hu⟩, (ks u E).mpr ⟨huD, huE⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 源到整个有限支撑极限的常值初等嵌入

完整测度在源内的限制保持原商；常值嵌入与任一分量的极限嵌入复合。
结果仍保留源代表、商投影及带标签节点三者的精确图方程。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 常值箭头的实际代表证书，保留代表的源内定义域及源内值域界。 -/
def Ep_constants_d (X q i : M.Domain) : Prop := ∀ x E, Rd_entry_d x E i →
  ∃ u a B f D, M.mem D X ∧ Sfun_d X D f ∧ Rs_const_d D x f ∧ M.mem f B ∧ KPair_d M u a B ∧ Rd_entry_d u E q

theorem ep_constant_limit_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q c C V a d : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C V) (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S)
    (had : Rd_entry_d a d Z) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ b j n D U G r Y W, Smem_d I b X R ∧ Smap_d I ω b c X C j ∧
      M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ Rd_entry_d a U F ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧ Rp_model_d I D X U R d G r Y W ∧
      ∀ x E, Rd_entry_d x E j ↔ M.mem x X ∧ ∃ f B u,
        M.mem f G ∧ Rs_const_d D x f ∧ Rd_entry_d f B r ∧ KPair_d M u a B ∧ Rd_entry_d u E q := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have models := h.components
  obtain ⟨n, D, U, G, r, Y, W, hn, ha, hD, haU, hG, hm⟩ := models a d had
  obtain ⟨b, hX⟩ := source.code
  obtain ⟨P, U', hP, hU', _, hm'⟩ := rs_restrict_model_l hZF source.omega source.transitive hX source.theory
    (source.space_mem_l hZF hn hD) (hF.at_l hZF.1 haU ha hD) hG hm
  obtain ⟨i, hi, is⟩ := rs_constant_embedding_l hZF source.omega source.transitive hX source.theory (source.uniform_l hZF hn hD)
    (source.space_mem_l hZF hn hD) hP hU' hG hm'
  obtain ⟨k, hk, ks⟩ := ep_stage_embedding_l hZF source.omega h.toEg_graph_d h.diagram limit elementary model had hm.code
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF hi hk
  refine ⟨b, j, n, D, U, G, r, Y, W, hX, hj, hn, ha, hD, haU, hG, hm, fun x E =>
    (js x E).trans (and_congr_right fun hx => ?_)⟩
  constructor
  · rintro ⟨B, hxB, hBE⟩
    obtain ⟨_, f, hf, hc, hfr⟩ := (is x B).mp hxB
    obtain ⟨_, u, hu, huE⟩ := (ks B E).mp hBE
    exact ⟨f, B, u, hf, hc, hfr, hu, huE⟩
  · rintro ⟨f, B, u, hf, hc, hfr, hu, huE⟩
    exact ⟨B, (is x B).mpr ⟨hx, f, hf, hc, hfr⟩,
      (ks B E).mpr ⟨hm.map.projection.output_mem_of_pairMember hfr, u, hu, huE⟩⟩

/-- 原始商的常值图与外延性先于任何良基性或坍塌构造。 -/
theorem ep_constant_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q c C V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C V) (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S) :
    ∃ b i, Smem_d (kp_pair_l (ZF.modelsKP hZF)) b X R ∧
      Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω b c X C i ∧ Ep_constants_d X q i ∧ Wc_ext_d C V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨B, hB⟩ := model.2.1
  obtain ⟨u, hu⟩ := (limit.range B).mp hB
  obtain ⟨a, ha, _⟩ := system.diagram.index.2.1 u (limit.projection.bound_l hu).1
  obtain ⟨_, hz⟩ := system.codes
  obtain ⟨d, _, had⟩ := hz.2.1 a ha
  obtain ⟨b, i, n, D, U, G, r, E, Q, hm, hi, hn, ha, hD, haU, hG, md, spec⟩ :=
    ep_constant_limit_l hZF source family system limit model elementary had
  have constants : Ep_constants_d X q i := by
    intro x H hxH
    obtain ⟨_, f, B, u, hf, hc, hfr, hu, huH⟩ := (spec x H).mp hxH
    exact ⟨u, a, B, f, D, source.space_mem_l hZF hn hD,
      source.function_l hZF ((hG f).mp hf).1 ((hG f).mp hf).2,
      hc, md.map.representative_l I (family.at_l hZF.1 haU ha hD).base hfr, hu, huH⟩
  have extX : Wc_ext_d X R := fun x hx y hy same => hZF.1.eq_of_same_members x y (fun z =>
    ⟨fun hz => ((hm.2 z y).mp ((same z (source.transitive x hx z hz)).mp
      ((hm.2 z x).mpr ⟨source.transitive x hx z hz, hx, hz⟩))).2.2,
     fun hz => ((hm.2 z x).mp ((same z (source.transitive y hy z hz)).mpr
      ((hm.2 z y).mpr ⟨source.transitive y hy z hz, hy, hz⟩))).2.2⟩)
  exact ⟨b, i, hm, hi, constants, hi.extensional_l hZF source.omega hm.1 model extX⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑极限的传递实现

外延性由常值初等嵌入实际传递，坍塌消费整个极限的内部良基性。
返回坍塌及其逆图的完整内部同构、源到传递目标的完整初等嵌入，
以及以 ω 为字母表的实际下一步源；新小字母表由该源重新装配。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 指定传递目标的原常值图及坍缩图；比较、长度与强度证书保持同一实现。 -/
def Ep_realizer_d (hZF : M.Models ZF) (ω X q b c C V d N i : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ t e, Smap_d I ω b c X C t ∧ Ep_constants_d X q t ∧ Wc_graph_d C V e ∧
    M.IsSetBijectionFromTo I e C N ∧ Smap_d I ω c d C N e ∧
    ∀ x y, Rd_entry_d x y i ↔ M.mem x X ∧ ∃ z, Rd_entry_d x z t ∧ Rd_entry_d z y e

def Ep_collapse_d (hZF : M.Models ZF) (ω X R q c C V : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  Wc_ext_d C V ∧ ∃ b i N e inv d W j, Smem_d I b X R ∧ Smap_d I ω b c X C i ∧ Ep_constants_d X q i ∧
    M.TransitiveSet N ∧ Wc_graph_d C V e ∧ M.IsSetBijectionFromTo I e C N ∧ Smem_d I d N W ∧
    Smap_d I ω c d C N e ∧ M.IsSetBijectionFromTo I inv N C ∧
    (∀ x y, Rd_entry_d y x inv ↔ Rd_entry_d x y e) ∧ Smap_d I ω d c N C inv ∧
    Smap_d I ω b d X N j ∧
    (∀ x y, Rd_entry_d x y j ↔ M.mem x X ∧ ∃ z, Rd_entry_d x z i ∧ Rd_entry_d z y e) ∧
    ∃ K, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K N W

theorem ep_collapse_l (hZF : M.Models ZF) {ω κ K L X R F J O Z A p T S q c C V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C V) (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S)
    (wf : Wf_rel_d C V) : Ep_collapse_d hZF ω X R q c C V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨b, i, hm, hi, constants, he⟩ := ep_constant_l hZF source hF h limit model elementary
  obtain ⟨N, e, inv, d, W, ht, hg, bij, hn, elem, bi, inverse, elemInv⟩ := wc_smaps_l hZF source.omega model wf he
  obtain ⟨j, hj, js⟩ := smap_comp_l I hZF hi elem
  have fix := hj.omega_l I hZF source.omega source.transitive ht hm hn source.omega_mem
  exact ⟨he, b, i, N, e, inv, d, W, j, hm, hi, constants, ht, hg, bij, hn, elem, bi, inverse, elemInv, hj, js,
    source.successor_l hZF hm hn ht hj (hj.1.1.output_mem_of_pairMember fix) (fun _ h => h)
      ((hj.small_l I hZF source.omega hm.1 hn.1 fix).mp (source.cardinal_small.mono_mem_l I hm source.omega_mem source.below))⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一个扩展器极限中的可定义关系

改换观察的原二元公式，源函数、商类、标签、过渡图和极限投影全部保留。
逐分量的 Łoś 方程把新关系识别为原公式的解释，供共同纤维证明良基性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_formula_system_l {ω κ K L X R F J O Z A p T S q c C W b Y V d j : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hm : Smem_d I b X R)
    (family : Em_source_d ω κ L X F) (h : Ep_system_d I ω κ L X R F J O Z A p T S)
    (limit : Di_limit_d A p T S q C W) (model : Smdl_d I c C W)
    (elementary : Di_elementary_d I ω O A p T S) (hn : Smdl_d I d Y V)
    (hj : Smap_d I ω c d C Y j) (φ : Formula 1 2) (hc : φ.FreeClosed) :
    ∃ Q U Z' S' e W', M.IsSetRelationOn I Q X ∧ M.IsSetRelationOn I U Y ∧
      (∀ x y : (smdl_structure_l I (R := R) hm.1.2.1).Domain, Rd_entry_d x.val y.val Q ↔
        Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := R) hm.1.2.1) x y) φ) ∧
      (∀ x y : (smdl_structure_l I (R := V) hn.2.1).Domain, Rd_entry_d x.val y.val U ↔
        Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := V) hn.2.1) x y) φ) ∧
      Ep_system_d I ω κ L X Q F J O Z' A p T S' ∧ Di_limit_d A p T S' q C W' ∧ Smdl_d I e C W' ∧
      ∀ E H x y, Rd_entry_d E x j → Rd_entry_d H y j → (Rd_entry_d E H W' ↔ Rd_entry_d x y U) := by
  obtain ⟨Q, hQ, qs⟩ := smdl_formula_relation_l hZF hm.1 φ hc
  obtain ⟨U, hU, us⟩ := smdl_formula_relation_l hZF hn φ hc
  obtain ⟨e, W', newModel, jr⟩ := smdl_pull_l hZF model.2.1 hj.1.1 U
  obtain ⟨S', diagram, newLimit, sr⟩ := di_relation_change_l hZF h.diagram limit newModel
  obtain ⟨Q₀, hz⟩ := h.codes
  have models := h.components
  obtain ⟨Z', Q₁, hz', models'⟩ := ep_components_l hZF source family
    (fun a ha => ((h.indices a).mp ha).elim fun n hn => ⟨n, hn.1, hn.2.1⟩) Q
  -- 同一代表族产生同一类集合；仅分量的关系码随公式改变。
  have carrier a B : Ep_at_d Z a B ↔ Ep_at_d Z' a B := by
    have move {Z₀ Z₁ Q₀ Q₁ R₀ R₁ : M.Domain} (hz₀ : Fn0_d J Q₀ Z₀) (hz₁ : Fn0_d J Q₁ Z₁)
        (m₀ : ∀ a c, Rd_entry_d a c Z₀ → Ep_component_d I ω κ L X R₀ F a c)
        (m₁ : ∀ a c, Rd_entry_d a c Z₁ → Ep_component_d I ω κ L X R₁ F a c)
        (ha : Ep_at_d Z₀ a B) : Ep_at_d Z₁ a B := by
      obtain ⟨c, C₀, R₀', hac, hca, hB⟩ := ha
      obtain ⟨d, _, had⟩ := hz₁.2.1 a (hz₀.bound_l hac).1
      obtain ⟨_, _, _, _, _, D, S₀, S₁, _, _, _, _, _, old, new⟩ :=
        ep_component_pair_l I hZF.1 family (m₀ a c hac) (m₁ a d had)
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hca old.code.1
      exact ⟨d, C₀, S₁, had, new.code.1, hB⟩
    exact ⟨move hz hz' models models', move hz' hz models' models⟩
  have nodes u : M.mem u A ↔ ∃ a B, KPair_d M u a B ∧ Ep_at_d Z' a B := by
    refine (h.nodes u).trans (exists_congr fun a => exists_congr fun B => ?_)
    exact and_congr Iff.rfl (carrier a B)
  have relation u v a B D (hu : KPair_d M u a B) (hv : KPair_d M v a D)
      (huA : M.mem u A) (hvA : M.mem v A) : Rd_entry_d u v S' ↔ Ep_rel_d Z' a B D := by
    have hua := (h.index u a B hu).mpr huA
    have hva := (h.index v a D hv).mpr hvA
    obtain ⟨c₀, _, hac⟩ := hz.2.1 a (h.projection.bound_l hua).2
    obtain ⟨c₁, _, had⟩ := hz'.2.1 a (h.projection.bound_l hua).2
    obtain ⟨n, E₀, M₀, G, r, D₀, R₀, R₁, hnω, ha, he₀, haM, hG, old, new⟩ :=
      ep_component_pair_l I hZF.1 family (models a c₀ hac) (models' a c₁ had)
    have hB := (ep_at_read_l hz hac old.code.1).mp (h.toEp_graph_d.at_l huA hu)
    have hD := (ep_at_read_l hz hac old.code.1).mp (h.toEp_graph_d.at_l hvA hv)
    obtain ⟨E, _, huE⟩ := limit.projection.2.1 u huA
    obtain ⟨H, _, hvH⟩ := limit.projection.2.1 v hvA
    obtain ⟨x, _, hEx⟩ := hj.1.1.2.2 E (limit.projection.bound_l huE).2
    obtain ⟨y, _, hHy⟩ := hj.1.1.2.2 H (limit.projection.bound_l hvH).2
    obtain ⟨k, hk, ks⟩ := ep_stage_embedding_l hZF source.omega h.toEg_graph_d h.diagram limit elementary model hac old.code
    obtain ⟨l, hl, ls⟩ := smap_comp_l I hZF hk hj
    have hBx := (ls B x).mpr ⟨hB, E, (ks B E).mpr ⟨hB, u, hu, huE⟩, hEx⟩
    have hDy := (ls D y).mpr ⟨hD, H, (ks D H).mpr ⟨hD, v, hv, hvH⟩, hHy⟩
    obtain ⟨f, hf⟩ := (old.map.range B).mp hB
    obtain ⟨g, hg⟩ := (old.map.range D).mp hD
    have los := rs_formula_relation_l hZF source.omega source.transitive hm source.theory
      (source.uniform_l hZF hnω he₀) (source.space_mem_l hZF hnω he₀)
      (family.at_l hZF.1 haM ha he₀) hG old hf hg φ hc qs
    have elem := smap_source_l I hZF source.omega old.code hn hl φ hc
      (sr_pair_env_l (N := smdl_structure_l I (R := R₀) old.code.2.1) ⟨B, hB⟩ ⟨D, hD⟩)
      (sr_pair_env_l (N := smdl_structure_l I (R := V) hn.2.1)
        ⟨x, hj.1.1.output_mem_of_pairMember hEx⟩ ⟨y, hj.1.1.output_mem_of_pairMember hHy⟩)
      (Fin.cases hDy (fun _ => hBx))
    have eq := (new.relation f g B D hf hg).trans (los.symm.trans (elem.trans
      (us ⟨x, hj.1.1.output_mem_of_pairMember hEx⟩ ⟨y, hj.1.1.output_mem_of_pairMember hHy⟩).symm))
    exact (sr u v a E H hua hva huE hvH).trans ((jr E H x y hEx hHy).trans
      (eq.symm.trans (ep_rel_read_l hz' had new.code.1).symm))
  have graph : Ep_graph_d I ω κ L X Q F J O Z' A p T S' := {
    order := h.order, order_spec := h.order_spec, projection := h.projection, indices := h.indices
    codes := ⟨Q₁, hz'⟩, components := models', nodes := nodes, index := h.index, arrows := h.arrows
    relations := fun u v => ⟨fun huv => by
      obtain ⟨a, hua, hva⟩ := diagram.locality u v huv
      obtain ⟨B, hu, _⟩ := h.toEp_graph_d.label_l hua
      obtain ⟨D, hv, _⟩ := h.toEp_graph_d.label_l hva
      exact ⟨(h.projection.bound_l hua).1, (h.projection.bound_l hva).1, a, B, D, hu, hv,
        (relation u v a B D hu hv (h.projection.bound_l hua).1 (h.projection.bound_l hva).1).mp huv⟩,
      fun ⟨huA, hvA, a, B, D, hu, hv, hr⟩ => (relation u v a B D hu hv huA hvA).mpr hr⟩ }
  exact ⟨Q, U, Z', S', e, W', hQ, hU, qs, us, ⟨graph, diagram, h.representatives⟩, newLimit, newModel, jr⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 相对测度族施加到实际源模型

先构造全部源内部代表的初等定向极限。此构造不需要良基性；跨模型施加
只消费子集一致性，良基性可随后由共同纤维或向良基模型的复制嵌入取得。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_ultrapower_l (hZF : M.Models ZF) {ω κ K L X R F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F)
    : ∃ J O Z A p T S q c C V,
      Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S ∧ Di_limit_d A p T S q C V ∧
      Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V ∧
      Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨J, O, Z, A, p, T, S, h⟩ := ep_system_exists_l hZF source hF coherent
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  have hzfn : Fn0_d z L z := ⟨fun r hr => (hz r hr).elim, fun r hr => (hz r hr).elim, fun r hr => (hz r hr).elim⟩
  have hzJ := (h.indices z).mpr ⟨z, hzω, hzfn, fun i j x hi _ => hi.elim fun r hr => (hz r hr.2).elim⟩
  obtain ⟨Q, hZ⟩ := h.codes
  have models := h.components
  obtain ⟨d, _, hzd⟩ := hZ.2.1 z hzJ
  obtain ⟨_, _, _, _, _, D, W, _, _, _, _, _, hm⟩ := models z d hzd
  obtain ⟨B, hBD⟩ := hm.code.2.1
  obtain ⟨u, hu⟩ := I.total z B
  have huA := (h.nodes u).mpr ⟨z, B, hu, d, D, W, hzd, hm.code.1, hBD⟩
  obtain ⟨c, q, C, V, limit, model⟩ := di_model_exists_l hZF h.diagram ⟨u, huA⟩
  exact ⟨J, O, Z, A, p, T, S, q, c, C, V, h, limit, model, h.toEp_graph_d.elementary_l hZF source hF coherent⟩

/-- 同一扩展器图在子集一致的另一源上生成实际完整初等超幂。 -/
theorem ep_apply_l (hZF : M.Models ZF) {ω κ K L N X R F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Em_source_d ω κ L N F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L N F)
    (agree : Ea_agree_d ω κ N X) : ∃ J O Z A p T S q c C V,
      Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S ∧ Di_limit_d A p T S q C V ∧
      Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C V ∧
      Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω O A p T S :=
  ep_ultrapower_l hZF source (owner.transfer_l agree) (coherent.transfer_l hZF agree)

end YesMetaZFC.SetTheory.LargeCardinal
