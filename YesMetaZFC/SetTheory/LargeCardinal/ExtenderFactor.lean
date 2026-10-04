import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEvaluationPull
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Factor

/-! # 全部有限支撑求值的装配与极限因子

带标签节点读出类中的任意代表；求值与过渡交换后，经真正的商泛性质下降。
因子是关系嵌入，定义方程是 k([a,f]) = j(f)(a)。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ee_node_d (j u y : M.Domain) : Prop := ∃ a D f, KPair_d M u a D ∧ M.mem f D ∧ Ee_value_d j a f y
def ee_node_m {d} (j u y : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (kpair_m u.weaken.weaken.weaken (.bound 2) (.bound 1)) (.conj (.mem .newest (.bound 1))
    (ee_value_m j.weaken.weaken.weaken (.bound 2) .newest y.weaken.weaken.weaken)))))
derive_free_closed ee_node_m

def Ee_factor_d (hZF : M.Models ZF) (j Y q C W : M.Domain) : Prop :=
  ∃ g, M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) g C Y ∧
    (∀ E y, Rd_entry_d E y g ↔ M.mem E C ∧ ∃ u, Rd_entry_d u E q ∧ Ee_node_d j u y) ∧
    (∀ E H y z, Rd_entry_d E y g → Rd_entry_d H z g → (Rd_entry_d E H W ↔ M.mem y z)) ∧
    ∀ u a B f E y, Rd_entry_d u E q → KPair_d M u a B → M.mem f B → Rd_entry_d E y g → Ee_value_d j a f y

theorem ee_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (j u y : Term d) :
    Formula.satisfies ρ (ee_node_m j u y) ↔ Ee_node_d (j.eval ρ) (u.eval ρ) (y.eval ρ) := by
  simp only [ee_node_m, Ee_node_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, Formula.satisfies_mem_iff, ee_value_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ee_node_pair_l {j u a D y : M.Domain} (hu : KPair_d M u a D) :
    Ee_node_d j u y ↔ ∃ f, M.mem f D ∧ Ee_value_d j a f y := by
  refine ⟨fun ⟨b, E, f, hv, hf, hy⟩ => ?_, fun ⟨f, hf, hy⟩ => ⟨a, D, f, hu, hf, hy⟩⟩
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hv
  exact ⟨f, hf, hy⟩

theorem ee_nodes_l (hZFC : M.Models ZFC) {ω δ X A Y B j κ k K R L S F J O Z D p T V : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X j κ k)
    (hL : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) j κ L S F)
    (system : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z D p T V) :
    ∃ e, Fn0_d D Y e ∧ (∀ u y, Rd_entry_d u y e ↔ M.mem u D ∧ Ee_node_d j u y) ∧
      (∀ u v y z, Rd_entry_d u v T → Rd_entry_d u y e → Rd_entry_d v z e → y = z) ∧
      (∀ u v a y z, Rd_entry_d u a p → Rd_entry_d v a p → Rd_entry_d u y e → Rd_entry_d v z e →
        (u = v ↔ y = z) ∧ (Rd_entry_d u v V ↔ M.mem y z)) ∧
      ∀ u a B y f, KPair_d M u a B → Rd_entry_d u y e → M.mem f B → Ee_value_d j a f y := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hZ, models⟩ := system.models
  have component a c (hac : Rd_entry_d a c Z) := ee_component_l hZFC source hV hδ h hY hc hL hS hSY hF (models a c hac)
  have atMap a E (hat : Ep_at_d Z a E) : ∃ c C W e, Rd_entry_d a c Z ∧ Smdl_d I c C W ∧
      M.mem E C ∧ M.IsSetInjectionFromTo I e C Y ∧
      (∀ D y, Rd_entry_d D y e ↔ M.mem D C ∧ ∃ f, M.mem f D ∧ Ee_value_d j a f y) ∧
      (∀ D y f, Rd_entry_d D y e → M.mem f D → Ee_value_d j a f y) ∧
      ∀ D E y z, Rd_entry_d D y e → Rd_entry_d E z e → (Rd_entry_d D E W ↔ M.mem y z) := by
    obtain ⟨c, C, W, hac, _, code, hE⟩ := ep_at_model_l hZF models hat
    obtain ⟨C', W', e, code', he, es, any, rel⟩ := component a c hac
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I code code'
    exact ⟨c, C, W, e, hac, code', hE, he, es, any, rel⟩
  let ρ : Env M 1 := ⟨fun _ => j, fun _ => j⟩
  let φ : BinarySchema 1 := { body := ee_node_m (.bound 2) (.bound 1) .newest }
  have sat u y : φ.denote ρ u y ↔ Ee_node_d j u y := ee_node_sat_l hZF.1 ..
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := Y)
    (fun u hu => by
      obtain ⟨a, E, hp, hat⟩ := (system.nodes u).mp hu
      obtain ⟨_, C, _, t, _, _, hE, ht, ts, _⟩ := atMap a E hat
      obtain ⟨y, _, hEy⟩ := ht.1.2.2 E hE
      exact ⟨y, (sat u y).mpr ((ee_node_pair_l hp).mpr ((ts E y).mp hEy).2)⟩)
    (fun u hu y z hy hz => by
      obtain ⟨a, E, hp, hat⟩ := (system.nodes u).mp hu
      obtain ⟨_, _, _, t, _, _, hE, ht, ts, _⟩ := atMap a E hat
      exact ht.1.1.2 E y z ((ts E y).mpr ⟨hE, (ee_node_pair_l hp).mp ((sat u y).mp hy)⟩)
        ((ts E z).mpr ⟨hE, (ee_node_pair_l hp).mp ((sat u z).mp hz)⟩))
    (fun u y hu hy => by
      obtain ⟨a, E, hp, hat⟩ := (system.nodes u).mp hu
      obtain ⟨_, _, _, t, _, _, hE, ht, ts, _⟩ := atMap a E hat
      exact ht.1.output_mem_of_pairMember ((ts E y).mpr ⟨hE, (ee_node_pair_l hp).mp ((sat u y).mp hy)⟩))
  have spec u y := (es u y).trans (and_congr_right fun _ => sat u y)
  have any u a E y f (hp : KPair_d M u a E) (hy : Rd_entry_d u y e) (hf : M.mem f E) : Ee_value_d j a f y := by
    obtain ⟨_, _, _, t, _, _, hE, _, ts, all, _⟩ := atMap a E (system.toEp_graph_d.at_l (he.input_mem_of_pairMember hy) hp)
    exact all E y f ((ts E y).mpr ⟨hE, (ee_node_pair_l hp).mp ((spec u y).mp hy).2⟩) hf
  refine ⟨e, fn0_of_function_l (ZF.modelsKP hZF) he, spec, ?_, ?_, any⟩
  · intro u v y z huv huy hvz
    obtain ⟨a, E, hu, _⟩ := (system.nodes u).mp (he.input_mem_of_pairMember huy)
    obtain ⟨b, H, hv, _⟩ := (system.nodes v).mp (he.input_mem_of_pairMember hvz)
    obtain ⟨f, hf, hfy⟩ := (ee_node_pair_l hu).mp ((spec u y).mp huy).2
    obtain ⟨m, n, q, g, hm, hn, hq, hnb, hqa, hg, pull⟩ := system.representatives u v a b E H hu hv huv f hf
    have haY : M.mem a Y := hSY a ((hS a).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) hqa.1⟩)
    have hbY : M.mem b Y := hSY b ((hS b).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hnb⟩)
    have hfX : M.mem f X := by
      obtain ⟨_, _, _, _, _, _, hj⟩ := h
      exact hfy.elim fun _ ht => hj.1.1.input_mem_of_pairMember ht.1
    exact ee_pull_l hZFC source hV hδ h hY hc hL hm hn hq haY hbY hnb hqa hfX pull hfy (any v b H z g hv hvz hg)
  · intro u v a y z hua hva huy hvz
    obtain ⟨E, hu, hat⟩ := system.toEp_graph_d.label_l hua
    obtain ⟨H, hv, hbt⟩ := system.toEp_graph_d.label_l hva
    obtain ⟨c, C, W, t, hac, code, hE, ht, ts, _, rel⟩ := atMap a E hat
    have hH := (ep_at_read_l hZ hac code.1).mp hbt
    have hEy := (ts E y).mpr ⟨hE, (ee_node_pair_l hu).mp ((spec u y).mp huy).2⟩
    have hHz := (ts H z).mpr ⟨hH, (ee_node_pair_l hv).mp ((spec v z).mp hvz).2⟩
    refine ⟨⟨fun eq => he.1.2 v y z (eq ▸ huy) hvz, fun eq => ?_⟩, ?_⟩
    · exact kpair_unique_l M hZF.1 hu ((ht.2 E H z (eq ▸ hEy) hHz).symm ▸ hv)
    · exact (system.toEp_graph_d.relation_l hu hv).trans ((and_congr_right fun _ => and_congr_right fun _ =>
        ep_rel_read_l hZ hac code.1).trans ⟨fun hr => (rel E H y z hEy hHz).mp hr.2.2,
          fun hr => ⟨he.input_mem_of_pairMember huy, he.input_mem_of_pairMember hvz, (rel E H y z hEy hHz).mpr hr⟩⟩)

/-- 整个极限到原目标的实际因子；每个商元素的所有代表都读同一个值。 -/
theorem ee_factor_l (hZFC : M.Models ZFC) {ω δ X A Y B j κ k K R L S F J O Z D p T V q C W : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X j κ k)
    (hL : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) j κ L S F)
    (system : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z D p T V)
    (limit : Di_limit_d D p T V q C W) : Ee_factor_d (ZFC.models_zf_l hZFC) j Y q C W := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨e, he, es, comm, fiber, any⟩ := ee_nodes_l hZFC source hV hδ h hY hc hL hS hSY hF system
  obtain ⟨g, hg, law, rel, _⟩ := di_factor_embedding_l hZF system.diagram limit he comm fiber
  refine ⟨g, hg, fun E y => ⟨?_, ?_⟩, rel, ?_⟩
  · intro hy
    have hE := hg.1.input_mem_of_pairMember hy
    obtain ⟨u, hu⟩ := (limit.range E).mp hE
    obtain ⟨z, _, huz⟩ := he.2.1 u (limit.projection.bound_l hu).1
    have eq := hg.1.1.2 E z y (law u E z hu huz) hy
    exact ⟨hE, u, hu, eq ▸ ((es u z).mp huz).2⟩
  · rintro ⟨_, u, hu, hnode⟩
    exact law u E y hu ((es u y).mpr ⟨(limit.projection.bound_l hu).1, hnode⟩)
  · intro u a B f E y hu hp hf hy
    obtain ⟨z, _, huz⟩ := he.2.1 u (limit.projection.bound_l hu).1
    exact hg.1.1.2 E z y (law u E z hu huz) hy ▸ any u a B z f hp huz hf

end YesMetaZFC.SetTheory.LargeCardinal
