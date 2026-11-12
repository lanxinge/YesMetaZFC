import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.DerivedPredicate
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.Model.SetTheory.DirectedSystem.Isomorphism

/-! # 原嵌入对实际源分量的因子图

规范类中任意一个代表都有同一个种子求值。唯一值替代构造真正的商函数，
原子真值定理同时证明单射性和成员关系的保持、反映。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

theorem ee_component_l (hZF : M.Models ZF) {ω δ X A Y B j κ k K R L S F a c : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k)
    (hL : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F)
    (hm : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ C T e, Smdl_d I c C T ∧ M.IsSetInjectionFromTo I e C Y ∧
      (∀ D y, Rd_entry_d D y e ↔ M.mem D C ∧ ∃ f, M.mem f D ∧ Ee_value_d j a f y) ∧
      (∀ D y f, Rd_entry_d D y e → M.mem f D → Ee_value_d j a f y) ∧
      ∀ D E y z, Rd_entry_d D y e → Rd_entry_d E z e → (Rd_entry_d D E T ↔ M.mem y z) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨n, D, U, G, p, C, T, hn, ha, hD, haU, hG, model⟩ := hm
  obtain ⟨haS, m, D₀, ha₀, hD₀, hu⟩ := (hF.2.2 a U).mp haU
  have eq := ha₀.domain_eq_l hZF.1 ha
  subst m
  have eq := hZF.1.eq_of_same_members D₀ D (fun s => (hD₀ s).trans (hD s).symm)
  subst D₀
  have hDX := source.space_mem_l hZF hn hD
  obtain ⟨D', _, hjD⟩ := hj.2.2 D hDX
  have hωκ := ed_critical_omega_l I hZF source.omega h source.transitive hY hc
  have haD := es_seed_l I hZF source.omega h source.transitive hY
    (hc.fixed n (hc.ordinal.transitive ω hωκ n hn)) hc.image hjD hD hL (hSY a haS) ha
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  have hPX := source.transitive P (v_power_mem_l I hV hδ hDX hP)
  obtain ⟨b, hX⟩ := source.code
  have sf f (hf : M.mem f G) := sc_function_domain_l (source.algebra_l (ZF.modelsKP hZF)) ((hG f).mp hf).1 ((hG f).mp hf).2
  have eval f (hf : M.mem f G) := ed_evaluation_l hZF source.omega h source.transitive hY hjD haD (sf f hf)
  have atoms f g y z (hf : M.mem f G) (hg : M.mem g G) (hy : Ee_value_d j a f y) (hz : Ee_value_d j a g z) :=
    ed_evaluation_atoms_l hZF source.omega h source.transitive hY hjD haD hP hPX hu hX (sf f hf) (sf g hg) hy hz
  have ultra := (es_measures_l hZF source.omega hV hδ h hY hc hL hS hSY hF).at_l hZF.1 haU ha hD
  have represent E (hE : M.mem E C) f (hf : M.mem f E) := model.map.member_l I hZF.1 ultra.1.base_l hE hf
  let ρ := (⟨fun _ => j, fun _ => j⟩ : Env M 1).push a
  let φ : BinarySchema 2 := {
    body := Formula.existsMem (.bound 1) (ee_value_m (.bound 4) (.bound 3) .newest (.bound 1)) }
  have sat E y : φ.denote ρ E y ↔ ∃ f, M.mem f E ∧ Ee_value_d j a f y := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, ee_value_sat_l hZF.1]; rfl
  have any E y (hE : M.mem E C) (hy : φ.denote ρ E y) f (hf : M.mem f E) : Ee_value_d j a f y := by
    obtain ⟨g, hg, hgy⟩ := (sat E y).mp hy
    have hgp := represent E hE g hg
    have hfp := represent E hE f hf
    have hfg := (rp_kernel_l I hZF.1 ultra.1.base_l model.map hfp hgp).mp rfl
    obtain ⟨z, _, hfz, _⟩ := eval f (model.map.projection.input_mem_of_pairMember hfp)
    exact (atoms f g z y (model.map.projection.input_mem_of_pairMember hfp)
      (model.map.projection.input_mem_of_pairMember hgp) hfz hgy).1.mp hfg ▸ hfz
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := Y)
    (fun E hE => by
      obtain ⟨f, hfp⟩ := (model.map.range E).mp hE
      obtain ⟨y, _, hy, _⟩ := eval f (model.map.projection.input_mem_of_pairMember hfp)
      exact ⟨y, (sat E y).mpr ⟨f, model.map.representative_l I ultra.1.base_l hfp, hy⟩⟩)
    (fun E hE y z hy hz => by
      obtain ⟨f, hf, hfy⟩ := (sat E y).mp hy
      obtain ⟨v, _, _, unique⟩ := eval f (model.map.projection.input_mem_of_pairMember (represent E hE f hf))
      exact (unique y hfy).trans (unique z (any E z hE hz f hf)).symm)
    (fun E y hE hy => by
      obtain ⟨f, hf, hfy⟩ := (sat E y).mp hy
      obtain ⟨z, hz, _, unique⟩ := eval f (model.map.projection.input_mem_of_pairMember (represent E hE f hf))
      exact (unique y hfy).symm ▸ hz)
  have repr E y (hy : Rd_entry_d E y e) : ∃ f, M.PairMember I f E p ∧ Ee_value_d j a f y := by
    obtain ⟨hE, hy⟩ := (es E y).mp hy
    obtain ⟨f, hf, hfy⟩ := (sat E y).mp hy
    exact ⟨f, represent E hE f hf, hfy⟩
  refine ⟨C, T, e, model.code, ⟨he, ?_⟩, fun E y => (es E y).trans (and_congr_right fun _ => sat E y),
    fun E y f hy hf => any E y ((es E y).mp hy).1 ((es E y).mp hy).2 f hf, ?_⟩
  · intro E H y hy hz
    obtain ⟨f, hfp, hfy⟩ := repr E y hy
    obtain ⟨g, hgp, hgy⟩ := repr H y hz
    exact (rp_kernel_l I hZF.1 ultra.1.base_l model.map hfp hgp).mpr
      ((atoms f g y y (model.map.projection.input_mem_of_pairMember hfp)
        (model.map.projection.input_mem_of_pairMember hgp) hfy hgy).1.mpr rfl)
  · intro E H y z hy hz
    obtain ⟨f, hfp, hfy⟩ := repr E y hy
    obtain ⟨g, hgp, hgz⟩ := repr H z hz
    exact (model.relation f g E H hfp hgp).trans (atoms f g y z
      (model.map.projection.input_mem_of_pairMember hfp) (model.map.projection.input_mem_of_pairMember hgp) hfy hgz).2

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原求值与有限坐标过渡交换 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ee_pull_l (hZF : M.Models ZF) {ω δ X A Y B j κ k K R L m n q a b f g y z : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k)
    (hL : M.MemberSubset L k) (hm : M.mem m ω) (hn : M.mem n ω) (hq : Fn0_d m n q)
    (ha : M.mem a Y) (hb : M.mem b Y) (hnb : Fn0_d n L b) (hqa : Cp0_d m n L q b a)
    (hfX : M.mem f X) (pull : Ep_pull_d κ X m n q f g)
    (hy : Ee_value_d j a f y) (hz : Ee_value_d j b g z) : y = z := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  obtain ⟨D, hD, hf⟩ := pull.1
  obtain ⟨E, hE, hg⟩ := pull.2.1
  have hωκ := ed_critical_omega_l I hZF source.omega h source.transitive hY hc
  obtain ⟨E', D', t, t', hjE, hjD, ht, ts, hjt, htb⟩ := ed_reindex_l I hZF source.omega hV hδ h hY hc
    (hc.ordinal.transitive ω hωκ m hm) (hc.ordinal.transitive ω hωκ n hn) hq hE hD hL hb ha hnb hqa
  obtain ⟨_, C, hCX, hFC⟩ := source.function_l hZF hfX hf
  have comp : Cp0_d E D X t f g := by
    refine ⟨hg, fun s hs => ?_⟩
    obtain ⟨r, hr, hsr⟩ := ht.2.1 s hs
    obtain ⟨x, hx, hrx⟩ := hf.2.1 r hr
    exact ⟨r, hr, x, hx, hsr, hrx, (pull.2.2 s r ((hE s).mp hs) ((ts s r).mp hsr).2 x).mpr hrx⟩
  obtain ⟨C', _, hjC⟩ := hj.2.2 C hCX
  obtain ⟨f', hjf, haf⟩ := hy
  obtain ⟨g', hjg, hbg⟩ := hz
  let φ : Formula 1 6 := cp0_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have tr := spred_delta_l I hZF source.omega h source.transitive hY φ (by simp -implicitDefEqProofs [φ]) (cp0_delta_l ..)
    ⟨Fin.cases g (Fin.cases f (Fin.cases t (Fin.cases C (Fin.cases D (fun _ => E))))), fun _ => E⟩
    ⟨Fin.cases g' (Fin.cases f' (Fin.cases t' (Fin.cases C' (Fin.cases D' (fun _ => E'))))), fun _ => E'⟩
    (Fin.cases hjg (Fin.cases hjf (Fin.cases hjt (Fin.cases hjC (Fin.cases hjD (fun _ => hjE))))))
  simp only [φ, cp0_sat_l hZF.1] at tr
  have comp' := tr.mp (comp.retarget_l hFC)
  have ht' := (spred_function_l I hZF source.omega h source.transitive hY hjE hjD hjt).mp ht
  have hf' := (spred_function_l I hZF source.omega h source.transitive hY hjD hjC hjf).mp hFC
  exact (fn0_function_l (ZF.modelsKP hZF) hf').1.2 a y z haf ((comp'.value_l ht' hf' htb).mp hbg)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部有限支撑求值的装配与极限因子

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

theorem ee_nodes_l (hZF : M.Models ZF) {ω δ X A Y B j κ k K R L S F J O Z D p T V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k)
    (hL : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z D p T V) :
    ∃ e, Fn0_d D Y e ∧ (∀ u y, Rd_entry_d u y e ↔ M.mem u D ∧ Ee_node_d j u y) ∧
      (∀ u v y z, Rd_entry_d u v T → Rd_entry_d u y e → Rd_entry_d v z e → y = z) ∧
      (∀ u v a y z, Rd_entry_d u a p → Rd_entry_d v a p → Rd_entry_d u y e → Rd_entry_d v z e →
        (u = v ↔ y = z) ∧ (Rd_entry_d u v V ↔ M.mem y z)) ∧
      ∀ u a B y f, KPair_d M u a B → Rd_entry_d u y e → M.mem f B → Ee_value_d j a f y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hZ⟩ := system.codes
  have models := system.components
  have component a c (hac : Rd_entry_d a c Z) := ee_component_l hZF source hV hδ h hY hc hL hS hSY hF (models a c hac)
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
    exact ee_pull_l hZF source hV hδ h hY hc hL hm hn hq haY hbY hnb hqa hfX pull hfy (any v b H z g hv hvz hg)
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
theorem ee_factor_l (hZF : M.Models ZF) {ω δ X A Y B j κ k K R L S F J O Z D p T V q C W : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k)
    (hL : M.MemberSubset L k) (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S)
    (hSY : M.MemberSubset S Y) (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z D p T V)
    (limit : Di_limit_d D p T V q C W) : Ee_factor_d hZF j Y q C W := by
  obtain ⟨e, he, es, comm, fiber, any⟩ := ee_nodes_l hZF source hV hδ h hY hc hL hS hSY hF system
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

/-! ## 每个支撑序数都有真实的坐标代表

先在 Vδ 中构造坐标函数，再把单点支撑送入既有全系统。因此长度以下的
每个序数确实属于原因子之像，无须预设目标已经包含这些极限元素。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ee_coordinate_l (hZF : M.Models ZF) {ω δ X A Y B j κ k L n D a i α : M.Domain}
    (hω : M.IsOmega ω) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.MemberSubset L k)
    (hn : M.mem n ω) (hD : Ep_space_d κ n D) (haY : M.mem a Y) (ha : Fn0_d n L a)
    (hi : Rd_entry_d i α a) : ∃ f, M.mem f X ∧ Fn0_d D X f ∧ Ee_value_d j a f α := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := v_transitive_l I hV
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  have hωκ := ed_critical_omega_l I hZF hω h ht hY hc
  have hnκ := hc.ordinal.transitive ω hωκ n hn
  have hDX := ZF.v_function_space_mem_l I hZF hV hδ hc.source (hc.ordinal.transitive n hnκ)
    (fun s => (hD s).trans ⟨fn0_function_l (ZF.modelsKP hZF), fn0_of_function_l (ZF.modelsKP hZF)⟩)
  let ρ : Env M 1 := ⟨fun _ => i, fun _ => i⟩
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 2) .newest (.bound 1) }
  have sat s x : φ.denote ρ s x ↔ Rd_entry_d i x s := rd_entry0_sat_l hZF.1 ..
  obtain ⟨f, hf, fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := κ)
    (fun s hs => (((hD s).mp hs).2.1 i (ha.bound_l hi).1).imp fun x hx => (sat s x).mpr hx.2)
    (fun s hs x y hx hy => (fn0_function_l (ZF.modelsKP hZF) ((hD s).mp hs)).1.2 i x y
      ((sat s x).mp hx) ((sat s y).mp hy))
    (fun s x hs hx => (((hD s).mp hs).bound_l ((sat s x).mp hx)).2)
  obtain ⟨Z, hZX, hDZ, hκZ⟩ := v_joint_bound_l I hV hDX hc.source
  have hfX : M.mem f X := v_relation_mem_l I hV hδ hZX (fun p hp => by
    obtain ⟨s, x, hpx⟩ := hf.1.1 p hp
    exact ⟨s, hDZ s (hf.input_mem_of_pairMember ⟨p, hpx, hp⟩), x,
      hκZ x (hf.output_mem_of_pairMember ⟨p, hpx, hp⟩), hpx⟩)
  obtain ⟨D', _, hjD⟩ := hj.2.2 D hDX
  obtain ⟨f', _, hjf⟩ := hj.2.2 f hfX
  let ψ : Formula 1 4 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 3)
    (.iff (rd_entry0_m (.bound 1) .newest (.bound 3)) (rd_entry0_m (.bound 2) .newest (.bound 1))))
  have tr := spred_delta_l I hZF hω h ht hY ψ (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))
    ⟨Fin.cases i (Fin.cases f (Fin.cases κ (fun _ => D))), fun _ => D⟩
    ⟨Fin.cases i (Fin.cases f' (Fin.cases k (fun _ => D'))), fun _ => D'⟩
    (Fin.cases (hc.fixed i (hc.ordinal.transitive n hnκ i (ha.bound_l hi).1))
      (Fin.cases hjf (Fin.cases hc.image (fun _ => hjD))))
  simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1] at tr
  have read := tr.mp (fun s hs x _ => (fs s x).trans
    ((and_congr_right fun _ => sat s x).trans ⟨And.right, fun hx => ⟨hs, hx⟩⟩))
  have haD := es_seed_l I hZF hω h ht hY (hc.fixed n hnκ) hc.image hjD hD hL haY ha
  exact ⟨f, hfX, (fn0_of_function_l (ZF.modelsKP hZF) hf).mono_target_l (ht κ hc.source),
    f', hjf, (read a haD α (hL α (ha.bound_l hi).2)).mpr hi⟩

theorem ee_ordinal_node_l (hZF : M.Models ZF) {ω δ X A Y B j κ k L S F R J O Z D p T V q C W α : M.Domain}
    (hω : M.IsOmega ω) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) (hδ : M.IsLimitOrdinal δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP hZF)) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP hZF)) X j κ k) (hL : M.MemberSubset L k)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hSY : M.MemberSubset S Y)
    (hF : Es_family_d (kp_pair_l (ZF.modelsKP hZF)) j κ L S F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
    (hα : M.mem α L) : ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u α := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨one, ⟨zero, hz, hs⟩, h1ω⟩ := hω.exists_ordinalOne_mem
  obtain ⟨a, ha, as⟩ := ZF.exists_constantFunction hZF I (source := one) hα
  have singleton i (hi : M.mem i one) : i = zero := ((hs i).mp hi).elim
    (fun he => (hz i he).elim) (hZF.1.eq_of_same_members i zero)
  have haJ := (system.indices a).mpr ⟨one, h1ω, fn0_of_function_l (ZF.modelsKP hZF) ha,
    fun i r x hi hr => (singleton i (ha.input_mem_of_pairMember hi)).trans (singleton r (ha.input_mem_of_pairMember hr)).symm⟩
  obtain ⟨_, hZ⟩ := system.codes
  have models := system.components
  obtain ⟨c, _, hac⟩ := hZ.2.1 a haJ
  obtain ⟨n, H, U, G, r, E, Q, hn, han, hH, haU, hG, model⟩ := models a c hac
  have eq := han.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) ha)
  subst n
  obtain ⟨f, hfX, hf, value⟩ := ee_coordinate_l hZF hω hV hδ h hY hc hL hn hH
    (hSY a ((hS a).mpr ⟨one, hn, ha⟩)) han ((as zero α).mpr ⟨hs.predecessor_mem, rfl⟩)
  obtain ⟨E₀, hE₀, hfE⟩ := model.map.projection.2.2 f ((hG f).mpr ⟨hfX, hf⟩)
  have ultra := (es_measures_l hZF hω hV hδ h hY hc hL hS hSY hF).at_l hZF.1 haU han hH
  obtain ⟨u, hu⟩ := I.total a E₀
  have huD := (system.nodes u).mpr ⟨a, E₀, hu, c, E, Q, hac, model.code.1, hE₀⟩
  obtain ⟨E₁, hE₁, huE₁⟩ := limit.projection.2.1 u huD
  exact ⟨E₁, u, hE₁, huE₁, a, E₀, f, hu, model.map.representative_l I ultra.1.base_l hfE, value⟩

end YesMetaZFC.SetTheory.LargeCardinal
