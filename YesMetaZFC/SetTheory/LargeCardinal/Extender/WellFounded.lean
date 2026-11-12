import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative
import YesMetaZFC.SetTheory.CountableChoice
import YesMetaZFC.SetTheory.Fiber

/-! # 极限边的共同有限支撑约束

把任意两个已选源代表之间的极限边，变成一个实际测度一集合上的统一点态
关系；共同纤维的解释与两个坐标投影交换，因此不会更换下降链的代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ee_constraint_d (κ L X R a f b g c E : M.Domain) : Prop := ∃ m n l q r f' g',
  Fn0_d m l q ∧ Fn0_d n l r ∧ Fn0_d l L c ∧ Cp0_d m l L q c a ∧ Cp0_d n l L r c b ∧
  Ep_pull_d κ X m l q f f' ∧ Ep_pull_d κ X n l r g g' ∧
    ∀ s, M.mem s E → Rp_atom_d I false X R f' g' s

def ee_constraint_m {d} (κ L X R a f b g c E : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+7) := x.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (fn0_m (.bound 6) (.bound 4) (.bound 3)) (.conj (fn0_m (.bound 5) (.bound 4) (.bound 2))
      (.conj (fn0_m (.bound 4) (w L) (w c)) (.conj (cp0_m (.bound 6) (.bound 4) (w L) (.bound 3) (w c) (w a))
        (.conj (cp0_m (.bound 5) (.bound 4) (w L) (.bound 2) (w c) (w b))
          (.conj (ep_pull_m (w κ) (w X) (.bound 6) (.bound 4) (.bound 3) (w f) (.bound 1))
            (.conj (ep_pull_m (w κ) (w X) (.bound 5) (.bound 4) (.bound 2) (w g) .newest)
              (Formula.forallMem (w E) (rp_atom_m (𝒞 := kpair_convention_l) false (w X).weaken (w R).weaken
                (.bound 2) (.bound 1) .newest)))))))))))))))
derive_free_closed ee_constraint_m

theorem ee_constraint_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L X R a f b g c E : Term d) :
    Formula.satisfies ρ (ee_constraint_m κ L X R a f b g c E) ↔
      Ee_constraint_d I (κ.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (a.eval ρ) (f.eval ρ)
        (b.eval ρ) (g.eval ρ) (c.eval ρ) (E.eval ρ) := by
  simp only [ee_constraint_m, Ee_constraint_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, cp0_sat_l hE, ep_pull_sat_l hE, Formula.satisfies_forallMem_iff,
    rp_atom_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ee_common_edge_l (hZF : M.Models ZF) {ω κ L X R F J O Z A p T S u v a b B C f g c w z : M.Domain}
    (hF : Em_source_d ω κ L X F) (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (hu : KPair_d M u a B) (hv : KPair_d M v b C) (hf : M.mem f B) (hg : M.mem g C)
    (hwc : Rd_entry_d w c p) (hzc : Rd_entry_d z c p) (huw : Rd_entry_d u w T)
    (hvz : Rd_entry_d v z T) (hwz : Rd_entry_d w z S) : ∃ E U, Rd_entry_d c U F ∧ M.mem E U ∧
      Ee_constraint_d (kp_pair_l (ZF.modelsKP hZF)) κ L X R a f b g c E := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hz⟩ := h.codes
  have models := h.components
  obtain ⟨D, hw, hatD⟩ := h.toEp_graph_d.label_l hwc
  obtain ⟨E, he, hatE⟩ := h.toEp_graph_d.label_l hzc
  obtain ⟨m, l, q, f', _, hl, hq, hlc, hqa, hf', hff'⟩ := h.representatives u w a c B D hu hw huw f hf
  obtain ⟨n, l', r, g', _, _, hr, hlc', hrb, hg', hgg'⟩ := h.representatives v z b c C E hv he hvz g hg
  have el := hlc'.domain_eq_l hZF.1 hlc
  subst l'
  obtain ⟨d, Y, V, hcd, hcM, hm, hDY⟩ := ep_at_model_l hZF models hatD
  have hEY := (ep_at_read_l hz hcd hm.1).mp hatE
  have rel := (ep_rel_read_l hz hcd hm.1).mp (((h.toEp_graph_d.relation_l hw he).mp hwz).2.2)
  obtain ⟨U, hcU⟩ := hF.total l c hl hlc
  obtain ⟨H, hHU, point⟩ := (ep_relation_l I hZF.1 hF hcM hm hDY hEY hf' hg' hcU).mp rel
  exact ⟨H, U, hcU, hHU, m, n, l, q, r, f', g', hq, hr, hlc, hqa, hrb, hff', hgg', point⟩

theorem Ee_constraint_d.realize_l (hKP : M.Models KP) {ω κ L X R a f b g c E H K s : M.Domain}
    (hh : Fn0_d ω L H) (hk : Fn0_d ω κ K) (he : Ee_constraint_d I κ L X R a f b g c E)
    (hs : M.mem s E) (eval : Ec_eval_d ω κ L H K c s) : ∃ r t x y,
      Ec_eval_d ω κ L H K a r ∧ Ec_eval_d ω κ L H K b t ∧
      Rd_entry_d r x f ∧ Rd_entry_d t y g ∧ M.PairMember I x y R := by
  obtain ⟨m, n, l, q, p, f', g', hq, hp, hc, hqa, hpb, hf, hg, point⟩ := he
  obtain ⟨l', u, _, hu, hsfn⟩ := eval
  have el := hu.1.domain_eq_l hKP.1 hc
  subst l'
  obtain ⟨r, hr⟩ := cp0_exists_l hKP hq hsfn.1
  obtain ⟨t, ht⟩ := cp0_exists_l hKP hp hsfn.1
  obtain ⟨x, _, y, _, hsx, hsy, hxy⟩ := point s hs
  have ev : Ec_eval_d ω κ L H K c s := ⟨l, u, ‹Fn0_d l ω u›, hu, hsfn⟩
  exact ⟨r, t, x, y, ec_eval_comp_l hKP hh hk hc hq hqa hr ev, ec_eval_comp_l hKP hh hk hc hp hpb ht ev,
    (hf.2.2 s r hsfn.1 hr x).mp hsx, (hg.2.2 s t hsfn.1 ht y).mp hsy, hxy⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 极限下降链及其点态约束的原公式

代表选择、测度一集合和最后的求值图都用下列真实公式收集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ee_hit_d (κ L X R a f b g c s : M.Domain) : Prop :=
  ∃ E, M.mem s E ∧ Ee_constraint_d I κ L X R a f b g c E
def ee_hit_m {d} (κ L X R a f b g c s : Term d) : Formula 1 d := .existsE (.conj (.mem s.weaken .newest)
  (ee_constraint_m κ.weaken L.weaken X.weaken R.weaken a.weaken f.weaken b.weaken g.weaken c.weaken .newest))
derive_free_closed ee_hit_m
theorem ee_hit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L X R a f b g c s : Term d) :
    Formula.satisfies ρ (ee_hit_m κ L X R a f b g c s) ↔
      Ee_hit_d I (κ.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (a.eval ρ) (f.eval ρ) (b.eval ρ) (g.eval ρ) (c.eval ρ) (s.eval ρ) := by
  simp only [ee_hit_m, Ee_hit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, ee_constraint_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ee_hit_length_l (hE : Extensional M) {κ L X R a f b g c s n : M.Domain}
    (hc : Fn0_d n L c) (hh : Ee_hit_d I κ L X R a f b g c s) : Fn0_d n κ s := by
  obtain ⟨E, hs, m, k, l, q, r, f', g', _, _, hlc, _, _, hf, _, point⟩ := hh
  have en := hlc.domain_eq_l hE hc
  subst l
  obtain ⟨D, hD, hff⟩ := hf.2.1
  obtain ⟨x, _, _, _, hsx, _⟩ := point s hs
  exact (hD s).mp (hff.bound_l hsx).1

def Ee_rep_d (H i a f : M.Domain) : Prop := ∃ u B, Rd_entry_d i u H ∧ KPair_d M u a B ∧ M.mem f B
def ee_rep_m {d} (H i a f : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (rd_entry_m i.weaken.weaken (.bound 1) H.weaken.weaken)
    (.conj (kpair_m (.bound 1) a.weaken.weaken .newest) (.mem f.weaken.weaken .newest))))
derive_free_closed ee_rep_m
theorem ee_rep_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H i a f : Term d) :
    Formula.satisfies ρ (ee_rep_m H i a f) ↔ Ee_rep_d (H.eval ρ) (i.eval ρ) (a.eval ρ) (f.eval ρ) := by
  simp only [ee_rep_m, Ee_rep_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, kpair_sat_l M hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

def Ee_row_d (H G i a f : M.Domain) : Prop := Rd_entry_d i f G ∧ Ee_rep_d H i a f
def ee_row_m {d} (H G i a f : Term d) : Formula 1 d := .conj (rd_entry_m i f G) (ee_rep_m H i a f)
derive_free_closed ee_row_m
theorem ee_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H G i a f : Term d) :
    Formula.satisfies ρ (ee_row_m H G i a f) ↔ Ee_row_d (H.eval ρ) (G.eval ρ) (i.eval ρ) (a.eval ρ) (f.eval ρ) := by
  simp only [ee_row_m, Ee_row_d, Formula.satisfies_conj_iff, rd_entry_sat_l hE, ee_rep_sat_l hE]

theorem ee_row_unique_l {ω A X H G i a b f g : M.Domain} (hH : Fn0_d ω A H) (hG : Fn0_d ω X G)
    (hf : Ee_row_d H G i a f) (hg : Ee_row_d H G i b g) : a = b ∧ f = g := by
  obtain ⟨hif, u, B, hiu, hu, _⟩ := hf
  obtain ⟨hig, v, C, hiv, hv, _⟩ := hg
  have e := hH.2.2 i (hH.bound_l hiu).1 v (hH.bound_l hiv).2 u (hH.bound_l hiu).2 hiv hiu
  exact ⟨(kpair_injective_l M hu (e ▸ hv)).1,
    hG.2.2 i (hG.bound_l hif).1 f (hG.bound_l hif).2 g (hG.bound_l hig).2 hif hig⟩

def Ee_test_d (κ L X R H G A i s : M.Domain) : Prop := ∃ m a b f g c, M.SuccessorOf m i ∧
  Ee_row_d H G i a f ∧ Ee_row_d H G m b g ∧ Rd_entry_d i c A ∧ Ee_hit_d I κ L X R b g a f c s
def ee_test_m {d} (κ L X R H G A i s : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+6) := x.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (Formula.isSuccessor (.bound 5) (w i))
    (.conj (ee_row_m (w H) (w G) (w i) (.bound 4) (.bound 2))
      (.conj (ee_row_m (w H) (w G) (.bound 5) (.bound 3) (.bound 1))
        (.conj (rd_entry_m (w i) .newest (w A))
          (ee_hit_m (w κ) (w L) (w X) (w R) (.bound 3) (.bound 1) (.bound 4) (.bound 2) .newest (w s)))))))))))
derive_free_closed ee_test_m
theorem ee_test_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L X R H G A i s : Term d) :
    Formula.satisfies ρ (ee_test_m κ L X R H G A i s) ↔
      Ee_test_d I (κ.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (H.eval ρ) (G.eval ρ) (A.eval ρ) (i.eval ρ) (s.eval ρ) := by
  simp only [ee_test_m, Ee_test_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, ee_row_sat_l hE, rd_entry_sat_l hE, ee_hit_sat_l I hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同纤维证明整个有限支撑极限良基

DC 给出指标递增的下降链和一张源代表图。每步的精确点态真值集合由分离
统一收集；共同纤维同时实现所有约束，最终值图在原源关系中严格下降。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_limit_wf_l (hZF : M.Models ZF) {ω κ L X R F J O Z A p T S q C V : M.Domain}
    (hω : M.IsOmega ω) (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω) (hωL : M.MemberSubset ω L)
    (hF : Em_family_d ω κ L F) (coherent : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (complete : ∀ H f, Ef_levels_d ω κ H → Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f → ∃ g, Ef_fiber_d ω κ H g)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C V)
    (wf : Wf_rel_d X R) : Wf_rel_d C V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have h := system.toEp_graph_d
  obtain ⟨Q, hz⟩ := h.codes
  have models := h.components
  apply di_wf_of_no_step_l hZF hDC system.diagram limit
  intro H hH step
  -- 固定指标递增的下降节点链 H；DC 在每个类中选出源代表，组成实际函数图 G。
  have rep i a f (hr : Ee_rep_d H i a f) : M.mem f X ∧ ∃ n, M.mem n ω ∧ Fn0_d n L a ∧ Ep_fun_d κ X n f := by
    obtain ⟨u, B, hiu, hu, hf⟩ := hr
    obtain ⟨c, D, W, _, hc, hm, hBD⟩ := ep_at_model_l hZF models (h.at_l (hH.bound_l hiu).2 hu)
    obtain ⟨n, hn, ha, _, funcs⟩ := ep_representatives_l I hZF.1 (hF.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X) hc hm hBD
    exact ⟨(funcs f hf).1, n, hn, ha, (funcs f hf).2⟩
  let choose : BinarySchema 1 := { body := .existsE (ee_rep_m (.bound 3) (.bound 2) .newest (.bound 1)) }
  have cs i f : choose.denote ⟨fun _ => H, fun _ => H⟩ i f ↔ ∃ a, Ee_rep_d H i a f := by
    simp only [choose, BinarySchema.denote, Formula.satisfies_exists_iff, ee_rep_sat_l hZF.1]; rfl
  obtain ⟨G, hG, gs⟩ := dc_uniformize_formula_l hZF choose ⟨fun _ => H, fun _ => H⟩ hω hDC (X := X) (fun i hi => by
    obtain ⟨u, huA, hiu⟩ := hH.2.1 i hi
    obtain ⟨a, B, hu, hat⟩ := (h.nodes u).mp huA
    obtain ⟨c, D, W, _, hc, hm, hBD⟩ := ep_at_model_l hZF models hat
    obtain ⟨_, _, _, ⟨f, hf⟩, funcs⟩ := ep_representatives_l I hZF.1 (hF.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X) hc hm hBD
    exact ⟨f, (funcs f hf).1, (cs i f).mpr ⟨a, u, B, hiu, hu, hf⟩⟩)
  have rows i (hi : M.mem i ω) : ∃ a f, Ee_row_d H G i a f := by
    obtain ⟨f, _, hif⟩ := hG.2.1 i hi
    obtain ⟨a, ha⟩ := (cs i f).mp (gs i f hif)
    exact ⟨a, f, hif, ha⟩
  -- N(i) 记录下一节点的支撑；它同时容纳本步下降的两个代表。
  let next : BinarySchema 2 := { body := .existsE (.existsE (.conj (Formula.isSuccessor (.bound 1) (.bound 3))
    (.conj (rd_entry_m (.bound 1) .newest (.bound 5)) (rd_entry_m .newest (.bound 2) (.bound 4))))) }
  let ρ : Env M 2 := (⟨fun _ => H, fun _ => H⟩ : Env M 1).push p
  have ns i a : next.denote ρ i a ↔ ∃ m u, M.SuccessorOf m i ∧ Rd_entry_d m u H ∧ Rd_entry_d u a p := by
    simp only [next, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_isSuccessor_iff, rd_entry_sat_l hZF.1]; rfl
  obtain ⟨N, hn, nn⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I next ρ (source := ω) (target := J)
    (fun i hi => by
      obtain ⟨m, hmi, hmω⟩ := hω.1.2 i hi
      obtain ⟨u, huA, hmu⟩ := hH.2.1 m hmω
      obtain ⟨a, _, hua⟩ := h.projection.2.1 u huA
      exact ⟨a, (ns i a).mpr ⟨m, u, hmi, hmu, hua⟩⟩)
    (fun i _ a b ha hb => by
      obtain ⟨m, u, hmi, hmu, hua⟩ := (ns i a).mp ha
      obtain ⟨m', v, hm'i, hmv, hvb⟩ := (ns i b).mp hb
      have em := Structure.SuccessorOf.eq hZF.1 hm'i hmi
      subst m'
      have eu := (fn0_function_l (ZF.modelsKP hZF) hH).1.2 m v u hmv hmu
      exact (fn0_function_l (ZF.modelsKP hZF) h.projection).1.2 u a b hua (eu ▸ hvb))
    (fun i a _ ha => ((ns i a).mp ha).elim fun _ hh => hh.elim fun _ ht => (h.projection.bound_l ht.2.2).2)
  obtain ⟨L₀, hL₀⟩ := ZF.fseq_space_exists_l I hZF hω L
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  have hN := fn0_of_function_l (ZF.modelsKP hZF) hn
  have hNL := hN.mono_target_l (fun a ha => (hL₀ a).mpr (((h.indices a).mp ha).elim
    fun n hh => ⟨n, hh.1, fn0_function_l (ZF.modelsKP hZF) hh.2.1⟩))
  let η := ((((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push L).push X).push R).push H).push G).push N
  let test : BinarySchema 7 := {
    body := ee_test_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have tests i s : test.denote η i s ↔ Ee_test_d I κ L X R H G N i s := ee_test_sat_l I hZF.1 _ _ _ _ _ _ _ _ _ _
  -- 分离并收集精确真值集 B(i)，由公共后继分量的关系证书证明 B(i) 属于对应测度。
  obtain ⟨P, _, B, hb, bs⟩ := ZF.fiber_function_l I hZF test η ω K
  have sets i E (hiE : Rd_entry_d i E B) s : M.mem s E ↔ M.mem s K ∧ Ee_test_d I κ L X R H G N i s :=
    (((bs i E).mp hiE).2 s).trans (and_congr_right fun _ => tests i s)
  have large i c E U (hic : Rd_entry_d i c N) (hiE : Rd_entry_d i E B) (hcU : Rd_entry_d c U F) : M.mem E U := by
    obtain ⟨hi, ht⟩ := (nn i c).mp hic
    obtain ⟨m, v, hmi, hmv, hvc⟩ := (ns i c).mp ht
    obtain ⟨a, f, hif, u, C₀, hiu, hu, hf⟩ := rows i hi
    obtain ⟨b, g, hmg, v', C₁, hmv', hv, hg⟩ := rows m (hH.bound_l hmv).1
    have ev := (fn0_function_l (ZF.modelsKP hZF) hH).1.2 m v' v hmv' hmv
    subst v'
    obtain ⟨c', w, hvc', hwc, huw, hvw⟩ := step i m u v hmi hiu hmv
    have ec := (fn0_function_l (ZF.modelsKP hZF) h.projection).1.2 v c' c hvc' hvc
    subst c'
    obtain ⟨E₀, U', hcU', hE₀, constraint⟩ := ee_common_edge_l hZF (hF.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X) system hv hu hg hf hvc hwc
      (system.diagram.identity v (hH.bound_l hmv).2) huw hvw
    have eu := hF.function c U' U hcU' hcU
    subst U'
    obtain ⟨n, D, hnω, hnc, hD, hU⟩ := hF.measure c U hcU
    apply hU.1.2.2.1 E₀ E hE₀
    · intro s hs
      exact (sets i E hiE s).mpr ⟨(hK s).mpr ⟨n, hnω, fn0_function_l (ZF.modelsKP hZF)
        ((hD s).mp (hU.1.1 E₀ hE₀ s hs))⟩,
        m, a, b, f, g, c, hmi, ⟨hif, u, C₀, hiu, hu, hf⟩, ⟨hmg, v, C₁, hmv, hv, hg⟩, hic, E₀, hs, constraint⟩
    · intro s hs
      obtain ⟨_, _, _, _, _, c', _, _, _, hic', hit⟩ := ((sets i E hiE s).mp hs).2
      have ec := hn.1.2 i c' c hic' hic
      exact (hD s).mpr (ee_hit_length_l I hZF.1 hnc (ec ▸ hit))
  obtain ⟨e, t, he, ht, cover, meet⟩ := es_joint_fiber_l hZF hω hωL hF coherent complete hL₀ hNL
    (fn0_of_function_l (ZF.modelsKP hZF) hb) large
  -- 同一个共同纤维解释全部支撑。坐标投影保证解释唯一，替代因而给出值图 Y。
  have covered i a f (row : Ee_row_d H G i a f) j x (hjx : Rd_entry_d j x a) : ∃ k, Rd_entry_d k x e := by
    obtain ⟨_, u, C₀, hiu, hu, _⟩ := row
    have hi := (hH.bound_l hiu).1
    obtain ⟨m, hmi, hmω⟩ := hω.1.2 i hi
    obtain ⟨v, _, hmv⟩ := hH.2.1 m hmω
    obtain ⟨c, w, hvc, hwc, huw, _⟩ := step i m u v hmi hiu hmv
    have hic := (nn i c).mpr ⟨hi, (ns i c).mpr ⟨m, v, hmi, hmv, hvc⟩⟩
    obtain ⟨D, hw, _⟩ := h.label_l hwc
    obtain ⟨l, n, r, _, _, _, _, hr, hnc, hra, _⟩ := ((h.arrow_l hu hw).mp huw).2.2
    obtain ⟨k, _, hjk⟩ := hr.2.1 j (hra.1.bound_l hjx).1
    exact cover i c k x hic ((hra.value_l hr hnc hjk).mp hjx)
  let δ := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push κ).push L).push e).push t).push H).push G
  let value : BinarySchema 7 := { body := .existsE (.existsE (.existsE (.conj
    (ee_row_m (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 1)) (.conj
      (ec_eval_m (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 2) .newest)
      (rd_entry_m .newest (.bound 3) (.bound 1)))))) }
  have vs i x : value.denote δ i x ↔ ∃ a f r, Ee_row_d H G i a f ∧ Ec_eval_d ω κ L e t a r ∧ Rd_entry_d r x f := by
    simp only [value, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      ee_row_sat_l hZF.1, ec_eval_sat_l hZF.1, rd_entry_sat_l hZF.1]; rfl
  obtain ⟨Y, hy, ys⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I value δ (source := ω) (target := X)
    (fun i hi => by
      obtain ⟨a, f, row⟩ := rows i hi
      obtain ⟨_, n, _, ha, D, hD, hf⟩ := rep i a f row.2
      obtain ⟨r, er⟩ := ec_eval_exists_l hZF ha he ht (covered i a f row)
      obtain ⟨x, _, hrx⟩ := hf.2.1 r ((hD r).mpr (ec_eval_type_l hZF.1 ha er))
      exact ⟨x, (vs i x).mpr ⟨a, f, r, row, er, hrx⟩⟩)
    (fun i _ x y hx hy => by
      obtain ⟨a, f, r, row, er, hrx⟩ := (vs i x).mp hx
      obtain ⟨b, g, s, row', es, hsy⟩ := (vs i y).mp hy
      obtain ⟨rfl, rfl⟩ := ee_row_unique_l hH hG row row'
      have e := ec_eval_unique_l hZF.1 he.2 ht es er
      subst s
      obtain ⟨_, _, _, _, D, _, hf⟩ := rep i a f row.2
      exact (fn0_function_l (ZF.modelsKP hZF) hf).1.2 r x y hrx hsy)
    (fun i x _ hx => by
      obtain ⟨a, f, r, row, _, hrx⟩ := (vs i x).mp hx
      obtain ⟨_, _, _, _, D, _, hf⟩ := rep i a f row.2
      exact (hf.bound_l hrx).2)
  apply wf_no_desc_l hZF hω wf (fn0_of_function_l (ZF.modelsKP hZF) hy)
  -- 每个 B(i) 在共同纤维上成立，所以 Y 的每个后继值都严格下降，矛盾。
  intro i m x y hmi hix hmy
  have hi := hy.input_mem_of_pairMember hix
  obtain ⟨c, _, hic⟩ := hn.2.2 i hi
  obtain ⟨E, _, hiE⟩ := hb.2.2 i hi
  obtain ⟨s, hs, es⟩ := meet i c E hic hiE
  obtain ⟨m', a, b, f, g, c', hmi', ra, rb, hic', hit⟩ := ((sets i E hiE s).mp hs).2
  have ec := hn.1.2 i c' c hic' hic
  subst c'
  have em := Structure.SuccessorOf.eq hZF.1 hmi' hmi
  subst m'
  obtain ⟨E', hs', constraint⟩ := hit
  obtain ⟨r, u, y', x', eb, ea, hry, hux, hr⟩ := constraint.realize_l I (ZF.modelsKP hZF)
    (fn0_of_function_l (ZF.modelsKP hZF) he.1) ht hs' es
  have ex := hy.1.2 i x' x ((ys i x').mpr ⟨hi, (vs i x').mpr ⟨a, f, u, ra, ea, hux⟩⟩) hix
  have ey := hy.1.2 m y' y ((ys m y').mpr ⟨hy.input_mem_of_pairMember hmy, (vs m y').mpr ⟨b, g, r, rb, eb, hry⟩⟩) hmy
  exact ex ▸ ey ▸ hr

end YesMetaZFC.SetTheory.LargeCardinal
