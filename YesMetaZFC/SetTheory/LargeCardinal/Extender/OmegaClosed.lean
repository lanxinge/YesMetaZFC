import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.SetTheory.CumulativeRelativeClosure
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceJointFiber
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.SetTheory.LargeCardinal.Extender.WellFounded
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceLimit
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceSubsets
import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraSupport
import YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthAgreement
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankEnumeration
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankSegment
import YesMetaZFC.SetTheory.LargeCardinal.Extender.ValueApply
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.Model.SetTheory.Relations.OmegaEvaluation

/-! # 可数支撑列属于所属源的严格秩段

源内支撑覆盖列的正则界同时界住每个有限坐标。两个有界关系构造依次
回收支撑列的值域和整张图，所需共尾性仅为源内部的 ω 界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ec_support_rank_l {ω κ K Y R L V S A : M.Domain}
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Y R) (hL : M.mem L Y) (limit : M.IsLimitOrdinal L)
    (hωL : M.mem ω L) (bound : Sc_omega_bound_d ω Y L) (hV : M.mem V Y) (rank : Vr_d Y L V)
    (hA : M.mem A Y) (seq : Fseq_space_d I ω L S) (fa : Fn0_d ω S A) : M.mem A V := by
  obtain ⟨e, he, fe, cover⟩ := ec_source_cover_l hZF owner hL (limit.1.transitive ω hωL) hA seq fa
  obtain ⟨β, hβ, bounded⟩ := bound e he (fn0_of_function_l (ZF.modelsKP hZF) fe.1)
  obtain ⟨c, code⟩ := owner.code
  obtain ⟨B, hB, values⟩ := sc_range_source_l hZF owner.omega owner.transitive code owner.theory hA
  have hωV := rank.ordinal_subset_l hZF owner.transitive hV ω hωL
  have hβV := rank.ordinal_subset_l hZF owner.transitive hV β hβ
  have hBV := rank.relations_mem_l owner.transitive hV limit hωV hβV hB (fun a ha p hp => by
    obtain ⟨i, hia⟩ := (values a).mp ha
    obtain ⟨n, hn, fn⟩ := (seq a).mp (fa.bound_l hia).2
    obtain ⟨j, hj, x, _, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) fn).1 p hp
    obtain ⟨k, hk⟩ := cover i a j x hia ⟨p, pair, hp⟩
    exact ⟨j, owner.omega.transitive (ZF.modelsKP hZF) n hn j hj, x, bounded k x hk, pair⟩)
  exact rank.relation_mem_l owner.transitive hV limit hωV hBV hA (fun p hp => by
    obtain ⟨i, hi, a, _, pair⟩ := fa.1 p hp
    exact ⟨i, hi, a, (values a).mpr ⟨i, p, pair, hp⟩, pair⟩)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有界可数闭所属模型实现背景中的全部可数测度约束

所有有限支撑属于所属源，所有测度一集合也由测度图回收。
有界值域的 ω 闭性使两列参数同时属于该源，原内部共同纤维公式遂可直接使用。
这里不要求所属模型包含于另一个施加模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem es_closed_joint_fiber_l {ω κ K Y R L F V S P A B : M.Domain}
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Y R) (closed : Sc_bounded_omega_closed_d I ω Y R)
    (loc : It_local_d I ω Y R κ L F) (hV : M.mem V Y) (power : FilterZF.Source_d Y K V)
    (seq : Fseq_space_d I ω L S) (fa : Fn0_d ω S A) (fb : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U) :
    ∃ f g, M.mem f Y ∧ M.mem g Y ∧ M.IsSetInjectionFromTo I f ω L ∧ Fn0_d ω κ g ∧
      (∀ i a j x, Rd_entry_d i a A → Rd_entry_d j x a → ∃ n, Rd_entry_d n x f) ∧
      ∀ i a E, Rd_entry_d i a A → Rd_entry_d i E B → ∃ r, M.mem r E ∧ Ec_eval_d ω κ L f g a r := by
  obtain ⟨c, model⟩ := owner.code
  have close := (sc_bounded_omega_closed_mem_l (ZF.modelsKP hZF) owner.omega owner.transitive model owner.omega_mem).mp closed
  have family := loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hV power)
  have coherent := loc.coherent_l hZF (owner.read_source_l hZF) owner.code
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code
  have local_copy := loc
  obtain ⟨hw, hk, hl, hf, pre⟩ := (it_local_mem_l I owner.code).mp local_copy
  have countable := (Formula.satisfies_conj_iff _ _ _).mp pre |>.2
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω L := fun x hx => ord.2.transitive κ pre.1.2.2.2.2.1 x (owner.below x hx)
  obtain ⟨S', hs, seq'⟩ := (owner.sequences_l (ZF.modelsKP hZF)).1 L hl
  have eq := hZF.1.eq_of_same_members S' S (fun a => (seq' a).trans (seq a).symm)
  have hS := eq ▸ hs
  have hA := close S hS A fa
  have values i E (hiE : Rd_entry_d i E B) : M.mem E V := by
    obtain ⟨a, ha, hia⟩ := fa.2.1 i (fb.bound_l hiE).1
    obtain ⟨n, hn, fn⟩ := (seq a).mp ha
    obtain ⟨U, hu⟩ := family.total n a hn (fn0_of_function_l (ZF.modelsKP hZF) fn)
    have hEU := large i a E U hia hiE hu
    have hU := (rd_entry_transitive_l owner.transitive hf hu).2
    obtain ⟨m, D, hm, _, space, ultra⟩ := family.measure a U hu
    exact (power E).mpr ⟨owner.transitive U hU E hEU, fun s hs => ((owner.finite_l (ZF.modelsKP hZF)) s).mpr
      ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) ((space s).mp (ultra.base.bounds E hEU s hs))⟩⟩
  have fbV := fb.retarget_l values
  have hB := close V hV B fbV
  obtain ⟨f, hfy, ff, covered⟩ := ec_source_cover_l hZF owner hl below hA seq fa
  obtain ⟨H, hH, levels, fiber, read⟩ := ec_source_levels_l hZF owner family coherent hl hV hA hB hfy seq fa fbV large ff
  obtain ⟨g, hgy, hg⟩ := ex_owned_fiber_l hZF owner.transitive (owner.algebra_l (ZF.modelsKP hZF)) hw hk hl hf countable hH hfy levels fiber
  exact ⟨f, g, hfy, hgy, ff, hg.1, covered, ec_levels_realize_l hZF owner.omega seq fa ff covered hg read⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有界可数闭所属模型的跨模型施加良基性

对上升支撑下降链逐步选取真实测度一证书。所属源的有界 ω 闭性回收整列证书，
原内部共同纤维实现全部下降边；无需所属模型包含于施加模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem It_local_d.closed_wf_l {ω κ K Y R' L F V X R J O Z A p T S q C W : M.Domain}
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Y R') (closed : Sc_bounded_omega_closed_d (kp_pair_l (ZF.modelsKP hZF)) ω Y R')
    (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω) (agree : Ea_agree_d ω κ X Y)
    (hV : M.mem V Y) (power : FilterZF.Source_d Y K V) (loc : It_local_d (kp_pair_l (ZF.modelsKP hZF)) ω Y R' κ L F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (wf : Wf_rel_d X R) : Wf_rel_d C W := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have reverse : Ea_agree_d ω κ Y X := fun n D E hn hd sub => (agree n D E hn hd sub).symm
  have owned := loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hV power)
  have hF := owned.transfer_l reverse
  have hω := owner.omega
  have local_copy := loc
  obtain ⟨_, _, _, hF_mem, _⟩ := local_copy
  have h := system.toEp_graph_d
  obtain ⟨Q, hz⟩ := h.codes
  have models := h.components
  apply di_wf_of_no_step_l hZF hDC system.diagram limit
  intro H hH step
  -- 固定指标递增的下降节点链 H；DC 在每个类中选出源代表，组成实际函数图 G。
  have rep i a f (hr : Ee_rep_d H i a f) : M.mem f X ∧ ∃ n, M.mem n ω ∧ Fn0_d n L a ∧ Ep_fun_d κ X n f := by
    obtain ⟨u, B, hiu, hu, hf⟩ := hr
    obtain ⟨c, D, W, _, hc, hm, hBD⟩ := ep_at_model_l hZF models (h.at_l (hH.bound_l hiu).2 hu)
    obtain ⟨n, hn, ha, _, funcs⟩ := ep_representatives_l I hZF.1 hF hc hm hBD
    exact ⟨(funcs f hf).1, n, hn, ha, (funcs f hf).2⟩
  let choose : BinarySchema 1 := { body := .existsE (ee_rep_m (.bound 3) (.bound 2) .newest (.bound 1)) }
  have cs i f : choose.denote ⟨fun _ => H, fun _ => H⟩ i f ↔ ∃ a, Ee_rep_d H i a f := by
    simp only [choose, BinarySchema.denote, Formula.satisfies_exists_iff, ee_rep_sat_l hZF.1]; rfl
  obtain ⟨G, hG, gs⟩ := dc_uniformize_formula_l hZF choose ⟨fun _ => H, fun _ => H⟩ hω hDC (X := X) (fun i hi => by
    obtain ⟨u, huA, hiu⟩ := hH.2.1 i hi
    obtain ⟨a, B, hu, hat⟩ := (h.nodes u).mp huA
    obtain ⟨c, D, W, _, hc, hm, hBD⟩ := ep_at_model_l hZF models hat
    obtain ⟨_, _, _, ⟨f, hf⟩, funcs⟩ := ep_representatives_l I hZF.1 hF hc hm hBD
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
  have hN := fn0_of_function_l (ZF.modelsKP hZF) hn
  have hNL := hN.mono_target_l (fun a ha => (hL₀ a).mpr (((h.indices a).mp ha).elim
    fun n hh => ⟨n, hh.1, fn0_function_l (ZF.modelsKP hZF) hh.2.1⟩))
  -- 每条边直接选取所属测度中的见证集，避免把背景分离集误认为源内集合。
  let η := (((((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push L).push X).push R).push H).push G).push N).push F
  let test : BinarySchema 8 := { body := .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
      (.conj (Formula.isSuccessor (.bound 6) (.bound 8))
        (.conj (ee_row_m (.bound 12) (.bound 11) (.bound 8) (.bound 5) (.bound 3))
          (.conj (ee_row_m (.bound 12) (.bound 11) (.bound 6) (.bound 4) (.bound 2))
            (.conj (rd_entry_m (.bound 8) (.bound 1) (.bound 10))
              (.conj (rd_entry_m (.bound 1) .newest (.bound 9))
                (.conj (.mem (.bound 7) .newest)
                  (ee_constraint_m (.bound 16) (.bound 15) (.bound 14) (.bound 13)
                    (.bound 4) (.bound 2) (.bound 5) (.bound 3) (.bound 1) (.bound 7)))))))))))))) }
  have tests i E : test.denote η i E ↔ ∃ m a b f g c U, M.SuccessorOf m i ∧
      Ee_row_d H G i a f ∧ Ee_row_d H G m b g ∧ Rd_entry_d i c N ∧ Rd_entry_d c U F ∧
        M.mem E U ∧ Ee_constraint_d I κ L X R b g a f c E := by
    simp only [test, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_isSuccessor_iff, ee_row_sat_l hZF.1, rd_entry_sat_l hZF.1,
      Formula.satisfies_mem_iff, ee_constraint_sat_l I hZF.1]; rfl
  obtain ⟨B, hb, bs⟩ := dc_uniformize_formula_l hZF test η hω hDC (X := V) (fun i hi => by
    obtain ⟨c, _, hic⟩ := hN.2.1 i hi
    obtain ⟨_, hc⟩ := (nn i c).mp hic
    obtain ⟨m, v, hmi, hmv, hvc⟩ := (ns i c).mp hc
    obtain ⟨a, f, hif, u, C₀, hiu, hu, hf⟩ := rows i hi
    obtain ⟨b, g, hmg, v', C₁, hmv', hv, hg⟩ := rows m (hH.bound_l hmv).1
    have ev := (fn0_function_l (ZF.modelsKP hZF) hH).1.2 m v' v hmv' hmv
    subst v'
    obtain ⟨c', w, hvc', hwc, huw, hvw⟩ := step i m u v hmi hiu hmv
    have ec := (fn0_function_l (ZF.modelsKP hZF) h.projection).1.2 v c' c hvc' hvc
    subst c'
    obtain ⟨E, U, hcU, hE, constraint⟩ := ee_common_edge_l hZF hF system hv hu hg hf hvc hwc
      (system.diagram.identity v (hH.bound_l hmv).2) huw hvw
    obtain ⟨n, D, hnω, _, space, ultra⟩ := owned.measure c U hcU
    have hEY := owner.transitive U (rd_entry_transitive_l owner.transitive hF_mem hcU).2 E hE
    have hEV := (power E).mpr ⟨hEY, fun s hs => ((owner.finite_l (ZF.modelsKP hZF)) s).mpr
      ⟨n, hnω, fn0_function_l (ZF.modelsKP hZF) ((space s).mp (ultra.base.bounds E hE s hs))⟩⟩
    exact ⟨E, hEV, (tests i E).mpr
      ⟨m, a, b, f, g, c, U, hmi, ⟨hif, u, C₀, hiu, hu, hf⟩, ⟨hmg, v, C₁, hmv, hv, hg⟩, hic, hcU, hE, constraint⟩⟩)
  have large i c E U (hic : Rd_entry_d i c N) (hiE : Rd_entry_d i E B) (hcU : Rd_entry_d c U F) : M.mem E U := by
    obtain ⟨_, _, _, _, _, c', U', _, _, _, hic', hcU', hE, _⟩ := (tests i E).mp (bs i E hiE)
    have ec := hn.1.2 i c' c hic' hic
    subst c'
    exact owned.function c U' U hcU' hcU ▸ hE
  obtain ⟨e, t, _, _, he, ht, cover, meet⟩ := es_closed_joint_fiber_l hZF owner closed loc hV power hL₀ hNL hb large
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
  obtain ⟨E, _, hiE⟩ := hb.2.1 i hi
  obtain ⟨s, hs, es⟩ := meet i c E hic hiE
  obtain ⟨m', a, b, f, g, c', _, hmi', ra, rb, hic', _, _, constraint⟩ := (tests i E).mp (bs i E hiE)
  have ec := hn.1.2 i c' c hic' hic
  subst c'
  have em := Structure.SuccessorOf.eq hZF.1 hmi' hmi
  subst m'
  obtain ⟨r, u, y', x', eb, ea, hry, hux, hr⟩ := constraint.realize_l I (ZF.modelsKP hZF)
    (fn0_of_function_l (ZF.modelsKP hZF) he.1) ht hs es
  have ex := hy.1.2 i x' x ((ys i x').mpr ⟨hi, (vs i x').mpr ⟨a, f, u, ra, ea, hux⟩⟩) hix
  have ey := hy.1.2 m y' y ((ys m y').mpr ⟨hy.input_mem_of_pairMember hmy, (vs m y').mpr ⟨b, g, r, rb, eb, hry⟩⟩) hmy
  exact ex ▸ ey ▸ hr

/-- 所属源的有界 ω 闭性直接生成同一扩展器的实际良基超幂。 -/
theorem It_local_d.closed_limit_l (hZFC : M.Models ZFC) {ω κ K X R K' Y S L F V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K X R)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K' Y S) (closed : Sc_bounded_omega_closed_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω Y S)
    (agree : Ea_agree_d ω κ X Y) (hV : M.mem V Y) (power : FilterZF.Source_d Y K' V)
    (loc : It_local_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω Y S κ L F) : Ep_limit_d (ZFC.models_zf_l hZFC) ω κ L X R F := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have reverse : Ea_agree_d ω κ Y X := fun n D E hn hd sub => (agree n D E hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hV power)).transfer_l reverse
  obtain ⟨J, O, Z, A, p, T, U, q, c, C, W, system, limit, model, elementary⟩ :=
    loc.apply_l hZFC source owner hV power reverse
  have wf : Wf_rel_d X R := by
    obtain ⟨_, code⟩ := source.code
    intro B _ nonempty
    obtain ⟨x, hx, least⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) nonempty
    exact ⟨x, hx, fun y hy hyx => least y hy (((code.2 y x).mp hyx).2.2)⟩
  have wf' := loc.closed_wf_l hZF owner closed (ZFC.dc_l I hZFC source.omega) agree hV power system limit wf
  exact ⟨J, O, Z, A, p, T, U, q, c, C, W, system, limit, model, wf', elementary,
    ep_collapse_l hZF source family system limit model elementary wf'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 指定跨源超幂与所属模型的共同强度秩段

所属模型自身超幂读取原强度证书。两次施加在支撑上的一致性与源内迹回收
将该覆盖送到指定后继，再由实际小秩层枚举识别整个共同秩段。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.strength_agree_l {ω κ K X R K' Y S Kₙ L F N V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω L Kₙ N V)
    (agree : Ea_agree_d ω κ X Y) (branches : Sc_branch_d ω Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (loc : It_local_d I ω Y S κ L F) (next : Ep_successor_d hZF ω κ L X R F N V)
    (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y F) :
    Es_strength_d Y L N ∧ ∃ K₀, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω L K₀ Y S ∧ ∀ μ, M.mem μ L → Ea_agree_d ω μ Y N := by
  obtain ⟨_, b, d, N', V', j, K₀, hm, hn, ultra, base, hLN, hLN', common, back⟩ :=
    loc.return_l hZFC source owner agree branches power cover next
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code
  have copy := loc
  obtain ⟨_, _, hLY, _, pre⟩ := (it_local_mem_l I owner.code).mp copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hωL := ord.2.transitive κ pre.1.2.2.2.2.1 ω pre.1.2.2.1
  have below := ord.2.transitive ω hωL
  obtain ⟨P, hP, ps⟩ := power K' owner.finite.mem_l
  have family := loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hP ps)
  have hj := ultra.elementary_l hZF hm.1 hn.1
  obtain ⟨Γ, _, hκΓ⟩ := hj.1.1.2.2 κ owner.cardinal_mem
  have bound := ultra.support_l hZF owner family (loc.coherent_l hZF (owner.read_source_l hZF) owner.code) (loc.atoms_l hZF (owner.read_source_l hZF) owner.code)
    (loc.normal_l hZF (owner.read_source_l hZF) owner.code) ord.1 ord.2 hm hn hκΓ
  have value := strength.realize_l hZF owner family hm hn ultra ord.1.transitive hκΓ bound
  obtain ⟨KY, sy⟩ := owner.rebase_l hLY below
    (sc_ordinal_small_l hZF owner.omega owner.transitive hm owner.theory hLY ord.2)
  obtain ⟨KN, sn⟩ := base.rebase_l hLN' below
    (sc_ordinal_small_l hZF base.omega base.transitive hn base.theory hLN' ord.2)
  have same := value.agree_l hZF sy sn ord.2 hωL back
  have strength : Es_strength_d Y L N := by
    refine ⟨fun α hα x hx sub => ?_, ?_⟩
    · have reverse : Ea_subset_d ω L N' N := fun n D A hn hd sub => (common n D A hn hd sub).mpr
      exact reverse.set_l hZF sn target (value.1 α hα x hx sub) (fun y hy => ord.2.transitive α hα y (sub y hy))
    · obtain ⟨x, hx, sub, missing⟩ := value.2
      exact ⟨x, hx, sub, fun hxN => missing (common.subset_l.set_l hZF target sn hxN sub)⟩
  exact ⟨strength, KY, sy, fun μ hμ n D A hn hd sub =>
    (same μ hμ n D A hn hd sub).trans
      ((common.mono_l hZF (ord.2.transitive μ hμ)) n D A hn hd sub).symm⟩

theorem It_local_d.rank_agree_l {ω κ K X R K' Y S Kₙ N V L F : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω L Kₙ N V)
    (agree : Ea_agree_d ω κ X Y) (branches : Sc_branch_d ω Y) (power : Sc_power_d Y) (cover : Sc_cover_d Y)
    (hierarchy : Sc_hierarchy_d N) (np : Sc_power_d N)
    (sizes : Sc_rank_size_d I Y L) (limit : M.IsLimitOrdinal L)
    (loc : It_local_d I ω Y S κ L F) (next : Ep_successor_d hZF ω κ L X R F N V)
    (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y F) : ∃ W,
      M.mem W Y ∧ Vr_d Y L W ∧ Er_level_d N L W ∧ Sc_rank_size_d I N L ∧ Es_strength_d Y L N ∧
      ∀ μ, M.mem μ L → Ea_agree_d ω μ Y N := by
  obtain ⟨es, K₀, ready, same⟩ := loc.strength_agree_l hZFC source owner target agree branches power cover next strength
  have copy := loc
  obtain ⟨_, _, _, _, pre⟩ := (it_local_mem_l I owner.code).mp copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hωL := limit.1.transitive κ pre.1.2.2.2.2.1 ω pre.1.2.2.1
  obtain ⟨W, f, hW, rank, _, _⟩ := sizes.level
  obtain ⟨W', hW', rank'⟩ := hierarchy L target.cardinal_mem limit.1
  have eq := ea_rank_agree_l hZF ready target limit hωL sizes same hW rank hW' rank'
  subst W'
  have sizes' := ea_rank_size_l hZF target np hierarchy owner.transitive limit hW' hW rank' rank sizes
  obtain ⟨B, f, hB, hb, hf, bij⟩ := sizes'.level
  have eq := hb.unique_l hZF target.transitive hB hW' rank'
  subst B
  obtain ⟨Q, hQ, _, iso⟩ := ep_transitive_code_l hZF target (rank'.transitive_l target.transitive hW') hf bij
  exact ⟨W, hW, rank, ⟨hW', rank', Q, f, hQ, hf, iso⟩, sizes', es, same⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## nice 后继保持背景可数闭性

可数目标序列选择成原代表列。源的闭性回收函数列，所属源的有界闭性与内部正则界
把支撑列放入两侧共同秩段。最后在目标内逐项计算 j(f)(a)，回收原序列本身。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_ultra_d.closed_l {ω κ K X R K' Y R' L F c d N S j : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y R')
    (agree : Ea_agree_d ω κ X Y) (closed : Sc_omega_closed_d I ω X R) (owner_closed : Sc_bounded_omega_closed_d I ω Y R')
    (hierarchy : Sc_hierarchy_d X) (power : Sc_power_d X) (op : Sc_power_d Y) (oc : Sc_cover_d Y)
    (bound : Sc_omega_bound_d ω Y L) (sizes : Sc_rank_size_d I Y L) (hL : M.IsLimitOrdinal L)
    (loc : It_local_d I ω Y R' κ L F) (strength : Ex_strength_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j) :
    Sc_omega_closed_d I ω N S := by
  have hN := ultra.transitive_l hZF hn.1
  obtain ⟨co, mo⟩ := owner.code
  have ownerClose := (sc_bounded_omega_closed_mem_l (ZF.modelsKP hZF) owner.omega owner.transitive mo owner.omega_mem).mp owner_closed
  obtain ⟨X₀, R₀, N₀, S₀, J, O, Z, D, p, T, V, q, b, C, W, i, e,
    mx, nx, system, limit, model, wc, bij, he, _, constants, hj, comp⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx.1 hn.1
  subst X₀ R₀ N₀ S₀
  obtain ⟨P, hP, subsets⟩ := op K' owner.finite.mem_l
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hP subsets)).transfer_l reverse
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF reverse
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code
  have local_copy := loc
  obtain ⟨_, _, hLY, _, pre⟩ := (it_local_mem_l I owner.code).mp local_copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hωL := hL.1.transitive κ pre.1.2.2.2.2.1 ω pre.1.2.2.1
  have below := hL.1.transitive ω hωL
  have fixed := (ep_seed_collapse_l hZF source ord.1.transitive hL.1.transitive family coherent
    (loc.atoms_l hZF (owner.read_source_l hZF) owner.code) ((loc.normal_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF owner source agree.subset_l)
    system limit wc (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  have hLN := ep_support_mem_l hZFC source family coherent system limit model hN hn he fixed ord.1 hL.1
  have hw := hj.omega_l I hZF source.omega source.transitive hN hm hn source.omega_mem
  obtain ⟨K₀, base⟩ := source.successor_l hZF hm hn hN hj (hj.1.1.output_mem_of_pairMember hw) (fun _ h => h)
    ((hj.small_l I hZF source.omega hm.1 hn.1 hw).mp (source.cardinal_small.mono_mem_l I hm source.omega_mem source.below))
  obtain ⟨K₁, target⟩ := base.rebase_l hLN below
    (sc_ordinal_small_l hZF source.omega hN hn base.theory hLN hL.1)
  have next : Ep_successor_d hZF ω κ L X R F N S :=
    ⟨J, O, Z, D, p, T, V, q, b, C, W, d, e, system, limit, model, hn, hN, wc, bij, he⟩
  obtain ⟨W₀, hWY, rank, level, _, _, _⟩ := loc.rank_agree_l hZFC source owner target agree
    (owner_closed.branch_l (ZF.modelsKP hZF) owner.omega owner.transitive mo owner.omega_mem) op oc
    ((sc_hierarchy_iff_l hZF source.omega source.transitive hN hm hn hj).mp hierarchy)
    ((sc_power_iff_l hZF source.omega source.transitive hN hm hn hj).mp power) sizes hL next strength
  -- 旧隶属实例直接调用原关系求值闭性；只在实际图处读取成员关系。
  obtain ⟨z₀, old, oldGraph⟩ := rr_layer_mem_l I hZF hm source.transitive source.omega_mem (source.omega.transitive (ZF.modelsKP hZF))
  obtain ⟨z₁, new, newGraph⟩ := rr_layer_mem_l I hZF hn hN target.omega_mem (source.omega.transitive (ZF.modelsKP hZF))
  have natural := hj.natural_l hZF source.omega source.transitive hN hm hn source.omega_mem
  have numeric n x (hnx : Rd_entry_d n x z₀) y : Rd_entry_d n y z₁ ↔ Rd_entry_d x y j := by
    obtain ⟨hnω, rfl⟩ := (oldGraph n x).mp hnx
    exact (newGraph n y).trans ⟨fun ⟨_, eq⟩ => eq ▸ natural n hnω,
      fun h => ⟨hnω, hj.1.1.1.2 n n y (natural n hnω) h⟩⟩
  have hJY := ep_indices_mem_l hZF owner hLY system.indices
  have hJN := ep_indices_mem_l hZF target hLN system.indices
  obtain ⟨u, fu, id⟩ := fn0_identity_l (ZF.modelsKP hZF) J
  have fu := fn0_function_l (ZF.modelsKP hZF) (fu.mono_target_l (hN J hJN))
  have inside b a (hba : Rd_entry_d b a u) : Rd_entry_d a J S := by
    obtain ⟨hb, rfl⟩ := (id b a).mp hba
    exact (hn.2 b J).mpr ⟨hN J hJN b hb, hJN, hb⟩
  have cover E (hE : M.mem E N) : ∃ a d f b F, M.mem a J ∧ Rf_fun_d I X R d f ∧
      Rd_entry_d a b u ∧ Rd_entry_d f F j ∧ Rf_val_d I N S b E F := by
    obtain ⟨H, hH, hHE⟩ := bij.2 E hE
    obtain ⟨n, a, D₀, f, hnω, haJ, _, space, hf, ff, rep⟩ := ep_repr_surjective_l hZF family system limit hH
    obtain ⟨F, hF, hfF⟩ := hj.1.1.2.2 f hf
    have value := ep_value_apply_l hZFC source family coherent system limit model hN hn he fixed constants comp hfF ⟨H, rep, hHE⟩
    exact ⟨a, D₀, f, a, F, haJ, (rf_fun_mem_l I hZF.1 source.transitive hm (source.space_mem_l hZF hnω space)).mpr
      (source.function_l hZF hf ff), (id a a).mpr ⟨haJ, rfl⟩, hfF, (rf_val_mem_l I hZF.1 hN hn hF).mpr value⟩
  obtain ⟨L₀, _, seq⟩ := (owner.sequences_l (ZF.modelsKP hZF)).1 L hLY
  have capture a (fa : Fn0_d ω N a) (boundJ : ∀ n x, Rd_entry_d n x a → Rd_entry_d x J S) :
      ∃ A, Rf_fun_d I N S ω A ∧ Rc_graph_d I N S z₁ A a := by
    have faJ := fa.retarget_l (fun n x hnx => ((hn.2 x J).mp (boundJ n x hnx)).2.2)
    have hA := ownerClose J hJY a faJ
    have fa' := faJ.mono_target_l (fun a ha => (seq a).mpr (((system.indices a).mp ha).elim
      fun n h => ⟨n, h.1, fn0_function_l (ZF.modelsKP hZF) h.2.1⟩))
    have hAW := ec_support_rank_l hZF owner hLY hL hωL bound hWY rank hA seq fa'
    have hAN := hN W₀ level.member a hAW
    refine ⟨a, (rf_fun_mem_l I hZF.1 hN hn target.omega_mem).mpr ⟨hAN, J, hJN, faJ⟩, ?_⟩
    intro n x y hnx
    obtain ⟨_, rfl⟩ := (newGraph n x).mp hnx
    exact (rf_val_mem_l I hZF.1 hN hn hAN).symm
  have uniform := target.collection.uniform_l I
    (target.cardinal_small.mono_mem_l I hn target.omega_mem target.below)
  exact closed.evaluation_l hZF source.omega (ZFC.dc_l I hZFC source.omega) hm.1 hn.1 hj
    (rf_ext_mem_l I hZF.1 source.transitive hm) old new hw numeric uniform fu inside cover capture

end YesMetaZFC.SetTheory.LargeCardinal
