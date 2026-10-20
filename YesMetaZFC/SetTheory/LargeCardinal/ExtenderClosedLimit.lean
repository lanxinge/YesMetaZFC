import YesMetaZFC.SetTheory.LargeCardinal.ExtenderClosedFiber
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderDescentSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceLimit

/-! # 有界可数闭所属模型的跨模型施加良基性

对上升支撑下降链逐步选取真实测度一证书。所属源的有界 ω 闭性回收整列证书，
原内部共同纤维实现全部下降边；无需所属模型包含于施加模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

theorem It_local_d.closed_wf_l {ω κ K Y R' L F V X R J O Z A p T S q C W : M.Domain}
    (owner : Ep_source_d hZF ω κ K Y R') (closed : Sc_bounded_omega_closed_d ω Y)
    (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω) (agree : Ea_agree_d ω κ X Y)
    (hV : M.mem V Y) (power : FilterZF.Source_d Y K V) (loc : It_local_d ω Y κ L F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (wf : Wf_rel_d X R) : Wf_rel_d C W := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have reverse : Ea_agree_d ω κ Y X := fun n D E hn hd sub => (agree n D E hn hd sub).symm
  have owned := loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory owner.finite hV power)
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
    have hEV := (power E).mpr ⟨hEY, fun s hs => (owner.finite s).mpr
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
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (owner : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y S) (closed : Sc_bounded_omega_closed_d ω Y)
    (agree : Ea_agree_d ω κ X Y) (hV : M.mem V Y) (power : FilterZF.Source_d Y K' V)
    (loc : It_local_d ω Y κ L F) : Ep_limit_d (ZFC.models_zf_l hZFC) ω κ L X R F := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have reverse : Ea_agree_d ω κ Y X := fun n D E hn hd sub => (agree n D E hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory owner.finite hV power)).transfer_l reverse
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
