import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystemSyntax

/-! # 全部有限支撑分量及映射的集合装配

类都是源函数集合的子集，因此整个带标号并有统一的幂集界。源模型图、标签图、
过渡图与分量关系一次实际生成，索引包含全部内部有限单射支撑。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_graphs_l (hZFC : M.Models ZFC) {ω κ K L X R F : M.Domain}
    (h : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (hωL : M.MemberSubset ω L) : ∃ J O Z A p T S, Ep_graph_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X R F J O Z A p T S := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨J, O, hj, ho, os⟩ := ei_order_l hZF h.omega hωL
  obtain ⟨Z, Q, hz, models⟩ := ep_components_l hZF h hF (fun a ha => ((hj a).mp ha).elim fun n hn => ⟨n, hn.1, hn.2.1⟩) R
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF X
  have bound a B (hat : Ep_at_d Z a B) : M.mem a J ∧ M.mem B P := by
    obtain ⟨c, C, S, hac, hc, hm, hB⟩ := ep_at_model_l hZF models hat
    obtain ⟨_, _, _, _, reps⟩ := ep_representatives_l I hZF.1 hF hc hm hB
    exact ⟨(hz.bound_l hac).1, (hP B).mpr (fun f hf => (reps f hf).1)⟩
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
  exact ⟨J, O, Z, A, p, T, S, ho, os, fn0_of_function_l (ZF.modelsKP hZF) hp, hj,
    ⟨Q, hz, models⟩, node, index, arrows, relations⟩

end YesMetaZFC.SetTheory.LargeCardinal
