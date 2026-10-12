import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReply

/-! # 在真实低层前缀后添加回答末位

给定原实现前缀确实属于低秩层，实际构造回答完整类型及原定义的子类型查询。
此构造选用恒等排列；规则和读取仍保留全部有限排列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_reply_append_l {ω κ τ e l n B C U V D P W b a z δ η Y c R r u s ν A S α : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M} {p : Tg_reply_queries_d M}
    (hω : M.IsOmega ω) (hn : M.SuccessorOf n l) (hτκ : M.mem τ κ)
    (prog : Ts_program_d hZF ω l b σ a z) (source : Ee_language_d hZF ω κ l B U D q)
    (target : Tg_reply_language_d hZF ω e l n τ C V W p)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n r δ U P u)
    (cut : M.IsRestrictionOf I s r l) (hA : V_d I ν A) (hνη : M.mem ν η)
    (fs : Fn0_d l A s) (constants : M.MemberSubset V A)
    (rS : Rd_entry_d e S s) (root : M.mem e S)
    (bound : Tg_bound_d I δ S α) (height : Tg_height_d α ν) :
    ∃ d H r' w, Smem_d I d A H ∧ Tt_realized_d I ω d A H n r' δ V W w ∧
      (∀ i x, M.mem i l → (Rd_entry_d i x r' ↔ Rd_entry_d i x s)) ∧ Rd_entry_d l α r' ∧
      Tg_reply_d I ω l n κ τ U D W u w b σ z p := by
  have hl := hω.transitive hZF n type.finite l hn.predecessor_mem
  have hαA : M.mem α A := by
    obtain ⟨β, γ, hb, hg, last⟩ := height
    exact ZF.v_ordinal_mem_l I hZF hA
      ((v_ordinal_l I hA).transitive γ last.predecessor_mem α
        (((v_ordinal_l I hA).mem last.predecessor_mem).transitive β hg.predecessor_mem α hb.predecessor_mem))
  have point := ZF.v_transitive_l I hZF hA α hαA δ bound.2.1
  obtain ⟨d, H, lower⟩ := smdl_membership_l I hZF ⟨δ, point⟩
  obtain ⟨D₀, pool₀⟩ := tt_pool_exists_l I hZF hω l V
  obtain ⟨v₀, truth₀, _⟩ := tt_truth_exists_l I hZF ω d l s δ D₀
  have prefixType : Tt_realized_d I ω d A H l s δ V D₀ v₀ := ⟨lower.1, hl, fs, point, constants, pool₀, truth₀⟩
  obtain ⟨r', w, full, _, kept, last⟩ := prefixType.append_l hZF hω hn hαA target.pool
  obtain ⟨s', v, cut', drop, prefixSource⟩ := type.dcp_l hZF hω hn source.pool
  have eqs := Structure.IsSetRelation.eq_of_pairMember_iff (𝕀 := I) hZF.1 cut'.1 cut.1
    (fun i x => (cut'.2 i x).trans (cut.2 i x).symm)
  subst s'
  obtain ⟨Z, d', H', r'', f, g, π, hZ, realized, type', ff, fg, graph, orig, bij, perm⟩ := ts_at_self_l hZF hω hA lower full
  have witness : Ts_at_d hZF ω δ l s n V W w ν :=
    ⟨Z, d', H', r'', f, g, π, hZ, realized, type', ff, fg, graph,
      fun i x hi => (kept i x hi).symm.trans (orig i x ((hn i).mpr (Or.inl hi))), bij, perm⟩
  have sub : M.MemberSubset w W := fun x hx => ((full.truth x).mp hx).1
  have subtype := (ts_subtype_realized_l hZF hω prog hY model prefixSource source.limit target.limit hτκ full.finite
    source.rank source.constants target.rank target.constants target.pool sub).mpr
      ⟨fun i hi => (hn i).mpr (Or.inl hi), ν, hνη, witness⟩
  have first := (kept e S (fs.bound_l rS).1).mpr rS
  exact ⟨d, H, r', w, lower, full, kept, last, sub, v, drop, subtype,
    (target.root.2 d A H r' δ w S lower (ZF.v_transitive_l I hZF hA) full first).mpr root,
    (target.bound.2 ν A d H r' δ w S α hA lower full first last).mpr bound,
    (target.height.2 ν A d H r' δ w α hA lower full last).mpr height⟩

end YesMetaZFC.SetTheory.LargeCardinal
