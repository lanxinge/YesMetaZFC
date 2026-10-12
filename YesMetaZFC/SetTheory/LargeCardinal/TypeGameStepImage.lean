import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRenewal
import YesMetaZFC.SetTheory.LargeCardinal.TypeOneStepImage
import YesMetaZFC.Model.SetTheory.Internal.TypeDropEmbedding

/-! # 每轮回答在同一实际超幂中的规则 (7)

先由原游戏的不可分辨点与完整节点生成回答和扩展器，再施加该扩展器。
dcp 与像交换、子类型查询更换定义域均已证明，故输出实际像 u 的完整回答。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_low_d.step_l {ω e δ S ν κ k l n α A c R r B U D P u v b a z χ s t g : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (heω : M.mem e ω)
    (hd : Woodin_d I δ) (low : Tg_low_d hZF ω e δ S ν) (root : M.mem e S)
    (hκδ : M.mem κ δ) (succ : M.SuccessorOf n l)
    (height : M.SuccessorOf α ν) (hA : V_d I α A) (model : Smem_d I c A R)
    (type : Tt_realized_d I ω c A R n r δ U P u)
    (language : Ee_language_d hZF ω κ l B U D q) (drop : Td_dcp_d I l n D u v)
    (elastic : Ee_elastic_d q v) (first : Rd_entry_d e S r) (last : Rd_entry_d l ν r)
    (set : Sg_set_d I e l r g) (node : Tg_node_d I k S s t g)
    (prog : Ts_program_d hZF ω l b σ a z) (hχ : M.mem χ δ) :
    ∃ τ C V Q w η Z d H, ∃ q' : Ee_queries_d M, ∃ p : Tg_reply_queries_d M,
    ∃ X K T L F c₀ d₀ Y T' j κ' U' D' u',
      M.mem χ τ ∧ M.mem κ τ ∧ M.mem τ δ ∧ Tg_height_d ν η ∧ V_d I η Z ∧ Smem_d I d Z H ∧
      Ee_language_d hZF ω τ n C V Q q' ∧ Tt_realized_d I ω d Z H n r δ V Q w ∧ Ee_elastic_d q' w ∧
      Tg_reply_language_d hZF ω e l n τ C V Q p ∧
      V_d I δ X ∧ Ep_source_d hZF ω κ K X T ∧ M.mem L δ ∧ M.mem κ L ∧ M.mem τ L ∧
      It_local_d ω X κ L F ∧ Sc_inaccessible_d ω X L ∧ Ex_strength_d hZF ω κ L X F ∧
      Smem_d I c₀ X T ∧ Smem_d I d₀ Y T' ∧ It_ultra_d hZF ω κ L F c₀ d₀ j ∧
      Wd_crit_d I X j κ κ' ∧ M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
      Rd_entry_d U U' j ∧ Rd_entry_d D D' j ∧ Rd_entry_d u u' j ∧ Tt_pool_d I ω l U' D' ∧
      Tg_reply_d I ω l n κ' τ U' D' Q u' w b σ z p := by
  obtain ⟨τ, C, V, Q, w, η, Z, d, H, q', p, hχτ, hκτ, hτδ, level, hZ, mdl, lang, real, el,
    target, qr, qb, qh, _, step⟩ := low.renew_l hZFC hω he heω hd root hκδ succ height hA model type language
      drop elastic first last set node prog hχ
  have woodin := hd
  obtain ⟨_, _, _, _, regular, _⟩ := woodin
  obtain ⟨r₀, v₀, _, drop₀, prefixType⟩ := type.dcp_l hZF hω succ language.pool
  have eq := drop₀.unique_l I hZF.1 drop
  subst v₀
  obtain ⟨X, K, T, L, F, c₀, d₀, Y, T', j, κ', U', D', v', hX, source, hLδ, hκL, hτL, loc, inacc, strength,
    mx, my, ultra, critical, bound, κlimit, hU, hD, hv, pool, subtype⟩ :=
    step.image_l hZF hω regular.isLimitOrdinal prog language hA model prefixType lang.limit type.finite
  have hj := ultra.elementary_l hZF mx.1 my.1
  have hY := ultra.transitive_l hZF my.1
  have theory := source.theory.map_l I hZF hω source.transitive hY mx my hj
  have hUX := hj.1.1.input_mem_of_pairMember hU
  have hPX := type.pool.rank_mem_l hZF hω hX regular.isLimitOrdinal source.omega_mem type.finite hUX
  have huX := ZF.v_subset_mem_l I hZF hX hPX (fun x hx => ((type.truth x).mp hx).1)
  obtain ⟨u', _, hu⟩ := hj.1.1.2.2 u huX
  have fixed := hj.natural_l hZF hω source.transitive hY mx my source.omega_mem
  have drop' := (hj.type_dcp_l hZF hω source.transitive hY mx my source.theory.algebra.pair theory.algebra.pair
    (fixed l prog.finite) (fixed n type.finite) hD hu hv).mp drop
  exact ⟨τ, C, V, Q, w, η, Z, d, H, q', p, X, K, T, L, F, c₀, d₀, Y, T', j, κ', U', D', u',
    hχτ, hκτ, hτδ, level, hZ, mdl, lang, real, el, target, hX, source, hLδ, hκL, hτL,
    loc, inacc, strength, mx, my, ultra, critical, bound, κlimit, hU, hD, hu, pool,
    ⟨fun x hx => ((real.truth x).mp hx).1, v', drop', subtype, qr, qb, qh⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
