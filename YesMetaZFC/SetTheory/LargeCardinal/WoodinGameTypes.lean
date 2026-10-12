import YesMetaZFC.SetTheory.LargeCardinal.WoodinTypes
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameElastic
import YesMetaZFC.Model.SetTheory.Internal.TypeGameMax

/-! # 武丁基数实际产生弹性 dcp 的游戏类型

在任意给定内部有限历史后添加实现高度；完整新类型的 dcp 字面等于
武丁工厂产生的弹性类型。参数域仍可超过任意给定下界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem woodin_game_type_l (hZFC : M.Models ZFC) {δ η : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hη : M.IsOrdinal η) (hδη : M.mem δ η) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω Z μ Y c R, M.IsOmega ω ∧ V_d I η Z ∧ M.SuccessorOf μ η ∧ V_d I μ Y ∧ Smem_d I c Y R ∧
      ∀ l s, M.mem l ω → Fn0_d l Z s → ∀ χ, M.mem χ δ →
        ∃ n κ B U D P r t v p, ∃ q : Ee_queries_d M,
          M.SuccessorOf n l ∧ M.mem χ κ ∧ M.mem κ δ ∧ Ee_language_d hZF ω κ l B U D q ∧
          Tt_realized_d I ω c Y R n r δ U P t ∧ Td_dcp_d I l n D t v ∧ Ee_elastic_d q v ∧
          Tg_elastic_d I l n D q t ∧
          (∀ i x, M.mem i l → (Rd_entry_d i x r ↔ Rd_entry_d i x s)) ∧ Rd_entry_d l η r ∧
          Tg_max_query_d I ω l n U P p ∧ M.mem p t := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, X, Z, μ, Y, b, H, c, R, hω, _, hZ, hμ, hY, _, model, all⟩ := woodin_elastic_l hZFC hd hη hδη
  refine ⟨ω, Z, μ, Y, c, R, hω, hZ, hμ, hY, model, fun l s hl fs χ hχ => ?_⟩
  obtain ⟨κ, K, S, B, U, D, q, w, v, above, hk, _, _, language, _, prefixType, _, elastic⟩ := all l s hl fs χ hχ
  obtain ⟨n, hn, _⟩ := hω.1.2 l hl
  obtain ⟨P, pool⟩ := tt_pool_exists_l I hZF hω n U
  obtain ⟨r, t, type, drop, kept, last⟩ := prefixType.append_l hZF hω hn
    (ZF.v_ordinal_mem_l I hZF hY hμ.predecessor_mem) pool
  obtain ⟨p, code⟩ := tt_max_query_l hZF hω hn.predecessor_mem pool
  exact ⟨n, κ, B, U, D, P, r, t, v, p, q, hn, above, hk, language, type, drop, elastic,
    ⟨v, drop, elastic⟩, kept, last, code, (code.2 μ Y c R r δ t η hY model type last).mpr hμ⟩

end YesMetaZFC.SetTheory.LargeCardinal
