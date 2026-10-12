import YesMetaZFC.SetTheory.LargeCardinal.WoodinGameTypes
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReset

/-! # 无界参数域的实际弹性重置类型

用武丁无界弹性构造 dcp，再实际添加高度对象。完整节点、空根、
最大序数与 dcp 弹性同时成立，故重置构造已接入规则 (3)、(5)。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem woodin_game_reset_l (hZFC : M.Models ZFC) {δ η B S e : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hB : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) η B) (hδη : M.mem δ η)
    (hS : M.mem S B) (he : ∀ x, ¬ M.mem x e) (root : M.mem e S) :
    let hZF := ZFC.models_zf_l hZFC
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω l μ Y c R, M.IsOmega ω ∧ M.SuccessorOf l e ∧ M.SuccessorOf μ η ∧ V_d I μ Y ∧ Smem_d I c Y R ∧
      ∀ χ, M.mem χ δ → ∃ n κ C U D P r t p₀ p₁ p₂, ∃ q : Ee_queries_d M,
        M.SuccessorOf n l ∧ M.mem χ κ ∧ M.mem κ δ ∧ Ee_language_d hZF ω κ l C U D q ∧
        Tt_realized_d I ω c Y R n r δ U P t ∧ Tg_elastic_d I l n D q t ∧ Rd_entry_d e S r ∧ Rd_entry_d l η r ∧
        Tg_node_query_d I ω e n l U P e e e p₀ ∧ M.mem p₀ t ∧
        Tg_root_query_d I ω e n U P p₁ ∧ M.mem p₁ t ∧ Tg_max_query_d I ω l n U P p₂ ∧ M.mem p₂ t := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ω, Z, μ, Y, c, R, hω, hZ, hμ, hY, model, all⟩ := woodin_game_type_l hZFC hd (v_ordinal_l I hB) hδη
  have eqB := ZF.v_unique_l I hZF hB hZ
  subst Z
  obtain ⟨e', he', heω⟩ := hω.1.1
  have eqe := hZF.1.eq_of_same_members e' e (fun x => iff_of_false (he' x) (he x))
  subst e'
  obtain ⟨l, hl, hlω⟩ := hω.1.2 e heω
  have zero := tg_graph_empty_l I he
  have empty : M.IsSetFunctionFromTo I e e B := ⟨zero.1, zero.2, fun i hi => (he i hi).elim⟩
  obtain ⟨s, fs, _, first⟩ := tt_column_append_l hZF (hω.members_areOrdinals hZF e heω) hl empty hS
  refine ⟨ω, l, μ, Y, c, R, hω, hl, hμ, hY, model, fun χ hχ => ?_⟩
  obtain ⟨n, κ, C, U, D, P, r, t, v, p₂, q, hn, above, hk, language, type, _, _, elastic, kept, last, maxCode, maxTrue⟩ :=
    all l s hlω (fn0_of_function_l (ZF.modelsKP hZF) fs) χ hχ
  have first' := (kept e S hl.predecessor_mem).mpr first
  have heU := (tt_constants_finite_l hZF hω heω language.limit language.rank language.constants).2
  have hen := (hn e).mpr (Or.inl hl.predecessor_mem)
  obtain ⟨p₀, nodeCode⟩ := tt_node_query_l hZF hω type.finite hn.predecessor_mem hl.predecessor_mem type.pool heU heU heU
  obtain ⟨p₁, rootCode⟩ := tt_root_query_l hZF hω he hen type.pool
  have set : Sg_set_d I e l r e := by
    intro x
    refine iff_of_false (he x) ?_
    rintro ⟨i, hi, ne, _⟩
    exact ((hl i).mp hi).elim (he i) (fun eq => ne (hZF.1.eq_of_same_members i e eq))
  refine ⟨n, κ, C, U, D, P, r, t, p₀, p₁, p₂, q, hn, above, hk, language, type, elastic, first', last,
    nodeCode, ?_, rootCode, ?_, maxCode, maxTrue⟩
  · exact (nodeCode.2 c Y R r δ t S model (ZF.v_transitive_l I hZF hY) type first').mpr
      ⟨e, type.constants e heU, set, (tg_node_empty_l I hZF.1 he).mpr root⟩
  · exact (rootCode.2 c Y R r δ t S model (ZF.v_transitive_l I hZF hY) type first').mpr root

end YesMetaZFC.SetTheory.LargeCardinal
