import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyDescent
import YesMetaZFC.SetTheory.LargeCardinal.WoodinGameTypes
import YesMetaZFC.Model.SetTheory.Internal.SubtypeInsertion
import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeRank
import YesMetaZFC.Model.SetTheory.Internal.TypeExceeds

/-! # 泛型 I 方向的无界继续类型

反例分支给出下一枚真实标签。原树的严格秩界使所有标签留在 Vβ，武丁工厂
随即产生任意高参数域的弹性类型；交换末两位的实际排列证明它超过原回答。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem woodin_game_continue_l {ω δ e l n τ U D w η Y c R r S g β s t g' x χ : M.Domain}
    (hd : Woodin_d I δ) (hω : M.IsOmega ω) (hel : M.mem e l) (hn : M.SuccessorOf n l)
    (hτ : M.IsOrdinal τ) (hτχ : M.MemberSubset τ χ) (hχ : M.mem χ δ)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n r δ U D w)
    (rS : Rd_entry_d e S r) (last : Rd_entry_d l β r) (set : Sg_set_d I e l r g)
    (bound : Tg_bound_d I δ S β) (height : Tg_height_d β η)
    (node : Tg_node_d I l S s t g') (extend : ∀ a, M.mem a g' ↔ M.mem a g ∨ a = x) :
    ∃ μ A d H κ B V E P m r' u, ∃ q : Ee_queries_d M,
      M.SuccessorOf μ β ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.mem χ κ ∧ M.mem κ δ ∧
      Ee_language_d hZF ω κ n B V E q ∧ M.SuccessorOf m n ∧
      Tt_realized_d I ω d A H m r' δ V P u ∧ Tg_elastic_d I n m E q u ∧
      Rd_entry_d e S r' ∧ Rd_entry_d l x r' ∧ Rd_entry_d n β r' ∧ Sg_set_d I e n r' g' ∧
      Tx_exceeds_d hZF ω δ τ n U D w κ m V P u := by
  obtain ⟨Z, hZ, hS⟩ := bound.2.2
  obtain ⟨ω', Z', μ, A, d, H, hw, hZ', hμ, hA, lower, all⟩ := woodin_game_type_l hZFC hd bound.1 bound.2.1
  have eqω := hZF.1.eq_of_same_members ω' ω (fun i => ⟨hw.2 ω hω.1 i, hω.2 ω' hw.1 i⟩)
  subst ω'
  have eqZ := ZF.v_unique_l I hZF hZ' hZ
  subst Z'
  have labels := node.labels_rank_l hZF hZ hS
  obtain ⟨a, cut⟩ := ZF.exists_restriction hZF I r l
  have fa := cut.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) type.tuple)
    (fun i hi => (hn i).mpr (Or.inl hi))
  have small : M.IsSetFunctionFromTo I a l Z := ⟨fa.1, fa.2.1, fun i hi => by
    obtain ⟨y, _, iy⟩ := fa.2.2 i hi
    have ry := ((cut.2 i y).mp iy).2
    refine ⟨y, ?_, iy⟩
    by_cases eq : i = e
    · exact ((fn0_function_l (ZF.modelsKP hZF) type.tuple).1.2 e y S (eq ▸ ry) rS).symm ▸ hS
    · exact labels y ((extend y).mpr (Or.inl ((set y).mpr ⟨i, hi, eq, ry⟩)))⟩
  have on := hω.members_areOrdinals hZF n type.finite
  obtain ⟨b, fb, kept, bx⟩ := tt_column_append_l hZF (on.mem hn.predecessor_mem) hn small
    (labels x ((extend x).mpr (Or.inr rfl)))
  obtain ⟨m, κ, B, V, E, P, r', u, v, p, q, hm, above, hk, language, full, _, _, elastic, keep, rb, _, _⟩ :=
    all n b type.finite (fn0_of_function_l (ZF.modelsKP hZF) fb) χ hχ
  have agree i y (hi : M.mem i l) : Rd_entry_d i y r ↔ Rd_entry_d i y r' :=
    (show Rd_entry_d i y r ↔ Rd_entry_d i y a from
      ⟨fun h => (cut.2 i y).mpr ⟨hi, h⟩, fun h => ((cut.2 i y).mp h).2⟩).trans
      ((kept i y hi).symm.trans (keep i y (on.transitive l hn.predecessor_mem i hi)).symm)
  have rx := (keep l x hn.predecessor_mem).mpr bx
  have nextSet : Sg_set_d I e n r' g' := by
    intro y
    constructor
    · intro hy
      rcases (extend y).mp hy with hy | eq
      · obtain ⟨i, hi, ne, iy⟩ := (set y).mp hy
        exact ⟨i, on.transitive l hn.predecessor_mem i hi, ne, (agree i y hi).mp iy⟩
      · exact ⟨l, hn.predecessor_mem, fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) l (eq.symm ▸ hel), eq.symm ▸ rx⟩
    · rintro ⟨i, hi, ne, iy⟩
      apply (extend y).mpr
      rcases (hn i).mp hi with hi | eq
      · exact Or.inl ((set y).mpr ⟨i, hi, ne, (agree i y hi).mpr iy⟩)
      · exact Or.inr ((fn0_function_l (ZF.modelsKP hZF) full.tuple).1.2 l y x
          (hZF.1.eq_of_same_members i l eq ▸ iy) rx)
  obtain ⟨μ', γ, succ, mid, top⟩ := height
  have eqμ := succ.eq hZF.1 hμ
  subst μ'
  have hγ : M.mem γ η := top.predecessor_mem
  exact ⟨μ, A, d, H, κ, B, V, E, P, m, r', u, q, hμ, hA, lower, above, hk, language, hm, full, elastic,
    (agree e S hel).mp rS, rx, rb, nextSet,
    ordinal_down_l (ZF.modelsKP hZF) hτ language.limit.1 hτχ above,
    fun i hi => (hm i).mpr (Or.inl hi), η, Y, c, R, r, hY, model, type, μ, γ, mid, hγ,
    ts_at_insert_l hZF hω hn hm hA lower full
      ⟨(fn0_function_l (ZF.modelsKP hZF) type.tuple).1, (fn0_function_l (ZF.modelsKP hZF) type.tuple).2.1⟩
      agree last rx rb⟩

end YesMetaZFC.SetTheory.LargeCardinal
