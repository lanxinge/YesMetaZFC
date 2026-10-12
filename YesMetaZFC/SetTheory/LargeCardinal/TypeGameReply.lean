import YesMetaZFC.SetTheory.LargeCardinal.TypeGameElastic
import YesMetaZFC.Model.SetTheory.Internal.TypeGameBound
import YesMetaZFC.Model.SetTheory.Internal.TypeGameHeight
import YesMetaZFC.Model.SetTheory.Internal.TypeGameRoot
import YesMetaZFC.Model.SetTheory.Internal.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyBase

/-! # 规则 (7) 的完整类型约束及实际读取

回答类型是 dcp(u) 的原定义子类型查询所指定的子类型，并包含空根、严格秩界
及末位加二最大序数三条查询。语言工厂实际构造全部代码，读取时恢复真实低层实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_reply_queries_d (M : Structure.{u}) where
  root : M.Domain
  bound : M.Domain
  height : M.Domain

def Tg_reply_d (I : kpair_convention_l.Interpretation M) (ω l n κ τ U D W u w b : M.Domain)
    (σ : Fin 7 → M.Domain) (z : M.Domain) (q : Tg_reply_queries_d M) : Prop :=
  M.MemberSubset w W ∧ ∃ v, Td_dcp_d I l n D u v ∧ Ts_subtype_d ω l κ τ n U w b σ z v ∧
    M.mem q.root w ∧ M.mem q.bound w ∧ M.mem q.height w

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_reply_language_d (ω e l n τ B V W : M.Domain) (q : Tg_reply_queries_d M) : Prop where
  finite : M.mem n ω
  root_slot : M.mem e n
  last_slot : M.mem l n
  limit : M.IsLimitOrdinal τ
  rank : V_d I τ B
  constants : ∀ x, M.mem x V ↔ M.mem x B ∨ x = τ
  pool : Tt_pool_d I ω n V W
  root : Tg_root_query_d I ω e n V W q.root
  bound : Tg_bound_query_d I ω e l n V W q.bound
  height : Tg_height_query_d I ω l n V W q.height
  base : Tg_reply_base_d I ω e l n q.root q.bound q.height

theorem tg_reply_language_l {ω e l n τ : M.Domain} (hω : M.IsOmega ω)
    (he : ∀ x, ¬ M.mem x e) (hn : M.mem n ω) (hen : M.mem e n) (hl : M.mem l n) (hτ : M.IsLimitOrdinal τ) :
    ∃ B V W, ∃ q : Tg_reply_queries_d M, Tg_reply_language_d hZF ω e l n τ B V W q := by
  obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF hτ.1
  obtain ⟨a, ha⟩ := KP.exists_pair (ZF.modelsKP hZF) τ τ
  obtain ⟨V, hv⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B a
  have constants x : M.mem x V ↔ M.mem x B ∨ x = τ := (hv x).trans
    (or_congr Iff.rfl ((ha x).trans ⟨fun h => h.elim id id, Or.inl⟩))
  obtain ⟨W, pool⟩ := tt_pool_exists_l I hZF hω n V
  have hw := (tt_constants_finite_l hZF hω hn hτ hB constants).1
  obtain ⟨r, b, h, base⟩ := tg_reply_base_l hZF hω he hen hl
  obtain ⟨hr, hb, hh⟩ := base.scope_l I (ZF.modelsKP hZF) pool hw
  exact ⟨B, V, W, ⟨r, b, h⟩, hn, hen, hl, hτ, hB, constants, pool, hr, hb, hh, base⟩

/-- 不假设回答类型可实现；它的实现由原定义的子类型查询实际给出。 -/
theorem Tg_reply_d.read_l {ω κ τ e l n B C U V D P W u w b a z δ η Y c R r : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M} {p : Tg_reply_queries_d M}
    (hω : M.IsOmega ω) (prog : Ts_program_d hZF ω l b σ a z)
    (source : Ee_language_d hZF ω κ l B U D q) (target : Tg_reply_language_d hZF ω e l n τ C V W p)
    (hY : V_d I η Y) (model : Smem_d I c Y R) (type : Tt_realized_d I ω c Y R n r δ U P u)
    (reply : Tg_reply_d I ω l n κ τ U D W u w b σ z p) :
    ∃ s v ν A d H r' S α, M.IsRestrictionOf I s r l ∧ Td_dcp_d I l n D u v ∧
      Tt_realized_d I ω c Y R l s δ U D v ∧ M.mem ν η ∧ Ts_at_d hZF ω δ l s n V W w ν ∧
      V_d I ν A ∧ Smem_d I d A H ∧ Tt_realized_d I ω d A H n r' δ V W w ∧
      Rd_entry_d e S r' ∧ Rd_entry_d l α r' ∧ M.mem e S ∧ Tg_bound_d I δ S α ∧ Tg_height_d α ν := by
  obtain ⟨sub, v, drop, subtype, root, bound, height⟩ := reply
  obtain ⟨s, v', cut, drop', prefixType⟩ := type.dcp_l hZF hω drop.1 source.pool
  have eq := drop'.unique_l I hZF.1 drop
  subst v'
  obtain ⟨_, ν, hν, witness⟩ := (ts_subtype_realized_l hZF hω prog hY model prefixType source.limit target.limit subtype.1
    target.finite source.rank source.constants target.rank target.constants target.pool sub).mp subtype
  obtain ⟨A, d, H, r', f, g, π, hA, lower, realized, rest⟩ := witness
  obtain ⟨S, _, rS⟩ := realized.tuple.2.1 e target.root_slot
  obtain ⟨α, _, rα⟩ := realized.tuple.2.1 l target.last_slot
  exact ⟨s, v, ν, A, d, H, r', S, α, cut, drop, prefixType, hν,
    ⟨A, d, H, r', f, g, π, hA, lower, realized, rest⟩, hA, lower, realized, rS, rα,
    (target.root.2 d A H r' δ w S lower (ZF.v_transitive_l I hZF hA) realized rS).mp root,
    (target.bound.2 ν A d H r' δ w S α hA lower realized rS rα).mp bound,
    (target.height.2 ν A d H r' δ w α hA lower realized rα).mp height⟩

end YesMetaZFC.SetTheory.LargeCardinal
