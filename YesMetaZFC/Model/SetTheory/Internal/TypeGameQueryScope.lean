import YesMetaZFC.Model.SetTheory.Internal.TypeGameQuerySyntax

/-! # 固定低参数域中的查询向更大常量域延伸

完整类型在较小常量域上取交即可；查询、元组和指定点不变。
因此节点和四个端点查询可以先在低参数域中固定，再用于任意更大的类型域。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hKP : M.Models KP)
include hKP

theorem Tt_realized_d.constants_restrict_l {ω c X R n r δ U D T V W : M.Domain}
    (type : Tt_realized_d I ω c X R n r δ U D T) (pool : Tt_pool_d I ω n V W)
    (sub : M.MemberSubset V U) :
    ∃ t, Tt_realized_d I ω c X R n r δ V W t ∧ ∀ q, M.mem q W → (M.mem q t ↔ M.mem q T) := by
  obtain ⟨t, cut⟩ := KP.intersection_exists_d hKP W T
  have smaller := pool.mono_l I type.pool sub
  refine ⟨t, ⟨type.model, type.finite, type.tuple, type.point,
    fun x hx => type.constants x (sub x hx), pool, ?_⟩, fun q hq => (cut q).trans (and_iff_right hq)⟩
  intro q
  exact (cut q).trans (and_congr_right fun hq => (type.truth q).trans (and_iff_right (smaller q hq)))

variable {ω e l n U D V W q s t k : M.Domain}
  (small : Tt_pool_d I ω n U D) (large : Tt_pool_d I ω n V W) (sub : M.MemberSubset U V)
include small large sub

theorem Tg_root_query_d.scope_l (h : Tg_root_query_d I ω e n U D q) : Tg_root_query_d I ω e n V W q := by
  refine ⟨small.mono_l I large sub q h.1, fun c X R r δ T S model trans type rS => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 c X R r δ a S model trans localType rS)

theorem Tg_max_query_d.scope_l (h : Tg_max_query_d I ω l n U D q) : Tg_max_query_d I ω l n V W q := by
  refine ⟨small.mono_l I large sub q h.1, fun ν X c R r δ T α rank model type rα => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 ν X c R r δ a α rank model localType rα)

theorem Tg_height_query_d.scope_l (h : Tg_height_query_d I ω l n U D q) : Tg_height_query_d I ω l n V W q := by
  refine ⟨small.mono_l I large sub q h.1, fun ν X c R r δ T α rank model type rα => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 ν X c R r δ a α rank model localType rα)

theorem Tg_bound_query_d.scope_l (h : Tg_bound_query_d I ω e l n U D q) : Tg_bound_query_d I ω e l n V W q := by
  refine ⟨small.mono_l I large sub q h.1, fun ν X c R r δ T S α rank model type rS rα => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 ν X c R r δ a S α rank model localType rS rα)

theorem Tg_node_query_d.scope_l (h : Tg_node_query_d I ω e n l U D s t k q) :
    Tg_node_query_d I ω e n l V W s t k q := by
  refine ⟨small.mono_l I large sub q h.1, fun c X R r δ T S model trans type rS => ?_⟩
  obtain ⟨a, localType, same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q h.1).symm.trans (h.2 c X R r δ a S model trans localType rS)

end YesMetaZFC.SetTheory.Internal
