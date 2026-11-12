import YesMetaZFC.SetTheory.LargeCardinal.Game.Elastic
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax
import YesMetaZFC.Model.SetTheory.Game.Graph

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
    ∃ s v ν A d H r' S α π, M.IsRestrictionOf I s r l ∧ Td_dcp_d I l n D u v ∧
      Tt_realized_d I ω c Y R l s δ U D v ∧ M.mem ν η ∧ Ts_at_d hZF ω δ l s n V W w ν ∧
      V_d I ν A ∧ Smem_d I d A H ∧ Tt_realized_d I ω d A H n r' δ V W w ∧
      Rd_entry_d e S r' ∧ Rd_entry_d l α r' ∧ M.mem e S ∧ Tg_bound_d I δ S α ∧ Tg_height_d α ν ∧
      M.IsSetBijectionFromTo I π n n ∧
      (∀ i j x, Rd_entry_d j i π → M.mem i l → (Rd_entry_d i x s ↔ Rd_entry_d j x r')) := by
  obtain ⟨sub, v, drop, subtype, root, bound, height⟩ := reply
  obtain ⟨s, v', cut, drop', prefixType⟩ := type.dcp_l hZF hω drop.1 source.pool
  have eq := drop'.unique_l I hZF.1 drop
  subst v'
  obtain ⟨_, ν, hν, witness⟩ := (ts_subtype_realized_l hZF hω prog hY model prefixType source.limit target.limit subtype.1
    target.finite source.rank source.constants target.rank target.constants target.pool sub).mp subtype
  obtain ⟨A, d, H, r', f, g, π, hA, lower, realized, ff, fg, graph, orig, bij, perm⟩ := witness
  obtain ⟨S, _, rS⟩ := realized.tuple.2.1 e target.root_slot
  obtain ⟨α, _, rα⟩ := realized.tuple.2.1 l target.last_slot
  refine ⟨s, v, ν, A, d, H, r', S, α, π, cut, drop, prefixType, hν,
    ⟨A, d, H, r', f, g, π, hA, lower, realized, ff, fg, graph, orig, bij, perm⟩, hA, lower, realized, rS, rα,
    (target.root.2 d A H r' δ w S lower (v_transitive_l I hA) realized rS).mp root,
    (target.bound.2 ν A d H r' δ w S α hA lower realized rS rα).mp bound,
    (target.height.2 ν A d H r' δ w α hA lower realized rα).mp height, bij, ?_⟩
  intro i j x ji hi
  have hj := bij.1.1.input_mem_of_pairMember ji
  constructor
  · intro hx
    have fx := (orig i x hi).mp hx
    exact (graph j x).mp ((perm j hj x (ff.output_mem_of_pairMember fx)).mpr
      ⟨i, bij.1.1.output_mem_of_pairMember ji, ji, fx⟩)
  · intro hx
    obtain ⟨i', _, ji', fx⟩ := (perm j hj x (realized.tuple.bound_l hx).2).mp ((graph j x).mpr hx)
    exact (orig i x hi).mpr (bij.1.1.1.2 j i' i ji' ji ▸ fx)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 在真实低层前缀后添加回答末位

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
  have hl := hω.transitive (ZF.modelsKP hZF) n type.finite l hn.predecessor_mem
  have hαA : M.mem α A := by
    obtain ⟨β, γ, hb, hg, last⟩ := height
    exact ZF.v_ordinal_mem_l I hZF hA
      ((v_ordinal_l I hA).transitive γ last.predecessor_mem α
        (((v_ordinal_l I hA).mem last.predecessor_mem).transitive β hg.predecessor_mem α hb.predecessor_mem))
  have point := v_transitive_l I hA α hαA δ bound.2.1
  obtain ⟨d, H, lower⟩ := smdl_membership_l I hZF ⟨δ, point⟩
  obtain ⟨D₀, pool₀⟩ := tt_pool_exists_l I hZF hω l V
  obtain ⟨v₀, truth₀, _⟩ := tt_truth_exists_l I hZF ω d l s δ D₀
  have prefixType : Tt_realized_d I ω d A H l s δ V D₀ v₀ := ⟨lower.1, hl, fs, point, constants, pool₀, truth₀⟩
  obtain ⟨r', w, full, _, kept, last⟩ := prefixType.append_l hZF hω hn hαA target.pool
  obtain ⟨s', v, cut', drop, prefixSource⟩ := type.dcp_l hZF hω hn source.pool
  have eqs := Structure.IsSetRelation.eq_of_pairMember_iff (𝕀 := I) hZF.1 cut'.1 cut.1
    (fun i x => (cut'.2 i x).trans (cut.2 i x).symm)
  subst s'
  have witness : Ts_at_d hZF ω δ l s n V W w ν :=
    ts_at_prefix_l hZF hω hA lower full (fun i hi => (hn i).mpr (Or.inl hi))
      (fun i x hi => (kept i x hi).symm)
  have sub : M.MemberSubset w W := fun x hx => ((full.truth x).mp hx).1
  have subtype := (ts_subtype_realized_l hZF hω prog hY model prefixSource source.limit target.limit hτκ full.finite
    source.rank source.constants target.rank target.constants target.pool sub).mpr
      ⟨fun i hi => (hn i).mpr (Or.inl hi), ν, hνη, witness⟩
  have first := (kept e S (fs.bound_l rS).1).mpr rS
  exact ⟨d, H, r', w, lower, full, kept, last, sub, v, drop, subtype,
    (target.root.2 d A H r' δ w S lower (v_transitive_l I hA) full first).mpr root,
    (target.bound.2 ν A d H r' δ w S α hA lower full first last).mpr bound,
    (target.height.2 ν A d H r' δ w α hA lower full last).mpr height⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 泛型 I 方向：任意排列下的原标签恢复与严格高度下降

回答末位是序数，原树和标签都不是序数，因此该末位只能占据子类型见证新加的
位置。排列遂保持整个旧前缀；空根固定原树，剩余坐标恰为原标签图。
此处不对内部自然数作外部有限枚举，也不加强原回答规则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_reply_d.descend_l {ω κ τ e l n B C U V D P W u w b a z δ η Y c R r S g α : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M} {p : Tg_reply_queries_d M}
    (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) (hel : M.mem e l)
    (prog : Ts_program_d hZF ω l b σ a z)
    (source : Ee_language_d hZF ω κ l B U D q) (target : Tg_reply_language_d hZF ω e l n τ C V W p)
    (hY : V_d I η Y) (height : M.SuccessorOf η α) (model : Smem_d I c Y R)
    (type : Tt_realized_d I ω c Y R n r δ U P u)
    (rS : Rd_entry_d e S r) (root : M.mem e S) (notOrd : ¬ M.IsOrdinal S)
    (set : Sg_set_d I e l r g) (labels : M.IsSetRelation I g)
    (reply : Tg_reply_d I ω l n κ τ U D W u w b σ z p) :
    ∃ ν A d H r' β, V_d I ν A ∧ Smem_d I d A H ∧ Tt_realized_d I ω d A H n r' δ V W w ∧
      Rd_entry_d e S r' ∧ Rd_entry_d l β r' ∧ Sg_set_d I e l r' g ∧
      Tg_bound_d I δ S β ∧ Tg_height_d β ν ∧ M.mem β α := by
  obtain ⟨s, v, ν, A, d, H, r', T, β, π, cut, drop, _, hν, _, hA, lower, full,
    first, last, rootT, bound, gap, bij, moved⟩ := reply.read_l hZF hω prog source target hY model type
  have on := hω.members_areOrdinals (ZF.modelsKP hZF) n type.finite
  have old i x (hi : M.mem i l) (hx : Rd_entry_d i x s) : x = S ∨ M.mem x g := by
    have hr := ((cut.2 i x).mp hx).2
    by_cases eq : i = e
    · exact Or.inl ((fn0_function_l (ZF.modelsKP hZF) type.tuple).1.2 e x S (eq ▸ hr) rS)
    · exact Or.inr ((set x).mpr ⟨i, hi, eq, hr⟩)
  have newLast i (hi : M.mem i l) : ¬ Rd_entry_d i β s := by
    intro hx
    rcases old i β hi hx with eq | hg
    · exact notOrd (eq ▸ bound.1)
    · obtain ⟨x, y, pair⟩ := labels β hg
      exact pair.not_transitive_l M (KP.mem_irrefl_d (ZF.modelsKP hZF)) bound.1.transitive
  -- 新高度排除全部旧坐标，故原任意排列固定最后一个位置。
  have fixed : Rd_entry_d l l π := by
    obtain ⟨i, hi, li⟩ := bij.1.1.2.2 l drop.1.predecessor_mem
    rcases (drop.1 i).mp hi with hi | eq
    · exact (newLast i hi ((moved i l β li hi).mpr last)).elim
    · exact hZF.1.eq_of_same_members i l eq ▸ li
  have inside j i (hj : M.mem j l) (ji : Rd_entry_d j i π) : M.mem i l := by
    rcases (drop.1 i).mp (bij.1.1.output_mem_of_pairMember ji) with hi | eq
    · exact hi
    · have eqi := hZF.1.eq_of_same_members i l eq
      have eqj := bij.1.2 j l l (eqi ▸ ji) fixed
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) l (eqj ▸ hj)).elim
  have fixedRoot : Rd_entry_d e e π ∧ T = S := by
    obtain ⟨i, _, ei⟩ := bij.1.1.2.2 e (on.transitive l drop.1.predecessor_mem e hel)
    have hi := inside e i hel ei
    have hx := (moved i e T ei hi).mpr first
    have eq : T = S := (old i T hi hx).elim id (fun hg => by
      obtain ⟨x, y, pair⟩ := labels T hg
      exact (KPair_d.empty_not_mem_l he pair rootT).elim)
    have ie : i = e := by
      apply Classical.byContradiction
      intro ne
      obtain ⟨x, y, pair⟩ := labels S ((set S).mpr ⟨i, hi, ne, eq ▸ ((cut.2 i T).mp hx).2⟩)
      exact KPair_d.empty_not_mem_l he pair root
    exact ⟨ie ▸ ei, eq⟩
  have same : Sg_set_d I e l r' g := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, ne, ix⟩ := (set x).mp hx
      obtain ⟨j, hj, ji⟩ := bij.2 i (on.transitive l drop.1.predecessor_mem i hi)
      have hjl : M.mem j l := by
        rcases (drop.1 j).mp hj with hj | eq
        · exact hj
        · have jl := hZF.1.eq_of_same_members j l eq
          have il := bij.1.1.1.2 l i l (jl ▸ ji) fixed
          exact (KP.mem_irrefl_d (ZF.modelsKP hZF) l (il ▸ hi)).elim
      have jne : j ≠ e := fun eq => ne (bij.1.1.1.2 e i e (eq ▸ ji) fixedRoot.1)
      exact ⟨j, hjl, jne, (moved i j x ji hi).mp ((cut.2 i x).mpr ⟨hi, ix⟩)⟩
    · rintro ⟨j, hj, ne, jx⟩
      obtain ⟨i, _, ji⟩ := bij.1.1.2.2 j (on.transitive l drop.1.predecessor_mem j hj)
      have hi := inside j i hj ji
      have ine : i ≠ e := fun eq => ne (bij.1.2 j e e (eq ▸ ji) fixedRoot.1)
      exact (set x).mpr ⟨i, hi, ine, ((cut.2 i x).mp ((moved i j x ji hi).mpr jx)).2⟩
  have lt : M.mem β α := by
    obtain ⟨β₁, β₂, h₁, h₂, h₃⟩ := gap
    have hβν := (v_ordinal_l I hA).transitive β₂ h₃.predecessor_mem β
      (((v_ordinal_l I hA).mem h₃.predecessor_mem).transitive β₁ h₂.predecessor_mem β h₁.predecessor_mem)
    rcases (height ν).mp hν with hνα | eq
    · exact ((v_ordinal_l I hY).mem height.predecessor_mem).transitive ν hνα β hβν
    · exact (eq β).mp hβν
  exact ⟨ν, A, d, H, r', β, hA, lower, full, fixedRoot.2 ▸ first, last, same,
    fixedRoot.2 ▸ bound, gap, lt⟩

end YesMetaZFC.SetTheory.LargeCardinal
