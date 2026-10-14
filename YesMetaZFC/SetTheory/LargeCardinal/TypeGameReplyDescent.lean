import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReply
import YesMetaZFC.Model.SetTheory.Internal.TypeGameGraph

/-! # 泛型 I 方向：任意排列下的原标签恢复与严格高度下降

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
  have on := hω.members_areOrdinals hZF n type.finite
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
