import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePast

/-! # 原超幂更新同时推进整列回答历史

共同支撑层保存此前全部行；本轮完整回答在产生它的奇数模型中打包，
再追加到内部历史。旧记录对应的四个低坐标和回答有序对沿偶数边固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一次真实树更新延伸任意已有有限历史，保留旧行、低坐标和树结点对应。 -/
def Tg_past_update_d (ω X κ i Y R μ K η C L V N κ' j Q Q' : M.Domain) (v : Fin 54 → M.Domain) : Prop :=
  ∀ n H b, M.mem n ω → Tg_past_d hZF ω n H X b → M.mem b κ → Tg_past_links_d I H Q →
    ∃ n' H' q, M.mem n' ω ∧ M.SuccessorOf n' n ∧ Tg_past_d hZF ω n' H' N κ' ∧
      Tg_saved_d hZF ω Y R μ K η C L V q ∧ Tg_saved_code_d ω V q v ∧ Tg_past_at_d H' n i Y R μ K η C L V q ∧
      (∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H)) ∧
      Tg_past_fixed_d H j ∧ Tg_past_links_d I H' Q'

/-- 任意内部有限历史都能加入本次实际回答，而不改变旧行。 -/
theorem Tg_past_d.answer_l {ω n H Y b R μ K η C L V N κ i : M.Domain}
    (past : Tg_past_d hZF ω n H Y b) (hn : M.mem n ω)
    (context : Tg_context_d ω Y η C) (source : Ic_model_d hZF ω μ K Y R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
    (valid : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val = ω)
    (limit : M.IsLimitOrdinal L) (member : M.mem V C) (rank : Vr_d Y L V)
    (below : M.mem (ρ.bound 15).val L) (answer : M.mem (ρ.bound 11).val V)
    (nt : M.TransitiveSet N) (hVN : M.mem V N) (next : Vr_d N L V)
    (oldBound : M.mem b L) (bound : M.MemberSubset L κ) :
    ∃ n' H' q, M.mem n' ω ∧ M.SuccessorOf n' n ∧ Tg_past_d hZF ω n' H' N κ ∧
      Tg_saved_d hZF ω Y R μ K η C L V q ∧ Tg_saved_code_d ω V q (fun i => (ρ.bound i).val) ∧
      Tg_past_at_d H' n i Y R μ K η C L V q ∧
      ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H) := by
  obtain ⟨q, saved, code⟩ := context.save_round_l hZF source nc ρ valid hw limit member rank below answer
  obtain ⟨n', succ, finite⟩ := source.source.omega.1.2 n hn
  have carried := past.transfer_l hZF source.source.transitive nt
    (source.source.transitive C context.member V member) rank hVN next limit oldBound
  obtain ⟨H', updated, newest, entries⟩ := carried.push_l hZF succ saved hVN next
    (fun x hx => bound x (limit.1.transitive b oldBound x hx)) bound (i := i)
  exact ⟨n', H', q, finite, succ, updated, saved, code, newest, entries⟩

/-- 先到本轮奇数源，再到新偶数源；两次共同秩段比较覆盖全部旧行。 -/
theorem Tg_context_d.past_update_l {ω X κ i Y R μ K η C θ U L V N κ' j W Q Q' c : M.Domain}
    (context : Tg_context_d ω Y η C) (source : Ic_model_d hZF ω μ K Y R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 54)
    (valid : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val = ω)
    (xt : M.TransitiveSet X) (hUX : M.mem U X) (left : Vr_d X θ U)
    (hUY : M.mem U Y) (right : Vr_d Y θ U) (hθ : M.IsLimitOrdinal θ) (hκθ : M.MemberSubset κ θ)
    (limit : M.IsLimitOrdinal L) (member : M.mem V C) (rank : Vr_d Y L V)
    (below : M.mem (ρ.bound 15).val L) (answer : M.mem (ρ.bound 11).val V) (hκL : M.MemberSubset κ L)
    (nt : M.TransitiveSet N) (hVN : M.mem V N) (next : Vr_d N L V) (bound : M.MemberSubset L κ')
    (hW : M.mem W X) (fixedRank : Vr_d X κ W) (fixed : ∀ x, M.mem x W → Rd_entry_d x x j)
    (keep : ∀ m d, Rd_entry_d m d Q → Rd_entry_d m d Q') (node : Rd_entry_d i c Q') (model : Smem_d I c Y R) :
    Tg_past_update_d hZF ω X κ i Y R μ K η C L V N κ' j Q Q' (fun i => (ρ.bound i).val) := by
  intro n H b hn past hb links
  have odd := past.transfer_l hZF xt source.source.transitive hUX left hUY right hθ (hκθ b hb)
  obtain ⟨n', H', q, finite, succ, updated, saved, code, newest, entries⟩ := odd.answer_l hZF hn context source nc ρ
    valid hw limit member rank below answer nt hVN next (hκL b hb) bound (i := i)
  have critical := fixedRank.ordinal_l hW
  exact ⟨n', H', q, finite, succ, updated, saved, code, newest, entries,
    past.fixed_l hZF xt hW fixedRank (critical.transitive b hb) fixed,
    updated.links_push_l hZF succ newest entries links keep node model⟩

/-- 由层的逐点固定性得到原回答的字面固定性，包括其有序对编码。 -/
theorem Tg_saved_d.answer_fixed_l {ω Y R μ K η C L V q j : M.Domain}
    (saved : Tg_saved_d hZF ω Y R μ K η C L V q)
    (fixed : ∀ x, M.mem x V → Rd_entry_d x x j) (nc : Nonempty {x // M.mem x C}) :
    ∃ ρ : Env (rt_model_l C nc) 54, Tg_saved_code_d ω V q (fun i => (ρ.bound i).val) ∧
      Formula.satisfies ρ tg_round0_m ∧ (ρ.bound 16).val = ω ∧
      Rd_entry_d (ρ.bound 15).val (ρ.bound 15).val j ∧ Rd_entry_d (ρ.bound 13).val (ρ.bound 13).val j ∧
      Rd_entry_d (ρ.bound 12).val (ρ.bound 12).val j ∧ Rd_entry_d (ρ.bound 11).val (ρ.bound 11).val j ∧
      ∀ a, KPair_d M a (ρ.bound 15).val (ρ.bound 11).val → Rd_entry_d a a j := by
  obtain ⟨ρ, code, valid, hw, hτ, hU, hD, hw'⟩ := saved.read_l hZF nc
  have hV := saved.source.source.transitive C saved.context.member V saved.member
  refine ⟨ρ, code, valid, hw, fixed _ hτ, fixed _ hU, fixed _ hD, fixed _ hw', ?_⟩
  intro a pair
  obtain ⟨a', ha', pair'⟩ := saved.source.source.theory.algebra.kpair_l
    (saved.source.source.transitive V hV _ hτ) (saved.source.source.transitive V hV _ hw')
  have eq := kpair_unique_l M hZF.1 pair' pair
  have ha : M.mem a Y := eq ▸ ha'
  exact fixed a (saved.rank.kpair_mem_l hZF saved.source.source.transitive hV saved.limit hτ hw' ha pair)

end YesMetaZFC.SetTheory.LargeCardinal
