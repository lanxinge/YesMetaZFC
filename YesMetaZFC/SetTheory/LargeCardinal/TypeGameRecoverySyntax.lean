import YesMetaZFC.SetTheory.LargeCardinal.TypeGameDecoding
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameQueryBase
import YesMetaZFC.Model.SetTheory.Internal.TypeExceedsSyntax

/-! # 一张图恢复的原语言句子

只检查原节点查询、旧图及实际任意排列见证。最大序数查询固定实现高度，
新图恰为旧图并上一个标签对；输出保留排列以及所有旧坐标的对应关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- ω,e,j,k,l,n,U,D,s,t；五条查询；旧元组 r、δ、S、α、旧图 a、实现高度 ν、新类型 u。
def tc_recover_seed0_m : Formula 1 22 :=
  let p : Fin 22 → Term 22 := Term.bound
  set[22] ⟪⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧ ⌜Formula.isEmpty⌝ₚ(⌜p 1⌝ₛ) ∧
    ⌜p 5⌝ₛ ∈ ⌜p 0⌝ₛ ∧ ⌜p 1⌝ₛ ∈ ⌜p 3⌝ₛ ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜p 3⌝ₛ, ⌜p 2⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜p 4⌝ₛ, ⌜p 3⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜p 5⌝ₛ, ⌜p 4⌝ₛ) ∧
    ⌜tg_query_base_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ, ⌜p 3⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ,
      ⌜p 10⌝ₛ, ⌜p 11⌝ₛ, ⌜p 12⌝ₛ, ⌜p 13⌝ₛ, ⌜p 14⌝ₛ) ∧
    ⌜p 0⌝ₛ ∈ ⌜p 6⌝ₛ ∧ ⌜p 3⌝ₛ ∈ ⌜p 6⌝ₛ ∧ ⌜p 8⌝ₛ ∈ ⌜p 6⌝ₛ ∧ ⌜p 9⌝ₛ ∈ ⌜p 6⌝ₛ ∧
    ⌜tg_bound_raw_m⌝ₚ(⌜p 16⌝ₛ, ⌜p 17⌝ₛ, ⌜p 18⌝ₛ) ∧
    ⌜rd_entry0_m⌝ₚ(⌜p 1⌝ₛ, ⌜p 17⌝ₛ, ⌜p 15⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜p 3⌝ₛ, ⌜p 18⌝ₛ, ⌜p 15⌝ₛ) ∧
    ⌜tg_graph_m⌝ₚ(⌜p 2⌝ₛ, ⌜p 19⌝ₛ) ∧ ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 15⌝ₛ, ⌜p 19⌝ₛ) ∧
    ⌜p 1⌝ₛ ∈ ⌜p 17⌝ₛ ∧ ⌜p 14⌝ₛ ∈ ⌜p 21⌝ₛ ∧ ⌜p 11⌝ₛ ∈ ⌜p 21⌝ₛ ∧
    ⌜ts_at_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 16⌝ₛ, ⌜p 4⌝ₛ, ⌜p 15⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ, ⌜p 21⌝ₛ, ⌜p 20⌝ₛ)⟫

def tc_recovered_m {d} (ω e j k l n U D s t r δ S α a ν u A c H r' g z π : Term d) : Formula 1 d := set[d] ⟪
  ⌜v_m kpair_convention_l⌝ₚ(⌜ν⌝ₛ, ⌜A⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜c⌝ₛ, ⌜A⌝ₛ, ⌜H⌝ₛ) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, ⌜c⌝ₛ, ⌜A⌝ₛ, ⌜H⌝ₛ, ⌜n⌝ₛ, ⌜r'⌝ₛ, ⌜δ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ) ∧
  ⌜Formula.isBijectionFromTo kpair_convention_l⌝ₚ(⌜π⌝ₛ, ⌜n⌝ₛ, ⌜n⌝ₛ) ∧
  (∀ i v x, ⌜rd_entry0_m⌝ₚ(v, i, ⌜π⌝ₛ) → i ∈ ⌜l⌝ₛ →
    (⌜rd_entry0_m⌝ₚ(i, x, ⌜r⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(v, x, ⌜r'⌝ₛ))) ∧
  ⌜Formula.isSuccessor⌝ₚ(⌜ν⌝ₛ, ⌜α⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, ⌜S⌝ₛ, ⌜r'⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, ⌜α⌝ₛ, ⌜r'⌝ₛ) ∧ ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜e⌝ₛ, ⌜l⌝ₛ, ⌜r'⌝ₛ, ⌜g⌝ₛ) ∧
  ⌜tg_node_m⌝ₚ(⌜k⌝ₛ, ⌜S⌝ₛ, ⌜s⌝ₛ, ⌜t⌝ₛ, ⌜g⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜j⌝ₛ, ⌜z⌝ₛ, ⌜g⌝ₛ) ∧
  (∀ p, p ∈ ⌜g⌝ₛ ↔ p ∈ ⌜a⌝ₛ ∨ ⌜kpair0_m⌝ₚ(p, ⌜j⌝ₛ, ⌜z⌝ₛ))⟫
derive_free_closed tc_recovered_m

-- 七个新见证占据量词栈顶；其余二十二项原输入及查询原样保留。
def tc_recovered0_m : Formula 1 29 := tc_recovered_m
  (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 13) (.bound 14)
  (.bound 15) (.bound 16) (.bound 22) (.bound 23) (.bound 24) (.bound 25) (.bound 26) (.bound 27)
  (.bound 28) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) (.bound 0)

theorem tc_recovered0_closed_l : tc_recovered0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_recovered0_m]

def tc_recover_result0_m : Formula 1 22 :=
  let p : Fin 22 → Term 22 := Term.bound
  set[22] ⟪∃ A c H r' g z π,
    ⌜tc_recovered_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ,
      ⌜p 8⌝ₛ, ⌜p 9⌝ₛ, ⌜p 15⌝ₛ, ⌜p 16⌝ₛ, ⌜p 17⌝ₛ, ⌜p 18⌝ₛ, ⌜p 19⌝ₛ, ⌜p 20⌝ₛ, ⌜p 21⌝ₛ, A, c, H, r', g, z, π)⟫

theorem tc_recover_seed0_closed_l : tc_recover_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_recover_seed0_m, Definitional.Formula.FreeClosed]
theorem tc_recover_result0_closed_l : tc_recover_result0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_recover_result0_m, Definitional.Formula.FreeClosed]

def tc_recover_m : Formula 1 0 := Formula.forallClosure 22 (.imp tc_recover_seed0_m tc_recover_result0_m)

theorem tc_recover_closed_l : tc_recover_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tc_recover_seed0_closed_l, tc_recover_result0_closed_l⟩

theorem tc_recover_true_l (hZF : M.Models ZF) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tc_recover_m := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [tc_recover_seed0_m, tc_recover_result0_m, tc_recovered_m, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff, tg_query_base_sat_l I (ZF.modelsKP hZF),
    tg_bound_raw_sat_l I hZF.1, rd_entry0_sat_l hZF.1, tg_graph_sat_l I hZF.1, sg_set_sat_l I hZF.1,
    ts_at_sat_l hZF, Formula.satisfies_exists_iff, v_sat_l I hZF.1, smem_sat_l I,
    tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_isBijectionFromTo_iff I hZF.1,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, tg_node_sat_l I hZF.1,
    Formula.satisfies_disj_iff, kpair0_sat_l hZF.1, Definitional.Term.eval_weaken]
  rintro ⟨hw, he, hn, hek, hk, hl, hln, base, hwU, hkU, hsU, htU, ⟨_, _, B, rank, hS⟩,
    first, last, graph, set, root, qn, qm, witness⟩
  have data := witness
  obtain ⟨_, _, _, _, _, _, _, _, _, type, _⟩ := data
  obtain ⟨_, max, _, _, node⟩ := base.scope_l I (ZF.modelsKP hZF) type.pool hwU hsU htU hkU
  exact tg_one_graph_recovery_l hZF hw he hn hek hk hl hln node max rank hS first last graph set root qn qm witness

end YesMetaZFC.SetTheory.LargeCardinal
