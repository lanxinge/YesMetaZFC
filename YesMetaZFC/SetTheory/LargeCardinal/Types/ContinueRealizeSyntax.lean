import YesMetaZFC.Model.SetTheory.Types.SubtypeUp
import YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax
import YesMetaZFC.SetTheory.CumulativeCertificate

/-! # 原子类型查询的低层实现句子

仅使用读取方向：原完整类型、同一编译程序和候选常量域足以产生实现。
不要求旧类型的整个常量域已有背景 Vκ 证书，也不预设候选的实现或排列。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- ω,n,b,z,η,Y,c,R,r,δ,U,D,t,κ,τ,m,A,V,W,u；最后七项是原程序槽位。
def tc_realize_seed0_m : Formula 1 27 :=
  let p : Fin 27 → Term 27 := Term.bound
  let σ : Fin 7 → Term 27 := fun i => [p 20, p 21, p 22, p 23, p 24, p 25, p 26].get i
  set[27] ⟪⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧ ⌜ts_numeric_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, ⌜σ⌝ₛ) ∧
    ⌜v_sigma_m⌝ₚ(⌜p 4⌝ₛ, ⌜p 5⌝ₛ) ∧ ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(⌜p 6⌝ₛ, ⌜p 5⌝ₛ, ⌜p 7⌝ₛ) ∧
    ⌜tt_realized_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 6⌝ₛ, ⌜p 5⌝ₛ, ⌜p 7⌝ₛ, ⌜p 1⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ, ⌜p 10⌝ₛ, ⌜p 11⌝ₛ, ⌜p 12⌝ₛ) ∧
    ⌜Formula.isLimitOrdinal⌝ₚ(⌜p 13⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜p 14⌝ₛ) ∧ ⌜p 15⌝ₛ ∈ ⌜p 0⌝ₛ ∧
    ⌜v_sigma_m⌝ₚ(⌜p 14⌝ₛ, ⌜p 16⌝ₛ) ∧ ⌜tt_constants0_m⌝ₚ(⌜p 14⌝ₛ, ⌜p 16⌝ₛ, ⌜p 17⌝ₛ) ∧
    ⌜tt_pool_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 15⌝ₛ, ⌜p 17⌝ₛ, ⌜p 18⌝ₛ) ∧
    ⌜ts_subtype_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 13⌝ₛ, ⌜p 14⌝ₛ, ⌜p 15⌝ₛ, ⌜p 10⌝ₛ, ⌜p 19⌝ₛ, ⌜p 2⌝ₛ, ⌜p 3⌝ₛ, ⌜p 12⌝ₛ, ⌜σ⌝ₛ)⟫

def tc_realize_result0_m : Formula 1 27 :=
  let p : Fin 27 → Term 27 := Term.bound
  set[27] ⟪∃ ν, ν ∈ ⌜p 4⌝ₛ ∧
    ⌜ts_at_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 9⌝ₛ, ⌜p 1⌝ₛ, ⌜p 8⌝ₛ, ⌜p 15⌝ₛ, ⌜p 17⌝ₛ, ⌜p 18⌝ₛ, ⌜p 19⌝ₛ, ν)⟫

theorem tc_realize_seed0_closed_l : tc_realize_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_realize_seed0_m, Definitional.Formula.FreeClosed]
  have hs : ∀ i : Fin 7, ([Term.bound 20, Term.bound 21, Term.bound 22, Term.bound 23,
      Term.bound 24, Term.bound 25, Term.bound 26].get i : Term 27).freeSupport = [] := by
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  exact ⟨ts_numeric_closed_l _ _ _ _ _ rfl rfl rfl rfl hs,
    ts_subtype_closed_l _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hs⟩

theorem tc_realize_result0_closed_l : tc_realize_result0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_realize_result0_m, Definitional.Formula.FreeClosed]

def tc_realize_m : Formula 1 0 := Formula.forallClosure 27 (.imp tc_realize_seed0_m tc_realize_result0_m)

theorem tc_realize_closed_l : tc_realize_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tc_realize_seed0_closed_l, tc_realize_result0_closed_l⟩

theorem tc_realize_true_l (hZF : M.Models ZF) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tc_realize_m := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [tc_realize_seed0_m, tc_realize_result0_m, Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, ts_numeric_sat_l hZF, v_sigma_sat_l (ZF.modelsKP hZF), smem_sat_l I,
    tt_realized_sat_l I (ZF.modelsKP hZF), Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_mem_iff,
    tt_constants0_sat_l hZF.1, tt_pool_sat_l I (ZF.modelsKP hZF), ts_subtype_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_exists_iff, ts_at_sat_l hZF, Definitional.Term.eval_weaken]
  rintro ⟨hw, ⟨a, program⟩, rank, model, type, hk, ht, hm, base, constants, pool, bound, _, q, query, hq⟩
  exact ((query.read_l hZF hw program rank model type hk ht bound hm base constants pool).mp hq).2

end YesMetaZFC.SetTheory.LargeCardinal
