import YesMetaZFC.Model.SetTheory.Internal.TypeMoveSource
import YesMetaZFC.Model.SetTheory.Internal.LocalTypeRead

/-! # 用指定点的完整类型读取移动后的较低类型 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u

def tm_params_l {α : Type u} (ω C κ k n Z E δ e t : α) : Fin 10 → α :=
  Fin.cases ω (Fin.cases C (Fin.cases κ (Fin.cases k (Fin.cases n
    (Fin.cases Z (Fin.cases E (Fin.cases δ (Fin.cases e (fun _ => t)))))))))

variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)

/-- 全部低参数只出现一次；指定高度 ν 是唯一随实现移动的坐标。 -/
theorem Tt_realized_d.move_read_l {ω e ν W F u c X R η C κ k n Z E δ t ξ β A B U D d S s : M.Domain}
    (l : Tt_realized_d Q ω c X R e e ν W F u) (model : Smem_d Q c X R)
    (hω : M.IsOmega ω) (hη : M.IsLimitOrdinal η) (hX : V_d Q η X)
    (hν : M.IsOrdinal ν) (hk : M.mem k ω) (sum : M.IsOrdinalAddition Q β ν k) (hβ : M.mem β η)
    (hA : V_d Q β A) (hων : M.MemberSubset ω β) (hκA : M.mem κ A)
    (hC : V_d Q ξ C) (hξ : M.IsLimitOrdinal ξ) (hωξ : M.mem ω ξ) (hκξ : M.mem κ ξ)
    (hB : V_d Q κ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ)
    (pool : Tt_pool_d Q ω n U D) (hm : Smem_d Q d A S) (hn : M.mem n ω)
    (names : Fn0_d n Z E) (assign : Tn_assign_d e e ν E s) (tuple : Fn0_d n A s) (point : M.mem δ A)
    (ha : ∀ i, M.mem (tm_params_l ω C κ k n Z E δ e t i) W) :
    Formula.satisfies (l.point_env_l Q (tm_params_l ω C κ k n Z E δ e t) ha) tm_type_f ↔
      Tt_truth_d Q ω d n s δ D t := by
  have hwX := l.constants ω (ha 0)
  let ny : Nonempty {x // M.mem x X} := ⟨⟨ω, hwX⟩⟩
  let a (i : Fin 10) : (rt_model_l X ny).Domain :=
    ⟨tm_params_l ω C κ k n Z E δ e t i, l.constants _ (ha i)⟩
  let v : (rt_model_l X ny).Domain := ⟨ν, l.point⟩
  let ρ : Env (rt_model_l X ny) 11 := ⟨Fin.cases v a, fun _ => v⟩
  have read := tm_type_source_l hZF hω hη hX hwX (a 1) (a 2) (a 3) (a 4) (a 5)
    (a 6) (a 7) (a 8) v (a 9) hν hk sum hβ hA hων hκA hC hξ hωξ hκξ hB constants pool
    hm hn names assign tuple point
  have env : (⟨Fin.cases v (Fin.cases ⟨ω, hwX⟩ (Fin.cases (a 1) (Fin.cases (a 2)
      (Fin.cases (a 3) (Fin.cases (a 4) (Fin.cases (a 5) (Fin.cases (a 6)
        (Fin.cases (a 7) (Fin.cases (a 8) (fun _ => a 9)))))))))), fun _ => v⟩ : Env (rt_model_l X ny) 11).bound = ρ.bound := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))))))) i
  have result : Formula.satisfies ρ tm_type_f ↔ Tt_truth_d Q ω d n s δ D t :=
    (Formula.closed_env_l tm_type_f tm_type_closed_l env.symm).trans read
  exact (smem_formula_l Q model ny tm_type_f ρ).symm.trans result

end YesMetaZFC.SetTheory.Internal
