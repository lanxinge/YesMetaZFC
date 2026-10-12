import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlMove

/-! # 三阶段控制位置的同一有限记录

前十九项为控制参数，后三项为内部轮号、历史图和时刻。阶段只有固定的
0、1、2 三种语法形状；轮号及历史均取遍模型自己的 ω。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_position_env_d (ρ : Env M 19) (n h i : M.Domain) : Env M 22 :=
  ⟨fun j => Fin.addCases (motive := fun _ => M.Domain) ρ.bound (fun j : Fin 3 => [n, h, i].get j) j, ρ.free⟩

structure Tg_position_d (I : kpair_convention_l.Interpretation M) (r : Fin 3) (v : Fin 22 → M.Domain) : Prop where
  control : Formula.satisfies (⟨fun i => v (i.castAdd 3), fun _ => v 0⟩ : Env M 19) tg_control0_m
  round : M.mem (v 19) (v 0)
  time : M.mem (v 21) (v 0)
  history : Fn0_d (v 21) (v 12) (v 20)
  position : M.mem (v 20) (v 18)
  clock : M.IsOrdinalDivision I (v 21) (v 4) (v 19) (v ([1, 2, 3].get r))

def tg_position0_m (r : Fin 3) : Formula 1 22 := .conj
  (tg_control0_m.rename (fun i => i.castAdd 3))
  (let v : Fin 22 → Term 22 := Term.bound
   set[22] ⟪⌜v 19⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜v 21⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜v 21⌝ₛ, ⌜v 12⌝ₛ, ⌜v 20⌝ₛ) ∧
     ⌜v 20⌝ₛ ∈ ⌜v 18⌝ₛ ∧
     ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(⌜v 21⌝ₛ, ⌜v 4⌝ₛ, ⌜v 19⌝ₛ, ⌜v ([1, 2, 3].get r)⌝ₛ)⟫)

theorem tg_position0_closed_l (r : Fin 3) : (tg_position0_m r).FreeClosed := by
  simp -implicitDefEqProofs [tg_position0_m, Definitional.Formula.FreeClosed, tg_control0_closed_l]

theorem tg_position_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (r : Fin 3) (ρ : Env M 22) : Formula.satisfies ρ (tg_position0_m r) ↔ Tg_position_d I r ρ.bound := by
  simp only [tg_position0_m, Formula.satisfies_conj_iff, Formula.satisfies_rename,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_isOrdinalDivision_iff I hE]
  have head := Formula.closed_env_l tg_control0_m tg_control0_closed_l
    (ρ := ρ.reindex (fun i => i.castAdd 3))
    (η := ⟨fun i => ρ.bound (i.castAdd 3), fun _ => ρ.bound 0⟩) rfl
  exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨head.mp a, b, c, d, e, f⟩,
    fun h => ⟨head.mpr h.control, h.round, h.time, h.history, h.position, h.clock⟩⟩

/-- 换入新的轮号、历史和时刻，保留同一整份控制参数。 -/
theorem tg_position_build_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (r : Fin 3) (ρ : Env M 19) (n h i : M.Domain) (control : Formula.satisfies ρ tg_control0_m)
    (round : M.mem n (ρ.bound 0)) (time : M.mem i (ρ.bound 0)) (history : Fn0_d i (ρ.bound 12) h)
    (position : M.mem h (ρ.bound 18))
    (clock : M.IsOrdinalDivision I i (ρ.bound 4) n (ρ.bound ([1, 2, 3].get r))) :
    Formula.satisfies (tg_position_env_d ρ n h i) (tg_position0_m r) := by
  apply (tg_position_sat_l I hE _ _).mpr
  have head : Formula.satisfies
      (⟨fun k => (tg_position_env_d ρ n h i).bound (k.castAdd 3),
        fun _ => (tg_position_env_d ρ n h i).bound 0⟩ : Env M 19) tg_control0_m := by
    apply (Formula.closed_env_l tg_control0_m tg_control0_closed_l (ρ := ρ) (η := _) ?_).mp control
    funext k
    simp only [tg_position_env_d, Fin.addCases_left]
  have phase : (tg_position_env_d ρ n h i).bound ([1, 2, 3].get r) = ρ.bound ([1, 2, 3].get r) := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))) r
  exact ⟨head, round, time, history, position, phase.symm ▸ clock⟩

end YesMetaZFC.SetTheory.LargeCardinal
