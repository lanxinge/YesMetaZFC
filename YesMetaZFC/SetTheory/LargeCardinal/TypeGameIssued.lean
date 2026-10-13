import YesMetaZFC.SetTheory.LargeCardinal.TypeGameControlMove

/-! # 已经落下的辅助走法及其原表项

前十九项为控制记录；其后依次为轮号、历史、走法、ℓ、t、κ、u、k、l、N、
B、U、D、四条弹性查询、程序长度与代码、七个程序槽位，末项为当前时刻。
此固定元数记录描述一次内部阶段；历史长度仍由模型自己的函数图给出。
同时保存产生这次走法的原前缀及全部辅助规则，供重置和继续分支共同读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_issued_slots_d {α : Type u} (v : Fin 46 → α) : Fin 7 → α :=
  Fin.cases (v 38) (Fin.cases (v 39) (Fin.cases (v 40)
    (Fin.cases (v 41) (Fin.cases (v 42) (Fin.cases (v 43) (fun _ => v 44))))))

/-- 实际回答沿用原请求：十四个自然数参数、临界点、两域、候选及标签图。 -/
def Tg_request_d (v : Fin 46 → M.Domain) (q : Fin 54 → M.Domain) : Prop :=
  ∀ i : Fin 19, q ([16, 17, 22, 23, 24, 36, 38, 47, 48, 49, 50, 51, 52, 53, 21, 31, 32, 34, 41].get i) =
    v ([0, 1, 26, 27, 28, 36, 37, 38, 39, 40, 41, 42, 43, 44, 24, 30, 31, 25, 23].get i)

def tg_issued_aux0_m : Formula 1 46 := .existsE (.conj
  (fseq_end_m (𝒞 := kpair_convention_l) (.bound 1) (.bound 21) .newest (.bound 22))
  (tg_aux_m (tg_control_params_d (fun i => (.bound (i.castAdd 27).succ : Term 47)))
    (.bound 20) .newest (.bound 22)))

theorem tg_issued_aux0_closed_l : tg_issued_aux0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_issued_aux0_m, Definitional.Formula.FreeClosed,
    tg_control_params_d]
  exact tg_aux_closed_l _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

structure Tg_issued_d (I : kpair_convention_l.Interpretation M) (v : Fin 46 → M.Domain) : Prop where
  control : Formula.satisfies (⟨fun i => v (i.castAdd 27), fun _ => v 0⟩ : Env M 19) tg_control0_m
  round : M.mem (v 19) (v 0)
  time : M.mem (v 45) (v 0)
  history : Fn0_d (v 45) (v 12) (v 20)
  position : M.mem (v 20) (v 18)
  clock : M.IsOrdinalDivision I (v 45) (v 4) (v 19) (v 2)
  event : Tg_event_d I (v 4) (v 19) (v 1) (v 20) (v 21)
  move : Tg_aux_data_d (v 21) (v 22) (v 23) (v 24) (v 25)
  bound : M.mem (v 24) (v 5)
  labels : Fn0_d (v 26) (v 0) (v 23)
  first : M.SuccessorOf (v 27) (v 26)
  last : M.SuccessorOf (v 28) (v 27)
  elastic : Tg_ee_data_d (v 9) (v 24) (v 27) (v 29) (v 30) (v 31) ⟨v 32, v 33, v 34, v 35⟩
  program : Tg_program_data_d (v 10) (v 27) (v 36) (v 37) (tg_issued_slots_d v)
  auxiliary : Formula.satisfies (⟨v, fun _ => v 0⟩ : Env M 46) tg_issued_aux0_m

def tg_issued0_m : Formula 1 46 := .conj
  (tg_control0_m.rename (fun i => i.castAdd 27))
  (.conj (let v : Fin 46 → Term 46 := Term.bound
   set[46] ⟪⌜v 19⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜v 45⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜v 45⌝ₛ, ⌜v 12⌝ₛ, ⌜v 20⌝ₛ) ∧
    ⌜v 20⌝ₛ ∈ ⌜v 18⌝ₛ ∧ ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(⌜v 45⌝ₛ, ⌜v 4⌝ₛ, ⌜v 19⌝ₛ, ⌜v 2⌝ₛ) ∧
    ⌜tg_event_m⌝ₚ(⌜v 4⌝ₛ, ⌜v 19⌝ₛ, ⌜v 1⌝ₛ, ⌜v 20⌝ₛ, ⌜v 21⌝ₛ) ∧
    ⌜tg_aux_data_m⌝ₚ(⌜v 21⌝ₛ, ⌜v 22⌝ₛ, ⌜v 23⌝ₛ, ⌜v 24⌝ₛ, ⌜v 25⌝ₛ) ∧
    ⌜v 24⌝ₛ ∈ ⌜v 5⌝ₛ ∧
    ⌜fn0_m⌝ₚ(⌜v 26⌝ₛ, ⌜v 0⌝ₛ, ⌜v 23⌝ₛ) ∧ ⌜Formula.isSuccessor⌝ₚ(⌜v 27⌝ₛ, ⌜v 26⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(⌜v 28⌝ₛ, ⌜v 27⌝ₛ) ∧
    ⌜tg_ee_data_m⌝ₚ(⌜v 9⌝ₛ, ⌜v 24⌝ₛ, ⌜v 27⌝ₛ, ⌜v 29⌝ₛ, ⌜v 30⌝ₛ, ⌜v 31⌝ₛ,
      ⌜v 32⌝ₛ, ⌜v 33⌝ₛ, ⌜v 34⌝ₛ, ⌜v 35⌝ₛ) ∧
    ⌜fun P n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P n b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜v 10⌝ₛ, ⌜v 27⌝ₛ, ⌜v 36⌝ₛ, ⌜v 37⌝ₛ, ⌜v 38⌝ₛ, ⌜v 39⌝ₛ, ⌜v 40⌝ₛ,
        ⌜v 41⌝ₛ, ⌜v 42⌝ₛ, ⌜v 43⌝ₛ, ⌜v 44⌝ₛ)⟫) tg_issued_aux0_m)

theorem tg_issued0_closed_l : tg_issued0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_issued0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ,
    tg_control0_closed_l, tg_issued_aux0_closed_l]

theorem tg_issued_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) (ρ : Env M 46) :
    Formula.satisfies ρ tg_issued0_m ↔ Tg_issued_d I ρ.bound := by
  simp only [tg_issued0_m, Formula.satisfies_conj_iff, Formula.satisfies_rename,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Formula.satisfies_isOrdinalDivision_iff I hE,
    tg_event_sat_l I hE, tg_aux_data_sat_l hE, Formula.satisfies_isSuccessor_iff,
    tg_ee_data_sat_l hE, tg_program_data_sat_l hE]
  have head := Formula.closed_env_l tg_control0_m tg_control0_closed_l
    (ρ := ρ.reindex (fun i => i.castAdd 27))
    (η := ⟨fun i => ρ.bound (i.castAdd 27), fun _ => ρ.bound 0⟩) rfl
  have aux := Formula.closed_env_l tg_issued_aux0_m tg_issued_aux0_closed_l
    (ρ := ρ) (η := ⟨ρ.bound, fun _ => ρ.bound 0⟩) rfl
  exact ⟨fun ⟨a, ⟨b, c, d, e, f, g, h, i, j, k, l, m, n⟩, o⟩ =>
      ⟨head.mp a, b, c, d, e, f, g, h, i, j, k, l, m, n, aux.mp o⟩,
    fun h => ⟨head.mpr h.control, ⟨h.round, h.time, h.history, h.position, h.clock,
      h.event, h.move, h.bound, h.labels, h.first, h.last, h.elastic, h.program⟩, aux.mpr h.auxiliary⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
