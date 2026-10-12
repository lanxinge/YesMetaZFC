import YesMetaZFC.SetTheory.LargeCardinal.TypeGameResetInput

/-! # 重置输入的原公式总构造

新三十八个坐标全部由存在量词产生，并逐项连接原树、原走法和固定程序表。
此有限公式作为控制记录的一部分反射，后续重置直接得到同一更新输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- 后十个参数为 ω,e,δ,S,ν,E,P、当前辅助走法、轮号和原字母表。
def tg_reset_body0_m : Formula 1 48 := .conj
  (tg_seed0_m.rename (fun i => ⟨i.val, by omega⟩))
  (let v : Fin 48 → Term 48 := Term.bound
   set[48] ⟪⌜v 0⌝ₛ = ⌜v 38⌝ₛ ∧ ⌜v 1⌝ₛ = ⌜v 39⌝ₛ ∧ ⌜v 2⌝ₛ = ⌜v 40⌝ₛ ∧
    ⌜v 3⌝ₛ = ⌜v 41⌝ₛ ∧ ⌜v 4⌝ₛ = ⌜v 42⌝ₛ ∧ ⌜v 6⌝ₛ = ⌜v 39⌝ₛ ∧ ⌜v 23⌝ₛ = ⌜v 5⌝ₛ ∧
    ⌜v 24⌝ₛ = ⌜v 39⌝ₛ ∧ ⌜v 25⌝ₛ = ⌜v 39⌝ₛ ∧ ⌜v 26⌝ₛ = ⌜v 39⌝ₛ ∧
    (∃ ℓ, ⌜tg_aux_data_m⌝ₚ(⌜v 45⌝ₛ, ℓ, ⌜v 25⌝ₛ, ⌜v 5⌝ₛ, ⌜v 18⌝ₛ)) ∧
    ⌜tg_ee_data_m⌝ₚ(⌜v 43⌝ₛ, ⌜v 5⌝ₛ, ⌜v 7⌝ₛ, ⌜v 14⌝ₛ, ⌜v 15⌝ₛ, ⌜v 16⌝ₛ,
      ⌜v 27⌝ₛ, ⌜v 28⌝ₛ, ⌜v 29⌝ₛ, ⌜v 30⌝ₛ) ∧
    ⌜fun P n b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P n b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜v 44⌝ₛ, ⌜v 7⌝ₛ, ⌜v 20⌝ₛ, ⌜v 22⌝ₛ, ⌜v 31⌝ₛ, ⌜v 32⌝ₛ, ⌜v 33⌝ₛ, ⌜v 34⌝ₛ, ⌜v 35⌝ₛ, ⌜v 36⌝ₛ, ⌜v 37⌝ₛ) ∧
      (⌜v 46⌝ₛ = ⌜v 39⌝ₛ → ⌜v 47⌝ₛ ∈ ⌜v 14⌝ₛ)⟫)

theorem tg_reset_body0_closed_l : tg_reset_body0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_reset_body0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]

def tg_reset_result0_m : Formula 1 10 := rt_exists_m 38 tg_reset_body0_m

theorem tg_reset_result0_closed_l : tg_reset_result0_m.FreeClosed :=
  (rt_exists_closed_l _).mpr tg_reset_body0_closed_l

def tg_reset_result_m {d} (ω e δ S ν E P a n A : Term d) : Formula 1 d :=
  tg_reset_result0_m.bind (fun i => [ω, e, δ, S, ν, E, P, a, n, A].get i)

@[simp] theorem tg_reset_result_closed_l {d} (ω e δ S ν E P a n A : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hd : δ.freeSupport = []) (hS : S.freeSupport = [])
    (hν : ν.freeSupport = []) (hE : E.freeSupport = []) (hP : P.freeSupport = [])
    (ha : a.freeSupport = []) (hn : n.freeSupport = [])
    (hA : A.freeSupport = []) : (tg_reset_result_m ω e δ S ν E P a n A).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_reset_result0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, he, hd, hS, hν, hE, hP, ha, hn, hA, fun i => Fin.elim0 i⟩

theorem Tg_setup_d.reset_result_l (hZFC : M.Models ZFC) {p : Tg_params_d M.Domain} {X n h a ℓ κ u : M.Domain}
    (setup : Tg_setup_d hZFC p X) (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p.δ)
    (root : M.mem p.e p.S) (aux : Tg_aux_d (ZFC.models_zf_l hZFC) p n h a) (data : Tg_aux_data_d a ℓ p.e κ u) :
    Formula.satisfies (⟨fun i => [p.ω, p.e, p.δ, p.S, p.ν, p.E, p.P, a, n, p.A].get i, fun _ => p.ω⟩ : Env M 10)
      tg_reset_result0_m := by
  let ρ : Env M 10 := ⟨fun i => [p.ω, p.e, p.δ, p.S, p.ν, p.E, p.P, a, n, p.A].get i, fun _ => p.ω⟩
  obtain ⟨v, seed, eq, hk, hb, hs, ht, hg, move, elastic, program, letters⟩ := setup.reset_input_l hZFC woodin root aux data
  apply (rt_exists_sat_l (n := 38) ρ tg_reset_body0_m).mpr
  refine ⟨v, (Formula.satisfies_conj_iff ..).mpr ⟨?_, ?_⟩⟩
  · apply (Formula.satisfies_rename ..).mpr
    exact (Formula.closed_env_l tg_seed0_m tg_seed0_closed_l
      (ρ := ⟨fun i => (rt_push_d ρ 38 v).bound ⟨i.val, by omega⟩, (rt_push_d ρ 38 v).free⟩)
      (η := ⟨v, fun _ => p.ω⟩) (funext (rt_push_new_l ρ v))).mpr seed
  · simp only [Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq (ZFC.models_zf_l hZFC).1,
      Formula.satisfies_exists_iff, tg_aux_data_sat_l (ZFC.models_zf_l hZFC).1, tg_ee_data_sat_l (ZFC.models_zf_l hZFC).1,
      tg_program_data_sat_l (ZFC.models_zf_l hZFC).1, tt_eval_cases_l, Definitional.Term.eval_weaken,
      Formula.satisfies_imp_iff, Formula.satisfies_mem_iff]
    exact ⟨eq 0, eq 1, eq 2, eq 3, eq 4, hk, hb, hs, ht, hg, ⟨ℓ, move⟩, elastic, program, letters⟩

def tg_reset_control_m {d} (p : Tg_params_d (Term d)) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken)
  set[d] ⟪∀ n h a, ⌜fun n h a => tg_aux_m q n h a⌝ₚ(n, h, a) →
    (∃ ℓ κ u, ⌜tg_aux_data_m⌝ₚ(a, ℓ, ⌜p.e⌝ₛ, κ, u)) →
    ⌜tg_reset_result_m⌝ₚ
      (⌜p.ω⌝ₛ, ⌜p.e⌝ₛ, ⌜p.δ⌝ₛ, ⌜p.S⌝ₛ, ⌜p.ν⌝ₛ, ⌜p.E⌝ₛ, ⌜p.P⌝ₛ, a, n, ⌜p.A⌝ₛ)⟫

theorem tg_reset_control_closed_l {d} (p : Tg_params_d (Term d)) (hp : p.closed_l) :
    (tg_reset_control_m p).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using hp
  rcases hp with ⟨hw, he, _, _, _, hd, hA, hS, hν, hE, hP, _⟩
  simp -implicitDefEqProofs [tg_reset_control_m, Definitional.Formula.FreeClosed, hw, he, hd, hA, hS, hν, hE, hP]
  exact tg_aux_closed_l _ _ _ _ hp' rfl rfl rfl

theorem tg_reset_control_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (p : Tg_params_d (Term d)) {X : M.Domain}
    (setup : Tg_setup_d hZFC (p.map_l (fun t => t.eval ρ)) X)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (p.δ.eval ρ))
    (root : M.mem (p.e.eval ρ) (p.S.eval ρ)) : Formula.satisfies ρ (tg_reset_control_m p) := by
  simp only [tg_reset_control_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, tg_aux_sat_l (ZFC.models_zf_l hZFC), tg_aux_data_sat_l (ZFC.models_zf_l hZFC).1,
    tg_reset_result_m, Formula.satisfies_bind, Tg_params_d.map_l, Definitional.Term.eval_weaken]
  intro n h a aux reset
  obtain ⟨ℓ, κ, u, data⟩ := reset
  have result := setup.reset_result_l hZFC woodin root aux data
  refine (Formula.closed_env_l tg_reset_result0_m tg_reset_result0_closed_l
    (ρ := ⟨fun i => [(p.ω.eval ρ), (p.e.eval ρ), (p.δ.eval ρ), (p.S.eval ρ), (p.ν.eval ρ), (p.E.eval ρ), (p.P.eval ρ), a, n, p.A.eval ρ].get i,
      fun _ => p.ω.eval ρ⟩) (η := _) ?_).mp result
  have eval (t : Term d) : t.eval ρ = t.weaken.weaken.weaken.eval (((ρ.push n).push h).push a) := by
    simp only [Definitional.Term.eval_weaken]
  funext i
  exact Fin.cases (eval p.ω) (Fin.cases (eval p.e) (Fin.cases (eval p.δ) (Fin.cases (eval p.S)
    (Fin.cases (eval p.ν) (Fin.cases (eval p.E) (Fin.cases (eval p.P) (Fin.cases rfl (Fin.cases rfl
      (Fin.cases (eval p.A) (fun j => Fin.elim0 j)))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
