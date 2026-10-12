import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAuxiliary

/-! # 玩家 I 的回答：原规则 (7) 及唯一新增的空根条件

回答读取固定的子类型程序、源 dcp 查询域及目标端点查询。这里没有把
可实现性列为额外规则；原定义的子类型查询为真时，已有读取定理自行恢复实际实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def tg_reply0_m : Formula 1 22 :=
  let ω := Term.bound 0; let l := Term.bound 1; let n := Term.bound 2; let κ := Term.bound 3
  let τ := Term.bound 4; let U := Term.bound 5; let D := Term.bound 6; let W := Term.bound 7
  let u := Term.bound 8; let w := Term.bound 9; let b := Term.bound 10; let z := Term.bound 11
  let r := Term.bound 12; let q := Term.bound 13; let h := Term.bound 14
  let σ : Fin 7 → Term 22 := Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
    (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21))))))
  .conj (Formula.subset w W) (.existsE (.conj (td_dcp_m l.weaken n.weaken D.weaken u.weaken .newest)
    (.conj (ts_subtype_m ω.weaken l.weaken κ.weaken τ.weaken n.weaken U.weaken w.weaken b.weaken z.weaken .newest
      (fun j => (σ j).weaken)) (.conj (.mem r.weaken w.weaken) (.conj (.mem q.weaken w.weaken) (.mem h.weaken w.weaken))))))

theorem tg_reply0_closed_l : tg_reply0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_reply0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]

def tg_reply_m {d} (ω l n κ τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d) : Formula 1 d :=
  tg_reply0_m.bind (fun i => [ω, l, n, κ, τ, U, D, W, u, w, b, z, r, q, h,
    σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i)

@[simp] theorem tg_reply_closed_l {d} (ω l n κ τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d)
    (hw : ω.freeSupport = []) (hl : l.freeSupport = []) (hn : n.freeSupport = []) (hk : κ.freeSupport = [])
    (ht : τ.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = []) (hW : W.freeSupport = [])
    (hu : u.freeSupport = []) (hv : w.freeSupport = []) (hb : b.freeSupport = []) (hz : z.freeSupport = [])
    (hr : r.freeSupport = []) (hq : q.freeSupport = []) (hh : h.freeSupport = []) (hσ : ∀ j, (σ j).freeSupport = []) :
    (tg_reply_m ω l n κ τ U D W u w b z r q h σ).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_reply0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw, hl, hn, hk, ht, hU, hD, hW, hu, hv, hb, hz, hr, hq, hh,
    hσ 0, hσ 1, hσ 2, hσ 3, hσ 4, hσ 5, hσ 6, fun i => Fin.elim0 i⟩

theorem tg_reply_sat_l {d} (ρ : Env M d) (ω l n κ τ U D W u w b z r q h : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (tg_reply_m ω l n κ τ U D W u w b z r q h σ) ↔ Tg_reply_d I
      (ω.eval ρ) (l.eval ρ) (n.eval ρ) (κ.eval ρ) (τ.eval ρ) (U.eval ρ) (D.eval ρ) (W.eval ρ)
      (u.eval ρ) (w.eval ρ) (b.eval ρ) (fun j => (σ j).eval ρ) (z.eval ρ) ⟨r.eval ρ, q.eval ρ, h.eval ρ⟩ := by
  simp only [tg_reply_m, Formula.satisfies_bind, tg_reply0_m, Tg_reply_d,
    Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_exists_iff, td_dcp_sat_l I hZF.1, ts_subtype_sat_l (ZF.modelsKP hZF),
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  have eq : (fun i => (Fin.cases (.bound 15) (Fin.cases (.bound 16) (Fin.cases (.bound 17)
      (Fin.cases (.bound 18) (Fin.cases (.bound 19) (Fin.cases (.bound 20) (fun _ => .bound 21)))))) i : Term 22).eval
      (Definitional.Env.substitute ρ (fun i => [ω, l, n, κ, τ, U, D, W, u, w, b, z, r, q, h,
        σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6].get i))) = (fun i => (σ i).eval ρ) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  rw [eq]
  rfl

def Tg_answer_d (p : Tg_params_d M.Domain) (n h v : M.Domain) : Prop :=
  ∃ a ℓ t κ u τ w k l N B U D g₀ g₁ g₂ g₃ C V W r m q f j b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
    Tg_event_d I p.c n p.e h a ∧ Tg_aux_data_d a ℓ t κ u ∧ KPair_d M v τ w ∧
    Fn0_d k p.ω t ∧ M.SuccessorOf l k ∧ M.SuccessorOf N l ∧
    Tg_ee_data_d p.E κ l B U D ⟨g₀, g₁, g₂, g₃⟩ ∧ M.mem τ p.δ ∧ Tg_query_request_d hZF p.ω τ k p.e p.e ∧
    Tg_query_data_d p.Q τ k p.e p.e C V W r m q f j ∧
    Tg_program_data_d p.P l b z (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃
      (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆))))))) ∧
    Tg_reply_d I p.ω l N κ τ U D W u w b (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂
      (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆))))))) z ⟨r, q, f⟩

def tg_answer0_m : Formula 1 15 :=
  let p : Tg_params_d (Term 15) := ⟨.bound 0, .bound 1, .bound 2, .bound 3, .bound 4, .bound 5,
    .bound 6, .bound 7, .bound 8, .bound 9, .bound 10, .bound 11⟩
  let n := Term.bound 12; let h := Term.bound 13; let v := Term.bound 14
  set[15] ⟪
  ∃ a ℓ t κ u τ w k l N B U D g₀ g₁ g₂ g₃ C V W r m q f j b z s₀ s₁ s₂ s₃ s₄ s₅ s₆,
  ⌜tg_event_m⌝ₚ(⌜p.c⌝ₛ, ⌜n⌝ₛ, ⌜p.e⌝ₛ, ⌜h⌝ₛ, a) ∧ ⌜tg_aux_data_m⌝ₚ(a, ℓ, t, κ, u) ∧ ⌜kpair0_m⌝ₚ(⌜v⌝ₛ, τ, w) ∧
  ⌜fn0_m⌝ₚ(k, ⌜p.ω⌝ₛ, t) ∧ ⌜Formula.isSuccessor⌝ₚ(l, k) ∧ ⌜Formula.isSuccessor⌝ₚ(N, l) ∧
  ⌜tg_ee_data_m⌝ₚ(⌜p.E⌝ₛ, κ, l, B, U, D, g₀, g₁, g₂, g₃) ∧ τ ∈ ⌜p.δ⌝ₛ ∧
  ⌜tg_query_request_m⌝ₚ(⌜p.ω⌝ₛ, τ, k, ⌜p.e⌝ₛ, ⌜p.e⌝ₛ) ∧ ⌜tg_query_data_m⌝ₚ(⌜p.Q⌝ₛ, τ, k, ⌜p.e⌝ₛ, ⌜p.e⌝ₛ, C, V, W, r, m, q, f, j) ∧
  ⌜fun P l b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P l b z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜p.P⌝ₛ, l, b, z, s₀, s₁, s₂, s₃, s₄, s₅, s₆) ∧
  ⌜fun ω l N κ τ U D W u w b z r q f s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_reply_m ω l N κ τ U D W u w b z r q f
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜p.ω⌝ₛ, l, N, κ, τ, U, D, W, u, w, b, z, r, q, f, s₀, s₁, s₂, s₃, s₄, s₅, s₆)⟫

@[simp] theorem tg_answer0_closed_l : tg_answer0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_answer0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]

def tg_answer_m {d} (p : Tg_params_d (Term d)) (n h v : Term d) : Formula 1 d :=
  tg_answer0_m.bind (fun i => [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, n, h, v].get i)

@[simp] theorem tg_answer_closed_l {d} (p : Tg_params_d (Term d)) (n h v : Term d)
    (hp : p.closed_l) (hn : n.freeSupport = []) (hh : h.freeSupport = []) (hv : v.freeSupport = []) :
    (tg_answer_m p n h v).FreeClosed := by
  rcases hp with ⟨hω, he, ha, hb, hc, hδ, hA, hS, hν, hE, hP, hQ⟩
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_answer0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hω, he, ha, hb, hc, hδ, hA, hS, hν, hE, hP, hQ, hn, hh, hv, fun i => Fin.elim0 i⟩

theorem tg_answer_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (n h v : Term d) :
    Formula.satisfies ρ (tg_answer_m p n h v) ↔ Tg_answer_d hZF (p.map_l (fun t => t.eval ρ)) (n.eval ρ) (h.eval ρ) (v.eval ρ) := by
  simp only [tg_answer_m, Formula.satisfies_bind, tg_answer0_m, Tg_answer_d, Tg_params_d.map_l,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    tg_event_sat_l I hZF.1, tg_aux_data_sat_l hZF.1, kpair0_sat_l hZF.1, fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff,
    tg_ee_data_sat_l hZF.1, Formula.satisfies_mem_iff, tg_query_request_sat_l hZF, tg_query_data_sat_l hZF.1,
    tg_program_data_sat_l hZF.1, tg_reply_sat_l hZF, tt_eval_cases_l, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
