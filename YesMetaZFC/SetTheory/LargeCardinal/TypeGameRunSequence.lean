import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunNext
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunAdvance
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameTreeStep
import YesMetaZFC.Model.SetTheory.ClassChoice

/-! # 统一历史的实际内部 ω 递归

原策略给出首轮，已证明的完整后继同时处理重置和继续。类依赖选择对这条
原一阶关系收集整列模型、树和历史，不预设统一秩界，也不假定外部 ω 标准。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_run_code_d.advance_l {ω c₀ o C γ Z A n s x : M.Domain}
    (h : Tg_run_code_d hZF ω c₀ o C γ Z A n s) (ho : ∀ z, ¬ M.mem z o)
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z) (hAZ : M.mem A Z) (hx : M.mem x A) :
    ∃ m t, M.SuccessorOf m n ∧ Tg_run_code_d hZF ω c₀ o C γ Z A m t ∧ Tg_run_edge_d hZF ω c₀ s t := by
  obtain ⟨q, code, run, num⟩ := h
  obtain ⟨v, u, next, edge⟩ := run.advance_l hZFC ho hγ hωZ hAZ hx
  have copy := edge
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, succ, _⟩ := copy
  have succ : M.SuccessorOf (u 19) n := num ▸ succ
  let r : Fin 64 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v u
  obtain ⟨t, code'⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) r
  have valid : Tg_run_code_d hZF ω c₀ o C γ Z A (u 19) t := by
    refine ⟨r, code', ?_, rfl⟩
    simpa only [r, Fin.addCases_left, Fin.addCases_right] using next
  let z : Fin 128 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) q r
  refine ⟨u 19, t, succ, valid, z, ?_, ?_, ?_⟩
  · simpa only [z, Fin.addCases_left] using code
  · simpa only [z, Fin.addCases_right] using code'
  · simpa only [z, r, Fin.addCases_left, Fin.addCases_right] using edge

def tg_run_index_m {d} (ω c₀ o C γ Z A i s : Term d) : Formula 1 d := set[d] ⟪
  ∃ n, ⌜KP.succ0_m⌝ₚ(n, ⌜i⌝ₛ) ∧ ⌜tg_run_code_m⌝ₚ(⌜ω⌝ₛ, ⌜c₀⌝ₛ, ⌜o⌝ₛ, ⌜C⌝ₛ, ⌜γ⌝ₛ, ⌜Z⌝ₛ, ⌜A⌝ₛ, n, ⌜s⌝ₛ)⟫
derive_free_closed tg_run_index_m

theorem tg_run_index_sat_l (h : M.Models ZF) {d} (η : Env M d) (ω c₀ o C γ Z A i s : Term d) :
    Formula.satisfies η (tg_run_index_m ω c₀ o C γ Z A i s) ↔ ∃ n, M.SuccessorOf n (i.eval η) ∧
      Tg_run_code_d h (ω.eval η) (c₀.eval η) (o.eval η) (C.eval η) (γ.eval η) (Z.eval η) (A.eval η) n (s.eval η) := by
  simp only [tg_run_index_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    KP.succ0_sat_l h.1, tg_run_code_sat_l h, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

/-- 从原 II 获胜策略出发，统一构造所有内部有限轮，并保留每次真实的两边扩张。 -/
theorem Tg_game_d.history_sequence_l {p : Tg_params_d M.Domain} {A F₀ L₀ G₀ J₀ B₀ W₀ O Z g σ x : M.Domain}
    (game : Tg_game_d hZFC p A F₀ L₀ G₀ J₀ B₀ W₀ O Z g) (woodin : Woodin_d I p.δ) (root : M.mem p.e p.S)
    (win : Cg_win_d I false p.ω A F₀ J₀ B₀ W₀ σ) (hx : M.mem x p.A) :
    ∃ θ X R c C γ V D f s₀, M.IsRegularCardinal I θ ∧ V_d I θ X ∧ Smem_d I c X R ∧
      M.IsLimitOrdinal γ ∧ M.mem p.ω V ∧ M.mem p.A V ∧ Fn0_d p.ω D f ∧ Rd_entry_d p.e s₀ f ∧
      Tg_run_code_d hZF p.ω c p.e C γ V p.A p.a s₀ ∧
      (∀ i s, Rd_entry_d i s f → ∃ n, M.SuccessorOf n i ∧ Tg_run_code_d hZF p.ω c p.e C γ V p.A n s) ∧
      ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s f → Rd_entry_d j t f → Tg_run_edge_d hZF p.ω c s t := by
  obtain ⟨θ, X, R, c, C, γ, V, regular, rank, model, limit, hωV, hAV, initial⟩ := game.run_start_l hZFC woodin root win
  obtain ⟨v, u, run, num⟩ := initial x hx
  obtain ⟨s₀, start⟩ := run.pack_l hZF
  have start : Tg_run_code_d hZF p.ω c p.e C γ V p.A p.a s₀ := num ▸ start
  let η : Env M 7 := ⟨fun i => [p.ω,c,p.e,C,γ,V,p.A].get i, fun _ => p.ω⟩
  let B : BinarySchema 7 := { body := tg_run_index_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest }
  let φ : UnarySchema 9 := { body := tg_run_edge_m (.bound 3) (.bound 4) (.bound 1) .newest }
  have valid i s : B.denote η i s ↔ ∃ n, M.SuccessorOf n i ∧ Tg_run_code_d hZF p.ω c p.e C γ V p.A n s :=
    tg_run_index_sat_l hZF ..
  have step i s t : φ.denote ((η.push i).push s) t ↔ Tg_run_edge_d hZF p.ω c s t := tg_run_edge_sat_l hZF ..
  obtain ⟨D, f, fn, first, all, edges⟩ := ZFC.class_indexed_choice_l I hZFC B φ η game.setup.omega game.setup.empty
    ((valid p.e s₀).mpr ⟨p.a, game.setup.one, start⟩) (by
      intro i j s _ succ hs
      obtain ⟨n, ns, run⟩ := (valid i s).mp hs
      obtain ⟨m, t, mt, next, edge⟩ := run.advance_l hZFC game.setup.empty limit hωV hAV hx
      have en : n = j := ns.eq hZF.1 succ
      exact ⟨t, (valid j t).mpr ⟨m, en ▸ mt, next⟩, (step i s t).mpr edge⟩)
  exact ⟨θ, X, R, c, C, γ, V, D, f, s₀, regular, rank, model, limit, hωV, hAV,
    fn0_of_function_l (ZF.modelsKP hZF) fn, first, start, fun i s hs => (valid i s).mp (all i s hs),
    fun i j s t succ hs ht => (step i s t).mp (edges i j s t succ hs ht)⟩

end YesMetaZFC.SetTheory.LargeCardinal
