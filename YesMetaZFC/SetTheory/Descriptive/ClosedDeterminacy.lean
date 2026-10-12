import YesMetaZFC.SetTheory.Descriptive.GameAvoidRun

/-! # 集合字母表上的闭博弈决定性

Gale–Stewart 证明采用 Neeman 4.16 的获胜局面集合：空局面若属于 II
获胜区便已有策略；否则 I 避开该区，所有有限前缀因而都在收益树中。
时序 J 任意，允许同一玩家连续行动；全程使用模型内部历史、策略与对局。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Cg_det_d (ω X F J B W : M.Domain) : Prop :=
  (∃ σ, Cg_win_d I true ω X F J B W σ) ∨ ∃ τ, Cg_win_d I false ω X F J B W τ

def cg_det_m {d} (ω X F J B W : Term d) : Formula 1 d := .disj
  (.existsE (cg_win_m true ω.weaken X.weaken F.weaken J.weaken B.weaken W.weaken .newest))
  (.existsE (cg_win_m false ω.weaken X.weaken F.weaken J.weaken B.weaken W.weaken .newest))
derive_free_closed cg_det_m

theorem cg_det_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X F J B W : Term d) :
    Formula.satisfies ρ (cg_det_m ω X F J B W) ↔ Cg_det_d I
      (ω.eval ρ) (X.eval ρ) (F.eval ρ) (J.eval ρ) (B.eval ρ) (W.eval ρ) := by
  simp only [cg_det_m, Cg_det_d, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    cg_win_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZF)

/-- 全部内部有限历史中的树体作为 I 收益时，至少一方有实际内部获胜策略。 -/
theorem cg_tree_det_l {ω X F J B W T a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d K ω X F) (runs : M.IsFunctionSpace K B ω X)
    (body : Body_d F B T W) (ha : M.mem a X) : Cg_det_d K ω X F J B W := by
  classical
  obtain ⟨Z, strategies⟩ := ZF.exists_functionSpace hZF K F X
  obtain ⟨Q, positions⟩ := cg_ii_l K hZF ω X F J B W
  obtain ⟨e, he, _⟩ := hω.1.1
  by_cases root : M.mem e Q
  · obtain ⟨_, σ, win⟩ := (positions e).mp root
    exact Or.inr ⟨σ, win.root_l K he⟩
  · obtain ⟨σ, fn, avoid⟩ := cg_avoid_l hZFC hω space runs strategies positions ha
    refine Or.inl ⟨σ, fn, fun f hf follows => (body f).mpr ⟨hf, fun s hs sf => ?_⟩⟩
    apply Classical.byContradiction
    intro bad
    exact cg_avoid_run_l hZF hω space runs strategies positions he root avoid hf follows s hs sf
      (cg_ii_bad_l hZF positions body hs bad ha)

/-- 相对补集开放的收益集合均决定；前缀树由闭集本身自动构造。 -/
theorem cg_closed_det_l {ω X F J B W O a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d K ω X F) (runs : M.IsFunctionSpace K B ω X) (ha : M.mem a X)
    (sub : M.MemberSubset W B) (complement : ∀ f, M.mem f O ↔ M.mem f B ∧ ¬ M.mem f W)
    (opened : Open_d F B O) : Cg_det_d K ω X F J B W := by
  obtain ⟨T, _, _, body⟩ := tree_of_closed_l (ZF.modelsKP hZF) sub complement opened
  exact cg_tree_det_l hZFC hω space runs body ha

end YesMetaZFC.SetTheory.Descriptive
