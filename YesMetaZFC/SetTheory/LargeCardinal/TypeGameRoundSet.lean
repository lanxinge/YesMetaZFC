import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReadyStep

/-! # 地模型中的可继续轮状态集合

把原有限状态公式分离为真实关系 D。扩张中的归纳只读取 D 的规范像，
不在扩张的分离公理中使用任意地模型谓词。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_round_set_l (p : Tg_params_d M.Domain) (X R : M.Domain) :
    ∃ D, M.IsSetRelation I D ∧ ∀ n h, Rd_entry_d n h D ↔ M.mem h R ∧ Tg_ready_d hZF p X n h := by
  obtain ⟨C, union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) p.ω R
  let ρ : Env M 8 := ⟨fun i => [p.ω, p.e, p.c, p.b, p.δ, p.A, X, R].get i, fun _ => p.ω⟩
  let φ : BinarySchema 8 := {
    body := .conj (.mem .newest (.bound 9))
      (tg_ready_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 1) .newest) }
  have sat n h : φ.denote ρ n h ↔ M.mem h R ∧ Tg_ready_d hZF p X n h := by
    have h := tg_ready_sat_l hZF ((ρ.push n).push h)
      (⟨.bound 2, .bound 3, .bound 3, .bound 5, .bound 4, .bound 6, .bound 7,
        .bound 3, .bound 3, .bound 3, .bound 3, .bound 3⟩ : Tg_params_d (Term 10)) (.bound 8) (.bound 1) .newest
    exact and_congr Iff.rfl h
  obtain ⟨D, rel, read⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ C
  refine ⟨D, rel.1, fun n h => (read n h).trans ?_⟩
  exact ⟨fun h => (sat n _).mp h.2.2, fun h =>
    ⟨(union n).mpr (Or.inl h.2.1), (union _).mpr (Or.inr h.1), (sat n _).mpr h⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
