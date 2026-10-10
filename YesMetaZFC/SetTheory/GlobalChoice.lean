import YesMetaZFC.SetTheory.Definitional.Project.GlobalOrder
import YesMetaZFC.SetTheory.Choice

/-! # 可定义全局良序产生原选择集公理

在并集内分离各成员的最小元。唯一性仅用严格序律；不选择外部函数。
-/
namespace YesMetaZFC.SetTheory.ZF
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem gw_choice_l (hZF : M.Models ZF) (φ : BinarySchema 0)
    (h : M.SatisfiesSentence (gw_sentence_s φ)) : M.SatisfiesSentence Axioms.choice := by
  rw [Structure.satisfiesSentence_iff]
  intro f
  have hw := (gw_sentence_sat_l hZF.1 φ (⟨Fin.elim0, f⟩ : Env M 0)).mp
    ((Structure.satisfiesSentence_iff M (gw_sentence_s φ)).mp h f)
  simp only [Axioms.choice, Sentence.ofFormula, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Formula.extensionalNe, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken]
  intro A hA
  let ρ : Env M 1 := ⟨fun _ => A, f⟩
  let ψ : UnarySchema 1 := {
    body := Formula.existsMem (.bound 1)
      (.conj (.mem (.bound 1) .newest) (Formula.forallMem .newest
        (.disj (Formula.extensionalEq (.bound 2) .newest)
          (binary_pred_m φ Fin.elim0 (.bound 2) .newest)))) }
  have rel (η : Env M 4) : Formula.satisfies η (binary_pred_m φ Fin.elim0 (.bound 2) .newest) ↔
      φ.denote ⟨Fin.elim0, f⟩ (η.bound 2) (η.bound 0) := by
    rw [binary_pred_sat_l]
    exact Formula.closed_env_l _ φ.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))
  have sat x : ψ.denote ρ x ↔ ∃ a, M.mem a A ∧ M.mem x a ∧
      ∀ y, M.mem y a → x = y ∨ φ.denote ⟨Fin.elim0, f⟩ x y := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, rel]
    rfl
  obtain ⟨U, hU⟩ := KP.exists_union (modelsKP hZF) A
  obtain ⟨C, hC⟩ := separation_exists_d hZF ψ ρ U
  refine ⟨C, fun a ha => ?_⟩
  obtain ⟨x, hx, hm⟩ := hw.2.2.2.1 a (hA.1 a ha)
  refine ⟨x, ⟨(hC x).mpr ⟨(hU x).mpr ⟨a, ha, hx⟩, (sat x).mpr ⟨a, ha, hx, hm⟩⟩, hx⟩, ?_⟩
  intro y hy
  obtain ⟨b, hb, hyb, hmin⟩ := (sat y).mp ((hC y).mp hy.1).2
  have eq : a = b := by
    apply Classical.byContradiction
    exact fun hn => hA.2 a ha b hb hn ⟨y, hy.2, hyb⟩
  subst b
  rcases hm y hy.2 with he | hxy
  · exact he.symm
  · exact (hmin x hx).elim id (fun hyx => (hw.1 y (hw.2.1 y x y hyx hxy)).elim)

theorem gw_zfc_l (hZF : M.Models ZF) (φ : BinarySchema 0)
    (h : M.SatisfiesSentence (gw_sentence_s φ)) : M.Models ZFC := by
  refine ⟨hZF.1, fun s hs => ?_⟩
  cases hs with
  | zf hs => exact hZF.2 s hs
  | choice => exact gw_choice_l hZF φ h

end YesMetaZFC.SetTheory.ZF
