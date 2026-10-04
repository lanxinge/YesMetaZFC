import YesMetaZFC.SetTheory.Filter.Countable
import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 内部有限测度约束的共同细化

对模型自身的有限长度作原公式归纳；只用滤子基的二元细化，不要求可数完备。
-/
namespace YesMetaZFC.SetTheory.FilterZF
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Mt_d (n U F C : M.Domain) : Prop := M.mem C U ∧
  ∀ i B, M.mem i n → Rd_entry_d i B F → M.MemberSubset C B

def mt_m {d} (n U F C : Term d) : Formula 1 d := .conj (.mem C U) (.forallE (.forallE
  (.imp (.mem (.bound 1) n.weaken.weaken) (.imp (rd_entry_m (.bound 1) .newest F.weaken.weaken)
    (Formula.subset C.weaken.weaken .newest)))))
derive_free_closed mt_m

theorem mt_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n U F C : Term d) :
    Formula.satisfies ρ (mt_m n U F C) ↔ Mt_d (n.eval ρ) (U.eval ρ) (F.eval ρ) (C.eval ρ) := by
  simp only [mt_m, Mt_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, rd_entry_sat_l hE,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

theorem finite_meet_l (hZF : M.Models ZF) {ω D U : M.Domain} (hω : M.IsOmega ω) (hU : Base_d D U) :
    ∀ n, M.mem n ω → ∀ F, Fn0_d n U F → ∃ C, Mt_d n U F C := by
  let ρ : Env M 1 := ⟨fun _ => U, fun _ => U⟩
  let φ : UnarySchema 1 := { body := .forallE (.imp (fn0_m (.bound 1) (.bound 2) .newest)
    (.existsE (mt_m (.bound 2) (.bound 3) (.bound 1) .newest))) }
  have sat n : φ.denote ρ n ↔ ∀ F, Fn0_d n U F → ∃ C, Mt_d n U F C := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      fn0_sat_l hZF.1, Formula.satisfies_exists_iff, mt_sat_l hZF.1]; rfl
  apply hω.induction (fun n => ∀ F, Fn0_d n U F → ∃ C, Mt_d n U F C)
  · obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨A, fun n => (hA n).trans (and_congr_right fun _ => sat n)⟩
  · intro z hz F _
    exact ⟨D, hU.top, fun i _ hi _ => (hz i hi).elim⟩
  · intro n _ ih s hs F hf
    let I := kp_pair_l (ZF.modelsKP hZF)
    obtain ⟨G, hg⟩ := ZF.exists_restriction hZF I F n
    have gn := hg.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) hf)
      (fun i hi => (hs i).mpr (Or.inl hi))
    obtain ⟨C, hCU, hC⟩ := ih G (fn0_of_function_l (ZF.modelsKP hZF) gn)
    obtain ⟨B, hBU, hnB⟩ := hf.2.1 n hs.predecessor_mem
    obtain ⟨E, hEU, hEC, hEB⟩ := hU.meet C B hCU hBU
    refine ⟨E, hEU, fun i A hi hiA x hx => ?_⟩
    rcases (hs i).mp hi with hin | hin
    · exact hC i A hin ((hg.2 i A).mpr ⟨hin, hiA⟩) x (hEC x hx)
    · have e := hZF.1.eq_of_same_members i n hin
      have e' := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 n B A hnB (e ▸ hiA)
      exact e' ▸ hEB x hx

end YesMetaZFC.SetTheory.FilterZF
