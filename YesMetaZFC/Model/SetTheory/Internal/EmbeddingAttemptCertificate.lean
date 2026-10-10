import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttemptSyntax
import YesMetaZFC.Model.SetTheory.Internal.FiniteEvaluation

/-! # 完整初等性检验与有限真值证书

全部内部程序均有实际有限值域与真值表；证书检验精确恢复原满足关系。
此等价供联合尝试节点使用，与传递源中的证书读取共用同一原公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem at_elementary_sat_l {d} (ρ : Env M d) (ω A R B S e n p Q J K : Term d)
    (hω : M.IsOmega (ω.eval ρ)) (hn : M.mem (n.eval ρ) (ω.eval ρ))
    (hQ : Fseq_space_d I (ω.eval ρ) (ω.eval ρ) (Q.eval ρ))
    (hJ : Fseq_space_d I (ω.eval ρ) (A.eval ρ) (J.eval ρ))
    (hK : Fseq_space_d I (ω.eval ρ) (B.eval ρ) (K.eval ρ)) :
    Formula.satisfies ρ (at_elementary_m ω A R B S e n p Q J K) ↔
      At_elementary_d I (ω.eval ρ) (A.eval ρ) (R.eval ρ) (B.eval ρ) (S.eval ρ)
        (e.eval ρ) (n.eval ρ) (p.eval ρ) := by
  simp only [at_elementary_m, at_witness_m, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, fb_program_sat_l (ZF.modelsKP hZF),
    at_cert_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken]
  constructor
  · intro h b l F E D q s t hb hF bound hE hD hq hs ht r hr
    obtain ⟨L, range⟩ := ZF.exists_range_of_setFunction hZF I hF.2.1.2.1 hF.2.1.2.2
    have fn : Fn0_d l L F := fn0_of_function_l (ZF.modelsKP hZF)
      ⟨hF.2.1.2.1, hF.2.1.2.2, fun a ha => ((hF.2.1.2.2 a).mp ha).imp
        fun x hx => ⟨(range x).mpr ⟨a, hx⟩, hx⟩⟩
    have program := fb_program_of_l (ZF.modelsKP hZF) hF hb bound fn
    obtain ⟨E', D', C, H, C', H', space, space', ev, ev', test⟩ := h b l L F program
    have eqE := hZF.1.eq_of_same_members E' E (fun f =>
      ((fv_space_l (ZF.modelsKP hZF) hb hJ).mp space f).trans (hE f).symm)
    have eqD := hZF.1.eq_of_same_members D' D (fun f =>
      ((fv_space_l (ZF.modelsKP hZF) hb hK).mp space' f).trans (hD f).symm)
    subst E' D'
    exact (ev.truth_l hZF hω program hE hr).symm.trans
      ((test r hr q ((hQ q).mpr ⟨b, hb, fn0_function_l (ZF.modelsKP hZF)
        (hq.mono_target_l (hω.transitive hZF _ hn))⟩)
        s ((hE s).mpr (fn0_function_l (ZF.modelsKP hZF) hs.1))
        t ((hD t).mpr (fn0_function_l (ZF.modelsKP hZF) ht.1)) hq hs ht).trans
          (ev'.truth_l hZF hω program hD hr))
  · intro h b l L F program
    obtain ⟨hF, bound⟩ := program.read_l hZF hω
    have evaluate A R : ∃ E C H, M.IsFunctionSpace I E b A ∧
        Fv_eval_d (ZF.modelsKP hZF) b A R E l L F C H := by
      obtain ⟨E, space⟩ := ZF.exists_functionSpace hZF I b A
      obtain ⟨H, ev⟩ := seval_exists_l I hZF A R E F hF.2.1.1
      obtain ⟨C, range⟩ := ZF.exists_range_of_setFunction hZF I ev.1.2.1 ev.1.2.2
      exact ⟨E, C, H, space, fv_eval_of_l hZF hω program space ev
        (fn0_of_function_l (ZF.modelsKP hZF) ⟨ev.1.2.1, ev.1.2.2, fun a ha =>
          ((ev.1.2.2 a).mp ha).imp fun x hx => ⟨(range x).mpr ⟨a, hx⟩, hx⟩⟩)⟩
    obtain ⟨E, C, H, space, ev⟩ := evaluate (A.eval ρ) (R.eval ρ)
    obtain ⟨D, C', H', space', ev'⟩ := evaluate (B.eval ρ) (S.eval ρ)
    refine ⟨E, D, C, H, C', H', (fv_space_l (ZF.modelsKP hZF) program.1 hJ).mpr space,
      (fv_space_l (ZF.modelsKP hZF) program.1 hK).mpr space', ev, ev', fun r hr q _ s _ t _ hq hs ht => ?_⟩
    exact (ev.truth_l hZF hω program space hr).trans
      ((h b l F E D q s t program.1 hF bound space space' hq hs ht r hr).trans
        (ev'.truth_l hZF hω program space' hr).symm)

end YesMetaZFC.SetTheory.Internal
