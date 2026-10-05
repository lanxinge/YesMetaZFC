import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.SetTheory.CumulativeClosure

/-! # 外部下降链的源内反射

此处直接陈述背景中存在下降链时源内也存在一条。Hχ 与 Vδ 的实例由实际
函数图闭包给出；该外部性质不随一般初等映射自动传递。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_branch_d (ω X : M.Domain) : Prop := ∀ A R, M.mem A X → M.mem R X →
  (∃ f, Fn0_d ω A f ∧ Wf_desc_d R f) → ∃ f, M.mem f X ∧ Fn0_d ω A f ∧ Wf_desc_d R f

theorem sc_h_branch_l (hZFC : M.Models ZFC) {ω χ H : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H)
    (hωH : M.mem ω H) : Sc_branch_d ω H := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro A R hA _ ⟨f, hf, hd⟩
  exact ⟨f, ZFC.h_function_l hZFC hω hχ hωχ hH hωH
    (fn0_function_l (ZF.modelsKP hZF) (hf.mono_target_l (ZF.h_transitive_l I hZF hH A hA))), hf, hd⟩

theorem sc_v_branch_l (hZF : M.Models ZF) {ω δ V : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ V) (hωV : M.mem ω V) : Sc_branch_d ω V := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  intro A R hA _ ⟨f, hf, hd⟩
  obtain ⟨Y, hY, hωY, hAY⟩ := ZF.v_joint_bound_l I hZF hV hωV hA
  exact ⟨f, ZF.v_relation_mem_l I hZF hV hδ hY (fun p hp =>
    (hf.1 p hp).elim fun i hi => hi.2.elim fun a ha => ⟨i, hωY i hi.1, a, hAY a ha.1, ha.2⟩), hf, hd⟩

end YesMetaZFC.SetTheory.Internal
