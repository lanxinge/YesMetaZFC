import YesMetaZFC.Model.Forcing.Boolean.RegularAlgebra
import YesMetaZFC.Model.Forcing.Ground.Collapse

/-! # 任意实际名字在同一内部完备化中的成员真值图

先构造整张原模型内函数图，再对每个接受基点的实际泛型读出它。
该接口保留全部规范名称对应；不把可能有核的真值图冒充完全嵌入。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem bv_name_map_l {B R z : M.Domain} (O : Cond_order_d M B R z) (b τ Q : M.Domain) :
    ∃ K S e F, (∀ V, M.mem V K ↔ Ropen_d B R z V) ∧ (∀ p, ¬ M.mem p e) ∧
      (∀ U V, Entry_d M U V S ↔ M.mem U K ∧ M.mem V K ∧ M.MemberSubset U V) ∧
      BooleanZF.Cba_d I K S e ∧
      M.IsSetFunctionFromTo I F Q K ∧
      (∀ q V, Entry_d M q V F ↔ M.mem q Q ∧ Bv_mem_d B R z b τ q V) ∧
      ∀ G, Generic_d M B R z G → G b → ∀ H : (extension_l M hZF B R z G).Domain,
        Qval_d M B R z G τ H → ∃ j : M.Domain → (extension_l M hZF B R z G).Domain,
          Function.Injective j ∧ (∀ a y, (extension_l M hZF B R z G).mem y (j a) ↔ ∃ c, M.mem c a ∧ j c = y) ∧
          (∀ a t, Check_d M b a t → Qval_d M B R z G t (j a)) ∧
          ∀ q V, Entry_d M q V F →
            ((∃ p, G p ∧ M.mem p V) ↔ (extension_l M hZF B R z G).mem (j q) H) := by
  obtain ⟨K,S,e,family,empty,order,algebra⟩ := ropen_completion_l hZF O
  obtain ⟨P,F,_,fn,values⟩ := bv_mem_graph_l hZF B R z b τ Q
  have typed : M.IsSetFunctionFromTo I F Q K := ⟨fn.1,fn.2.1,fun q hq => by
    obtain ⟨V,_,qV⟩ := fn.2.2 q hq
    have value := ((values q V).mp qV).2
    exact ⟨V,(family V).mpr ⟨fun p hp => ⟨((value p).mp hp).1,((value p).mp hp).2.1⟩,
      value.regular_l hZF O⟩,qV⟩⟩
  refine ⟨K,S,e,F,family,empty,order,algebra,typed,values,?_⟩
  intro G generic hb H valueH
  obtain ⟨j,checks,full,inj⟩ := check_map_l O hZF generic hb
  refine ⟨j,inj,full,checks,?_⟩
  intro q V qV
  obtain ⟨a,check,_,_⟩ := zf_check_l M hZF (generic.proper b hb).1 q
  exact (((values q V).mp qV).2).value_l hZF O generic check (checks q a check) valueH

end YesMetaZFC.Model.Forcing.Internal
