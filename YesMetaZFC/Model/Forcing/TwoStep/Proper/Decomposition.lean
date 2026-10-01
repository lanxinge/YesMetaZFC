import YesMetaZFC.Model.Forcing.TwoStep.Proper.Second
import YesMetaZFC.Model.Forcing.TwoStep.Proper.Composition
import YesMetaZFC.Model.Forcing.TwoStep.Proper.Projection

/-! # 二步主条件的完整双向分解

(q,t) 是 N 的主条件，当且仅当 q 是 N 的主条件且 q 迫使 t 是 N[G] 的主条件。
自动入口同时构造规范 N[G] 名称，适用于任意外部非良基地模型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

theorem two_step_master_iff_l {ω χ H c J d N K v q t μ} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N K) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N) (hC : M.mem C N) (hS : M.mem S N)
    (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hT : Name_d M B T)
    (hv : M.mem v C) (hvq : KPair_d M v q t) (hμ : Ng_name_d M B N μ) :
    Mstr_d M C S C N v ↔ Mstr_d M B R z N q ∧ Forces_d M B R z mstr_body_m (mstr_env_l A T μ t) q :=
  ⟨fun hm => ⟨two_step_master_first_l O hZF hω hχ.isLimitOrdinal hH hJ hSub hElem hC h L hT hvq hm,
    two_step_master_second_l O hZFC hω hχ hωχ hH hJ hSub hElem hB hR hz hC hS h L hT hvq hm hμ⟩,
    fun hm => two_step_master_l O hZFC hω hχ hωχ hH hJ hSub hElem hB hR hz h L hT hv hvq hm.1 hμ hm.2⟩

/-- 一次构造 N[G] 名称及主条件的完整等价式，调用者无需额外名称选择。 -/
theorem two_step_master_decompose_l {ω χ H c J d N K v q t} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N K) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hz : M.mem z N) (hC : M.mem C N) (hS : M.mem S N)
    (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C) (hT : Name_d M B T)
    (hv : M.mem v C) (hvq : KPair_d M v q t) : ∃ μ, Ng_name_d M B N μ ∧
      (Mstr_d M C S C N v ↔ Mstr_d M B R z N q ∧ Forces_d M B R z mstr_body_m (mstr_env_l A T μ t) q) := by
  obtain ⟨μ, hμ⟩ := ng_name_exists_l M hZF B N
  exact ⟨μ, hμ, two_step_master_iff_l O hZFC hω hχ hωχ hH hJ hSub hElem hB hR hz hC hS h L hT hv hvq hμ⟩

end YesMetaZFC.Model.Forcing.Internal
