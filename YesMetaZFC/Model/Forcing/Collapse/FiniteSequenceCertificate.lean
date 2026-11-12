import YesMetaZFC.Model.Forcing.Collapse.NameCode
import YesMetaZFC.Model.Forcing.Collapse.PartialFunctionCertificate

/-! # 有限序列坍缩的实际存在式力迫证书

逐坐标、逐值的真实加强给出部分函数满射证书，并由统一泛型并图定理得到坍缩力迫。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem fseq_psurj_l {B R ω X : M.Domain} (hω : M.IsOmega ω) (space : Fseq_space_d I ω X B)
    (order : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (inh : ∃ x, M.mem x X) : Psurj_d hZF B R B ω X := by
  refine ⟨?_,fun p q pq => ((order p q).mp pq).2.2,?_,?_⟩
  · intro p hp
    obtain ⟨n,hn,fn⟩ := (space p).mp hp
    exact ⟨fn.1,fun i x ix => ⟨hω.transitive (ZF.modelsKP hZF) n hn i (fn.input_mem_of_pairMember ix),
      fn.output_mem_of_pairMember ix⟩⟩
  · intro i hi p hp _
    exact fseq_input_extend_l hZF hω space order inh hi hp
  · intro x hx p hp _
    exact fseq_output_extend_l hZF hω space order hx hp

theorem fseq_collapses_l {B R ω X a : M.Domain} (O : Cond_order_d M B R B) (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X B)
    (order : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p)
    (inh : ∃ x, M.mem x X) (ha : M.mem a B) : Collapses_d B R B a ω X :=
  (fseq_psurj_l hZF hω space order inh).collapse_l hZF O ha
    (fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ ha))

end YesMetaZFC.Model.Forcing.Internal
