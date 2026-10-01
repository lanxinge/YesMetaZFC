import YesMetaZFC.Model.Forcing.Iteration.Names.QuotientOrder
import YesMetaZFC.Model.Forcing.Internal.Check.Relation

/-! # 商名称的加强与实际尾部比较

先在同时决定两个名称的分支上反射旧序关系，再应用阶段链接的稠密尾部闭性。
因此稠密选择得到的新名称之下的真实尾部加强，仍在原输入名称之下。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 在原前缀上被迫 σ≤τ 时，低于 σ 的实际尾部加强也低于 τ；无需偏序分离性。 -/
theorem row_quot_lower_mono_l (hZF : M.Models ZF) {α B R b D V N σ τ p q K ν}
    (h : Row_stage_d M α B R b) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (hq : M.mem q D)
    (hpq : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b D N K)
    (hσ : Name_d M B σ) (hτ : Name_d M B τ) (hν : Check_d M b V ν)
    (hσK : Mem_force_d M B R B p σ K) (hστ : Rel_force_d M B R B ν p σ τ)
    (hl : Row_quot_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D V N σ p q) :
    Row_quot_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D V N τ p q := by
  have hn {x t} (ht : Check_d M b x t) := check_name_l M (check_range_l M hZF) h.base ht
  have hνn := hn hν
  intro r a v c hc hcp w hw
  obtain ⟨hr, _, ha, har, hrv, hca, hτv⟩ := hc
  have hwD := (k.splice q p c w hq hpq hcp.1 hcp.2.2 hw).1
  have hcw : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c w α :=
    ⟨(k.rows c hcp.1).graph, row_splice_prefix_l (k.rows c hcp.1) hw⟩
  apply k.tail w r c a hwD hr hcw har hca.2.2
  intro d hdc
  obtain ⟨e, hed, s, a', u, he⟩ := row_quot_decide_l hK hσK d (below_trans_l h.order hσK.1 hdc hcp)
  have hec := below_trans_l h.order hcp.1 hed hdc
  have hep := below_trans_l h.order hσK.1 hec hcp
  have he' := he
  obtain ⟨hs, _, _, _, hsu, _, hσu⟩ := he'
  have hτv' := eq_force_lower_l h.order hZF hτ (hn hrv) c e hcp.1 hec hτv
  have hστ' := (rel_force_regular_l h.order hZF hνn hσ hτ).1 p e hσK.1 hep hστ
  have hforce := (rel_force_congr_l h.order hZF hνn hσ hτ (hn hsu) (hn hrv) hed.1 hed.2.1 hσu hτv').mp hστ'
  have hsr := check_rel_reflect_l h.order hZF h.base hν hsu hrv
    ⟨hed.1, hed.2.1, h.top e hed.1⟩ hforce
  refine ⟨e, hed, fun t ht => ?_⟩
  have ht' := row_splice_overwrite_l (fun _ h => h) (k.rows c hcp.1) hw ht
  have htD := (k.splice q p e t hq hpq hed.1 hep.2.2 ht').1
  exact L.trans t s r htD hs hr (hl s a' u e he hep t ht') hsr

end YesMetaZFC.Model.Forcing.Internal
