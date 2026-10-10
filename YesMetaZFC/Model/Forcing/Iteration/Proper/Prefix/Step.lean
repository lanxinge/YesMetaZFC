import YesMetaZFC.Model.Forcing.Iteration.Proper.Prefix.Comparison
import YesMetaZFC.Model.Forcing.Internal.Check.Relation

/-! # 变动前缀的旧名称比较保持

新名称在当前主前缀下加强旧名称。先在决定分支上反射真实旧序，再借较短前缀
已有的比较和稠密尾部闭性，证明延长后的前缀仍加强旧条件的相应限制。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

/-- 任意两段索引间的比较保持，只需 ZF；新旧主前缀可以跨越非相邻阶段。 -/
theorem row_cut_step_l {α B R b D V N τ p β E S q γ F T q' σ K ν}
    (hαβ : M.MemberSubset α β) (hβγ : M.MemberSubset β γ)
    (h : Row_stage_d M α B R b) (h' : Row_stage_d M β E S b) (L : Cond_order_d M F T F)
    (k : Row_link_d I α B R E S) (l : Row_link_d I β E S F T) (j : Row_link_d I γ F T D V)
    (hq' : M.mem q' F) (hpq : M.IsRestrictionOf I p q α) (hqq' : M.IsRestrictionOf I q q' β)
    (hτ : Name_d M B τ) (hσ : Name_d M E σ) (hK : Row_quot_d I β E b D N K)
    (hσK : Mem_force_d M E S E q σ K) (hν : Check_d M b V ν) (hστ : Rel_force_d M E S E ν q σ τ)
    (hOld : Row_cut_lower_d I α B R b D N τ p β S q)
    (hNew : Row_cut_lower_d I β E S b D N σ q γ T q') :
    Row_cut_lower_d I α B R b D N τ p γ T q' := by
  have hq := hσK.1
  have all := row_link_comp_l hZF L hαβ k l
  have hpre := hpq.comp_l hqq' hαβ
  intro r a v c hc hcp w t hw htr
  have hc' := hc
  obtain ⟨hr, _, _, _, hrv, _, hτv⟩ := hc'
  have hwF := (all.splice q' p c w hq' hpre hcp.1 hcp.2.2 hw).1
  obtain ⟨t', ht', ht'r⟩ := j.restrict r hr
  have htF : M.mem t F := (htr.eq hZF.1 ht'r).symm ▸ ht'
  obtain ⟨x, hx, hxw⟩ := l.restrict w hwF
  obtain ⟨y, hy, hyt⟩ := l.restrict t htF
  have hcRow := h.rows c hcp.1
  have hxsp := row_splice_cut_l hZF.1 hαβ hcRow.graph hcRow.domain hxw.1 hqq'.2 hxw.2 hw
  have hxy := hOld r a v c hc hcp x y hxsp (hyt.comp_l htr hβγ)
  obtain ⟨_, hxq, hxc⟩ := k.splice q p c x hq hpq hcp.1 hcp.2.2 hxsp
  apply l.tail w t x y hwF htF hxw hyt hxy
  intro d hdx
  have hdq : Below_d M E S E d q := ⟨hdx.1, hdx.2.1, h'.order.trans d x q hdx.1 hx hq hdx.2.2 hxq⟩
  obtain ⟨e, hed, s, a', u, he⟩ := row_quot_decide_l hK hσK d hdq
  have heq := below_trans_l h'.order hq hed hdq
  have hex := below_trans_l h'.order hx hed hdx
  have hec : Below_d M E S E e c := ⟨hed.1, hed.2.1,
    h'.order.trans e x c hed.1 hx (k.mem c hcp.1) hex.2.2 hxc⟩
  have he' := he
  obtain ⟨hs, _, _, _, hsu, _, hσu⟩ := he'
  have hvB := check_name_l M (check_range_l M hZF) h.base hrv
  have hτE := row_name_l k hτ
  have hvE := row_name_l k hvB
  have hτv' := eq_force_lower_l h'.order hZF hτE hvE c e (k.mem c hcp.1) hec
    ((row_eq_force_l hZF h.order h'.order k hcp.1 hτ hvB).mp hτv)
  have hn {x z} (hz : Check_d M b x z) := check_name_l M (check_range_l M hZF) h'.base hz
  have hστ' := (rel_force_regular_l h'.order hZF (hn hν) hσ hτE).1 q e hq heq hστ
  have hsr := check_rel_reflect_l h'.order hZF h'.base hν hsu hrv
    ⟨hed.1, hed.2.1, h'.top e hed.1⟩
    ((rel_force_congr_l h'.order hZF (hn hν) hσ hτE (hn hsu) hvE hed.1 hed.2.1 hσu hτv').mp hστ')
  obtain ⟨s', hs', hs's⟩ := j.restrict s hs
  have hs't := j.mono s r s' t hs hr hs's htr hsr
  refine ⟨e, hed, fun z hz => ?_⟩
  have hz' := row_splice_overwrite_l hαβ hcRow hw hz
  have hzF := (l.splice q' q e z hq' hqq' hed.1 heq.2.2 hz').1
  exact L.trans z s' t hzF hs' htF (hNew s a' u e he heq z s' hz' hs's) hs't

end YesMetaZFC.Model.Forcing.Internal
