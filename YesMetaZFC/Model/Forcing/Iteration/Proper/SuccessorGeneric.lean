import YesMetaZFC.Model.Forcing.Iteration.Proper.Successor
import YesMetaZFC.Model.Forcing.Iteration.Proper.Lemma

/-! # proper 迭代引理的完整相邻后继结论

将坐标决定分支上的加强转成后继泛型滤子的真实成员力迫。因此输出条件不仅
保持前缀及主性，还迫使输入旧条件名称属于 G∩check(N)，可用于阶段归纳。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 后继坐标比较给出任意阶段共用的实际尾部加强规格。 -/
theorem row_quot_lower_step_l (hZF : M.Models ZF) {α B R b A T t W C S D V N τ p s q}
    (h : Row_stage_d M α B R b) (hStep : Two_step_d M B R B b A T W C S)
    (k : Row_repr_d M α t C S D V)
    (hLink : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (hp : M.mem p B) (hq : M.mem q D) (hpq : Row_append_d M α t p s q)
    (hl : Row_below_name_d (M := M) α B R b t D N T τ p s) :
    Row_quot_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D V N τ p q := by
  have hα := KP.mem_irrefl_d (ZF.modelsKP hZF) α
  have hpq' : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α :=
    ⟨(h.rows p hp).graph, row_append_prefix_l hα (h.rows p hp) hpq⟩
  intro r a v c hc hcp w hw
  obtain ⟨hr, hrN, ha, hpre, hrv, hca, heq⟩ := hc
  obtain ⟨x, hx, a', u, hxa, har⟩ := (k.conditions r).mp hr
  have ha' := ((two_step_mem_l hStep hxa).mp hx).2.1.1
  have hea := hpre.eq hZF.1 ⟨(h.rows a' ha').graph, row_append_prefix_l hα (h.rows a' ha') har⟩
  subst a'
  obtain ⟨w', hw'⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t c s
  have hew := row_splice_unique_l M hZF.1 hw (row_append_splice_l hZF.1 hα (h.rows p hp) hpq hw')
  subst w'
  have hwD := (hLink.splice q p c w hq hpq' hcp.1 hcp.2.2 hw).1
  have hl' : Row_below_name_d (M := M) α B R b t D N T τ c s :=
    fun u a hu hac => hl u a hu (below_trans_l h.order hp hac hcp)
  exact row_below_name_ground_l hZF h hStep k hwD hcp.1 hw' hr hrN ha har hca.2.2 hrv heq hl'

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 相邻后继的完整内部迭代引理；统一量化全部商名称和主前缀。 -/
theorem row_step_pil_l {ω χ H c J' d N K δ F G e w v α B R A T t W C S D V w' X J}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hRel : ∀ x y, M.PairMember I x y J' ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J' N K) (hElem : Selem_d I ω c d)
    (hLift : Hlift_d M ω δ F G e χ H N w v)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G) (hFN : M.mem F N) (hGN : M.mem G N)
    (hα : M.mem α δ) (hαN : M.mem α N) (hiB : Entry_d M α B F) (hiR : Entry_d M α R G)
    (htN : M.mem t N) (hCN : M.mem C N) (hDN : M.mem D N)
    (h : Row_stage_d M α B R e) (hStep : Two_step_d M B R B e A T W C S)
    (hPool : Name_pool_d M B A t W) (k : Row_repr_d M α t C S D V) (L : Cond_order_d M D V D)
    (hLink : Row_link_d I α B R D V)
    (hPr : Pr_name_d M B R B e A T w' X J) (hwN : M.mem w' N) (hJN : M.mem J N) :
    Row_pil_d I α B R e D V N := by
  intro τ p L' hQ hτ hτQ hm
  obtain ⟨s, q, _, hpq, hq, hpre, hqm, hle⟩ := row_step_proper_name_l hZFC hω hχ hωχ hH hRel
    hSub hElem hLift hF hG hFN hGN hα hαN hiB hiR htN hCN hDN h hStep hPool k L hPr hwN hJN hQ hτ hτQ hm
  exact ⟨q, hq, hpre, hqm, row_quot_lower_step_l hZF h hStep k hLink hm.1 hq hpq hle⟩

end YesMetaZFC.Model.Forcing.Internal
