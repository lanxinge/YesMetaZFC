import YesMetaZFC.Model.Forcing.Iteration.Proper.Master
import YesMetaZFC.Model.Forcing.Proper.Forcing
import YesMetaZFC.Model.Forcing.Proper.Family.Forcing
import YesMetaZFC.Model.Forcing.Iteration.Names.NameOrder

/-! # proper 后继的固定前缀主加强

从统一 H(χ) 提升证书及 N 中的实际 club 名称开始，先在同一个 N[G] 内取得
主加强的存在力迫，再装配真实坐标条件。输入前缀始终原样保留。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 旧条件可以是任意商条件名称；同一主前缀延长为低于该名称的后继主条件。 -/
theorem row_step_proper_name_l {ω χ H c J' d N K δ F G e w v α B R A T t W C S D V w' X J L' τ p}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hRel : ∀ x y, M.PairMember I x y J' ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J' N K) (hElem : Selem_d I ω c d)
    (hLift : Hlift_d M ω δ F G e χ H N w v)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G) (hFN : M.mem F N) (hGN : M.mem G N)
    (hα : M.mem α δ) (hαN : M.mem α N) (hiB : Entry_d M α B F) (hiR : Entry_d M α R G)
    (htN : M.mem t N) (hCN : M.mem C N) (hDN : M.mem D N)
    (h : Row_stage_d M α B R e) (hStep : Two_step_d M B R B e A T W C S)
    (hPool : Name_pool_d M B A t W) (k : Row_repr_d M α t C S D V) (L : Cond_order_d M D V D)
    (hPr : Pr_name_d M B R B e A T w' X J) (hwN : M.mem w' N) (hJN : M.mem J N)
    (hQ : Row_quot_d I α B e D N L') (hτ : Name_d M B τ)
    (hτQ : Mem_force_d M B R B p τ L') (hm : Mstr_d M B R B N p) :
    ∃ s q, Name_d M B s ∧ Row_append_d M α t p s q ∧ M.mem q D ∧
      M.IsRestrictionOf I p q α ∧ Mstr_d M D V D N q ∧
      Row_below_name_d (M := M) α B R e t D N T τ p s := by
  have htr := ZF.h_transitive_l I hZF hH
  have hBN := selem_entry_value_l I hRel htr hZF hω hSub hElem hFN hαN hF.2 hiB
  have hRN := selem_entry_value_l I hRel htr hZF hω hSub hElem hGN hαN hG.2 hiR
  obtain ⟨μ, hμ⟩ := ng_name_exists_l M hZF B N
  obtain ⟨u, huW, huA, hsel⟩ := row_select_l hZF h hStep hPool k hQ hτ hτQ
  have hu : Name_d M B u := ⟨W, huW, hStep.closed⟩
  -- 混合名称本身未必属于 N；在每个决定分支上，它等于 N 中的实际坐标名称。
  have huN : Mem_force_d M B R B p u μ := by
    apply mem_force_dense_l h.order hm.1
    intro q hq
    obtain ⟨a, haq, s, hs⟩ := row_pick_dense_l hZF h hStep k hQ hτQ q hq
    have he := hsel s a hs
    obtain ⟨r, b, _, hr, hrN, hb, hbr, _⟩ := hs
    obtain ⟨hsW, _, x, hx, hxb⟩ := row_repr_decode_l hZF h hStep k hr hb hbr
    have hsN := (row_repr_coords_mem_l hZFC hω hχ hωχ hH hRel hSub hElem hαN htN hCN hDN
      hStep h.rows k hx ⟨b, s, hxb, hbr⟩ hxb hrN).2
    have hs : Name_d M B s := ⟨W, hsW, hStep.closed⟩
    have hsm := mem_force_entry_l h.order hZF haq.1 hs haq.1
      ((hμ.2 s a).mpr ⟨hsN, hs, haq.1⟩) (h.order.refl a haq.1)
    exact ⟨a, haq, mem_force_left_l h.order hZF hs hu hμ.1 (eq_force_symm_l hZF hu hs he) hsm⟩
  have hPr' := pr_name_lower_l h.order hZF h.base hPr ⟨hm.1, hm.2.1, h.top p hm.1⟩
  have hex := hlift_master_exists_l h.order hZFC hLift hα hαN hiB hiR h.base hm
    (h.top p hm.1) hPr' hwN hJN hμ hu huN huA
  let ρ := mstr_env_l A T μ u
  have hρ : ∀ i, Name_d M B (ρ.bound i) := Fin.cases hu (Fin.cases hμ.1 (Fin.cases hPr.2.1 (fun _ => hPr.1)))
  obtain ⟨s, x, hsW, hxp, hx, hsF⟩ := two_step_witness_l h.order hZFC mstr_lower_s ρ 3 hρ hStep hPool
    ⟨hm.1, hm.2.1, h.top p hm.1⟩ hex
  obtain ⟨hsu, hsM⟩ := force_mstr_lower_l hZF.1 hsF
  have hs : Name_d M B s := ⟨W, hsW, hStep.closed⟩
  have hxM := two_step_master_l h.order hZFC hω hχ hωχ hH hRel hSub hElem hBN hRN hBN hStep
    (row_repr_order_l hZF hStep h.rows k L) hPr.2.1 hx hxp hm hμ hsM
  obtain ⟨q, hq⟩ := row_append_exists_l M (ZF.modelsKP hZF) α t p s
  have hxq : Row_code_d M α t x q := ⟨p, s, hxp, hq⟩
  exact ⟨s, q, hs, hq, (k.conditions q).mpr ⟨x, hx, hxq⟩,
    ⟨(h.rows p hm.1).graph, row_append_prefix_l (KP.mem_irrefl_d (ZF.modelsKP hZF) α) (h.rows p hm.1) hq⟩,
    row_repr_master_l hZFC hω hχ hωχ hH hRel hSub hElem hαN htN hCN hDN hStep h.rows k hxM hxq,
    row_select_below_l hZF h hStep k hPr.2.1 hu hs hm.1 hsu hsel⟩

/-- 对 N 内旧条件，指定的 N 主前缀一次延长为后继 N 主加强，不另加主加强存在假设。 -/
theorem row_step_proper_l {ω χ H c J' d N K δ F G e w v α B R A T t W C S D V w' X J r a p}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hRel : ∀ x y, M.PairMember I x y J' ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J' N K) (hElem : Selem_d I ω c d)
    (hLift : Hlift_d M ω δ F G e χ H N w v)
    (hF : M.IsSetFunction I F) (hG : M.IsSetFunction I G) (hFN : M.mem F N) (hGN : M.mem G N)
    (hα : M.mem α δ) (hαN : M.mem α N) (hiB : Entry_d M α B F) (hiR : Entry_d M α R G)
    (htN : M.mem t N) (hCN : M.mem C N) (hDN : M.mem D N)
    (h : Row_stage_d M α B R e) (hStep : Two_step_d M B R B e A T W C S)
    (hPool : Name_pool_d M B A t W) (k : Row_repr_d M α t C S D V) (L : Cond_order_d M D V D)
    (hPr : Pr_name_d M B R B e A T w' X J) (hwN : M.mem w' N) (hJN : M.mem J N)
    (hr : M.mem r D) (hrN : M.mem r N) (hpre : M.IsRestrictionOf I a r α)
    (hpa : Entry_d M p a R) (hm : Mstr_d M B R B N p) :
    ∃ s q, Name_d M B s ∧ Row_append_d M α t p s q ∧ M.mem q D ∧ Entry_d M q r V ∧
      M.IsRestrictionOf I p q α ∧ Mstr_d M D V D N q := by
  obtain ⟨x, hx, a', u, hxa, har⟩ := (k.conditions r).mp hr
  have ha := ((two_step_mem_l hStep hxa).mp hx).2.1
  have he := hpre.eq hZF.1 ⟨(h.rows a' ha.1).graph,
    row_append_prefix_l (KP.mem_irrefl_d (ZF.modelsKP hZF) α) (h.rows a' ha.1) har⟩
  subst a'
  obtain ⟨L', hQ⟩ := row_quot_exists_l hZF h.base α D N
  obtain ⟨τ, hτr, hτ, _⟩ := zf_check_l M hZF h.base r
  have hτQ := row_quot_check_l hZF h.order h.base hQ hr hrN ha.1 hpre hτr hm.1 hpa
  obtain ⟨s, q, hs, hq, hqD, hpre', hqM, hle⟩ := row_step_proper_name_l hZFC hω hχ hωχ hH hRel
    hSub hElem hLift hF hG hFN hGN hα hαN hiB hiR htN hCN hDN h hStep hPool k L hPr hwN hJN hQ hτ hτQ hm
  exact ⟨s, q, hs, hq, hqD, row_below_name_ground_l hZF h hStep k hqD hm.1 hq hr hrN ha.1 har hpa hτr
    (eq_force_refl_l h.order hZF hm.1 hτ) hle, hpre', hqM⟩

end YesMetaZFC.Model.Forcing.Internal
