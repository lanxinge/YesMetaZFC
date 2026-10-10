import YesMetaZFC.Model.Forcing.Iteration.Names.Representation
import YesMetaZFC.Model.Forcing.Iteration.Names.Witness
import YesMetaZFC.Model.Forcing.TwoStep.Closed

/-! # 坐标后继的可数闭性与固定前缀下界

在已有 Row_next 的真实二步表示上回拉下降链，构造下界后再用同一表示送回。
回拉使用实际逆函数和复合图；不改换后继偏序，也不重新选择坐标名称。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

private theorem chain_pull_l {C S D V F ω f} (hF : M.IsSetBijectionFromTo I F C D)
    (hmap : ∀ c d p q, Entry_d M c p F → Entry_d M d q F → (Entry_d M p q V ↔ Entry_d M c d S))
    (hf : Chain_d I D V D ω f) : ∃ g, Chain_d I C S C ω g ∧
      ∀ i c, Entry_d M i c g ↔ ∃ p, Entry_d M i p f ∧ Entry_d M c p F := by
  obtain ⟨H, hH, hInv⟩ := ZF.exists_inverseBijectionWithPairs hZF I hF
  obtain ⟨g, hg, hGraph⟩ := ZF.exists_compositionFunction hZF I hf.1 hH.1.1
  have edge i c : Entry_d M i c g ↔ ∃ p, Entry_d M i p f ∧ Entry_d M c p F := by
    change (M.PairMember I i c g ↔ _)
    rw [hGraph i c]
    exact ⟨fun ⟨_, p, hip, hpc⟩ => ⟨p, hip, (hInv p c).mp hpc⟩,
      fun ⟨p, hip, hcp⟩ => ⟨hf.1.input_mem_of_pairMember hip, p, hip, (hInv p c).mpr hcp⟩⟩
  refine ⟨g, ⟨hg, fun i c hic he => KP.mem_irrefl_d (ZF.modelsKP hZF) C (he ▸ hg.output_mem_of_pairMember hic),
    fun i j c d hij hic hjd => ?_⟩, edge⟩
  obtain ⟨p, hip, hcp⟩ := (edge i c).mp hic
  obtain ⟨q, hjq, hdq⟩ := (edge j d).mp hjd
  exact (hmap d c q p hdq hcp).mp (hf.2.2 i j p q hij hip hjq)

omit hZF in
/-- 已压住整条后继链的旧前缀，在共同下界中按原对象精确保留。 -/
theorem row_next_chain_bound_l (hZFC : M.Models ZFC) {α B R b A T t D V ω w f p}
    (h : Row_stage_d M α B R b) (hNext : Row_next_d M α B R b A T t D V)
    (L : Cond_order_d M D V D) (hT : Name_d M B T) (hω : M.IsOmega ω) (hw : Check_d M b ω w)
    (hf : Chain_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) D V D ω f)
    (hp : M.mem p B)
    (hpf : ∀ i r a, Entry_d M i r f →
      M.IsRestrictionOf (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) a r α →
      Entry_d M p a R)
    (hc : Forces_d M B R B (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
      (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) p) :
    ∃ q, M.mem q D ∧ M.IsRestrictionOf
      (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) p q α ∧
      ∀ i r, Entry_d M i r f → Entry_d M q r V := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨W, C, S, hW, hs, hk⟩ := hNext
  obtain ⟨F, hF, hcode, hmap⟩ := row_repr_map_l hZF hs h.rows hk
  obtain ⟨g, hg, hedge⟩ := chain_pull_l hZF hF hmap hf
  have LS := row_repr_order_l hZF hs h.rows hk L
  have pre c a s r (hc : M.mem c C) (hca : KPair_d M c a s) (hcr : Entry_d M c r F) :
      M.IsRestrictionOf (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP hZF))) a r α := by
    obtain ⟨_, a', s', hc', happ⟩ := (hcode c r).mp hcr
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hca hc'
    have ha := ((two_step_mem_l hs hca).mp hc).2.1.1
    exact ⟨(h.rows a ha).graph, row_append_prefix_l (KP.mem_irrefl_d (ZF.modelsKP hZF) α) (h.rows a ha) happ⟩
  obtain ⟨c, s, hcC, hcp, hcg⟩ := two_step_chain_bound_l h.order hZFC hs hW hT LS hω hw hg
    ⟨hp, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp), h.top p hp⟩ (by
      intro i c a s hic hca
      obtain ⟨r, hir, hcr⟩ := (hedge i c).mp hic
      exact hpf i r a hir (pre c a s r (hg.1.output_mem_of_pairMember hic) hca hcr)) hc
  obtain ⟨q, hq, hcq⟩ := hF.1.1.2.2 c hcC
  refine ⟨q, hq, pre c p s q hcC hcp hcq, fun i r hir => ?_⟩
  obtain ⟨d, _, hid⟩ := hg.1.2.2 i (hf.1.input_mem_of_pairMember hir)
  obtain ⟨r', hir', hdr⟩ := (hedge i d).mp hid
  have he := hf.1.1.2 i r' r hir' hir
  subst r'
  exact (hmap c d q r hcq hdr).mpr (hcg i d hid)

omit hZF in
/-- 可数闭性沿实际重编码传到已有坐标后继。 -/
theorem row_next_closed_l (hZFC : M.Models ZFC) {α B R b A T t D V ω w}
    (h : Row_stage_d M α B R b) (hNext : Row_next_d M α B R b A T t D V) (hT : Name_d M B T)
    (hP : Forces_d M B R B (preord_m .newest (.bound 1)) (ord_env_l M A T) b)
    (hω : M.IsOmega ω) (hw : Check_d M b ω w)
    (hB : Closed_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) B R B ω)
    (hc : Forces_d M B R B (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
      (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) b) :
    Closed_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) D V D ω := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨W, C, S, hW, hs, hk⟩ := hNext
  obtain ⟨F, hF, _, hmap⟩ := row_repr_map_l hZF hs h.rows hk
  have hClosed := two_step_closed_l h.order hZFC hs hW hT hP hω hw hB hc
  intro f hf
  obtain ⟨g, hg, hedge⟩ := chain_pull_l hZF hF hmap hf
  obtain ⟨c, hc, _, hcg⟩ := hClosed g hg
  obtain ⟨q, hq, hcq⟩ := hF.1.1.2.2 c hc
  refine ⟨q, hq, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hq), fun i r hir => ?_⟩
  obtain ⟨d, _, hid⟩ := hg.1.2.2 i (hf.1.input_mem_of_pairMember hir)
  obtain ⟨r', hir', hdr⟩ := (hedge i d).mp hid
  have he := hf.1.1.2 i r' r hir' hir
  subst r'
  exact (hmap c d q r hcq hdr).mpr (hcg i d hid)

end YesMetaZFC.Model.Forcing.Internal
