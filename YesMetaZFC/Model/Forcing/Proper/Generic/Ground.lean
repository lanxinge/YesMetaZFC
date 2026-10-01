import YesMetaZFC.Model.Forcing.Proper.Family.Forcing
import YesMetaZFC.Model.Forcing.Proper.Generic.Member

/-! # 同一个 N[G] 中旧条件的精确回拉

先构造覆盖整个阶段图传递闭包的规范名称递归图，并把该图放入共同 N。
主条件把隶属见证回拉到 N 后，规范名称图的单射性恢复真正的旧模型条件。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 一个实际规范名称图同时覆盖给定集合的整个传递闭包。 -/
theorem check_cover_l (hZF : M.Models ZF) (b X : M.Domain) : ∃ T J,
    Tc_d (M := M) X T ∧ Check_graph_d M b J ∧
    ∀ x, M.mem x T → ∃ t, Entry_d M x t J := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨T, hT⟩ := ZF.tc_exists_l I hZF X
  obtain ⟨t, J, hJ, hTt⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b T
  exact ⟨T, J, hT, hJ, (hJ.2 T t hTt).1⟩

/-- 名称回拉所需的规范图和全阶段 H(χ) 提升证书一次构造，均属于同一个 N。 -/
theorem ng_family_ground_l (hZFC : M.Models ZFC) {ω δ F G b A} (hω : M.IsOmega ω)
    (hF : M.IsSetFunction (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) F)
    (hG : M.IsSetFunction (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) G)
    (ha : M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) A ω) :
    ∃ χ H N w v J, Hsub_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω χ H N ∧
      M.MemberSubset A N ∧ M.mem F N ∧ M.mem G N ∧ M.mem δ N ∧ M.mem b N ∧ M.mem J N ∧
      Hlift_d M ω δ F G b χ H N w v ∧ Check_graph_d M b J ∧
      ∀ i P, Entry_d M i P F → ∃ t, Entry_d M P t J := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨T, J, hT, hJ, hc⟩ := check_cover_l hZF b F
  obtain ⟨A', hA'⟩ := KP.exists_insert (ZF.modelsKP hZF) A J
  obtain ⟨χ, H, N, w, v, hN, hAN, hFN, hGN, hδN, hbN, hLift⟩ :=
    ng_family_forcing_l (δ := δ) (b := b) hZFC hω hF hG (ZF.countable_insert_l I hZF hω ha hA')
  exact ⟨χ, H, N, w, v, J, hN, (fun a ha => hAN a ((hA' a).mpr (Or.inl ha))), hFN, hGN, hδN, hbN,
    hAN J ((hA' J).mpr (Or.inr rfl)), hLift, hJ,
    fun i P hiP => hc P (trans_entry_l hT.1 hT.2.1 hiP).2⟩

/-- 主条件下 N[G] 中属于旧集合 P 的对象，恰好来自 N∩P；没有外部良基假设。 -/
theorem ng_ground_trace_l (hZFC : M.Models ZFC) {ω χ H c T d N S B R z b q P J t}
    (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ)
    (hωχ : M.mem ω χ)
    (hH : H_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) χ H)
    (hRel : ∀ x y, M.PairMember (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) x y T ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) c d H T N S)
    (hElem : Selem_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω c d)
    (O : Cond_order_d M B R z) {U} (hU : Generic_d M B R z U)
    (hBN : M.mem B N) (hRN : M.mem R N) (hzN : M.mem z N) (hJN : M.mem J N) (hPN : M.mem P N)
    (hJ : Check_graph_d M b J) (hPt : Entry_d M P t J) (hb : U b)
    (hm : Mstr_d M B R z N q) (hq : U q)
    (e : M.Domain → (extension_l M (ZFC.models_zf_l hZFC) B R z U).Domain)
    (he : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    (x : (extension_l M (ZFC.models_zf_l hZFC) B R z U).Domain) :
    (Ng_mem_d M B R z U N x ∧ x ∈ e P) ↔ ∃ p, M.mem p N ∧ M.mem p P ∧ e p = x := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP hZF))
  have htr := ZF.h_transitive_l I hZF hH
  have fn a s t (hs : Entry_d M a s J) (ht : Entry_d M a t J) : s = t :=
    check_unique_l M hZF.1 (check_ind_l M hZF) b a s t ⟨J, hJ, hs⟩ ⟨J, hJ, ht⟩
  have htN := selem_entry_value_l I hRel htr hZF hω hSub hElem hJN hPN fn hPt
  have ht := he P t ⟨J, hJ, hPt⟩
  constructor
  · rintro ⟨⟨s, hsN, hs⟩, hx⟩
    obtain ⟨a, k, haN, _, hak, _, ha⟩ := ng_member_pick_l hZFC hω hχ hωχ hH hRel O hU
      hSub hElem hBN hRN hzN hsN htN hm hq hs ht hx
    obtain ⟨r, hr, hrt⟩ := hak
    obtain ⟨p, a', hpP, hpa, hr'⟩ := ((hJ.2 P t hPt).2 r).mp hrt
    have hea := (kpair_injective_l M hr hr').1
    subst a'
    obtain ⟨p', hp'N, hp'a⟩ := selem_entry_witness_l I hRel htr hZF hω hSub hElem hJN haN ⟨p, hpa⟩
    have hpp := check_injective_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF))
      b p p' a ⟨J, hJ, hpa⟩ ⟨J, hJ, hp'a⟩
    exact ⟨p', hp'N, hpp ▸ hpP, qval_unique_l (he p' a ⟨J, hJ, hp'a⟩) ha⟩
  · rintro ⟨p, hpN, hpP, rfl⟩
    obtain ⟨s, hps⟩ := (hJ.2 P t hPt).1 p hpP
    have hsN := selem_entry_value_l I hRel htr hZF hω hSub hElem hJN hpN fn hps
    have hs := he p s ⟨J, hJ, hps⟩
    have hst := (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF))
      ⟨J, hJ, hPt⟩ s b).mpr ⟨rfl, p, hpP, J, hJ, hps⟩
    exact ⟨⟨s, hsN, hs⟩, (qval_mem_l O hZF hU ht).mpr ⟨s, b, hst, hb, hs⟩⟩

end YesMetaZFC.Model.Forcing.Internal
