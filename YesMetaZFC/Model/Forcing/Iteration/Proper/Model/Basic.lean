import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Family
import YesMetaZFC.Model.Forcing.Iteration.Proper.SuccessorGeneric
import YesMetaZFC.Model.Forcing.Iteration.Proper.Natural
import YesMetaZFC.Model.Forcing.Proper.Generic.Ground

/-! # 全部 proper 后继共用的内部初等模型

将实际辅助图加入可数种子。函数求值与有序对坐标闭包自动把每个成员阶段的
后继索引和必要名称取回同一个 N，再直接调用已证明的名称后继迭代引理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 辅助图属于 N 即足以统一取得其全部成员阶段的相邻后继迭代引理。 -/
theorem row_pr_family_pil_l {ω δ F G b U χ H N w v}
    (h : Row_system_d I δ F G b) (hU : Row_pr_family_d I δ F G b U)
    (hN : Hsub_d I ω χ H N) (hLift : Hlift_d M ω δ F G b χ H N w v)
    (hFN : M.mem F N) (hGN : M.mem G N) (hUN : M.mem U N) :
    ∀ α β B R D V, M.mem α N → M.SuccessorOf β α → Entry_d M α B F → Entry_d M α R G →
      Entry_d M β D F → Entry_d M β V G → Row_pil_d I α B R b D V N := by
  obtain ⟨hω, hχ, hωχ, hH, _, c, J, d, S, hM, hSub, hElem⟩ := hN
  have htr := ZF.h_transitive_l I hZF hH
  intro α β B R D V hαN hβ hB hR hD hV
  have hαδ := (h.conditions.2.2 α).mpr ⟨B, hB⟩
  have hβδ := (h.conditions.2.2 β).mpr ⟨D, hD⟩
  obtain ⟨x, hx⟩ := (hU.domain α).mpr ⟨β, hβδ, hβ⟩
  have hxN := selem_entry_value_l I hM.2 htr hZF hω hSub hElem hUN hαN hU.function.2 hx
  obtain ⟨y, hxy, hy⟩ := row_pr_pick_resolve_l hZF.1 h.conditions.2.1.2 h.relations.2.1.2 hβ hB hR hD hV (hU.picks α x hx)
  obtain ⟨hβN, hyN⟩ := selem_kpair_coords_l I hZF hω htr hM.2 hSub hElem hxN hxy
  obtain ⟨t, C, w', J', u, v', hyt, hu, hv, A, T, W, Q, X, hPool, hStep, hRep, hPr⟩ := hy
  obtain ⟨htN, huN⟩ := selem_kpair_coords_l I hZF hω htr hM.2 hSub hElem hyN hyt
  obtain ⟨hCN, hvN⟩ := selem_kpair_coords_l I hZF hω htr hM.2 hSub hElem huN hu
  obtain ⟨hwN, hJN⟩ := selem_kpair_coords_l I hZF hω htr hM.2 hSub hElem hvN hv
  have hDN := selem_entry_value_l I hM.2 htr hZF hω hSub hElem hFN hβN h.conditions.2.1.2 hD
  exact row_step_pil_l hZFC hω hχ hωχ hH hM.2 hSub hElem hLift h.conditions.2.1 h.relations.2.1
    hFN hGN hαδ hαN hB hR htN hCN hDN (h.stages α B R hB hR) hStep hPool hRep
    (h.stages β D V hD hV).order (h.links α β B R D V hB hR hD hV (fun i hi => (hβ i).mpr (Or.inl hi))) hPr hwN hJN

/-- 从真实 proper 后继和种子一次构造共同 N、相邻区间及全部内部有限区间。 -/
theorem row_pr_prepare_l {ω δ F G b A U} (hω : M.IsOmega ω) (h : Row_system_d I δ F G b)
    (hU : Row_pr_family_d I δ F G b U)
    (ha : M.CardinalLessOrEqual I A ω) :
    ∃ U χ H N w v J, Row_pr_family_d I δ F G b U ∧ Hsub_d I ω χ H N ∧ M.MemberSubset A N ∧
      M.mem ω N ∧ M.mem F N ∧ M.mem G N ∧ M.mem δ N ∧ M.mem b N ∧ M.mem U N ∧ M.mem J N ∧
      Hlift_d M ω δ F G b χ H N w v ∧ Check_graph_d M b J ∧
      (∀ i P, Entry_d M i P F → ∃ t, Entry_d M P t J) ∧
      (∀ α β B R D V, M.mem α N → M.SuccessorOf β α → Entry_d M α B F → Entry_d M α R G →
        Entry_d M β D F → Entry_d M β V G → Row_pil_d I α B R b D V N) ∧
      ∀ i, M.mem i ω → Row_pil_stage_d I F G b N i := by
  obtain ⟨A₀, hA₀⟩ := KP.exists_insert (ZF.modelsKP hZF) A ω
  obtain ⟨A₁, hA₁⟩ := KP.exists_insert (ZF.modelsKP hZF) A₀ U
  obtain ⟨χ, H, N, w, v, J, hN, hA, hFN, hGN, hδN, hbN, hJN, hLift, hJ, hCheck⟩ :=
    ng_family_ground_l (δ := δ) (b := b) hZFC hω h.conditions.2.1 h.relations.2.1
      (ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω ha hA₀) hA₁)
  have hAN a (ha : M.mem a A) : M.mem a N := hA a ((hA₁ a).mpr (Or.inl ((hA₀ a).mpr (Or.inl ha))))
  have hωN := hA ω ((hA₁ ω).mpr (Or.inl ((hA₀ ω).mpr (Or.inr rfl))))
  have hUN := hA U ((hA₁ U).mpr (Or.inr rfl))
  have hStep := row_pr_family_pil_l hZFC h hU hN hLift hFN hGN hUN
  have hN' := hN
  obtain ⟨_, hχ, _, hH, _, c, T, d, S, hM, hSub, hElem⟩ := hN'
  have hNat := row_pil_nat_l hZF hω hχ.isLimitOrdinal hH hM.2 hSub hElem hωN h hStep
  exact ⟨U, χ, H, N, w, v, J, hU, hN, hAN, hωN, hFN, hGN, hδN, hbN, hUN, hJN, hLift, hJ, hCheck,
    hStep, hNat⟩

end YesMetaZFC.Model.Forcing.Internal
