import YesMetaZFC.Model.Forcing.Iteration.Proper.Lemma

/-! # 零前缀的迭代引理给出旧条件的真实主加强

把旧条件的 check 名称输入零阶段商。零阶段的主条件就是空函数，商名称的
尾部比较在这条决定分支上直接成为旧偏序中的字面加强。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pil_ground_l {b B R D V N} (hb : ∀ x, ¬ M.mem x b) (hbN : M.mem b N)
    (h : Row_stage_d M b B R b) (hD : ∀ q, M.mem q D → M.IsSetRelation I q)
    (hP : Row_pil_d I b B R b D V N) {p} (hp : M.mem p D) (hpN : M.mem p N) :
    ∃ q, Below_d M D V D q p ∧ Mstr_d M D V D N q := by
  have hz : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ h.base)
  have eq {r} (hr : M.mem r B) : r = b := hZF.1.eq_of_same_members r b (fun v =>
    ⟨fun hv => by
      obtain ⟨i, s, his⟩ := (h.rows r hr).graph v hv
      exact (hb i ((h.rows r hr).domain i s ⟨v, his, hv⟩)).elim,
      fun hv => (hb v hv).elim⟩)
  have hm : Mstr_d M B R B N b := by
    refine ⟨h.base, hz, fun E _ hd r hr => ?_⟩
    obtain ⟨s, hs, hsE⟩ := hd.2 b h.base hz
    have he := eq hs.1
    subst s
    exact ⟨b, hsE, hbN, r, below_refl_l h.order hr.1 hr.2.1, hr.2.2⟩
  have cut r : M.IsRestrictionOf I b r b := ⟨(row_empty_l M (α := b) hb).graph, fun i s =>
    iff_of_false (fun ⟨v, _, hv⟩ => hb v hv) (fun hx => hb i hx.1)⟩
  obtain ⟨K, hK⟩ := row_quot_exists_l hZF h.base b D N
  obtain ⟨τ, hτ⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b p
  have hτn := check_name_l M (check_range_l M hZF) h.base hτ
  have hbb := below_refl_l h.order h.base hz
  have hτK := row_quot_check_l hZF h.order h.base hK hp hpN h.base (cut p) hτ h.base hbb.2.2
  obtain ⟨q, hq, hpre, hqm, hl⟩ := hP τ b K hK hτn hτK hm
  have hdec : Row_dec_d I b B R b D N τ b p b τ :=
    ⟨hp, hpN, h.base, cut p, hτ, hbb, eq_force_refl_l h.order hZF h.base hτn⟩
  have hsplice := row_splice_restore_l hZF.1 (hD q hq) (row_empty_l M (α := b) hb).graph hpre.2
  exact ⟨q, ⟨hq, hqm.2.1, hl p b τ b hdec hbb q hsplice⟩, hqm⟩

end YesMetaZFC.Model.Forcing.Internal
