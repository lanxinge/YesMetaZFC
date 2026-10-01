import YesMetaZFC.Model.Forcing.Iteration.Names.ProjectionName
import YesMetaZFC.Model.Forcing.Iteration.Names.QuotientOrder

/-! # 变动主前缀对旧商名称的逐阶段比较

在决定原名称的每个分支上，当前主前缀加强旧条件的当前阶段限制。
当前前缀尚不覆盖整个旧条件的支撑，因此比较必须保留目标限制的阶段参数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Row_cut_lower_d (I : kpair_convention_l.Interpretation M) (α B R b D N τ p β V q : M.Domain) : Prop :=
  ∀ r a v c, Row_dec_d I α B R b D N τ c r a v → Below_d M B R B c p →
    ∀ w t, Row_splice_d M α c q w → M.IsRestrictionOf I t r β → Entry_d M w t V

def row_cut_lower_m {n} (α B R b D N τ p β V q : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE
    (.imp (row_dec_m α.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
      b.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken N.weaken.weaken.weaken.weaken
      τ.weaken.weaken.weaken.weaken .newest (.bound 3) (.bound 2) (.bound 1))
      (.imp (below_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken
        .newest p.weaken.weaken.weaken.weaken)
        (.forallE (.forallE (.imp (row_splice_m α.weaken.weaken.weaken.weaken.weaken.weaken
          (.bound 2) q.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1))
          (.imp (Formula.isRestriction kpair_convention_l .newest (.bound 5) β.weaken.weaken.weaken.weaken.weaken.weaken)
            (entry_m (.bound 1) .newest V.weaken.weaken.weaken.weaken.weaken.weaken))))))))))
derive_free_closed row_cut_lower_m

theorem row_cut_lower_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R b D N τ p β V q : Term n) : Formula.satisfies ρ (row_cut_lower_m α B R b D N τ p β V q) ↔
      Row_cut_lower_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (N.eval ρ)
        (τ.eval ρ) (p.eval ρ) (β.eval ρ) (V.eval ρ) (q.eval ρ) := by
  simp only [row_cut_lower_m, Row_cut_lower_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    row_dec_sat_l I hE, below_sat_l M hE, row_splice_sat_l M hE, Formula.satisfies_isRestriction_iff I,
    entry_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

/-- 原主前缀本身给出比较的起点；不需要主性或集合论公理。 -/
theorem row_cut_base_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {α B R b D N τ p}
    (h : Row_stage_d M α B R b) (hp : M.mem p B) :
    Row_cut_lower_d (kpair_interpretation_l M hE hP) α B R b D N τ p α R p := by
  intro r a v c hc _ w t hw ht
  obtain ⟨_, _, _, har, _, hca, _⟩ := hc
  have he := har.eq hE ht
  have hwc := row_splice_absorb_l hE (h.rows p hp) hw
  subst t; subst w
  exact hca.2.2

/-- 实际投影名称之下的尾部加强，正是对原名称的当前阶段限制的比较。 -/
theorem row_cut_project_l (hZF : M.Models ZF) {ω χ H c J d N S α B R b D τ p β E T f σ q}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y J ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H J N S)
    (hElem : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hβN : M.mem β N) (hαβ : M.MemberSubset α β) (h : Row_stage_d M α B R b)
    (hf : Row_proj_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β D E f)
    (hApp : Check_app_d M B R B b f τ σ)
    (hl : Row_quot_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b E T N σ p q) :
    Row_cut_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D N τ p β T q := by
  intro r a v c hc hcp w t hw ht
  obtain ⟨hr, hrN, ha, har, hrv, hca, heq⟩ := hc
  obtain ⟨x, hx, hrx⟩ := hf.1.2.2 r hr
  have hxr := ((hf.2 r x).mp hrx).2
  have hxN := selem_restriction_l hZF hω hχ hH hJ hSub hElem hβN hrN hxr
  obtain ⟨u, hxu, _, _⟩ := zf_check_l M hZF h.base x
  have hσu := hApp c r x v u ⟨hcp.1, hcp.2.1, h.top c hcp.1⟩ hrx hrv hxu heq
  have hxt := hxr.eq hZF.1 ht
  exact hxt ▸ hl x a u c ⟨hx, hxN, ha, hxr.trans har hαβ, hxu, hca, hσu⟩ hcp w hw

end YesMetaZFC.Model.Forcing.Internal
