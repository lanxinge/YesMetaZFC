import YesMetaZFC.Model.Forcing.Iteration.Names.QuotientComparison
import YesMetaZFC.Model.Forcing.Iteration.Names.QuotientTransfer
import YesMetaZFC.Model.Forcing.Iteration.Names.DenseName

/-! # proper 迭代引理的内部命题与区间复合

结论统一量化全部商条件名称和主前缀，并保留实际尾部加强。恒等区间有直接实例，
相邻后继由原名称主加强构造实现；已证明区间的复合及指定稠密集选择均保持此结论。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Row_pil_d (I : kpair_convention_l.Interpretation M) (α B R b D V N : M.Domain) : Prop :=
  ∀ τ p K, Row_quot_d I α B b D N K → Name_d M B τ → Mem_force_d M B R B p τ K → Mstr_d M B R B N p →
    ∃ q, M.mem q D ∧ M.IsRestrictionOf I p q α ∧ Mstr_d M D V D N q ∧ Row_quot_lower_d I α B R b D V N τ p q

def row_pil_m {n} (α B R b D V N : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE
    (.imp (row_quot_m α.weaken.weaken.weaken B.weaken.weaken.weaken b.weaken.weaken.weaken
      D.weaken.weaken.weaken N.weaken.weaken.weaken .newest)
      (.imp (name_m B.weaken.weaken.weaken (.bound 2))
        (.imp (mem_force_m B.weaken.weaken.weaken R.weaken.weaken.weaken B.weaken.weaken.weaken (.bound 1) (.bound 2) .newest)
          (.imp (mstr_m B.weaken.weaken.weaken R.weaken.weaken.weaken B.weaken.weaken.weaken N.weaken.weaken.weaken (.bound 1))
            (.existsE (.conj (.mem .newest D.weaken.weaken.weaken.weaken)
              (.conj (Formula.isRestriction kpair_convention_l (.bound 2) .newest α.weaken.weaken.weaken.weaken)
                (.conj (mstr_m D.weaken.weaken.weaken.weaken V.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken
                  N.weaken.weaken.weaken.weaken .newest)
                  (row_quot_lower_m α.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken
                    R.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken D.weaken.weaken.weaken.weaken
                    V.weaken.weaken.weaken.weaken N.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) .newest)))))))))))
derive_free_closed row_pil_m

theorem row_pil_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R b D V N : Term n) : Formula.satisfies ρ (row_pil_m α B R b D V N) ↔
      Row_pil_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ) (N.eval ρ) := by
  simp only [row_pil_m, Row_pil_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRestriction_iff I, row_quot_sat_l I hE, name_sat_l M hE, mem_force_sat_l M hE,
    mstr_sat_l M hE, row_quot_lower_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

/-- 恒等区间的真实迭代引理；没有延长条件或额外主性假设。 -/
theorem row_pil_id_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {α B R b N}
    (h : Row_stage_d M α B R b) : Row_pil_d (kpair_interpretation_l M hE hP) α B R b B R N := by
  have self p (hp : M.mem p B) : M.IsRestrictionOf (kpair_interpretation_l M hE hP) p p α :=
    ⟨(h.rows p hp).graph, fun i s => ⟨fun hi => ⟨(h.rows p hp).domain i s hi, hi⟩, And.right⟩⟩
  intro τ p K _ _ _ hm
  refine ⟨p, hm.1, self p hm.1, hm, fun r a v c hc _ w hw => ?_⟩
  obtain ⟨hr, _, _, har, _, hca, _⟩ := hc
  have he := har.eq hE (self r hr)
  have hwc := row_splice_absorb_l hE (h.rows p hm.1) hw
  subst a; subst w
  exact hca.2.2

/-- 任一已经证明的区间自动给出泛型滤子和 check(N) 中的成员力迫。 -/
theorem row_pil_value_l (hZF : M.Models ZF) {α B R b D V N τ p K}
    (h : Row_stage_d M α B R b) (L : Cond_order_d M D V D)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V)
    (hP : Row_pil_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D V N)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b D N K)
    (hτ : Name_d M B τ) (hτK : Mem_force_d M B R B p τ K) (hm : Mstr_d M B R B N p) :
    ∃ q γ ν, M.mem q D ∧ M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α ∧
      Mstr_d M D V D N q ∧ Row_quot_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D V N τ p q ∧
      Gname_d (M := M) D b γ ∧ Check_d M b N ν ∧ Mem_force_d M D V D q τ γ ∧ Mem_force_d M D V D q τ ν := by
  obtain ⟨q, hq, hpre, hqm, hl⟩ := hP τ p K hK hτ hτK hm
  obtain ⟨γ, hγ⟩ := gname_exists_l hZF (k.mem b h.base)
  obtain ⟨ν, hν, hνn, _⟩ := zf_check_l M hZF h.base N
  have hτN := row_quot_subset_l hZF h.order h.base hK (fun _ _ hrN => hrN) hν (h.top p hm.1) hτK
  have hqτN := (regular_mem_l L τ ν).1 p q (k.mem p hm.1) ⟨hq, hqm.2.1, k.below q p hq hpre⟩
    ((row_mem_force_l hZF h.order L k hm.1 hτ hνn).mp hτN)
  exact ⟨q, γ, ν, hq, hpre, hqm, hl, hγ, hν,
    row_quot_accept_l hZF h.order L k hτ hq hpre hK hτK hγ hl, hqτN⟩

/-- 两个已证明区间的迭代引理复合；中间商名称与所有投影均自动构造。 -/
theorem row_pil_comp_l (hZF : M.Models ZF) {ω χ H c J d N S α B R b β E T D V}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y J ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H J N S)
    (hElem : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hβN : M.mem β N) (hαβ : M.MemberSubset α β)
    (h : Row_stage_d M α B R b) (L : Cond_order_d M E T E)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R E T)
    (k' : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β E T D V)
    (hP : Row_pil_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b E T N)
    (hQ : Row_pil_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β E T b D V N) :
    Row_pil_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D V N := by
  intro τ p K hK hτ hτK hm
  obtain ⟨σ, K', f, F, hσ, hK', hf, hF, happ, hσK, hτσ⟩ :=
    row_project_name_l hZF hω hχ hH hJ hSub hElem hβN hαβ h k' hK hτ hτK
  obtain ⟨q, hq, hpq, hqm, hl⟩ := hP σ p K' hK' hσ hσK hm
  obtain ⟨γ, hγ⟩ := gname_exists_l hZF (k.mem b h.base)
  have hσγ := row_quot_accept_l hZF h.order L k hσ hq hpq hK' hσK hγ hl
  obtain ⟨K'', hK'', hτ', hτK'⟩ := row_quot_transfer_l hZF h L k hq hpq hf hF hK hτ hσ hτK hτσ hγ hσγ
  obtain ⟨r, hr, hqr, hrm, hl'⟩ := hQ τ q K'' hK'' hτ' hτK' hqm
  exact ⟨r, hr, hpq.comp_l hqr hαβ, hrm,
    row_quot_lower_comp_l hZF hω hχ hH hJ hSub hElem hβN hαβ h L k hf happ hτ hq hpq hqr hl hl'⟩

end YesMetaZFC.Model.Forcing.Internal
