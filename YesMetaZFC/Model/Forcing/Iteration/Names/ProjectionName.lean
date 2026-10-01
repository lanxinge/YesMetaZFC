import YesMetaZFC.Model.Forcing.Proper.Elementary.Restriction
import YesMetaZFC.Model.Forcing.Internal.Check.Application
import YesMetaZFC.Model.Forcing.Iteration.Names.Quotient

/-! # 旧条件名称的前缀投影

限制映射是模型内唯一确定的集合函数。将它应用于任意商条件名称后，得到
较短阶段的商条件名称；内部初等性保证投影仍取值于同一个 N。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Row_proj_d (I : kpair_convention_l.Interpretation M) (β D E f : M.Domain) : Prop :=
  M.IsSetFunctionFromTo I f D E ∧ ∀ r a, Entry_d M r a f ↔ M.mem r D ∧ M.IsRestrictionOf I a r β

def row_proj_m {n} (β D E f : Term n) : Formula 1 n :=
  .conj (Formula.isFunctionFromTo kpair_convention_l f D E)
    (.forallE (.forallE (.iff (entry_m (.bound 1) .newest f.weaken.weaken)
      (.conj (.mem (.bound 1) D.weaken.weaken)
        (Formula.isRestriction kpair_convention_l .newest (.bound 1) β.weaken.weaken)))))
derive_free_closed row_proj_m

theorem row_proj_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (β D E f : Term n) : Formula.satisfies ρ (row_proj_m β D E f) ↔
      Row_proj_d I (β.eval ρ) (D.eval ρ) (E.eval ρ) (f.eval ρ) := by
  simp only [row_proj_m, Row_proj_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, entry_sat_l M hE, Formula.satisfies_mem_iff,
    Formula.satisfies_isRestriction_iff I, Definitional.Term.eval_weaken]
  rfl

theorem row_proj_exists_l (hZF : M.Models ZF) {β E S D V}
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β E S D V) :
    ∃ f, Row_proj_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β D E f := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 1 := ⟨fun _ => β, fun _ => β⟩
  let φ : BinarySchema 1 := { body := Formula.isRestriction kpair_convention_l .newest (.bound 1) (.bound 2) }
  have hφ r a : φ.denote ρ r a ↔ M.IsRestrictionOf I a r β := Formula.satisfies_isRestriction_iff I _ _ _ _
  obtain ⟨f, hf, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := E)
    (fun r hr => (k.restrict r hr).elim fun a ha => ⟨a, (hφ r a).mpr ha.2⟩)
    (fun r _ a b ha hb => ((hφ r a).mp ha).eq hZF.1 ((hφ r b).mp hb)) (by
      intro r a hr ha
      obtain ⟨b, hb, hbr⟩ := k.restrict r hr
      exact (((hφ r a).mp ha).eq hZF.1 hbr).symm ▸ hb)
  exact ⟨f, hf, fun r a => (he r a).trans (and_congr_right fun _ => hφ r a)⟩

/-- 自动构造前缀名称、实际限制函数及其函数值力迫；p 和 N 始终保持不变。 -/
theorem row_project_name_l (hZF : M.Models ZF) {ω χ H c J d N S α B R b β E T D V τ p K}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y J ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H J N S)
    (hElem : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hβN : M.mem β N) (hαβ : M.MemberSubset α β) (h : Row_stage_d M α B R b)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β E T D V)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b D N K)
    (hτ : Name_d M B τ) (hτK : Mem_force_d M B R B p τ K) : ∃ σ K' f F,
    Name_d M B σ ∧ Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b E N K' ∧
    Row_proj_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β D E f ∧ Check_d M b f F ∧
    Check_app_d M B R B b f τ σ ∧
    Mem_force_d M B R B p σ K' ∧ Rel_force_d M B R B F p τ σ := by
  obtain ⟨f, hf⟩ := row_proj_exists_l hZF k
  obtain ⟨σ, c', d', F, hσ, hc', _, hF, hForce, hApp⟩ := check_apply_l h.order hZF h.base hf.1 hτ
  obtain ⟨K', hK'⟩ := row_quot_exists_l hZF h.base α E N
  have hτc := row_quot_subset_l hZF h.order h.base hK (fun _ hr _ => hr) hc' (h.top p hτK.1) hτK
  have hrel := (hForce p ⟨hτK.1, (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hτK.1)), h.top p hτK.1⟩ hτc).2
  refine ⟨σ, K', f, F, hσ, hK', hf, hF, hApp, mem_force_dense_l h.order hτK.1 (fun q hq => ?_), hrel⟩
  obtain ⟨r, hrq, s, a, v, hs, hsN, ha, has, hsv, hra, heq⟩ := row_quot_decide_l hK hτK q hq
  obtain ⟨x, hx, hsx⟩ := hf.1.2.2 s hs
  have hxs := ((hf.2 s x).mp hsx).2
  have hxN := selem_restriction_l hZF hω hχ hH hJ hSub hElem hβN hsN hxs
  obtain ⟨u, hxu, hun, _⟩ := zf_check_l M hZF h.base x
  have hσu := hApp r s x v u ⟨hrq.1, hrq.2.1, h.top r hrq.1⟩ hsx hsv hxu heq
  have huK := mem_force_entry_l h.order hZF hrq.1 hun ha
    ((hK'.2 u a).mpr ⟨ha, x, hx, hxN, hxs.trans has hαβ, hxu⟩) hra.2.2
  exact ⟨r, hrq, mem_force_left_l h.order hZF hun hσ hK'.1 (eq_force_symm_l hZF hσ hun hσu) huK⟩

end YesMetaZFC.Model.Forcing.Internal
