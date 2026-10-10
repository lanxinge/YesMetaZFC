import YesMetaZFC.Model.Forcing.Applications.Collapse.Basic
import YesMetaZFC.Model.Forcing.Closed.Syntax
import YesMetaZFC.Model.Forcing.TwoStep.Top

/-! # 可数部分函数偏序的原公式规格

条件集和完整反向包含关系由参数唯一确定；只在证明可数闭性时使用 ZFC。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Coll_spec_d (I : kpair_convention_l.Interpretation M) (ω X Y Q T : M.Domain) : Prop :=
  (∀ p, M.mem p Q ↔ Coll_d I ω X Y p) ∧ (∀ v, M.mem v T → ∃ p q, KPair_d M v p q) ∧
    ∀ p q, Entry_d M p q T ↔ M.mem p Q ∧ M.mem q Q ∧ M.MemberSubset q p

def coll_spec_m {n} (ω X Y Q T : Term n) : Formula 1 n :=
  .conj (.forallE (.iff (.mem .newest Q.weaken)
    (coll_m kpair_convention_l ω.weaken X.weaken Y.weaken .newest)))
    (.conj (Formula.isRelation kpair_convention_l T) (.forallE (.forallE
      (.iff (entry_m (.bound 1) .newest T.weaken.weaken)
        (.conj (.mem (.bound 1) Q.weaken.weaken)
          (.conj (.mem .newest Q.weaken.weaken) (Formula.subset .newest (.bound 1))))))))
derive_free_closed coll_spec_m

theorem coll_spec_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (ω X Y Q T : Term n) : Formula.satisfies ρ (coll_spec_m ω X Y Q T) ↔
      Coll_spec_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) (Q.eval ρ) (T.eval ρ) := by
  simp only [coll_spec_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, coll_sat_l I hE]
  simp only [Coll_spec_d, Formula.satisfies_mem_iff, Formula.isRelation,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, kpair_sat_l M hE,
    kpair_convention_l, entry_sat_l M hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem coll_spec_exists_l (hZF : M.Models ZF) (ω X Y : M.Domain) : ∃ Q T,
    Coll_spec_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω X Y Q T := by
  obtain ⟨Q, hQ⟩ := coll_set_l (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) hZF ω X Y
  obtain ⟨T, hT, _, hGraph⟩ := subset_order_l M hZF Q
  exact ⟨Q, T, hQ, hGraph, hT⟩

theorem coll_spec_unique_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {ω X Y Q T Q' T'}
    (h : Coll_spec_d I ω X Y Q T) (h' : Coll_spec_d I ω X Y Q' T') : Q = Q' ∧ T = T' := by
  have he := hE.eq_of_same_members Q Q' (fun p => (h.1 p).trans (h'.1 p).symm)
  subst Q'
  exact ⟨rfl, entry_ext_l M hE h.2.1 h'.2.1 (fun p q => (h.2.2 p q).trans (h'.2.2 p q).symm)⟩

theorem coll_spec_top_l (I : kpair_convention_l.Interpretation M) {ω X Y Q T o}
    (h : Coll_spec_d I ω X Y Q T) (ho : ∀ x, ¬ M.mem x o) :
    Preord_d M Q T ∧ M.mem o Q ∧ ∀ p, M.mem p Q → Entry_d M p o T := by
  have hoQ := (h.1 o).mpr (coll_empty_l I ho)
  exact ⟨⟨fun p hp => (h.2.2 p p).mpr ⟨hp, hp, fun _ h => h⟩,
    fun p q r hp _ hr hpq hqr => (h.2.2 p r).mpr
      ⟨hp, hr, fun x hx => ((h.2.2 p q).mp hpq).2.2 x (((h.2.2 q r).mp hqr).2.2 x hx)⟩⟩,
    hoQ, fun p hp => (h.2.2 p o).mpr ⟨hp, hoQ, fun x hx => (ho x hx).elim⟩⟩

theorem coll_spec_top_unique_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {ω X Y Q T t u}
    (h : Coll_spec_d I ω X Y Q T)
    (ht : M.mem t Q ∧ ∀ p, M.mem p Q → Entry_d M p t T)
    (hu : M.mem u Q ∧ ∀ p, M.mem p Q → Entry_d M p u T) : t = u :=
  hE.eq_of_same_members t u (fun x =>
    ⟨((h.2.2 u t).mp (ht.2 u hu.1)).2.2 x, ((h.2.2 t u).mp (hu.2 t ht.1)).2.2 x⟩)

theorem coll_spec_closed_l (hZFC : M.Models ZFC) {ω X Y Q T} (hω : M.IsOmega ω)
    (h : Coll_spec_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC))))
      ω X Y Q T) : Closed_d (kpair_interpretation_l M hZFC.1
        (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) Q T Q ω := by
  have hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hP := (coll_spec_top_l I h ho).1
  have O : Cond_order_d M Q T Q := ⟨hP.1, hP.2,
    fun p _ hp => (KP.mem_irrefl_d (ZF.modelsKP hZF) Q ((h.2.2 p Q).mp hp).2.1).elim⟩
  intro f hf
  obtain ⟨q, hq, hqs⟩ := coll_union_l I hZFC hω h.1 hf.1 (fun i j p q hij hip hjq =>
    ((h.2.2 q p).mp (chain_lower_l O hZF hω hf i j p q hij hip hjq)).2.2)
  exact ⟨q, hq, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) Q (he ▸ hq),
    fun i p hip => (h.2.2 q p).mpr ⟨hq, hf.1.output_mem_of_pairMember hip, hqs i p hip⟩⟩

end YesMetaZFC.Model.Forcing.Internal
