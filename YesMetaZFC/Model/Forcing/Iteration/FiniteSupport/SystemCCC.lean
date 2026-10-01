import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.CCC
import YesMetaZFC.Model.Forcing.Iteration.FiniteSupport.SuccessorCCC

/-! # 模型内有限支撑迭代的 CCC 定理

后继证书指明真实名称偏序、被迫 CCC 及实际二步重编码。零阶段由空函数刻画，
非零极限由有限尾支撑计数处理；最后对原 CCC 公式作内部超限归纳。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 后继规格保存实际被迫 CCC 的名称及其坐标装配。 -/
def Row_ccc_next_d (α B R e D V : M.Domain) : Prop := ∃ A T t,
  Name_d M B T ∧
  Forces_d M B R B (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) e ∧
  Forces_d M B R B (ccc_exists_m (.bound 0) (.bound 1)) (ord_env_l M A T) e ∧
  Row_next_d M α B R e A T t D V

/-- 每个名称后继被迫 CCC 的有限支撑系统，其所有内部阶段都满足 CCC。 -/
theorem row_system_ccc_l (hZFC : M.Models ZFC) {γ F H e ω}
    (h : Row_system_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) γ F H e)
    (hω : M.IsOmega ω)
    (hS : Row_system_supp_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) false ω F)
    (hNext : ∀ α β D V, M.SuccessorOf β α → Entry_d M β D F → Entry_d M β V H →
      ∃ B R, Entry_d M α B F ∧ Entry_d M α R H ∧ Row_ccc_next_d α B R e D V) :
    ∀ δ D V, Entry_d M δ D F → Entry_d M δ V H → Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω D V D := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 3 := ((⟨fun _ => F, fun _ => F⟩ : Env M 1).push H).push ω
  let φ : UnarySchema 3 := {
    body := .forallE (.forallE (.imp (entry_m (.bound 2) (.bound 1) (.bound 5))
      (.imp (entry_m (.bound 2) .newest (.bound 4)) (ccc_m kpair_convention_l (.bound 3) (.bound 1) .newest (.bound 1))))) }
  have hφ δ : φ.denote ρ δ ↔ ∀ D V, Entry_d M δ D F → Entry_d M δ V H → Ccc_d M I ω D V D := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      entry_sat_l M hZF.1, ccc_sat_l I hZF.1]
    rfl
  intro δ D V hD hV
  apply (hφ δ).mp ?_ D V hD hV
  apply (h.conditions.1.mem ((h.conditions.2.2 δ).mpr ⟨D, hD⟩)).induction (fun β => φ.denote ρ β)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ.neg ρ δ
    exact ⟨C, fun β => by simpa only [UnarySchema.denote, UnarySchema.neg, Formula.satisfies_neg_iff] using hC β⟩
  · intro β hβ ih
    apply (hφ β).mpr
    intro D V hD hV
    rcases Structure.IsOrdinal.classify hZF.1 hβ with hz | hs | hl
    · intro A ha
      obtain ⟨o, ho, hoω⟩ := hω.1.1
      have he := hZF.1.eq_of_same_members o e (fun i => iff_of_false (ho i) (h.empty i))
      have heω : M.mem e ω := he ▸ hoω
      apply ZF.exists_inclusionInjection hZF I
      intro p hp
      have hr := (h.stages β D V hD hV).rows p (ha.1 p hp).1
      have he := row_ext_l hZF.1 hr (row_empty_l M (α := β) h.empty) (fun i s =>
        ⟨fun his => False.elim (hz i (hr.domain i s his)),
          fun ⟨v, _, hv⟩ => False.elim (h.empty v hv)⟩)
      exact he ▸ heω
    · obtain ⟨α, _, hs⟩ := hs
      obtain ⟨B, R, hB, hR, A, T, t, hT, hP, hC, hn⟩ := hNext α β D V hs hD hV
      exact row_next_ccc_l hZFC hω (h.stages α B R hB hR) hs
        ((hφ α).mp (ih α hs.predecessor_mem) B R hB hR) hT hP hC hn
    · exact row_stage_ccc_l hZFC h hω hl hS hD hV
        (fun α B R hα hB hR => (hφ α).mp (ih α hα) B R hB hR)

end YesMetaZFC.Model.Forcing.Internal
