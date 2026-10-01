import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Witness
import YesMetaZFC.Model.Forcing.Iteration.Stage.System
import YesMetaZFC.SetTheory.CollectionChoice

/-! # 整个迭代共用的 proper 辅助图

图的定义域恰为后继阶段仍在系统内的索引。每个值保存该后继索引及实际辅助码，
整张图由对象收集与选择构造，不枚举外部序数，也不预设见证名称的秩界。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_pr_pick_d (F G b α x : M.Domain) : Prop := ∃ β B R D V y,
  M.SuccessorOf β α ∧ Entry_d M α B F ∧ Entry_d M α R G ∧ Entry_d M β D F ∧ Entry_d M β V G ∧
    KPair_d M x β y ∧ Row_pr_aux_d α B R b D V y

def row_pr_pick_m {n} (F G b α x : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (Formula.isSuccessor (.bound 5) α.weaken.weaken.weaken.weaken.weaken.weaken)
      (.conj (entry_m α.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) F.weaken.weaken.weaken.weaken.weaken.weaken)
        (.conj (entry_m α.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3) G.weaken.weaken.weaken.weaken.weaken.weaken)
          (.conj (entry_m (.bound 5) (.bound 2) F.weaken.weaken.weaken.weaken.weaken.weaken)
            (.conj (entry_m (.bound 5) (.bound 1) G.weaken.weaken.weaken.weaken.weaken.weaken)
              (.conj (kpair_m x.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) .newest)
                (row_pr_aux_m α.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3)
                  b.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))))))))))
derive_free_closed row_pr_pick_m

theorem row_pr_pick_sat_l (hE : Extensional M) {n} (ρ : Env M n) (F G b α x : Term n) :
    Formula.satisfies ρ (row_pr_pick_m F G b α x) ↔ Row_pr_pick_d (F.eval ρ) (G.eval ρ) (b.eval ρ) (α.eval ρ) (x.eval ρ) := by
  simp only [row_pr_pick_m, Row_pr_pick_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, entry_sat_l M hE, kpair_sat_l M hE, row_pr_aux_sat_l hE, Definitional.Term.eval_weaken]
  rfl

structure Row_pr_family_d (I : kpair_convention_l.Interpretation M) (δ F G b U : M.Domain) : Prop where
  function : M.IsSetFunction I U
  domain : ∀ α, (∃ x, Entry_d M α x U) ↔ ∃ β, M.mem β δ ∧ M.SuccessorOf β α
  picks : ∀ α x, Entry_d M α x U → Row_pr_pick_d F G b α x

def row_pr_family_m {n} (δ F G b U : Term n) : Formula 1 n :=
  .conj (Formula.isFunction kpair_convention_l U)
    (.conj (.forallE (.iff (.existsE (entry_m (.bound 1) .newest U.weaken.weaken))
      (.existsE (.conj (.mem .newest δ.weaken.weaken) (Formula.isSuccessor .newest (.bound 1))))))
      (.forallE (.forallE (.imp (entry_m (.bound 1) .newest U.weaken.weaken)
        (row_pr_pick_m F.weaken.weaken G.weaken.weaken b.weaken.weaken (.bound 1) .newest)))))
derive_free_closed row_pr_family_m

theorem row_pr_family_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (δ F G b U : Term n) : Formula.satisfies ρ (row_pr_family_m δ F G b U) ↔
      Row_pr_family_d I (δ.eval ρ) (F.eval ρ) (G.eval ρ) (b.eval ρ) (U.eval ρ) := by
  simp only [row_pr_family_m, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff, entry_sat_l M hE,
    Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff, Formula.satisfies_imp_iff,
    row_pr_pick_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.function, h.domain, h.picks⟩⟩

/-- 任意实际 proper 名称后继系统都有统一的内部辅助函数图。 -/
theorem row_pr_family_l (hZFC : M.Models ZFC) {δ F G b}
    (h : Row_system_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) δ F G b)
    (hn : ∀ α β D V, M.SuccessorOf β α → Entry_d M β D F → Entry_d M β V G →
      ∃ B R, Entry_d M α B F ∧ Entry_d M α R G ∧ Row_pr_next_d (M := M) α B R b D V) :
    ∃ U, Row_pr_family_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) δ F G b U := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let θ : UnarySchema 1 := { body := .existsE (.conj (.mem .newest (.bound 2)) (Formula.isSuccessor .newest (.bound 1))) }
  obtain ⟨J, hJ⟩ := ZF.separation_exists_d hZF θ ⟨fun _ => δ, fun _ => δ⟩ δ
  have mem α : M.mem α J ↔ ∃ β, M.mem β δ ∧ M.SuccessorOf β α := by
    have ht : θ.denote (⟨fun _ => δ, fun _ => δ⟩ : Env M 1) α ↔ ∃ β, M.mem β δ ∧ M.SuccessorOf β α := by
      simp only [UnarySchema.denote, θ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_mem_iff, Formula.satisfies_isSuccessor_iff]
      rfl
    exact (hJ α).trans ((and_congr_right fun _ => ht).trans
      ⟨And.right, fun ⟨β, hβ, hβα⟩ => ⟨h.conditions.1.transitive β hβ α hβα.predecessor_mem, β, hβ, hβα⟩⟩)
  let ρ : Env M 3 := ((⟨fun _ => F, fun _ => F⟩ : Env M 1).push G).push b
  let φ : BinarySchema 3 := { body := row_pr_pick_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ α x : φ.denote ρ α x ↔ Row_pr_pick_d (M := M) F G b α x := row_pr_pick_sat_l hZF.1 _ _ _ _ _ _
  obtain ⟨X, U, hU, hu⟩ := ZFC.collect_choice_l I hZFC φ ρ J (by
    intro α hα
    obtain ⟨β, hβ, hβα⟩ := (mem α).mp hα
    obtain ⟨D, hD⟩ := (h.conditions.2.2 β).mp hβ
    obtain ⟨V, hV⟩ := (h.relations.2.2 β).mp hβ
    obtain ⟨B, R, hB, hR, hp⟩ := hn α β D V hβα hD hV
    obtain ⟨y, hy⟩ := row_pr_aux_exists_l hZFC (h.stages α B R hB hR) hp
    obtain ⟨x, hx⟩ := I.total β y
    exact ⟨x, (hφ α x).mpr ⟨β, B, R, D, V, y, hβα, hB, hR, hD, hV, hx, hy⟩⟩)
  exact ⟨U, hU.1, fun α => (hU.2.1 α).symm.trans (mem α), fun α x hx => (hφ α x).mp (hu α x hx)⟩

/-- 实际阶段函数的单值性使所选辅助码同时适用于该后继的任意给定解码。 -/
theorem row_pr_pick_resolve_l (hE : Extensional M) {F G b α β B R D V x}
    (hF : ∀ i a b, Entry_d M i a F → Entry_d M i b F → a = b)
    (hG : ∀ i a b, Entry_d M i a G → Entry_d M i b G → a = b) (hβ : M.SuccessorOf β α)
    (hB : Entry_d M α B F) (hR : Entry_d M α R G) (hD : Entry_d M β D F) (hV : Entry_d M β V G)
    (hx : Row_pr_pick_d (M := M) F G b α x) : ∃ y, KPair_d M x β y ∧ Row_pr_aux_d (M := M) α B R b D V y := by
  obtain ⟨β', B', R', D', V', y, hβ', hB', hR', hD', hV', hxy, hy⟩ := hx
  have hb := hE.eq_of_same_members β' β (fun t => (hβ' t).trans (hβ t).symm)
  subst β'
  have hBB := hF α B' B hB' hB
  have hRR := hG α R' R hR' hR
  have hDD := hF β D' D hD' hD
  have hVV := hG β V' V hV' hV
  subst B'; subst R'; subst D'; subst V'
  exact ⟨y, hxy, hy⟩

end YesMetaZFC.Model.Forcing.Internal
