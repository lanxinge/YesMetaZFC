import YesMetaZFC.Model.Forcing.Iteration.Stage.Basic
import YesMetaZFC.Model.Forcing.Applications.Cohen.Names

/-! # 添加量名称参数化的坐标后继实例

Cohen 条件集、序关系和顶名称由既有全局构造取得，再装入部分函数后继。
添加量可以依赖先前泛型，第二坐标继续使用前阶段的内部名称力迫。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

/-- 添加量名称确定整个 Cohen 后继，规范名称和偏序集合均由实际构造式给出。 -/
def Row_cohen_d (I : kpair_convention_l.Interpretation M) (α B R e κ D V : M.Domain) : Prop :=
  ∃ A T t, Cohen_names_d I B R B κ A T t ∧ Row_next_d M α B R e A T t D V

def row_cohen_m {n} (α B R e κ D V : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj
    (cohen_names_m B.weaken.weaken.weaken R.weaken.weaken.weaken B.weaken.weaken.weaken
      κ.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
    (row_next_m α.weaken.weaken.weaken B.weaken.weaken.weaken R.weaken.weaken.weaken e.weaken.weaken.weaken
      (.bound 2) (.bound 1) .newest D.weaken.weaken.weaken V.weaken.weaken.weaken))))
derive_free_closed row_cohen_m

theorem row_cohen_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (α B R e κ D V : Term n) : Formula.satisfies ρ (row_cohen_m α B R e κ D V) ↔
      Row_cohen_d I (α.eval ρ) (B.eval ρ) (R.eval ρ) (e.eval ρ) (κ.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_cohen_m, Row_cohen_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    cohen_names_sat_l I hE, row_next_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 唯一性同时消去名称见证差异与具体二步条件表示差异。 -/
theorem row_cohen_unique_l (hZF : M.Models ZF) {α B R e κ D V D' V'}
    (O : Cond_order_d M B R B) (hκ : Name_d M B κ)
    (h : Row_cohen_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R e κ D V)
    (h' : Row_cohen_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R e κ D' V') :
    D = D' ∧ V = V' := by
  obtain ⟨A, T, t, hN, hD⟩ := h
  obtain ⟨A', T', t', hN', hD'⟩ := h'
  obtain ⟨ha, hr, ht⟩ := cohen_names_unique_l O hZF hκ hN hN'
  subst A'
  subst T'
  subst t'
  exact row_next_unique_l M hZF.1 hD hD'

/-- 任意已有坐标阶段都可实际添加指定名称数量的 Cohen 实数后继，保留两类支撑。 -/
theorem row_cohen_successor_l (hZF : M.Models ZF)
    {α β B R e κ : M.Domain} (h : Row_stage_d M α B R e) (hβ : M.SuccessorOf β α)
    (hκ : Name_d M B κ) : ∃ D V G, Row_stage_d M β D V e ∧
        Row_cohen_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R e κ D V ∧
        Reg_embed_d M B R B D V D G ∧
        (∀ p q, Entry_d M p q G ↔ M.mem p B ∧ q = p) ∧
        Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R D V ∧
        ∀ {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) k ω, M.IsOmega ω →
          (∀ p, M.mem p B → Row_supp_d I k ω p) → ∀ q, M.mem q D → Row_supp_d I k ω q := by
  have nz {p} (hp : M.mem p B) : p ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hp)
  obtain ⟨A, T, t, hNames, _⟩ := cohen_names_l h.order hZF hκ
  obtain ⟨D, V, G, hStage, hNext, hReg, hId, hRestr, hSupp⟩ :=
    row_successor_l hZF h hβ hNames.1.1 hNames.1.2.1 hNames.1.2.2
      (hNames.2.2.2.1 e h.base (nz h.base)) (hNames.2.2.2.2 e h.base (nz h.base))
  exact ⟨D, V, G, hStage, ⟨A, T, t, hNames, hNext⟩, hReg, hId, hRestr, hSupp⟩

end YesMetaZFC.Model.Forcing.Internal
