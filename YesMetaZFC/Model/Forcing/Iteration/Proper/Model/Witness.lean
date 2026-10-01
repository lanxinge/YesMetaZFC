import YesMetaZFC.Model.Forcing.Proper.Name
import YesMetaZFC.Model.Forcing.Iteration.Stage.Basic

/-! # proper 后继的实际辅助见证

辅助码只保存同一个 N 必须包含的四个对象：顶名称、二步条件集、内部 ω 名称、
proper club 名称。名称库及其余装配见证由实际原公式量化，不加入新的存在前提。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_pr_next_d (α B R b D V : M.Domain) : Prop := ∃ A T t, Name_d M B T ∧
  Forces_d M B R B (proper_exists_m .newest (.bound 1)) (ord_env_l M A T) b ∧ Row_next_d M α B R b A T t D V

def Row_pr_wit_d (α B R b D V t C w J : M.Domain) : Prop := ∃ A T W S X,
  Name_pool_d M B A t W ∧ Two_step_d M B R B b A T W C S ∧ Row_repr_d M α t C S D V ∧ Pr_name_d M B R B b A T w X J

def row_pr_wit_m {n} (α B R b D V t C w J : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (name_pool_m B.weaken.weaken.weaken.weaken.weaken (.bound 4) t.weaken.weaken.weaken.weaken.weaken (.bound 2))
      (.conj (two_step_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken
        b.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 2) C.weaken.weaken.weaken.weaken.weaken (.bound 1))
        (.conj (row_repr_m α.weaken.weaken.weaken.weaken.weaken t.weaken.weaken.weaken.weaken.weaken
          C.weaken.weaken.weaken.weaken.weaken (.bound 1) D.weaken.weaken.weaken.weaken.weaken V.weaken.weaken.weaken.weaken.weaken)
          (pr_name_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken
            b.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) w.weaken.weaken.weaken.weaken.weaken
            .newest J.weaken.weaken.weaken.weaken.weaken))))))))
derive_free_closed row_pr_wit_m

theorem row_pr_wit_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α B R b D V t C w J : Term n) :
    Formula.satisfies ρ (row_pr_wit_m α B R b D V t C w J) ↔
      Row_pr_wit_d (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ)
        (t.eval ρ) (C.eval ρ) (w.eval ρ) (J.eval ρ) := by
  simp only [row_pr_wit_m, Row_pr_wit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    name_pool_sat_l M hE, two_step_sat_l hE, row_repr_sat_l M hE, pr_name_sat_l hE, Definitional.Term.eval_weaken]
  rfl

def Row_pr_aux_d (α B R b D V x : M.Domain) : Prop := ∃ t C w J u v,
  KPair_d M x t u ∧ KPair_d M u C v ∧ KPair_d M v w J ∧ Row_pr_wit_d α B R b D V t C w J

def row_pr_aux_m {n} (α B R b D V x : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (kpair_m x.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 1))
      (.conj (kpair_m (.bound 1) (.bound 4) .newest) (.conj (kpair_m .newest (.bound 3) (.bound 2))
        (row_pr_wit_m α.weaken.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken.weaken
          R.weaken.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken.weaken
          D.weaken.weaken.weaken.weaken.weaken.weaken V.weaken.weaken.weaken.weaken.weaken.weaken
          (.bound 5) (.bound 4) (.bound 3) (.bound 2))))))))))
derive_free_closed row_pr_aux_m

theorem row_pr_aux_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α B R b D V x : Term n) :
    Formula.satisfies ρ (row_pr_aux_m α B R b D V x) ↔
      Row_pr_aux_d (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ) (x.eval ρ) := by
  simp only [row_pr_aux_m, Row_pr_aux_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, row_pr_wit_sat_l hE, Definitional.Term.eval_weaken]
  rfl

/-- 每个实际被迫 proper 的后继都产生一个辅助码；整个构造只在对象 ZFC 中选择。 -/
theorem row_pr_aux_exists_l (hZFC : M.Models ZFC) {α B R b D V}
    (h : Row_stage_d M α B R b) (hp : Row_pr_next_d (M := M) α B R b D V) : ∃ x, Row_pr_aux_d (M := M) α B R b D V x := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨A, T, t, hT, hPr, W, C, S, hW, hStep, hRep⟩ := hp
  have hA : Name_d M B A := ⟨W, hW.left, hStep.closed⟩
  obtain ⟨w, X, J, hJ⟩ := pr_name_exists_l h.order hZFC hA hT h.base
    (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ h.base)) hPr
  obtain ⟨v, hv⟩ := I.total w J
  obtain ⟨u, hu⟩ := I.total C v
  obtain ⟨x, hx⟩ := I.total t u
  exact ⟨x, t, C, w, J, u, v, hx, hu, hv, A, T, W, S, X, hW, hStep, hRep, hJ⟩

end YesMetaZFC.Model.Forcing.Internal
