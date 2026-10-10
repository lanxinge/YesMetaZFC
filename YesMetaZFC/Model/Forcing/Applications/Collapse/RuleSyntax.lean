import YesMetaZFC.Model.Forcing.Applications.Collapse.NameSyntax
import YesMetaZFC.Model.Forcing.Iteration.Recursion.Rule

/-! # 参数化塌缩的确定后继规则

固定旧 ω、源集和目标集参数；每阶段重新取其规范名称，再使用已证明唯一的
塌缩名称三元组和 Row_next 构造。规则输入保留完整历史，输出为真实坐标偏序。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_coll_d (I : kpair_convention_l.Interpretation M) (ω X Y α B R b D V : M.Domain) : Prop :=
  ∃ w x y A T t, Check_d M b ω w ∧ Check_d M b X x ∧ Check_d M b Y y ∧
    Coll_names_d I B R B w x y A T t ∧ Row_next_d M α B R b A T t D V

def row_coll_m {n} (ω X Y α B R b D V : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (check_m b.weaken.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5))
      (.conj (check_m b.weaken.weaken.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4))
        (.conj (check_m b.weaken.weaken.weaken.weaken.weaken.weaken Y.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3))
          (.conj (coll_names_m B.weaken.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken.weaken
            B.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
            (row_next_m α.weaken.weaken.weaken.weaken.weaken.weaken B.weaken.weaken.weaken.weaken.weaken.weaken
              R.weaken.weaken.weaken.weaken.weaken.weaken b.weaken.weaken.weaken.weaken.weaken.weaken
              (.bound 2) (.bound 1) .newest D.weaken.weaken.weaken.weaken.weaken.weaken V.weaken.weaken.weaken.weaken.weaken.weaken))))))))))
derive_free_closed row_coll_m

theorem row_coll_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (ω X Y α B R b D V : Term n) : Formula.satisfies ρ (row_coll_m ω X Y α B R b D V) ↔
      Row_coll_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) (α.eval ρ) (B.eval ρ) (R.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [row_coll_m, Row_coll_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    check_sat_l M hE, coll_names_sat_l I hE, row_next_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

def Coll_rule_d (I : kpair_convention_l.Interpretation M) (ω X Y δ F G b D V : M.Domain) : Prop :=
  ∃ α B R, M.SuccessorOf δ α ∧ Entry_d M α B F ∧ Entry_d M α R G ∧ Row_coll_d I ω X Y α B R b D V

def coll_rule_m {n} (ω X Y δ F G b D V : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj (Formula.isSuccessor δ.weaken.weaken.weaken (.bound 2))
    (.conj (entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken)
      (.conj (entry_m (.bound 2) .newest G.weaken.weaken.weaken)
        (row_coll_m ω.weaken.weaken.weaken X.weaken.weaken.weaken Y.weaken.weaken.weaken
          (.bound 2) (.bound 1) .newest b.weaken.weaken.weaken D.weaken.weaken.weaken V.weaken.weaken.weaken))))))
derive_free_closed coll_rule_m

theorem coll_rule_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (ω X Y δ F G b D V : Term n) : Formula.satisfies ρ (coll_rule_m ω X Y δ F G b D V) ↔
      Coll_rule_d I (ω.eval ρ) (X.eval ρ) (Y.eval ρ) (δ.eval ρ) (F.eval ρ) (G.eval ρ) (b.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [coll_rule_m, Coll_rule_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, entry_sat_l M hE, row_coll_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

def coll_rule_s : BinarySchema 7 := {
  body := coll_rule_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }

theorem coll_rule_denote_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 3) (δ F G b D V) : coll_rule_s.denote (row_rule_env_l ρ δ F G b) D V ↔
      Coll_rule_d I (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) δ F G b D V :=
  coll_rule_sat_l I hE (((row_rule_env_l ρ δ F G b).push D).push V) _ _ _ _ _ _ _ _ _

end YesMetaZFC.Model.Forcing.Internal
