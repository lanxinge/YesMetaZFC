import YesMetaZFC.Model.Forcing.Stage.Names
import YesMetaZFC.Model.Forcing.Stage.Reduction

/-! # 阶段原子力迫传输的双模拟公式

正向关系在阶段像以下继承源等号力迫；反向关系使用目标等号力迫及其源约减。
两种关系都由实际原公式给出，随后通过有界分离构造内部双模拟。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Eq_push_d (P R z S F q s t : M.Domain) : Prop :=
  ∃ p y a b, Entry_d M p y F ∧ Entry_d M q y S ∧ Name_d M P a ∧ Name_d M P b ∧
    Nmap_d M F a s ∧ Nmap_d M F b t ∧ Eq_force_d M P R z p a b

def eq_push_m {n} (P R z S F q s t : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (entry_m (.bound 3) (.bound 2) F.weaken.weaken.weaken.weaken)
      (.conj (entry_m q.weaken.weaken.weaken.weaken (.bound 2) S.weaken.weaken.weaken.weaken)
        (.conj (name_m P.weaken.weaken.weaken.weaken (.bound 1))
          (.conj (name_m P.weaken.weaken.weaken.weaken .newest)
            (.conj (nmap_m F.weaken.weaken.weaken.weaken (.bound 1) s.weaken.weaken.weaken.weaken)
              (.conj (nmap_m F.weaken.weaken.weaken.weaken .newest t.weaken.weaken.weaken.weaken)
                (eq_force_m P.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken
                  z.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest))))))))))
derive_free_closed eq_push_m

def Eq_pull_d (R Q S w F p s t : M.Domain) : Prop :=
  ∃ q a b, Nmap_d M F s a ∧ Nmap_d M F t b ∧ Eq_force_d M Q S w q a b ∧ Red_d M R Q S w F q p

def eq_pull_m {n} (R Q S w F p s t : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE
    (.conj (nmap_m F.weaken.weaken.weaken s.weaken.weaken.weaken (.bound 1))
      (.conj (nmap_m F.weaken.weaken.weaken t.weaken.weaken.weaken .newest)
        (.conj (eq_force_m Q.weaken.weaken.weaken S.weaken.weaken.weaken w.weaken.weaken.weaken
          (.bound 2) (.bound 1) .newest)
          (red_m R.weaken.weaken.weaken Q.weaken.weaken.weaken S.weaken.weaken.weaken
            w.weaken.weaken.weaken F.weaken.weaken.weaken (.bound 2) p.weaken.weaken.weaken))))))
derive_free_closed eq_pull_m

theorem eq_push_sat_l (hE : Extensional M) {n} (ρ : Env M n) (P R z S F q s t : Term n) :
    Formula.satisfies ρ (eq_push_m P R z S F q s t) ↔
      Eq_push_d M (P.eval ρ) (R.eval ρ) (z.eval ρ) (S.eval ρ) (F.eval ρ) (q.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [eq_push_m, Eq_push_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, name_sat_l M hE, nmap_sat_l M hE, eq_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem eq_pull_sat_l (hE : Extensional M) {n} (ρ : Env M n) (R Q S w F p s t : Term n) :
    Formula.satisfies ρ (eq_pull_m R Q S w F p s t) ↔
      Eq_pull_d M (R.eval ρ) (Q.eval ρ) (S.eval ρ) (w.eval ρ) (F.eval ρ) (p.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [eq_pull_m, Eq_pull_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    nmap_sat_l M hE, eq_force_sat_l M hE, red_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

end YesMetaZFC.Model.Forcing.Internal
