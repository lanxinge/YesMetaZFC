import YesMetaZFC.Model.Forcing.TwoStep.Flatten.Construction
import YesMetaZFC.Model.Forcing.TwoStep.Names.Forcing

/-! # 名称摊平后求值还原的内部归纳公式

在首阶段根条件以下，若原名称解释为第二阶段名称，则所有第二阶段条件都
迫使它等于摊平后再转换的名称。该断言保留为原模型内的一条实际力迫公式。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def round_body_m : Formula 1 4 := .imp (name_m (.bound 3) (.bound 1))
  (.forallE (.imp (.mem .newest (.bound 4)) (eq_force_m (.bound 4) (.bound 3) (.bound 4) .newest (.bound 2) (.bound 1))))
@[simp] theorem round_closed_l : round_body_m.FreeClosed := by
  simp only [round_body_m, Definitional.Formula.FreeClosed]
  exact ⟨name_m_freeClosed _ _ rfl rfl, ⟨rfl, rfl⟩, eq_force_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl⟩

def round_env_l {M : SetTheory.Structure.{u}} (A T x t : M.Domain) : Env M 4 :=
  (((⟨fun _ => A, fun _ => A⟩ : Env M 1).push T).push x).push t

def Round_force_d (M : SetTheory.Structure.{u}) (B R z A T p x t : M.Domain) : Prop :=
  Forces_d M B R z round_body_m (round_env_l A T x t) p

def round_force_m {n} (B R z A T p x t : Term n) : Formula 1 n :=
  force_at_m round_body_m (Fin.cases t (Fin.cases x (Fin.cases T (fun _ => A)))) B R z p

@[simp] theorem round_force_m_freeClosed {n} (B R z A T p x t : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hA : A.freeSupport = []) (hT : T.freeSupport = []) (hp : p.freeSupport = [])
    (hx : x.freeSupport = []) (ht : t.freeSupport = []) : (round_force_m B R z A T p x t).FreeClosed :=
  force_at_closed_l _ _ _ _ _ _ round_closed_l
    (Fin.cases ht (Fin.cases hx (Fin.cases hT (fun _ => hA)))) hB hR hz hp

theorem round_body_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) (ρ : Env M 4) :
    Formula.satisfies ρ round_body_m ↔ (Name_d M (ρ.bound 3) (ρ.bound 1) → ∀ q,
      M.mem q (ρ.bound 3) → Eq_force_d M (ρ.bound 3) (ρ.bound 2) (ρ.bound 3) q (ρ.bound 1) (ρ.bound 0)) := by
  simp only [round_body_m, Formula.satisfies_imp_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_mem_iff, name_sat_l M hE, eq_force_sat_l M hE]
  rfl

theorem round_force_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z A T p x t : Term n) : Formula.satisfies ρ (round_force_m B R z A T p x t) ↔
      Round_force_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (A.eval ρ) (T.eval ρ) (p.eval ρ) (x.eval ρ) (t.eval ρ) := by
  unfold round_force_m Round_force_d
  refine (force_at_sat_l _ _ _ _ _ _ _).trans (forces_env_l hE _ round_closed_l _ _ ?_ _)
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))

def Flat_round_d (M : SetTheory.Structure.{u}) (B R z b A T C x : M.Domain) : Prop :=
  Name_d M B x → ∀ f t p, Flat_d M B R z C x f ∧ Curry_d M B C f t ∧ Below_d M B R z p b →
    Round_force_d M B R z A T p x t

def flat_round_m {n} (B R z b A T C x : Term n) : Formula 1 n :=
  .imp (name_m B x) (.forallE (.forallE (.forallE (.imp
    (.conj (flat_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken C.weaken.weaken.weaken
      x.weaken.weaken.weaken (.bound 2))
      (.conj (curry_m B.weaken.weaken.weaken C.weaken.weaken.weaken (.bound 2) (.bound 1))
        (below_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken .newest b.weaken.weaken.weaken)))
    (round_force_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken A.weaken.weaken.weaken
      T.weaken.weaken.weaken .newest x.weaken.weaken.weaken (.bound 1))))))
derive_free_closed flat_round_m

theorem flat_round_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z b A T C x : Term n) : Formula.satisfies ρ (flat_round_m B R z b A T C x) ↔
      Flat_round_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (A.eval ρ) (T.eval ρ) (C.eval ρ) (x.eval ρ) := by
  simp only [flat_round_m, Flat_round_d, Formula.satisfies_imp_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_conj_iff, name_sat_l M hE, flat_sat_l M hE, curry_sat_l M hE,
    below_sat_l M hE, round_force_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def flat_round_children_m {n} (B R z b A T C x : Term n) : Formula 1 n :=
  .forallE (.imp (entry_path_m 3 x.weaken .newest)
    (flat_round_m B.weaken R.weaken z.weaken b.weaken A.weaken T.weaken C.weaken .newest))
derive_free_closed flat_round_children_m

theorem flat_round_children_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z b A T C x : Term n) : Formula.satisfies ρ (flat_round_children_m B R z b A T C x) ↔
      ∀ a, Entry_path_d M 3 (x.eval ρ) a →
        Flat_round_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (A.eval ρ) (T.eval ρ) (C.eval ρ) a := by
  simp only [flat_round_children_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    entry_path_sat_l hE, flat_round_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
