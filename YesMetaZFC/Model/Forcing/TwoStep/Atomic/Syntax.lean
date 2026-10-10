import YesMetaZFC.Model.Forcing.TwoStep.Names.Forcing

/-! # 二步名称等号传输的内部归纳公式

归纳结论本身是一条原模型公式：首坐标迫使第二阶段的内部等号力迫。
子名称归纳因此使用原 ZF 的条目归纳，而不要求模型在外部良基。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def iter_eq_body_m : Formula 1 5 := eq_force_m (.bound 4) (.bound 3) (.bound 4) (.bound 2) (.bound 1) .newest
@[simp] theorem iter_eq_closed_l : iter_eq_body_m.FreeClosed := eq_force_m_freeClosed _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl

def iter_eq_env_l {M : SetTheory.Structure.{u}} (A T s u v : M.Domain) : Env M 5 :=
  ((((⟨fun _ => A, fun _ => A⟩ : Env M 1).push T).push s).push u).push v

def Iter_eq_d (M : SetTheory.Structure.{u}) (B R z A T p s u v : M.Domain) : Prop :=
  Forces_d M B R z iter_eq_body_m (iter_eq_env_l A T s u v) p

def iter_eq_m {n} (B R z A T p s u v : Term n) : Formula 1 n :=
  force_at_m iter_eq_body_m (Fin.cases v (Fin.cases u (Fin.cases s (Fin.cases T (fun _ => A))))) B R z p

@[simp] theorem iter_eq_m_freeClosed {n} (B R z A T p s u v : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hA : A.freeSupport = []) (hT : T.freeSupport = []) (hp : p.freeSupport = [])
    (hs : s.freeSupport = []) (hu : u.freeSupport = []) (hv : v.freeSupport = []) :
    (iter_eq_m B R z A T p s u v).FreeClosed :=
  force_at_closed_l _ _ _ _ _ _ iter_eq_closed_l
    (Fin.cases hv (Fin.cases hu (Fin.cases hs (Fin.cases hT (fun _ => hA))))) hB hR hz hp

theorem iter_eq_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z A T p s u v : Term n) : Formula.satisfies ρ (iter_eq_m B R z A T p s u v) ↔
      Iter_eq_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (A.eval ρ) (T.eval ρ) (p.eval ρ) (s.eval ρ) (u.eval ρ) (v.eval ρ) := by
  unfold iter_eq_m Iter_eq_d
  refine (force_at_sat_l _ _ _ _ _ _ _).trans (forces_env_l hE _ iter_eq_closed_l _ _ ?_ _)
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))

def Curry_eq_d (M : SetTheory.Structure.{u}) (B R z A T C S x : M.Domain) : Prop :=
  Name_d M C x → ∀ y c p s u v,
    Name_d M C y ∧ KPair_d M c p s ∧ Eq_force_d M C S C c x y ∧
      Curry_d M B C x u ∧ Curry_d M B C y v → Iter_eq_d M B R z A T p s u v

def curry_eq_m {n} (B R z A T C S x : Term n) : Formula 1 n :=
  .imp (name_m C x) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (.conj (name_m C.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5))
      (.conj (kpair_m (.bound 4) (.bound 3) (.bound 2))
        (.conj (eq_force_m C.weaken.weaken.weaken.weaken.weaken.weaken S.weaken.weaken.weaken.weaken.weaken.weaken
          C.weaken.weaken.weaken.weaken.weaken.weaken (.bound 4) x.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5))
          (.conj (curry_m B.weaken.weaken.weaken.weaken.weaken.weaken C.weaken.weaken.weaken.weaken.weaken.weaken
            x.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1))
            (curry_m B.weaken.weaken.weaken.weaken.weaken.weaken C.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) .newest)))))
    (iter_eq_m B.weaken.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken.weaken
      z.weaken.weaken.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken.weaken.weaken
      T.weaken.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest))))))))
derive_free_closed curry_eq_m

theorem curry_eq_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z A T C S x : Term n) : Formula.satisfies ρ (curry_eq_m B R z A T C S x) ↔
      Curry_eq_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (A.eval ρ) (T.eval ρ) (C.eval ρ) (S.eval ρ) (x.eval ρ) := by
  simp only [curry_eq_m, Curry_eq_d, Formula.satisfies_imp_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_conj_iff, name_sat_l M hE, kpair_sat_l M hE, eq_force_sat_l M hE,
    curry_sat_l M hE, iter_eq_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def curry_children_m {n} (B R z A T C S x : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (entry_m (.bound 1) .newest x.weaken.weaken)
    (curry_eq_m B.weaken.weaken R.weaken.weaken z.weaken.weaken A.weaken.weaken T.weaken.weaken
      C.weaken.weaken S.weaken.weaken (.bound 1))))
derive_free_closed curry_children_m

theorem curry_children_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z A T C S x : Term n) : Formula.satisfies ρ (curry_children_m B R z A T C S x) ↔
      ∀ a c, Entry_d M a c (x.eval ρ) →
        Curry_eq_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (A.eval ρ) (T.eval ρ) (C.eval ρ) (S.eval ρ) a := by
  simp only [curry_children_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, entry_sat_l M hE,
    curry_eq_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
