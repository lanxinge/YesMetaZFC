import YesMetaZFC.Model.Forcing.TwoStep.Atomic.Syntax

/-! # 反向二步等号传输的内部双模拟谓词

条件的首坐标迫使其第二坐标下的名称等号。把两个等号方向同时纳入关系，
其对称性成为直接的见证交换；后续证明再把此谓词分离为实际集合。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def Curry_pull_d (M : SetTheory.Structure.{u}) (B R z A T C c x y : M.Domain) : Prop :=
  ∃ p s u v, KPair_d M c p s ∧ Curry_d M B C x u ∧ Curry_d M B C y v ∧
    (Iter_eq_d M B R z A T p s u v ∨ Iter_eq_d M B R z A T p s v u)

def curry_pull_m {n} (B R z A T C c x y : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (kpair_m c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))
      (.conj (curry_m B.weaken.weaken.weaken.weaken C.weaken.weaken.weaken.weaken x.weaken.weaken.weaken.weaken (.bound 1))
        (.conj (curry_m B.weaken.weaken.weaken.weaken C.weaken.weaken.weaken.weaken y.weaken.weaken.weaken.weaken .newest)
          (.disj (iter_eq_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken z.weaken.weaken.weaken.weaken
            A.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)
            (iter_eq_m B.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken z.weaken.weaken.weaken.weaken
              A.weaken.weaken.weaken.weaken T.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) .newest (.bound 1)))))))))
derive_free_closed curry_pull_m

theorem curry_pull_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z A T C c x y : Term n) : Formula.satisfies ρ (curry_pull_m B R z A T C c x y) ↔
      Curry_pull_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (A.eval ρ) (T.eval ρ) (C.eval ρ) (c.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [curry_pull_m, Curry_pull_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, kpair_sat_l M hE, curry_sat_l M hE, iter_eq_sat_l hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem curry_pull_symm_l {M : SetTheory.Structure.{u}} {B R z A T C c x y}
    (h : Curry_pull_d M B R z A T C c x y) : Curry_pull_d M B R z A T C c y x := by
  obtain ⟨p, s, u, v, hc, hu, hv, he⟩ := h
  exact ⟨p, s, v, u, hc, hv, hu, he.symm⟩

def Curry_pull_wit_d (M : SetTheory.Structure.{u}) (B R z A T C S q a y : M.Domain) : Prop :=
  ∃ r e f, Below_d M C S C r q ∧ Entry_d M e f y ∧ Entry_d M r f S ∧ Curry_pull_d M B R z A T C r a e

def curry_pull_wit_m {n} (B R z A T C S q a y : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj
    (below_m C.weaken.weaken.weaken S.weaken.weaken.weaken C.weaken.weaken.weaken (.bound 2) q.weaken.weaken.weaken)
    (.conj (entry_m (.bound 1) .newest y.weaken.weaken.weaken)
      (.conj (entry_m (.bound 2) .newest S.weaken.weaken.weaken)
        (curry_pull_m B.weaken.weaken.weaken R.weaken.weaken.weaken z.weaken.weaken.weaken A.weaken.weaken.weaken
          T.weaken.weaken.weaken C.weaken.weaken.weaken (.bound 2) a.weaken.weaken.weaken (.bound 1)))))))
derive_free_closed curry_pull_wit_m

theorem curry_pull_wit_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z A T C S q a y : Term n) : Formula.satisfies ρ (curry_pull_wit_m B R z A T C S q a y) ↔
      Curry_pull_wit_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (A.eval ρ) (T.eval ρ) (C.eval ρ) (S.eval ρ)
        (q.eval ρ) (a.eval ρ) (y.eval ρ) := by
  simp only [curry_pull_wit_m, Curry_pull_wit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    below_sat_l M hE, entry_sat_l M hE, curry_pull_sat_l hE, Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.Model.Forcing.Internal
