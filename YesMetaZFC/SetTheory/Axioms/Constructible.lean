import YesMetaZFC.SetTheory.InnerModel.Jensen.Class
import YesMetaZFC.SetTheory.Axioms.ZF

/-! # 可构造公理及原演绎核中的 KP、ZF 构造性扩张

公理是封闭的原 Project 句子：每个对象属于某个内部序数处的 J 层。
语法侧只依赖这个确定的句子；使用者不必携带任何 Jensen 模型或构造证书。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project

def Axioms.vl_axiom : Sentence := Sentence.ofFormula
  (.forallE (InnerModel.l_m .newest)) (by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed])

namespace KPL
inductive Axiom : Definitional.Project.Theory where
  | kp {s : Sentence} : KP s → Axiom s
  | constructible : Axiom Axioms.vl_axiom
end KPL

abbrev KPL : Definitional.Project.Theory := KPL.Axiom

namespace ZFL
inductive Axiom : Definitional.Project.Theory where
  | zf {s : Sentence} : ZF s → Axiom s
  | constructible : Axiom Axioms.vl_axiom
end ZFL

abbrev ZFL : Definitional.Project.Theory := ZFL.Axiom

theorem KPL.constructibility_d : Definitional.Project.Derives KPL Axioms.vl_axiom := by
  have h := Logic.FirstOrder.Derives.theory_axiom
    (free := []) (Γ := []) (T := fo_theory KPL)
    (show fo_theory KPL (fo_sentence Axioms.vl_axiom) from ⟨_, .constructible, rfl⟩)
  simpa [Logic.FirstOrder.Formula.fromSentence, Logic.FirstOrder.Renaming.emptyFree] using! h

theorem ZFL.constructibility_d : Definitional.Project.Derives ZFL Axioms.vl_axiom := by
  have h := Logic.FirstOrder.Derives.theory_axiom
    (free := []) (Γ := []) (T := fo_theory ZFL)
    (show fo_theory ZFL (fo_sentence Axioms.vl_axiom) from ⟨_, .constructible, rfl⟩)
  simpa [Logic.FirstOrder.Formula.fromSentence, Logic.FirstOrder.Renaming.emptyFree] using! h

end YesMetaZFC.SetTheory
