import YesMetaZFC.SetTheory.Axioms.Common

/-! # Zermelo 集合论（含无穷与基础）

直接使用原 Project 公理公式与完整带参数分离模式；替换和收集不在本理论中。
-/
namespace YesMetaZFC.SetTheory
namespace Z
inductive Axiom : Definitional.Project.Theory where
  | extensionality : Axiom Axioms.extensionality
  | emptySet : Axiom Axioms.emptySet
  | pairing : Axiom Axioms.pairing
  | union : Axiom Axioms.union
  | powerSet : Axiom Axioms.powerSet
  | infinity : Axiom Axioms.infinity
  | foundation : Axiom Axioms.foundation
  | separation {n : Nat} (φ : Definitional.Project.UnarySchema n) :
      Axiom (Axioms.Schema.separation φ)
end Z
abbrev Z : Definitional.Project.Theory := Z.Axiom
end YesMetaZFC.SetTheory
