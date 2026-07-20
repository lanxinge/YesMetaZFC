import YesMetaZFC.SetTheory.Axioms.KP

/-!
# Zermelo--Fraenkel 集合论

这里采用全分离与全收集的标准呈现。Jech 风格替换句仍由公共公理模块提供。
-/

namespace YesMetaZFC
namespace SetTheory

namespace ZF

/-- ZF 的公理谓词。 -/
inductive Axiom : Definitional.Project.Theory where
  | extensionality : Axiom Axioms.extensionality
  | emptySet : Axiom Axioms.emptySet
  | pairing : Axiom Axioms.pairing
  | union : Axiom Axioms.union
  | powerSet : Axiom Axioms.powerSet
  | infinity : Axiom Axioms.infinity
  | foundation : Axiom Axioms.foundation
  | separation {parameterCount : Nat}
      (schema : Definitional.Project.UnarySchema parameterCount) :
      Axiom (Axioms.Schema.separation schema)
  | collection {parameterCount : Nat}
      (schema : Definitional.Project.BinarySchema parameterCount) :
      Axiom (Axioms.Schema.collection schema)

end ZF

/-- Zermelo--Fraenkel 集合论。 -/
abbrev ZF : Definitional.Project.Theory :=
  ZF.Axiom

end SetTheory
end YesMetaZFC
