import YesMetaZFC.SetTheory.Axioms.Common
import YesMetaZFC.SetTheory.Theory

/-!
# Kripke--Platek 集合论（含无穷）

本包采用外延、空集、配对、并、无穷、基础、`Delta0` 分离和 `Delta0` 收集。
-/

namespace YesMetaZFC
namespace SetTheory

namespace KP

/-- KP（含无穷）的公理谓词。 -/
inductive Axiom : Definitional.Project.Theory where
  | extensionality : Axiom Axioms.extensionality
  | emptySet : Axiom Axioms.emptySet
  | pairing : Axiom Axioms.pairing
  | union : Axiom Axioms.union
  | infinity : Axiom Axioms.infinity
  | foundation : Axiom Axioms.foundation
  | separation {parameterCount : Nat}
      (schema : Definitional.Project.Delta0UnarySchema parameterCount) :
      Axiom (Axioms.Schema.separation schema.toUnarySchema)
  | collection {parameterCount : Nat}
      (schema : Definitional.Project.Delta0BinarySchema parameterCount) :
      Axiom (Axioms.Schema.collection schema.toBinarySchema)

end KP

/-- 带无穷公理的 Kripke--Platek 集合论。 -/
abbrev KP : Definitional.Project.Theory :=
  KP.Axiom

end SetTheory
end YesMetaZFC
