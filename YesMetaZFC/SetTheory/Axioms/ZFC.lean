import YesMetaZFC.SetTheory.Axioms.ZF

/-!
# ZFC

ZFC 在 ZF 上加入选择集形式的选择公理。
-/

namespace YesMetaZFC
namespace SetTheory

namespace ZFC

/-- ZFC 的公理谓词。 -/
inductive Axiom : Definitional.Project.Theory where
  | zf {sentence : Definitional.Project.Sentence} :
      ZF sentence → Axiom sentence
  | choice : Axiom Axioms.choice

end ZFC

/-- 带选择公理的 Zermelo--Fraenkel 集合论。 -/
abbrev ZFC : Definitional.Project.Theory :=
  ZFC.Axiom

end SetTheory
end YesMetaZFC
