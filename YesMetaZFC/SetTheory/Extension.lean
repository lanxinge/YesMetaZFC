import YesMetaZFC.SetTheory.Axioms.ZFC

/-!
# 公理系统扩张与定理继承

`strong.Extends weak` 不要求弱理论公理在强理论中逐字出现；只要求强理论能证明弱理论
的每一条公理。由此得到用户期望的通用继承原则：强理论自动继承弱理论的全部语义
定理。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Theory

/-- 逐字包含的公理子理论关系。 -/
def Subtheory (weak strong : Theory) : Prop :=
  ∀ sentence, weak sentence → strong sentence

/-- 强理论能证明弱理论的每一条公理。 -/
def Extends (strong weak : Theory) : Prop :=
  ∀ sentence, weak sentence → SemanticallyEntails.{u} strong sentence

namespace Subtheory

/-- 公理逐字包含蕴含语义扩张。 -/
theorem toExtends {strong weak : Theory} (hSubset : Subtheory weak strong) :
    Extends.{u} strong weak :=
  fun sentence hSentence => entails_of_mem (hSubset sentence hSentence)

end Subtheory

namespace Extends

/-- 每个理论扩张自身。 -/
theorem refl (theory : Theory) : Extends.{u} theory theory :=
  fun _ hSentence => entails_of_mem hSentence

/-- 扩张关系可传递。 -/
theorem trans {strong middle weak : Theory}
    (hStrong : Extends.{u} strong middle)
    (hMiddle : Extends.{u} middle weak) :
    Extends.{u} strong weak := by
  intro sentence hSentence
  intro ℳ hModels
  apply hMiddle sentence hSentence ℳ
  refine ⟨hModels.1, ?_⟩
  intro candidate hCandidate
  exact hStrong candidate hCandidate ℳ hModels

end Extends

/--
定理继承主定理。

若 `strong` 能证明 `weak` 的全部公理，则 `weak` 的每个语义定理也是 `strong` 的定理。
-/
theorem entails_of_extends {strong weak : Theory}
    {target : Definitional.Project.Sentence}
    (hExtends : Extends.{u} strong weak)
    (hTheorem : SemanticallyEntails.{u} weak target) :
    SemanticallyEntails.{u} strong target := by
  intro ℳ hModels
  apply hTheorem ℳ
  refine ⟨hModels.1, ?_⟩
  intro sentence hSentence
  exact hExtends sentence hSentence ℳ hModels

end Theory

namespace ZF

/-- ZF 扩张带无穷的 KP。 -/
theorem extendsKP : Theory.Extends.{u} SetTheory.ZF SetTheory.KP := by
  intro sentence hSentence
  cases hSentence with
  | extensionality =>
      exact Theory.entails_of_mem Axiom.extensionality
  | emptySet =>
      exact Theory.entails_of_mem Axiom.emptySet
  | pairing =>
      exact Theory.entails_of_mem Axiom.pairing
  | union =>
      exact Theory.entails_of_mem Axiom.union
  | infinity =>
      exact Theory.entails_of_mem Axiom.infinity
  | foundation =>
      exact Theory.entails_of_mem Axiom.foundation
  | separation schema =>
      exact Theory.entails_of_mem (Axiom.separation schema.toUnarySchema)
  | collection schema =>
      exact Theory.entails_of_mem (Axiom.collection schema.toBinarySchema)

/-- 每个 ZF 模型按扩张关系自动成为 KP 模型。 -/
theorem modelsKP {ℳ : Structure.{u}}
    (hZF : ℳ.Models SetTheory.ZF) :
    ℳ.Models SetTheory.KP := by
  refine ⟨hZF.1, ?_⟩
  intro sentence hSentence
  exact extendsKP sentence hSentence ℳ hZF

end ZF

namespace ZFC

/-- ZFC 扩张 ZF。 -/
theorem extendsZF : Theory.Extends.{u} SetTheory.ZFC SetTheory.ZF :=
  fun _ hSentence => Theory.entails_of_mem (Axiom.zf hSentence)

/-- ZFC 因传递性自动扩张带无穷的 KP。 -/
theorem extendsKP : Theory.Extends.{u} SetTheory.ZFC SetTheory.KP :=
  Theory.Extends.trans extendsZF ZF.extendsKP

end ZFC

/-- ZF 自动继承 KP 的每个定理。 -/
theorem zf_inherits_kp {target : Definitional.Project.Sentence}
    (hTheorem : SemanticallyEntails.{u} KP target) :
    SemanticallyEntails.{u} ZF target :=
  Theory.entails_of_extends ZF.extendsKP hTheorem

/-- ZFC 自动继承 ZF 的每个定理。 -/
theorem zfc_inherits_zf {target : Definitional.Project.Sentence}
    (hTheorem : SemanticallyEntails.{u} ZF target) :
    SemanticallyEntails.{u} ZFC target :=
  Theory.entails_of_extends ZFC.extendsZF hTheorem

/-- ZFC 自动继承 KP 的每个定理。 -/
theorem zfc_inherits_kp {target : Definitional.Project.Sentence}
    (hTheorem : SemanticallyEntails.{u} KP target) :
    SemanticallyEntails.{u} ZFC target :=
  Theory.entails_of_extends ZFC.extendsKP hTheorem

end SetTheory
end YesMetaZFC
