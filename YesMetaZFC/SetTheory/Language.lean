import YesMetaZFC.Logic.Syntax

/-!
# 纯集合论一阶签名

本模块只保存集合论向通用一阶逻辑核暴露的单关系签名 `ℒ`。项目公式 AST 位于
`SetTheory.Definitional.Project`；旧纯 `∈` AST 只位于显式审计模块。
-/

namespace YesMetaZFC
namespace SetTheory

/-- 纯集合论只有一个对象 sort。 -/
inductive SetSort where
  | set
  deriving DecidableEq, Repr

/-- 纯集合论没有函数符号。 -/
abbrev FunctionSymbol := Empty

/-- 纯集合论唯一的底层关系符号。 -/
inductive RelationSymbol where
  | membership
  deriving DecidableEq, Repr

/-- 纯集合论向通用一阶逻辑核暴露的签名。 -/
def signature : Logic.Signature where
  SortSymbol := SetSort
  FuncSymbol := FunctionSymbol
  RelSymbol := RelationSymbol
  funcDomain := fun symbol => nomatch symbol
  funcCodomain := fun symbol => nomatch symbol
  relDomain
    | RelationSymbol.membership => [SetSort.set, SetSort.set]

/-- 纯集合论语言的公开接口名称。 -/
abbrev PureSetLanguage : Logic.Signature := signature

notation "ℒ" => SetTheory.PureSetLanguage

instance signatureSortDecidableEq : DecidableEq signature.SortSymbol := by
  unfold signature
  infer_instance

instance signatureRelationDecidableEq : DecidableEq signature.RelSymbol := by
  unfold signature
  infer_instance

end SetTheory
end YesMetaZFC
