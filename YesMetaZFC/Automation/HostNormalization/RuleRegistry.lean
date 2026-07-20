import Lean

/-!
# `prove_auto` 宿主正规化规则注册表

本模块只保存规则声明的 proof-free 元数据，不执行任何表达式规约、目标改写或
局部上下文迁移。规则编译、候选索引、等式闭包和 checked 事务分别由后续模块承担。
-/

namespace YesMetaZFC
namespace Automation
namespace HostNormalization

open Lean Elab Tactic Meta

/-- 宿主规则正规化的稳定阶段。 -/
inductive Phase where
  | definitionExposure
  | indexAlgebra
  | semanticAlignment
  | logicalCleanup
deriving BEq, Repr, Inhabited

def Phase.label : Phase → String
  | .definitionExposure => "definition"
  | .indexAlgebra => "index"
  | .semanticAlignment => "semantic"
  | .logicalCleanup => "logical"

private def Phase.ofName? : Name → Option Phase
  | `definition => some .definitionExposure
  | `index => some .indexAlgebra
  | `semantic => some .semanticAlignment
  | `logical => some .logicalCleanup
  | _ => none

/-- 与具体搜索索引解耦的声明级注册项。 -/
structure RegisteredRule where
  declaration : Name
  phase : Phase
deriving Inhabited

private def pushRegisteredRuleUnique
    (rules : Array RegisteredRule) (rule : RegisteredRule) :
    Array RegisteredRule :=
  if rules.any fun existing => existing.declaration == rule.declaration then
    rules
  else
    rules.push rule

private initialize normalizationRuleExtension :
    PersistentEnvExtension RegisteredRule RegisteredRule
      (Array RegisteredRule) ←
  registerPersistentEnvExtension {
    name := `YesMetaZFC.Automation.HostNormalization.normalizationRuleExtension
    mkInitial := pure #[]
    addImportedFn := fun imported =>
      pure <| imported.foldl
        (fun rules entries =>
          entries.foldl pushRegisteredRuleUnique rules) #[]
    addEntryFn := pushRegisteredRuleUnique
    exportEntriesFn := id
    statsFn := fun rules =>
      s!"prove_auto normalization rules: {rules.size}"
  }

/--
读取当前环境可见的规则元数据。

结果按声明名稳定排序，不读取 theorem proof 或 simplifier 内部索引。
-/
def registeredRules (environment : Environment) : Array RegisteredRule :=
  normalizationRuleExtension.getState environment
    |>.qsort fun left right =>
      Name.quickLt left.declaration right.declaration

private def addRegisteredRule
    (declaration : Name) (phase : Phase) : AttrM Unit := do
  let action : MetaM Unit := do
    let info ← getAsyncConstInfo declaration
    unless (← isProp info.sig.get.type) || info.kind == .defn do
      throwError
        "`prove_auto_norm` expected a proposition theorem or definition, \
        got `{declaration}`"
    modifyEnv fun environment =>
      normalizationRuleExtension.addEntry
        (asyncDecl := declaration) environment { declaration, phase }
  discard <| action.run {} {}

/--
把定理或定义注册到 proof-free 宿主规则面。

阶段参数为 `definition`、`index`、`semantic` 或 `logical`。
-/
initialize proveAutoNormAttr : ParametricAttribute Phase ←
  registerParametricAttribute {
    name := `prove_auto_norm
    descr := "phase-specific prove_auto host normalization rule"
    applicationTime := .afterCompilation
    getParam := fun declaration stx => do
      let identifier ← Attribute.Builtin.getIdent stx
      let phaseName := identifier.getId.eraseMacroScopes
      let some phase := Phase.ofName? phaseName
        | throwErrorAt identifier
            "unknown prove_auto normalization phase `{phaseName}`; \
            expected definition, index, semantic or logical"
      addRegisteredRule declaration phase
      pure phase
  }

end HostNormalization
end Automation
end YesMetaZFC
