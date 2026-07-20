import Lean

/-!
# 已移除的旧自动化路线

本模块只保存旧 LCF/MF1 生态中已经从类型层和调度层删除的 route 名称，供迁移审计与
诊断使用。这里没有兼容入口，也不提供回退实现；后续同名能力若重新出现，必须作为
产生显式 DAG 证书的新后端重新设计。
-/

namespace YesMetaZFC
namespace Automation
namespace LegacyRemoved

/-- 已从新自动化主线删除的旧 route。 -/
inductive Capability where
  | pureCdclReplay
  | sequentCdclReplay
  | sourceCompilerDirectReplay
  | sourceCompilerTheoryReplay
  | sourceCompilerComposedReplay
  | groundReflection
  | egraphThunkReplay
  | localFactSequentReplay
  | tableauReflection
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace Capability

/-- 审计日志中的旧 route 名称。 -/
def label : Capability → String
  | pureCdclReplay => "pure CDCL LCF replay"
  | sequentCdclReplay => "sequent CDCL LCF replay"
  | sourceCompilerDirectReplay => "SourceCompiler direct replay"
  | sourceCompilerTheoryReplay => "SourceCompiler in-theory replay"
  | sourceCompilerComposedReplay => "SourceCompiler composed replay"
  | groundReflection => "ground reflection"
  | egraphThunkReplay => "egraph thunk replay"
  | localFactSequentReplay => "local-fact sequent replay"
  | tableauReflection => "tableau reflection"

/-- 删除旧 route 后由新主线承担的能力，或未来重新引入时必须满足的合同。 -/
def replacement : Capability → String
  | pureCdclReplay =>
      "DAG propositional/residual CDCL materialization"
  | sequentCdclReplay =>
      "guarded DAG residual CDCL inputs and checked source nodes"
  | sourceCompilerDirectReplay =>
      "DAG source/local-rule materialization"
  | sourceCompilerTheoryReplay =>
      "checked theory/context fact source certificates"
  | sourceCompilerComposedReplay =>
      "explicit DAG replay rules"
  | groundReflection =>
      "residual CDCL for propositional closure and superposition for equality"
  | egraphThunkReplay =>
      "future equality explanations must emit explicit congruence/rewrite DAG evidence"
  | localFactSequentReplay =>
      "checked context-fact source certificates"
  | tableauReflection =>
      "clausification, AVATAR, residual CDCL and superposition"

/-- 单条已移除 route 的审计摘要。 -/
def summary (capability : Capability) : String :=
  s!"removed {capability.label}; replacement={capability.replacement}"

end Capability

/-- 当前已从类型层和调度层移除的旧 route 清单。 -/
def all : Array Capability := #[
  .pureCdclReplay,
  .sequentCdclReplay,
  .sourceCompilerDirectReplay,
  .sourceCompilerTheoryReplay,
  .sourceCompilerComposedReplay,
  .groundReflection,
  .egraphThunkReplay,
  .localFactSequentReplay,
  .tableauReflection
]

/-- 多条已移除 route 的审计摘要。 -/
def summaryAll (capabilities : Array Capability := all) : String :=
  String.intercalate "; " (capabilities.toList.map Capability.summary)

end LegacyRemoved
end Automation
end YesMetaZFC
