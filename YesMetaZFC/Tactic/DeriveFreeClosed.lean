import Lean
import YesMetaZFC.SetTheory.Definitional.Language

/-!
# 公式缩写的闭合性合同派生

只为指定公式构造派生普通定理：项、参数向量和公式输入分别提供闭合性前提，
其余参数保持原样。证明只展开该构造一层，再消费已有的子公式合同；生成结果由
Lean 内核检查，不改变对象公式、模板证书或公理。
-/
namespace YesMetaZFC.Automation
open Lean Meta Elab Command Term
open SetTheory Definitional

private def closedPremise? (arg : Expr) : MetaM (Option Expr) := do
  let type ← whnf (← inferType arg)
  if type.isAppOf ``Definitional.Term then
    return some (← mkEq (← mkAppM ``Definitional.Term.freeSupport #[arg])
      (← mkListLit (mkConst ``FreeVarId) []))
  if type.isAppOf ``TermVector then
    return some (← mkAppM ``TermVector.FreeClosed #[arg])
  if type.isAppOf ``Definitional.Formula then
    return some (← mkAppM ``Definitional.Formula.FreeClosed #[arg])
  return none

/-- 为公式构造 `f` 生成并注册 `f_freeClosed`；不支持的构造必须显式给出合同。 -/
syntax (name := deriveFreeClosed) "derive_free_closed " ident : command

elab_rules : command
  | `(derive_free_closed $id:ident) => do
      let source ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      let theoremName := source.appendAfter "_freeClosed"
      liftTermElabM do
        let info ← getConstInfo source
        let type ← forallTelescope info.type fun args result => do
          unless (← whnf result).isAppOf ``Definitional.Formula do
            throwError "derive_free_closed 要求返回 Definitional.Formula 的构造"
          let conclusion ← mkAppM ``Definitional.Formula.FreeClosed
            #[mkAppN (mkConst source (info.levelParams.map Level.param)) args]
          let mut type := conclusion
          for arg in args.reverse do
            if let some premise ← closedPremise? arg then
              type ← mkArrow premise type
          mkForallFVars args type
        let proof ← elabTermEnsuringType (← `(by
          intros
          simp -implicitDefEqProofs [$id:term, Definitional.Formula.FreeClosed, *])) type
        synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars proof
        if proof.hasSorry || proof.hasMVar then
          throwError "闭合性合同未完成内核证明"
        addDecl (.thmDecl {
          name := theoremName
          levelParams := info.levelParams
          type := type
          value := proof })
      elabCommand (← `(attribute [simp] $(mkIdent theoremName)))

end YesMetaZFC.Automation
