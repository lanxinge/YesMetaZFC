import YesMetaZFC.Automation.HOSearchMaterialization

/-!
# Checked 高阶 replay 的纯 DAG 引用

高阶搜索器在元层完成搜索与材料化后，只把 concrete `SearchSignature` HO-DAG
引用为 Lean 表达式。这里不生成证明，也不信任材料化结果；调用者必须继续构造
`DAG.check = true`、selector/witness registry、capability gate 与 problem 对齐证明。
-/

namespace YesMetaZFC
namespace Automation
namespace HOSearchMaterialization
namespace ReplayQuotation

open Lean

private def signatureExpr : Expr :=
  mkConst ``SearchSignature

private def baseSortTypeExpr : Expr :=
  mkConst ``BaseSort

private def higherOrderConst (declaration : Name) : Expr :=
  mkConst declaration [.zero, .zero, .zero]

private def unaryZeroConst (declaration : Name) : Expr :=
  mkConst declaration [.zero]

private def simpleTypeTypeExpr : Expr :=
  mkApp (unaryZeroConst ``Logic.HigherOrder.SimpleType) baseSortTypeExpr

private def termTypeExpr : Expr :=
  mkApp (higherOrderConst ``Logic.HigherOrder.Term) signatureExpr

private def appliedType (declaration : Name) : Expr :=
  mkApp (higherOrderConst declaration) signatureExpr

instance : ToExpr SearchSignature.BaseSort :=
  inferInstanceAs (ToExpr BaseSort)

instance : ToExpr SearchSignature.FuncSymbol :=
  inferInstanceAs (ToExpr CoreSyntax.Search.FunctionSymbol)

instance : ToExpr SearchSignature.RelSymbol :=
  inferInstanceAs (ToExpr RelSymbol)

private def simpleTypeExpr :
    Logic.HigherOrder.SimpleType SearchSignature.BaseSort → Expr
  | .base symbol =>
      mkAppN (unaryZeroConst ``Logic.HigherOrder.SimpleType.base)
        #[baseSortTypeExpr, toExpr symbol]
  | .arrow domain codomain =>
      mkAppN (unaryZeroConst ``Logic.HigherOrder.SimpleType.arrow)
        #[baseSortTypeExpr, simpleTypeExpr domain, simpleTypeExpr codomain]

instance : ToExpr (Logic.HigherOrder.SimpleType SearchSignature.BaseSort) where
  toTypeExpr := simpleTypeTypeExpr
  toExpr := simpleTypeExpr

private def varExpr : Logic.HigherOrder.Var SearchSignature → Expr
  | .bvar sort index =>
      mkAppN (higherOrderConst ``Logic.HigherOrder.Var.bvar)
        #[signatureExpr, toExpr sort, toExpr index]
  | .fvar sort id =>
      mkAppN (higherOrderConst ``Logic.HigherOrder.Var.fvar)
        #[signatureExpr, toExpr sort, toExpr id]

mutual
  private def termExpr : Term → Expr
    | .var value =>
        mkAppN (higherOrderConst ``Logic.HigherOrder.Term.var)
          #[signatureExpr, varExpr value]
    | .app symbol arguments =>
        mkAppN (higherOrderConst ``Logic.HigherOrder.Term.app)
          #[signatureExpr, toExpr symbol, termListExpr arguments]
    | .apply function argument =>
        mkAppN (higherOrderConst ``Logic.HigherOrder.Term.apply)
          #[signatureExpr, termExpr function, termExpr argument]
    | .lam domain codomain body =>
        mkAppN (higherOrderConst ``Logic.HigherOrder.Term.lam)
          #[signatureExpr, toExpr domain, toExpr codomain, termExpr body]

  private def termListExpr : List Term → Expr
    | [] =>
        mkApp (unaryZeroConst ``List.nil) termTypeExpr
    | head :: tail =>
        mkAppN (unaryZeroConst ``List.cons)
          #[termTypeExpr, termExpr head, termListExpr tail]
end

instance : ToExpr Term where
  toTypeExpr := termTypeExpr
  toExpr := termExpr

private def termBindingExpr
    (binding : Logic.HigherOrder.TermBinding SearchSignature) : Expr :=
  mkAppN (higherOrderConst ``Logic.HigherOrder.TermBinding.mk)
    #[signatureExpr, toExpr binding.sort, toExpr binding.id,
      toExpr binding.replacement]

instance : ToExpr (Logic.HigherOrder.TermBinding SearchSignature) where
  toTypeExpr := appliedType ``Logic.HigherOrder.TermBinding
  toExpr := termBindingExpr

private def atomExpr : Atom → Expr
  | .rel symbol arguments =>
      mkAppN (higherOrderConst ``HODAGCertificate.Atom.rel)
        #[signatureExpr, toExpr symbol, toExpr arguments]
  | .equal sort left right =>
      mkAppN (higherOrderConst ``HODAGCertificate.Atom.equal)
        #[signatureExpr, toExpr sort, toExpr left, toExpr right]

instance : ToExpr Atom where
  toTypeExpr := appliedType ``HODAGCertificate.Atom
  toExpr := atomExpr

private def literalExpr (literal : Literal) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Literal.mk)
    #[signatureExpr, toExpr literal.polarity, toExpr literal.atom]

instance : ToExpr Literal where
  toTypeExpr := appliedType ``HODAGCertificate.Literal
  toExpr := literalExpr

private def clauseExpr (clause : Clause) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Clause.mk)
    #[signatureExpr, toExpr clause.literals]

instance : ToExpr Clause where
  toTypeExpr := appliedType ``HODAGCertificate.Clause
  toExpr := clauseExpr

private def betaPayloadExpr (payload : BetaPayload) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Beta.Payload.mk)
    #[signatureExpr, toExpr payload.domain, toExpr payload.codomain,
      toExpr payload.body, toExpr payload.argument]

instance : ToExpr BetaPayload where
  toTypeExpr := appliedType ``HODAGCertificate.Beta.Payload
  toExpr := betaPayloadExpr

private def etaPayloadExpr (payload : EtaPayload) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Eta.Payload.mk)
    #[signatureExpr, toExpr payload.domain, toExpr payload.codomain,
      toExpr payload.function]

instance : ToExpr EtaPayload where
  toTypeExpr := appliedType ``HODAGCertificate.Eta.Payload
  toExpr := etaPayloadExpr

private def betaEtaTraceExpr : BetaEtaTrace → Expr
  | .refl term =>
      mkAppN (higherOrderConst ``HODAGCertificate.BetaEta.Trace.refl)
        #[signatureExpr, toExpr term]
  | .appArgument symbol before argument suffix =>
      mkAppN (higherOrderConst ``HODAGCertificate.BetaEta.Trace.appArgument)
        #[signatureExpr, toExpr symbol, toExpr before,
          betaEtaTraceExpr argument, toExpr suffix]
  | .applyFunction function argument =>
      mkAppN (higherOrderConst ``HODAGCertificate.BetaEta.Trace.applyFunction)
        #[signatureExpr, betaEtaTraceExpr function, toExpr argument]
  | .applyArgument function argument =>
      mkAppN (higherOrderConst ``HODAGCertificate.BetaEta.Trace.applyArgument)
        #[signatureExpr, toExpr function, betaEtaTraceExpr argument]
  | .lam domain codomain body =>
      mkAppN (higherOrderConst ``HODAGCertificate.BetaEta.Trace.lam)
        #[signatureExpr, toExpr domain, toExpr codomain,
          betaEtaTraceExpr body]
  | .beta domain codomain body argument =>
      mkAppN (higherOrderConst ``HODAGCertificate.BetaEta.Trace.beta)
        #[signatureExpr, toExpr domain, toExpr codomain,
          toExpr body, toExpr argument]
  | .eta domain codomain function =>
      mkAppN (higherOrderConst ``HODAGCertificate.BetaEta.Trace.eta)
        #[signatureExpr, toExpr domain, toExpr codomain, toExpr function]
  | .trans first second =>
      mkAppN (higherOrderConst ``HODAGCertificate.BetaEta.Trace.trans)
        #[signatureExpr, betaEtaTraceExpr first, betaEtaTraceExpr second]

instance : ToExpr BetaEtaTrace where
  toTypeExpr := appliedType ``HODAGCertificate.BetaEta.Trace
  toExpr := betaEtaTraceExpr

private def parentClauseExpr (parent : ParentClause) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.ParentClause.mk)
    #[signatureExpr, toExpr parent.id, toExpr parent.clause]

instance : ToExpr ParentClause where
  toTypeExpr := appliedType ``HODAGCertificate.ParentClause
  toExpr := parentClauseExpr

private def substitutionEvidenceExpr
    (evidence : SubstitutionEvidence) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Substitution.Evidence.mk)
    #[signatureExpr, toExpr evidence.parent, toExpr evidence.substitution]

instance : ToExpr SubstitutionEvidence where
  toTypeExpr := appliedType ``HODAGCertificate.Substitution.Evidence
  toExpr := substitutionEvidenceExpr

private def standardizeApartEvidenceExpr
    (evidence : StandardizeApartEvidence) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.StandardizeApart.Evidence.mk)
    #[signatureExpr, toExpr evidence.parent, toExpr evidence.offset]

instance : ToExpr StandardizeApartEvidence where
  toTypeExpr := appliedType ``HODAGCertificate.StandardizeApart.Evidence
  toExpr := standardizeApartEvidenceExpr

private def resolutionEvidenceExpr
    (evidence : ResolutionEvidence) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Resolution.Evidence.mk)
    #[signatureExpr, toExpr evidence.left, toExpr evidence.right,
      toExpr evidence.pivot, toExpr evidence.leftPolarity]

instance : ToExpr ResolutionEvidence where
  toTypeExpr := appliedType ``HODAGCertificate.Resolution.Evidence
  toExpr := resolutionEvidenceExpr

private def factoringEvidenceExpr
    (evidence : FactoringEvidence) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Factoring.Evidence.mk)
    #[signatureExpr, toExpr evidence.parent, toExpr evidence.conclusion]

instance : ToExpr FactoringEvidence where
  toTypeExpr := appliedType ``HODAGCertificate.Factoring.Evidence
  toExpr := factoringEvidenceExpr

private def equalityResolutionEvidenceExpr
    (evidence : EqualityResolutionEvidence) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.EqualityResolution.Evidence.mk)
    #[signatureExpr, toExpr evidence.parent, toExpr evidence.sort,
      toExpr evidence.left, toExpr evidence.right]

instance : ToExpr EqualityResolutionEvidence where
  toTypeExpr := appliedType ``HODAGCertificate.EqualityResolution.Evidence
  toExpr := equalityResolutionEvidenceExpr

private def booleanExtensionalityEvidenceExpr
    (evidence : BooleanExtensionalityEvidence) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.BooleanExtensionality.Evidence.mk)
    #[signatureExpr, toExpr evidence.parent, toExpr evidence.literalIndex,
      toExpr evidence.sort, toExpr evidence.polarity,
      toExpr evidence.left, toExpr evidence.right]

instance : ToExpr BooleanExtensionalityEvidence where
  toTypeExpr := appliedType ``HODAGCertificate.BooleanExtensionality.Evidence
  toExpr := booleanExtensionalityEvidenceExpr

private def termContextExpr : TermContext → Expr
  | .hole =>
      mkApp (higherOrderConst ``HODAGCertificate.TermContext.hole) signatureExpr
  | .app symbol before context suffix =>
      mkAppN (higherOrderConst ``HODAGCertificate.TermContext.app)
        #[signatureExpr, toExpr symbol, toExpr before,
          termContextExpr context, toExpr suffix]
  | .applyFunction context argument =>
      mkAppN (higherOrderConst ``HODAGCertificate.TermContext.applyFunction)
        #[signatureExpr, termContextExpr context, toExpr argument]
  | .applyArgument function context =>
      mkAppN (higherOrderConst ``HODAGCertificate.TermContext.applyArgument)
        #[signatureExpr, toExpr function, termContextExpr context]
  | .lam domain codomain context =>
      mkAppN (higherOrderConst ``HODAGCertificate.TermContext.lam)
        #[signatureExpr, toExpr domain, toExpr codomain,
          termContextExpr context]

instance : ToExpr TermContext where
  toTypeExpr := appliedType ``HODAGCertificate.TermContext
  toExpr := termContextExpr

private def atomContextExpr : AtomContext → Expr
  | .rel symbol before context suffix =>
      mkAppN (higherOrderConst ``HODAGCertificate.AtomContext.rel)
        #[signatureExpr, toExpr symbol, toExpr before,
          toExpr context, toExpr suffix]
  | .equalLeft sort context right =>
      mkAppN (higherOrderConst ``HODAGCertificate.AtomContext.equalLeft)
        #[signatureExpr, toExpr sort, toExpr context, toExpr right]
  | .equalRight sort left context =>
      mkAppN (higherOrderConst ``HODAGCertificate.AtomContext.equalRight)
        #[signatureExpr, toExpr sort, toExpr left, toExpr context]

instance : ToExpr AtomContext where
  toTypeExpr := appliedType ``HODAGCertificate.AtomContext
  toExpr := atomContextExpr

private def rewriteEvidenceExpr (evidence : RewriteEvidence) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Rewrite.Evidence.mk)
    #[signatureExpr, toExpr evidence.equality, toExpr evidence.target,
      toExpr evidence.context, toExpr evidence.sort, toExpr evidence.lhs,
      toExpr evidence.rhs, toExpr evidence.equalityReversed,
      toExpr evidence.targetPolarity]

instance : ToExpr RewriteEvidence where
  toTypeExpr := appliedType ``HODAGCertificate.Rewrite.Evidence
  toExpr := rewriteEvidenceExpr

private def argumentCongruenceEvidenceExpr
    (evidence : ArgumentCongruenceEvidence) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.ArgumentCongruence.Evidence.mk)
    #[signatureExpr, toExpr evidence.parent, toExpr evidence.domain,
      toExpr evidence.codomain, toExpr evidence.left, toExpr evidence.right,
      toExpr evidence.argument]

instance : ToExpr ArgumentCongruenceEvidence where
  toTypeExpr := appliedType ``HODAGCertificate.ArgumentCongruence.Evidence
  toExpr := argumentCongruenceEvidenceExpr

private def functionExtensionalityEvidenceExpr
    (evidence : FunctionExtensionalityEvidence) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.FunctionExtensionality.Evidence.mk)
    #[signatureExpr, toExpr evidence.parent, toExpr evidence.domain,
      toExpr evidence.codomain, toExpr evidence.left, toExpr evidence.right,
      toExpr evidence.witnessSymbol]

instance : ToExpr FunctionExtensionalityEvidence where
  toTypeExpr := appliedType ``HODAGCertificate.FunctionExtensionality.Evidence
  toExpr := functionExtensionalityEvidenceExpr

private def problemExpr (problem : Problem) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Problem.mk)
    #[signatureExpr, toExpr problem.initialClauses]

instance : ToExpr Problem where
  toTypeExpr := appliedType ``HODAGCertificate.Problem
  toExpr := problemExpr

private def propLiteralLinkExpr (link : PropLiteralLink) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.PropLiteralLink.mk)
    #[signatureExpr, toExpr link.prop, toExpr link.object]

instance : ToExpr PropLiteralLink where
  toTypeExpr := appliedType ``HODAGCertificate.PropLiteralLink
  toExpr := propLiteralLinkExpr

private def propParentClauseLinkExpr
    (link : PropParentClauseLink) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.PropParentClauseLink.mk)
    #[signatureExpr, toExpr link.parent, toExpr link.literalLinks]

instance : ToExpr PropParentClauseLink where
  toTypeExpr := appliedType ``HODAGCertificate.PropParentClauseLink
  toExpr := propParentClauseLinkExpr

private def propGuardActivationLinkExpr
    (link : PropGuardActivationLink) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.PropGuardActivationLink.mk)
    #[signatureExpr, toExpr link.parent, toExpr link.guards,
      toExpr link.literalLinks]

instance : ToExpr PropGuardActivationLink where
  toTypeExpr := appliedType ``HODAGCertificate.PropGuardActivationLink
  toExpr := propGuardActivationLinkExpr

private def propLearnedClauseLinkExpr
    (link : PropLearnedClauseLink) : Expr :=
  mkAppN (mkConst ``HODAGCertificate.PropLearnedClauseLink.mk)
    #[toExpr link.parent, toExpr link.guards, toExpr link.clause]

instance : ToExpr PropLearnedClauseLink where
  toTypeExpr := mkConst ``HODAGCertificate.PropLearnedClauseLink
  toExpr := propLearnedClauseLinkExpr

private def propAvatarSkeletonLinkExpr
    (link : PropAvatarSkeletonLink) : Expr :=
  mkAppN (mkConst ``HODAGCertificate.PropAvatarSkeletonLink.mk)
    #[toExpr link.parent, toExpr link.skeleton]

instance : ToExpr PropAvatarSkeletonLink where
  toTypeExpr := mkConst ``HODAGCertificate.PropAvatarSkeletonLink
  toExpr := propAvatarSkeletonLinkExpr

private def propInitialJustificationExpr :
    PropInitialJustification → Expr
  | .parentClause link =>
      mkAppN
        (higherOrderConst ``HODAGCertificate.PropInitialJustification.parentClause)
        #[signatureExpr, toExpr link]
  | .guardActivationClause link =>
      mkAppN
        (higherOrderConst
          ``HODAGCertificate.PropInitialJustification.guardActivationClause)
        #[signatureExpr, toExpr link]
  | .propLearnedClause link =>
      mkAppN
        (higherOrderConst
          ``HODAGCertificate.PropInitialJustification.propLearnedClause)
        #[signatureExpr, toExpr link]
  | .avatarSkeleton link =>
      mkAppN
        (higherOrderConst
          ``HODAGCertificate.PropInitialJustification.avatarSkeleton)
        #[signatureExpr, toExpr link]

instance : ToExpr PropInitialJustification where
  toTypeExpr := appliedType ``HODAGCertificate.PropInitialJustification
  toExpr := propInitialJustificationExpr

private def propositionalClosurePayloadExpr
    (payload : PropositionalClosurePayload) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.PropositionalClosurePayload.mk)
    #[signatureExpr, toExpr payload.atomMap, toExpr payload.initialClauses,
      toExpr payload.initialJustifications, toExpr payload.proof]

instance : ToExpr PropositionalClosurePayload where
  toTypeExpr := appliedType ``HODAGCertificate.PropositionalClosurePayload
  toExpr := propositionalClosurePayloadExpr

private def avatarSplitPayloadExpr
    (payload : HODAGCertificate.AvatarSplitPayload SearchSignature) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.AvatarSplitPayload.mk)
    #[signatureExpr, toExpr payload.source, toExpr payload.partitions,
      toExpr payload.selectors]

instance : ToExpr (HODAGCertificate.AvatarSplitPayload SearchSignature) where
  toTypeExpr := appliedType ``HODAGCertificate.AvatarSplitPayload
  toExpr := avatarSplitPayloadExpr

private def avatarComponentPayloadExpr
    (payload : HODAGCertificate.AvatarComponentPayload SearchSignature) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.AvatarComponentPayload.mk)
    #[signatureExpr, toExpr payload.split, toExpr payload.componentIndex,
      toExpr payload.component, toExpr payload.selector]

instance : ToExpr (HODAGCertificate.AvatarComponentPayload SearchSignature) where
  toTypeExpr := appliedType ``HODAGCertificate.AvatarComponentPayload
  toExpr := avatarComponentPayloadExpr

private def theoryConflictPayloadExpr
    (payload : TheoryConflictPayload) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.TheoryConflictPayload.mk)
    #[signatureExpr, toExpr payload.conflict]

instance : ToExpr TheoryConflictPayload where
  toTypeExpr := appliedType ``HODAGCertificate.TheoryConflictPayload
  toExpr := theoryConflictPayloadExpr

private def propositionalLearnedClausePayloadExpr
    (payload : PropositionalLearnedClausePayload) : Expr :=
  mkAppN (mkConst ``HODAGCertificate.PropositionalLearnedClausePayload.mk)
    #[toExpr payload.conflict, toExpr payload.learned]

instance : ToExpr PropositionalLearnedClausePayload where
  toTypeExpr := mkConst ``HODAGCertificate.PropositionalLearnedClausePayload
  toExpr := propositionalLearnedClausePayloadExpr

private def payloadExpr : Payload → Expr
  | .source initialIndex =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.source)
        #[signatureExpr, toExpr initialIndex]
  | .avatarSplit payload =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.avatarSplit)
        #[signatureExpr, toExpr payload]
  | .avatarComponent payload =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.avatarComponent)
        #[signatureExpr, toExpr payload]
  | .beta payload =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.beta)
        #[signatureExpr, toExpr payload]
  | .eta payload =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.eta)
        #[signatureExpr, toExpr payload]
  | .substitution evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.substitution)
        #[signatureExpr, toExpr evidence]
  | .standardizeApart evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.standardizeApart)
        #[signatureExpr, toExpr evidence]
  | .resolution evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.resolution)
        #[signatureExpr, toExpr evidence]
  | .factoring evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.factoring)
        #[signatureExpr, toExpr evidence]
  | .equalityResolution evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.equalityResolution)
        #[signatureExpr, toExpr evidence]
  | .booleanExtensionality evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.booleanExtensionality)
        #[signatureExpr, toExpr evidence]
  | .demodulation evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.demodulation)
        #[signatureExpr, toExpr evidence]
  | .positiveSuperposition evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.positiveSuperposition)
        #[signatureExpr, toExpr evidence]
  | .negativeSuperposition evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.negativeSuperposition)
        #[signatureExpr, toExpr evidence]
  | .extensionalParamodulation evidence =>
      mkAppN
        (higherOrderConst ``HODAGCertificate.Payload.extensionalParamodulation)
        #[signatureExpr, toExpr evidence]
  | .argumentCongruence evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.argumentCongruence)
        #[signatureExpr, toExpr evidence]
  | .functionExtensionality evidence =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.functionExtensionality)
        #[signatureExpr, toExpr evidence]
  | .theoryConflict payload =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.theoryConflict)
        #[signatureExpr, toExpr payload]
  | .propositionalLearnedClause payload =>
      mkAppN
        (higherOrderConst ``HODAGCertificate.Payload.propositionalLearnedClause)
        #[signatureExpr, toExpr payload]
  | .residualCdcl payload =>
      mkAppN (higherOrderConst ``HODAGCertificate.Payload.residualCdcl)
        #[signatureExpr, toExpr payload]

instance : ToExpr Payload where
  toTypeExpr := appliedType ``HODAGCertificate.Payload
  toExpr := payloadExpr

private def nodeExpr (node : Node) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.Node.mk)
    #[signatureExpr, toExpr node.id, toExpr node.parents,
      toExpr node.guards, toExpr node.payload]

instance : ToExpr Node where
  toTypeExpr := appliedType ``HODAGCertificate.Node
  toExpr := nodeExpr

/--
引用材料化 HO-DAG，并由调用者提供本次 replay 的 core problem 表达式。

节点完整来自材料化结果；source 与 core problem 的一致性由随后执行的 `DAG.check`
复核。
-/
def dagExprWithProblem (problem : Expr) (dag : DAG) : Expr :=
  mkAppN (higherOrderConst ``HODAGCertificate.DAG.mk)
    #[signatureExpr, problem, toExpr dag.root, toExpr dag.nodes]

private def dagExpr (dag : DAG) : Expr :=
  dagExprWithProblem (toExpr dag.problem) dag

instance : ToExpr DAG where
  toTypeExpr := appliedType ``HODAGCertificate.DAG
  toExpr := dagExpr

end ReplayQuotation
end HOSearchMaterialization
end Automation
end YesMetaZFC
