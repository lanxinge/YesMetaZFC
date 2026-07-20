import YesMetaZFC.Automation.SearchMaterialization

/-!
# Checked replay 的纯 DAG 引用

搜索器在元层完成依赖切片与材料化后，只把 concrete `SearchSignature` DAG 引用为
Lean 表达式。这里不生成证明，也不信任材料化结果；调用者必须继续构造
`DAG.check = true`、capability gate 与 problem 对齐的内核证明。
-/

namespace YesMetaZFC
namespace Automation
namespace SearchMaterialization
namespace ReplayQuotation

open Lean

private def signatureExpr : Expr :=
  mkConst ``SearchSignature

private def firstOrderConst (declaration : Name) : Expr :=
  mkConst declaration [.zero, .zero, .zero]

private def unaryZeroConst (declaration : Name) : Expr :=
  mkConst declaration [.zero]

private def binaryZeroConst (declaration : Name) : Expr :=
  mkConst declaration [.zero, .zero]

private def appliedType (declaration : Name) : Expr :=
  mkApp (mkConst declaration) signatureExpr

private def termTypeExpr : Expr :=
  mkApp (firstOrderConst ``Logic.FirstOrder.Term) signatureExpr

private def formulaTypeExpr : Expr :=
  mkApp (firstOrderConst ``Logic.FirstOrder.Formula) signatureExpr

private def literalTypeExpr : Expr :=
  appliedType ``DAGCertificate.Literal

private def clauseTypeExpr : Expr :=
  appliedType ``DAGCertificate.Clause

private def parentClauseTypeExpr : Expr :=
  appliedType ``DAGCertificate.ParentClause

private def varExpr : Logic.FirstOrder.Var SearchSignature → Expr
  | .bvar sort index =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Var.bvar)
        #[signatureExpr, toExpr (show SearchSort from sort), toExpr index]
  | .fvar sort index =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Var.fvar)
        #[signatureExpr, toExpr (show SearchSort from sort), toExpr index]

mutual
  private def termExpr : Term → Expr
    | .var value =>
        mkAppN (firstOrderConst ``Logic.FirstOrder.Term.var)
          #[signatureExpr, varExpr value]
    | .app function arguments =>
        mkAppN (firstOrderConst ``Logic.FirstOrder.Term.app)
          #[signatureExpr, toExpr (show SearchFunc from function), termListExpr arguments]

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

private partial def formulaExpr : Formula → Expr
  | .falsum =>
      mkApp (firstOrderConst ``Logic.FirstOrder.Formula.falsum) signatureExpr
  | .truth =>
      mkApp (firstOrderConst ``Logic.FirstOrder.Formula.truth) signatureExpr
  | .rel relation arguments =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Formula.rel)
        #[signatureExpr, toExpr (show RelSymbol from relation), toExpr arguments]
  | .equal left right =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Formula.equal)
        #[signatureExpr, toExpr left, toExpr right]
  | .neg body =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Formula.neg)
        #[signatureExpr, formulaExpr body]
  | .conj left right =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Formula.conj)
        #[signatureExpr, formulaExpr left, formulaExpr right]
  | .disj left right =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Formula.disj)
        #[signatureExpr, formulaExpr left, formulaExpr right]
  | .imp left right =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Formula.imp)
        #[signatureExpr, formulaExpr left, formulaExpr right]
  | .iff left right =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Formula.iff)
        #[signatureExpr, formulaExpr left, formulaExpr right]
  | .forallE sort body =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Formula.forallE)
        #[signatureExpr, toExpr (show SearchSort from sort), formulaExpr body]
  | .existsE sort body =>
      mkAppN (firstOrderConst ``Logic.FirstOrder.Formula.existsE)
        #[signatureExpr, toExpr (show SearchSort from sort), formulaExpr body]

instance : ToExpr Formula where
  toTypeExpr := formulaTypeExpr
  toExpr := formulaExpr

private def literalExpr : Literal → Expr
  | ⟨polarity, atom⟩ =>
      mkAppN (mkConst ``DAGCertificate.Literal.mk)
        #[signatureExpr, toExpr polarity, toExpr atom]

instance : ToExpr Literal where
  toTypeExpr := literalTypeExpr
  toExpr := literalExpr

private def clauseExpr : Clause → Expr
  | ⟨literals⟩ =>
      mkAppN (mkConst ``DAGCertificate.Clause.mk)
        #[signatureExpr, toExpr literals]

instance : ToExpr Clause where
  toTypeExpr := clauseTypeExpr
  toExpr := clauseExpr

private def clauseProblemExpr : ClauseProblem → Expr
  | ⟨initialClauses⟩ =>
      mkAppN (mkConst ``DAGCertificate.ClauseProblem.mk)
        #[signatureExpr, toExpr initialClauses]

instance : ToExpr ClauseProblem where
  toTypeExpr := appliedType ``DAGCertificate.ClauseProblem
  toExpr := clauseProblemExpr

private def parentClauseExpr : ParentClause → Expr
  | ⟨id, clause⟩ =>
      mkAppN (mkConst ``DAGCertificate.ParentClause.mk)
        #[signatureExpr, toExpr id, toExpr clause]

instance : ToExpr ParentClause where
  toTypeExpr := parentClauseTypeExpr
  toExpr := parentClauseExpr

private def substitutionExpr :
    DAGCertificate.TermSubstitution SearchSignature → Expr
  | [] =>
      let entryType :=
        mkApp2 (binaryZeroConst ``Prod)
          (mkConst ``SearchSort)
          (mkApp2 (binaryZeroConst ``Prod) (mkConst ``Nat) termTypeExpr)
      mkApp (unaryZeroConst ``List.nil) entryType
  | (sort, index, replacement) :: tail =>
      let entryType :=
        mkApp2 (binaryZeroConst ``Prod)
          (mkConst ``SearchSort)
          (mkApp2 (binaryZeroConst ``Prod) (mkConst ``Nat) termTypeExpr)
      let pair :=
        mkAppN (binaryZeroConst ``Prod.mk)
          #[mkConst ``Nat, termTypeExpr, toExpr index, toExpr replacement]
      let entry :=
        mkAppN (binaryZeroConst ``Prod.mk)
          #[mkConst ``SearchSort,
            mkApp2 (binaryZeroConst ``Prod) (mkConst ``Nat) termTypeExpr,
            toExpr (show SearchSort from sort), pair]
      mkAppN (unaryZeroConst ``List.cons)
        #[entryType, entry, substitutionExpr tail]

private def standardizeApartSideExpr
    (evidence : DAGCertificate.StandardizeApartSideEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.StandardizeApartSideEvidence.mk)
    #[signatureExpr, toExpr evidence.parent, toExpr evidence.offset, toExpr evidence.renamed]

instance : ToExpr (DAGCertificate.StandardizeApartSideEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.StandardizeApartSideEvidence
  toExpr := standardizeApartSideExpr

private def standardizeApartExpr
    (evidence : DAGCertificate.StandardizeApartEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.StandardizeApartEvidence.mk)
    #[signatureExpr, toExpr evidence.left, toExpr evidence.right]

instance : ToExpr (DAGCertificate.StandardizeApartEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.StandardizeApartEvidence
  toExpr := standardizeApartExpr

private def localRuleFamilyExpr : DAGCertificate.LocalRuleFamily → Expr
  | .parentCdcl => mkConst ``DAGCertificate.LocalRuleFamily.parentCdcl
  | .equality => mkConst ``DAGCertificate.LocalRuleFamily.equality
  | .congruence => mkConst ``DAGCertificate.LocalRuleFamily.congruence
  | .quantifier => mkConst ``DAGCertificate.LocalRuleFamily.quantifier
  | .theory => mkConst ``DAGCertificate.LocalRuleFamily.theory
  | .composite => mkConst ``DAGCertificate.LocalRuleFamily.composite

instance : ToExpr DAGCertificate.LocalRuleFamily where
  toTypeExpr := mkConst ``DAGCertificate.LocalRuleFamily
  toExpr := localRuleFamilyExpr

private def resolutionEvidenceExpr
    (evidence : DAGCertificate.ResolutionEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.ResolutionEvidence.mk)
    #[signatureExpr, toExpr evidence.left, toExpr evidence.right,
      toExpr evidence.pivot, toExpr evidence.leftPolarity]

instance : ToExpr (DAGCertificate.ResolutionEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.ResolutionEvidence
  toExpr := resolutionEvidenceExpr

private def factoringEvidenceExpr
    (evidence : DAGCertificate.FactoringEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.FactoringEvidence.mk)
    #[signatureExpr, toExpr evidence.parent]

instance : ToExpr (DAGCertificate.FactoringEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.FactoringEvidence
  toExpr := factoringEvidenceExpr

private def equalityResolutionEvidenceExpr
    (evidence : DAGCertificate.EqualityResolutionEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.EqualityResolutionEvidence.mk)
    #[signatureExpr, toExpr evidence.parent, toExpr evidence.left, toExpr evidence.right]

instance : ToExpr (DAGCertificate.EqualityResolutionEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.EqualityResolutionEvidence
  toExpr := equalityResolutionEvidenceExpr

private partial def termContextExpr :
    DAGCertificate.TermContext SearchSignature → Expr
  | .hole =>
      mkApp (mkConst ``DAGCertificate.TermContext.hole) signatureExpr
  | .app function before context suffix =>
      mkAppN (mkConst ``DAGCertificate.TermContext.app)
        #[signatureExpr, toExpr (show SearchFunc from function), toExpr before,
          termContextExpr context, toExpr suffix]

instance : ToExpr (DAGCertificate.TermContext SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.TermContext
  toExpr := termContextExpr

private def atomContextExpr : DAGCertificate.AtomContext SearchSignature → Expr
  | .rel relation before context suffix =>
      mkAppN (mkConst ``DAGCertificate.AtomContext.rel)
        #[signatureExpr, toExpr (show RelSymbol from relation), toExpr before,
          toExpr context, toExpr suffix]
  | .equalLeft context right =>
      mkAppN (mkConst ``DAGCertificate.AtomContext.equalLeft)
        #[signatureExpr, toExpr context, toExpr right]
  | .equalRight left context =>
      mkAppN (mkConst ``DAGCertificate.AtomContext.equalRight)
        #[signatureExpr, toExpr left, toExpr context]

instance : ToExpr (DAGCertificate.AtomContext SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.AtomContext
  toExpr := atomContextExpr

private def rewriteEvidenceExpr
    (evidence : DAGCertificate.RewriteEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.RewriteEvidence.mk)
    #[signatureExpr, toExpr evidence.equality, toExpr evidence.target,
      toExpr evidence.context, toExpr evidence.lhs, toExpr evidence.rhs,
      toExpr evidence.equalityReversed, toExpr evidence.targetPolarity]

instance : ToExpr (DAGCertificate.RewriteEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.RewriteEvidence
  toExpr := rewriteEvidenceExpr

private def substitutedResolutionExpr
    (evidence : DAGCertificate.SubstitutedResolutionEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.SubstitutedResolutionEvidence.mk)
    #[signatureExpr, toExpr evidence.left, toExpr evidence.right,
      substitutionExpr evidence.substitution, toExpr evidence.pivot,
      toExpr evidence.leftPolarity]

instance : ToExpr (DAGCertificate.SubstitutedResolutionEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.SubstitutedResolutionEvidence
  toExpr := substitutedResolutionExpr

private def substitutedFactoringExpr
    (evidence : DAGCertificate.SubstitutedFactoringEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.SubstitutedFactoringEvidence.mk)
    #[signatureExpr, toExpr evidence.parent, substitutionExpr evidence.substitution]

instance : ToExpr (DAGCertificate.SubstitutedFactoringEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.SubstitutedFactoringEvidence
  toExpr := substitutedFactoringExpr

private def substitutedEqualityResolutionExpr
    (evidence :
      DAGCertificate.SubstitutedEqualityResolutionEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.SubstitutedEqualityResolutionEvidence.mk)
    #[signatureExpr, toExpr evidence.parent, substitutionExpr evidence.substitution,
      toExpr evidence.left, toExpr evidence.right]

instance :
    ToExpr (DAGCertificate.SubstitutedEqualityResolutionEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.SubstitutedEqualityResolutionEvidence
  toExpr := substitutedEqualityResolutionExpr

private def substitutedRewriteExpr
    (evidence : DAGCertificate.SubstitutedRewriteEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.SubstitutedRewriteEvidence.mk)
    #[signatureExpr, toExpr evidence.equality, toExpr evidence.target,
      substitutionExpr evidence.substitution, toExpr evidence.context, toExpr evidence.lhs,
      toExpr evidence.rhs, toExpr evidence.equalityReversed,
      toExpr evidence.targetPolarity]

instance : ToExpr (DAGCertificate.SubstitutedRewriteEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.SubstitutedRewriteEvidence
  toExpr := substitutedRewriteExpr

private def standardizedSubstitutedResolutionExpr
    (evidence :
      DAGCertificate.StandardizedSubstitutedResolutionEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.StandardizedSubstitutedResolutionEvidence.mk)
    #[signatureExpr, toExpr evidence.standardizeApart,
      substitutionExpr evidence.substitution,
      toExpr evidence.pivot, toExpr evidence.leftPolarity]

instance :
    ToExpr (DAGCertificate.StandardizedSubstitutedResolutionEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.StandardizedSubstitutedResolutionEvidence
  toExpr := standardizedSubstitutedResolutionExpr

private def standardizedSubstitutedRewriteExpr
    (evidence :
      DAGCertificate.StandardizedSubstitutedRewriteEvidence SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.StandardizedSubstitutedRewriteEvidence.mk)
    #[signatureExpr, toExpr evidence.standardizeApart,
      substitutionExpr evidence.substitution,
      toExpr evidence.context, toExpr evidence.lhs, toExpr evidence.rhs,
      toExpr evidence.equalityReversed, toExpr evidence.targetPolarity]

instance :
    ToExpr (DAGCertificate.StandardizedSubstitutedRewriteEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.StandardizedSubstitutedRewriteEvidence
  toExpr := standardizedSubstitutedRewriteExpr

private def localRuleEvidenceExpr :
    DAGCertificate.LocalRuleEvidence SearchSignature → Expr
  | .parentCopy parent =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.parentCopy)
        #[signatureExpr, toExpr parent]
  | .resolution evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.resolution)
        #[signatureExpr, toExpr evidence]
  | .factoring evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.factoring)
        #[signatureExpr, toExpr evidence]
  | .equalityResolution evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.equalityResolution)
        #[signatureExpr, toExpr evidence]
  | .demodulation evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.demodulation)
        #[signatureExpr, toExpr evidence]
  | .positiveSuperposition evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.positiveSuperposition)
        #[signatureExpr, toExpr evidence]
  | .negativeSuperposition evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.negativeSuperposition)
        #[signatureExpr, toExpr evidence]
  | .substitutedResolution evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.substitutedResolution)
        #[signatureExpr, toExpr evidence]
  | .substitutedFactoring evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.substitutedFactoring)
        #[signatureExpr, toExpr evidence]
  | .substitutedEqualityResolution evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.substitutedEqualityResolution)
        #[signatureExpr, toExpr evidence]
  | .substitutedDemodulation evidence =>
      mkAppN (mkConst ``DAGCertificate.LocalRuleEvidence.substitutedDemodulation)
        #[signatureExpr, toExpr evidence]
  | .substitutedPositiveSuperposition evidence =>
      mkAppN
        (mkConst ``DAGCertificate.LocalRuleEvidence.substitutedPositiveSuperposition)
        #[signatureExpr, toExpr evidence]
  | .substitutedNegativeSuperposition evidence =>
      mkAppN
        (mkConst ``DAGCertificate.LocalRuleEvidence.substitutedNegativeSuperposition)
        #[signatureExpr, toExpr evidence]
  | .standardizedSubstitutedResolution evidence =>
      mkAppN
        (mkConst ``DAGCertificate.LocalRuleEvidence.standardizedSubstitutedResolution)
        #[signatureExpr, toExpr evidence]
  | .standardizedSubstitutedDemodulation evidence =>
      mkAppN
        (mkConst ``DAGCertificate.LocalRuleEvidence.standardizedSubstitutedDemodulation)
        #[signatureExpr, toExpr evidence]
  | .standardizedSubstitutedPositiveSuperposition evidence =>
      mkAppN
        (mkConst
          ``DAGCertificate.LocalRuleEvidence.standardizedSubstitutedPositiveSuperposition)
        #[signatureExpr, toExpr evidence]
  | .standardizedSubstitutedNegativeSuperposition evidence =>
      mkAppN
        (mkConst
          ``DAGCertificate.LocalRuleEvidence.standardizedSubstitutedNegativeSuperposition)
        #[signatureExpr, toExpr evidence]

instance : ToExpr (DAGCertificate.LocalRuleEvidence SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.LocalRuleEvidence
  toExpr := localRuleEvidenceExpr

private def localRulePayloadExpr
    (payload : DAGCertificate.LocalRulePayload SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.LocalRulePayload.mk)
    #[signatureExpr, toExpr payload.family, toExpr payload.evidence, toExpr payload.note]

instance : ToExpr (DAGCertificate.LocalRulePayload SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.LocalRulePayload
  toExpr := localRulePayloadExpr

private def propLiteralLinkExpr
    (link : DAGCertificate.PropLiteralLink SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.PropLiteralLink.mk)
    #[signatureExpr, toExpr link.prop, toExpr link.object]

instance : ToExpr (DAGCertificate.PropLiteralLink SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.PropLiteralLink
  toExpr := propLiteralLinkExpr

private def propParentClauseLinkExpr
    (link : DAGCertificate.PropParentClauseLink SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.PropParentClauseLink.mk)
    #[signatureExpr, toExpr link.parent, toExpr link.literalLinks]

instance : ToExpr (DAGCertificate.PropParentClauseLink SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.PropParentClauseLink
  toExpr := propParentClauseLinkExpr

private def propGuardActivationLinkExpr
    (link : DAGCertificate.PropGuardActivationLink SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.PropGuardActivationLink.mk)
    #[signatureExpr, toExpr link.parent, toExpr link.guards, toExpr link.literalLinks]

instance : ToExpr (DAGCertificate.PropGuardActivationLink SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.PropGuardActivationLink
  toExpr := propGuardActivationLinkExpr

private def propLearnedClauseLinkExpr
    (link : DAGCertificate.PropLearnedClauseLink) : Expr :=
  mkAppN (mkConst ``DAGCertificate.PropLearnedClauseLink.mk)
    #[toExpr link.parent, toExpr link.clause]

instance : ToExpr DAGCertificate.PropLearnedClauseLink where
  toTypeExpr := mkConst ``DAGCertificate.PropLearnedClauseLink
  toExpr := propLearnedClauseLinkExpr

private def propAvatarSkeletonLinkExpr
    (link : DAGCertificate.PropAvatarSkeletonLink) : Expr :=
  mkAppN (mkConst ``DAGCertificate.PropAvatarSkeletonLink.mk)
    #[toExpr link.parent, toExpr link.skeleton]

instance : ToExpr DAGCertificate.PropAvatarSkeletonLink where
  toTypeExpr := mkConst ``DAGCertificate.PropAvatarSkeletonLink
  toExpr := propAvatarSkeletonLinkExpr

private def propInitialJustificationExpr :
    DAGCertificate.PropInitialJustification SearchSignature → Expr
  | .parentClause link =>
      mkAppN (mkConst ``DAGCertificate.PropInitialJustification.parentClause)
        #[signatureExpr, toExpr link]
  | .guardActivationClause link =>
      mkAppN (mkConst ``DAGCertificate.PropInitialJustification.guardActivationClause)
        #[signatureExpr, toExpr link]
  | .propLearnedClause link =>
      mkAppN (mkConst ``DAGCertificate.PropInitialJustification.propLearnedClause)
        #[signatureExpr, toExpr link]
  | .avatarSkeleton link =>
      mkAppN (mkConst ``DAGCertificate.PropInitialJustification.avatarSkeleton)
        #[signatureExpr, toExpr link]

instance : ToExpr (DAGCertificate.PropInitialJustification SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.PropInitialJustification
  toExpr := propInitialJustificationExpr

private def propositionalClosurePayloadExpr
    (payload : DAGCertificate.PropositionalClosurePayload SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.PropositionalClosurePayload.mk)
    #[signatureExpr, toExpr payload.atomMap, toExpr payload.initialClauses,
      toExpr payload.initialJustifications, toExpr payload.proof,
      toExpr payload.stats, toExpr payload.note]

instance : ToExpr (DAGCertificate.PropositionalClosurePayload SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.PropositionalClosurePayload
  toExpr := propositionalClosurePayloadExpr

private def avatarSplitPayloadExpr
    (payload : DAGCertificate.AvatarSplitPayload SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.AvatarSplitPayload.mk)
    #[signatureExpr, toExpr payload.source, toExpr payload.partitions,
      toExpr payload.selectors, toExpr payload.note]

instance : ToExpr (DAGCertificate.AvatarSplitPayload SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.AvatarSplitPayload
  toExpr := avatarSplitPayloadExpr

private def avatarComponentPayloadExpr
    (payload : DAGCertificate.AvatarComponentPayload SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.AvatarComponentPayload.mk)
    #[signatureExpr, toExpr payload.split, toExpr payload.componentIndex,
      toExpr payload.note]

instance : ToExpr (DAGCertificate.AvatarComponentPayload SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.AvatarComponentPayload
  toExpr := avatarComponentPayloadExpr

private def theoryConflictPayloadExpr
    (payload : DAGCertificate.TheoryConflictPayload SearchSignature) : Expr :=
  mkAppN (mkConst ``DAGCertificate.TheoryConflictPayload.mk)
    #[signatureExpr, toExpr payload.conflict, toExpr payload.note]

instance : ToExpr (DAGCertificate.TheoryConflictPayload SearchSignature) where
  toTypeExpr := appliedType ``DAGCertificate.TheoryConflictPayload
  toExpr := theoryConflictPayloadExpr

private def propositionalLearnedClausePayloadExpr
    (payload : DAGCertificate.PropositionalLearnedClausePayload) : Expr :=
  mkAppN (mkConst ``DAGCertificate.PropositionalLearnedClausePayload.mk)
    #[toExpr payload.conflict, toExpr payload.learned, toExpr payload.note]

instance : ToExpr DAGCertificate.PropositionalLearnedClausePayload where
  toTypeExpr := mkConst ``DAGCertificate.PropositionalLearnedClausePayload
  toExpr := propositionalLearnedClausePayloadExpr

private def payloadExpr : Payload → Expr
  | .source initialIndex =>
      mkAppN (mkConst ``DAGCertificate.Payload.source)
        #[signatureExpr, toExpr initialIndex]
  | .avatarSplit payload =>
      mkAppN (mkConst ``DAGCertificate.Payload.avatarSplit)
        #[signatureExpr, toExpr payload]
  | .avatarComponent payload =>
      mkAppN (mkConst ``DAGCertificate.Payload.avatarComponent)
        #[signatureExpr, toExpr payload]
  | .localRule payload =>
      mkAppN (mkConst ``DAGCertificate.Payload.localRule)
        #[signatureExpr, toExpr payload]
  | .theoryConflict payload =>
      mkAppN (mkConst ``DAGCertificate.Payload.theoryConflict)
        #[signatureExpr, toExpr payload]
  | .propositionalLearnedClause payload =>
      mkAppN (mkConst ``DAGCertificate.Payload.propositionalLearnedClause)
        #[signatureExpr, toExpr payload]
  | .residualCdcl payload =>
      mkAppN (mkConst ``DAGCertificate.Payload.residualCdcl)
        #[signatureExpr, toExpr payload]

instance : ToExpr Payload where
  toTypeExpr := appliedType ``DAGCertificate.Payload
  toExpr := payloadExpr

private def nodeExpr (node : Node) : Expr :=
  mkAppN (mkConst ``DAGCertificate.Node.mk)
    #[signatureExpr, toExpr node.id, toExpr node.parents, toExpr node.ruleTags,
      toExpr node.guards, toExpr node.conclusion, toExpr node.payload]

instance : ToExpr Node where
  toTypeExpr := appliedType ``DAGCertificate.Node
  toExpr := nodeExpr

/--
引用材料化 DAG，并由调用者提供本次 replay 的 clause problem 表达式。

节点仍完整来自材料化结果；source 对 clause problem 的一致性由随后执行的 `DAG.check`
复核。
-/
def dagExprWithProblem (problem : Expr) (dag : DAG) : Expr :=
  mkAppN (mkConst ``DAGCertificate.DAG.mk)
    #[signatureExpr, problem, toExpr dag.root, toExpr dag.nodes]

private def dagExpr (dag : DAG) : Expr :=
  dagExprWithProblem (toExpr dag.problem) dag

instance : ToExpr DAG where
  toTypeExpr := appliedType ``DAGCertificate.DAG
  toExpr := dagExpr

end ReplayQuotation
end SearchMaterialization
end Automation
end YesMetaZFC
