import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.Data.ClauseMetadata

/-!
# Subsumption 字句签名

这里只记录匹配中不能被 pattern 变量消去的刚性特征。签名碰撞只会保留额外候选；
最终包含关系仍由搜索层的完整 `clauseSubsumes` 判定。
-/

namespace YesMetaZFC
namespace Automation
namespace Data
namespace ClauseSignature

open CoreSyntax
open CoreSyntax.Search

private def symbolKindCode : SymbolKind → Nat
  | .parameter => 1
  | .skolem => 2
  | .definition => 3
  | .choice => 4
  | .builtin => 5
  | .extensionalWitness => 6
  | .tuple => 7

private def predicateRoleCode : PredicateRole → Nat
  | .relation => 1
  | .equalityProxy => 2
  | .membership => 3
  | .definition => 4
  | .builtin => 5

private def predicateCode : PredicateKind → Nat
  | .equal => 11
  | .member => 12
  | .boolHolds => 13
  | .definition id arity => 1009 + id * 17 + arity * 131
  | .predicate symbol =>
      2003 + symbol.id * 17 + symbol.arity * 131 +
        predicateRoleCode symbol.role * 977

/--
插入项的刚性构造特征。`var/fvar` 是 pattern matching 可绑定变量，因此不能进入必要条件。
-/
partial def insertTermFeatures (signature : Signature256) :
    CoreSyntax.Search.Term → Signature256
  | .var _ => signature
  | .fvar _ _ => signature
  | .bvar _ _ => signature.insertNat 3001
  | .app symbol arguments =>
      let signature :=
        signature.insertNat
          (4001 + symbol.id * 17 + symbol.arity * 131 +
            symbolKindCode symbol.kind * 977)
      arguments.foldl insertTermFeatures signature
  | .apply fn arg =>
      insertTermFeatures (insertTermFeatures (signature.insertNat 5003) fn) arg
  | .lam _ _ body =>
      insertTermFeatures (signature.insertNat 6007) body

/-- 构造 subsumption 的固定 256 位必要条件签名。 -/
def ofClause (clause : CoreSyntax.Search.Clause) : Signature256 :=
  clause.foldl
    (fun signature literal =>
      let polarity := if literal.positive then 1 else 0
      let signature :=
        signature.insertNat (7001 + predicateCode literal.predicate * 2 + polarity)
      insertTermFeatures (insertTermFeatures signature literal.left) literal.right)
    Signature256.empty

/-- 构造与稳定字句节点缓存的 subsumption 键。 -/
def key (clause : CoreSyntax.Search.Clause) : ClauseSubsumptionKey := {
  literalCount := clause.size
  signature := ofClause clause
}

end ClauseSignature
end Data
end Automation
end YesMetaZFC
