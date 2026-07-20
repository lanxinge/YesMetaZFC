import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.Data.ClauseSignature
import YesMetaZFC.Automation.Data.Fixpoint
import YesMetaZFC.Automation.Data.GivenWorkspace
import YesMetaZFC.Automation.Data.ModelRoundWorkspace
import YesMetaZFC.Automation.Data.Replay
import YesMetaZFC.Automation.Data.StableIdLiveness
import YesMetaZFC.Automation.Data.StableIdRegistry
import YesMetaZFC.Automation.Data.Util
import YesMetaZFC.Automation.Redundancy
import YesMetaZFC.Automation.Resolution
import YesMetaZFC.Automation.ResourceTrace
import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.Superposition.DiscriminationTree
/-!
# MF1 公共自动化：小型超消元叠加演算核心

本文件是双核自动化的第一阶后端核心。当前版本刻意保持很小：

* 旧内部 Skolem 字句只作为尚未迁移的证明数据保留；
* 实现普通 factoring、等词 factoring、等词消解与带最大文字限制的二元 resolution；
* 实现基于正等词来源的 ordered positive/negative superposition，不把等词替换公理塞回输入；
* 实现基于定向单位等词的 demodulation，把等词推理中的规范化单独下沉；
* 使用 KBO 风格的可计算项序来定向等词并过滤最大文字；
* 产物映射到公共 `Certificate.Node`，供双核调度器组合 CDCL residual。

这里仍然只是自动化证书搜索语法，不向对象语言加入新公理。
-/

namespace YesMetaZFC
namespace Automation
namespace Superposition

open Redundancy

/-- 超消元叠加演算后续证书节点的稳定命名空间。 -/
abbrev ClauseId := Nat

/-- 叠加演算内部字句直接使用 core search 子句语法。 -/
abbrev Clause := CoreSyntax.Search.Clause

/-- AVATAR support 使用的命题 guard 集。语义上按合取解释。 -/
abbrev GuardSet := PropResolution.Clause

/-- guard 集的稳定排序与去重。 -/
def canonicalGuards (guards : GuardSet) : GuardSet :=
  PropResolution.canonicalClause guards

/-- 合并两个父 support。 -/
def mergeGuards (left right : GuardSet) : GuardSet :=
  canonicalGuards (left ++ right)

/-- `left` 是否是 `right` 的更弱或相等 support。 -/
def guardSubset (left right : GuardSet) : Bool :=
  let right := canonicalGuards right
  (canonicalGuards left).all fun guard => right.contains guard

/-- 一条带 AVATAR support 的输入字句。 -/
structure GuardedClause where
  guards : GuardSet := #[]
  clause : Clause
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- 搜索器和 proof chain 共用的规则标签。 -/
inductive Rule where
  | ordinaryFactoring (parent : ClauseId)
  | equalityFactoring (parent : ClauseId)
  | equalityResolution (parent : ClauseId)
  | demodulation (equality target : ClauseId)
  | extensionalParamodulation (equality target : ClauseId)
  | booleanExtensionality (parent : ClauseId)
  | argumentCongruence (parent : ClauseId)
  | binaryResolution (left right : ClauseId)
  | positiveSuperposition (equality target : ClauseId)
  | negativeSuperposition (equality target : ClauseId)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace Rule

/-- 规则父节点列表。 -/
def parents : Rule → Array ClauseId
  | ordinaryFactoring parent => #[parent]
  | equalityFactoring parent => #[parent]
  | equalityResolution parent => #[parent]
  | demodulation equality target => #[equality, target]
  | extensionalParamodulation equality target => #[equality, target]
  | booleanExtensionality parent => #[parent]
  | argumentCongruence parent => #[parent]
  | binaryResolution left right => #[left, right]
  | positiveSuperposition equality target => #[equality, target]
  | negativeSuperposition equality target => #[equality, target]

/-- 审计日志中的规则名。 -/
def label : Rule → String
  | ordinaryFactoring _ => "ordinary factoring"
  | equalityFactoring _ => "equality factoring"
  | equalityResolution _ => "equality resolution"
  | demodulation _ _ => "demodulation"
  | extensionalParamodulation _ _ => "extensional paramodulation"
  | booleanExtensionality _ => "boolean extensionality"
  | argumentCongruence _ => "argument congruence"
  | binaryResolution _ _ => "binary resolution"
  | positiveSuperposition _ _ => "positive superposition"
  | negativeSuperposition _ _ => "negative superposition"

/-- 规则是否属于 lambda/FOOL 扩展后的高阶规则族。 -/
def isHOLambdaRule : Rule → Bool
  | extensionalParamodulation .. => true
  | booleanExtensionality .. => true
  | argumentCongruence .. => true
  | _ => false

/-- 映射到公共证书规则族标签。 -/
def certificateTag : Rule → Certificate.RuleTag
  | ordinaryFactoring .. => Certificate.RuleTag.firstOrderResolution
  | equalityFactoring .. => Certificate.RuleTag.firstOrderResolution
  | equalityResolution .. => Certificate.RuleTag.firstOrderResolution
  | demodulation .. => Certificate.RuleTag.demodulation
  | extensionalParamodulation .. => Certificate.RuleTag.hoLambdaSuperposition
  | booleanExtensionality .. => Certificate.RuleTag.booleanExtensionality
  | argumentCongruence .. => Certificate.RuleTag.hoLambdaSuperposition
  | binaryResolution .. => Certificate.RuleTag.firstOrderResolution
  | positiveSuperposition .. => Certificate.RuleTag.firstOrderSuperposition
  | negativeSuperposition .. => Certificate.RuleTag.firstOrderSuperposition

end Rule

/-- 线性 proof chain 的一步。节点编号由链位置隐式确定。 -/
structure ProofStep where
  rule : Rule
  substitution : CoreSyntax.Search.Substitution := []
  clause : Clause
  resource? : Option ResourceTrace.LocalStepWitness := none
  deriving Repr, BEq, Lean.ToExpr

/-- 小型核心停止原因。 -/
inductive Status where
  | refuted
  | cdclRefuted
  | saturated
  | fuelExhausted
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace Status

/-- 审计日志中的停止原因。 -/
def label : Status → String
  | refuted => "refuted"
  | cdclRefuted => "refuted by CDCL"
  | saturated => "saturated"
  | fuelExhausted => "fuel exhausted"

end Status

/-- 当前阶段的叠加演算证书摘要。 -/
structure Summary where
  generated : Nat := 0
  retained : Nat := 0
  residuals : Nat := 0
  steps : Nat := 0
  fuel : Nat := 0
  deriving Repr, Inhabited, Lean.ToExpr

namespace Summary

/-- 转成公共证书摘要。 -/
def toCertificateStats (summary : Summary) : Certificate.Stats :=
  {
    steps := summary.steps
    generated := summary.generated
    retained := summary.retained
    residuals := summary.residuals
    fuel := summary.fuel
  }

end Summary

/-- 字句数组中的文字总数；搜索核不再依赖旧 clausification 前端。 -/
def clauseLiteralCount (clauses : Array Clause) : Nat :=
  clauses.foldl (fun count clause => count + clause.size) 0

/-- 词项索引的根符号键；变量作为通配桶处理。 -/
inductive TermIndexKey where
  | varKey
  | bvarKey (sort : CoreSyntax.CoreSort) (index : Nat)
  | applyKey
  | lamKey (domain codomain : CoreSyntax.CoreSort)
  | symbol (kind : CoreSyntax.Search.SymbolKind) (id arity : Nat)
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace TermIndexKey

/-- 两个根键是否可能合一。变量根键与任意根兼容。 -/
def unifiable (left right : TermIndexKey) : Bool :=
  match left, right with
  | varKey, _ => true
  | _, varKey => true
  | bvarKey sort index, bvarKey sort' index' => sort == sort' && index == index'
  | applyKey, applyKey => true
  | lamKey domain codomain, lamKey domain' codomain' =>
      domain == domain' && codomain == codomain'
  | symbol kind id arity, symbol kind' id' arity' =>
      kind == kind' && id == id' && arity == arity'
  | _, _ => false

/-- `pattern` 根键是否可能匹配 `target` 根键。 -/
def canMatch (pattern target : TermIndexKey) : Bool :=
  match pattern, target with
  | varKey, _ => true
  | bvarKey sort index, bvarKey sort' index' => sort == sort' && index == index'
  | applyKey, applyKey => true
  | lamKey domain codomain, lamKey domain' codomain' =>
      domain == domain' && codomain == codomain'
  | symbol kind id arity, symbol kind' id' arity' =>
      kind == kind' && id == id' && arity == arity'
  | _, _ => false

end TermIndexKey

/-- 词项根键。 -/
def termRootKey : CoreSyntax.Search.Term → TermIndexKey
  | CoreSyntax.Search.Term.var _ => TermIndexKey.varKey
  | CoreSyntax.Search.Term.bvar sort index => TermIndexKey.bvarKey sort index
  | CoreSyntax.Search.Term.fvar .. => TermIndexKey.varKey
  | CoreSyntax.Search.Term.app symbol _ => TermIndexKey.symbol symbol.kind symbol.id symbol.arity
  | CoreSyntax.Search.Term.apply .. => TermIndexKey.applyKey
  | CoreSyntax.Search.Term.lam domain codomain _ => TermIndexKey.lamKey domain codomain

/-- 一个索引中的词项出现。 -/
structure TermOccurrence where
  clauseId : ClauseId
  literalIndex : Nat
  side : LiteralSide
  path : TermPath
  term : CoreSyntax.Search.Term
  deriving Repr, Lean.ToExpr

/-- bucket 词项索引桶。 -/
structure BucketTermIndexBucket where
  key : TermIndexKey
  entries : Array TermOccurrence := #[]
  deriving Repr, Lean.ToExpr

/--
轻量 bucket 词项索引 backend。

这里先采用 root-key bucket 的 path/discrimination index 雏形：查找时只扫描兼容根桶，
再由真正的合一/匹配函数验证候选。这已经把全体子项线性扫描压缩到少数根桶。
-/
structure BucketTermIndex where
  buckets : Array BucketTermIndexBucket := #[]
  deriving Repr, Lean.ToExpr

namespace BucketTermIndex

/-- 空词项索引。 -/
def empty : BucketTermIndex := {}

/-- 插入一个词项出现。 -/
def insert (index : BucketTermIndex) (entry : TermOccurrence) : BucketTermIndex :=
  let key := termRootKey entry.term
  Id.run do
    let mut buckets := #[]
    let mut inserted := false
    for h : i in [:index.buckets.size] do
      let bucket := index.buckets[i]
      if !inserted && bucket.key == key then
        buckets := buckets.push { bucket with entries := bucket.entries.push entry }
        inserted := true
      else
        buckets := buckets.push bucket
    unless inserted do
      buckets := buckets.push { key := key, entries := #[entry] }
    return { buckets := buckets }

/-- 折叠所有可能与 `term` 合一的词项出现，并允许 visitor 提前停止。 -/
def foldUnifiableUntil {β : Type} (index : BucketTermIndex)
    (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  let key := termRootKey term
  (Data.foldArrayUntilStep index.buckets initial fun out bucket =>
      if TermIndexKey.unifiable key bucket.key then
        Data.foldArrayUntilStep bucket.entries out visit
      else
        .next out).value

/-- 折叠所有可能与 `term` 合一的词项出现。 -/
def foldUnifiable {β : Type} (index : BucketTermIndex) (term : CoreSyntax.Search.Term)
    (initial : β) (visit : β → TermOccurrence → β) : β :=
  index.foldUnifiableUntil term initial fun state occurrence =>
    .next (visit state occurrence)

/-- 折叠所有可能与 `term` 合一的词项出现；bucket backend 中它等同于 root-key 近似。 -/
def foldUnifiableApprox {β : Type} (index : BucketTermIndex) (term : CoreSyntax.Search.Term)
    (initial : β) (visit : β → TermOccurrence → β) : β :=
  foldUnifiable index term initial visit

/-- root-key 近似合一查询的可提前停止版本。 -/
def foldUnifiableApproxUntil {β : Type} (index : BucketTermIndex)
    (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.foldUnifiableUntil term initial visit

/-- 把可能与 `term` 合一的 occurrence 追加到同一个数组。 -/
def appendUnifiableApprox (index : BucketTermIndex) (term : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) : Array TermOccurrence :=
  let key := termRootKey term
  Id.run do
    let mut out := initial
    for bucket in index.buckets do
      if TermIndexKey.unifiable key bucket.key then
        out := Data.appendArray out bucket.entries
    return out

/-- 折叠可能被 `pattern` 匹配的目标，并允许 visitor 提前停止。 -/
def foldMatchedByUntil {β : Type} (index : BucketTermIndex)
    (pattern : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  let key := termRootKey pattern
  (Data.foldArrayUntilStep index.buckets initial fun out bucket =>
      if TermIndexKey.canMatch key bucket.key then
        Data.foldArrayUntilStep bucket.entries out visit
      else
        .next out).value

/-- 折叠所有可能被 `pattern` 匹配的目标词项出现。 -/
def foldMatchedBy {β : Type} (index : BucketTermIndex) (pattern : CoreSyntax.Search.Term)
    (initial : β) (visit : β → TermOccurrence → β) : β :=
  index.foldMatchedByUntil pattern initial fun state occurrence =>
    .next (visit state occurrence)

/-- 把可能被 `pattern` 匹配的 occurrence 追加到同一个数组。 -/
def appendMatchedBy (index : BucketTermIndex) (pattern : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) : Array TermOccurrence :=
  let key := termRootKey pattern
  Id.run do
    let mut out := initial
    for bucket in index.buckets do
      if TermIndexKey.canMatch key bucket.key then
        out := Data.appendArray out bucket.entries
    return out

/-- 折叠可能匹配 `target` 的模式，并允许 visitor 提前停止。 -/
def foldPatternsMatchingUntil {β : Type} (index : BucketTermIndex)
    (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  let key := termRootKey target
  (Data.foldArrayUntilStep index.buckets initial fun out bucket =>
      if TermIndexKey.canMatch bucket.key key then
        Data.foldArrayUntilStep bucket.entries out visit
      else
        .next out).value

/-- 折叠所有可能匹配 `target` 的模式词项出现。 -/
def foldPatternsMatching {β : Type} (index : BucketTermIndex)
    (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldPatternsMatchingUntil target initial fun state occurrence =>
    .next (visit state occurrence)

/-- 把可能匹配 `target` 的模式 occurrence 追加到同一个数组。 -/
def appendPatternsMatching (index : BucketTermIndex) (target : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) : Array TermOccurrence :=
  let key := termRootKey target
  Id.run do
    let mut out := initial
    for bucket in index.buckets do
      if TermIndexKey.canMatch bucket.key key then
        out := Data.appendArray out bucket.entries
    return out

end BucketTermIndex

/-- 文字索引键，用于互补文字预筛。 -/
structure LiteralIndexKey where
  positive : Bool
  predicate : CoreSyntax.Search.PredicateKind
  left : TermIndexKey
  right : TermIndexKey
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace LiteralIndexKey

/-- 单个 term root 是否可能互补合一。 -/
def rootCompatible (query candidate : TermIndexKey) : Bool :=
  TermIndexKey.unifiable query candidate

/-- 两个文字键是否可能互补。等词允许左右交换。 -/
def complementary (query candidate : LiteralIndexKey) : Bool :=
  query.positive != candidate.positive &&
    query.predicate == candidate.predicate &&
      ((TermIndexKey.unifiable query.left candidate.left &&
          TermIndexKey.unifiable query.right candidate.right) ||
        (query.predicate == CoreSyntax.Search.PredicateKind.equal &&
          TermIndexKey.unifiable query.left candidate.right &&
          TermIndexKey.unifiable query.right candidate.left))

end LiteralIndexKey

/-- literal 判别索引 key：按极性、谓词和两侧 root 分桶。 -/
structure LiteralDiscriminationKey where
  positive : Bool
  predicate : CoreSyntax.Search.PredicateKind
  left : TermIndexKey
  right : TermIndexKey
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace LiteralDiscriminationKey

/-- 从 literal 构造精确分桶 key。 -/
def ofLiteral (literal : CoreSyntax.Search.Literal) : LiteralDiscriminationKey :=
  {
    positive := literal.positive
    predicate := literal.predicate
    left := termRootKey literal.left
    right := termRootKey literal.right
  }

/-- 分桶 key 是否可能是给定 query 的互补文字。 -/
def complementaryToLiteral (query : CoreSyntax.Search.Literal)
    (candidate : LiteralDiscriminationKey) : Bool :=
  LiteralIndexKey.complementary {
    positive := query.positive
    predicate := query.predicate
    left := termRootKey query.left
    right := termRootKey query.right
  } {
    positive := candidate.positive
    predicate := candidate.predicate
    left := candidate.left
    right := candidate.right
  }

end LiteralDiscriminationKey

/-- 文字根键。 -/
def literalIndexKey (literal : CoreSyntax.Search.Literal) : LiteralIndexKey :=
  {
    positive := literal.positive
    predicate := literal.predicate
    left := termRootKey literal.left
    right := termRootKey literal.right
  }

/-- 一个索引中的文字出现。 -/
structure LiteralOccurrence where
  clauseId : ClauseId
  literalIndex : Nat
  literal : CoreSyntax.Search.Literal
  deriving Repr, Lean.ToExpr

/-- bucket 文字索引桶。 -/
structure BucketLiteralIndexBucket where
  key : LiteralDiscriminationKey
  entries : Array LiteralOccurrence := #[]
  deriving Repr, Lean.ToExpr

/-- literal 判别索引的 polarity/predicate 分区。 -/
structure LiteralDiscriminationPartition where
  positive : Bool
  predicate : CoreSyntax.Search.PredicateKind
  buckets : Array BucketLiteralIndexBucket := #[]
  deriving Repr, Lean.ToExpr

/-- predicate/root/sort-aware literal 索引。只用于互补候选检索。 -/
structure LiteralDiscriminationIndex where
  partitions : Array LiteralDiscriminationPartition := #[]
  deriving Repr, Lean.ToExpr

namespace LiteralDiscriminationIndex

/-- 空 literal 判别索引。 -/
def empty : LiteralDiscriminationIndex := {}

/-- 在一个 polarity/predicate 分区中插入 literal。 -/
def insertIntoPartition (partition : LiteralDiscriminationPartition)
    (entry : LiteralOccurrence) : LiteralDiscriminationPartition :=
  let key := LiteralDiscriminationKey.ofLiteral entry.literal
  Id.run do
    let mut buckets := #[]
    let mut inserted := false
    for h : i in [:partition.buckets.size] do
      let bucket := partition.buckets[i]
      if !inserted && bucket.key == key then
        buckets := buckets.push { bucket with entries := bucket.entries.push entry }
        inserted := true
      else
        buckets := buckets.push bucket
    unless inserted do
      buckets := buckets.push { key := key, entries := #[entry] }
    return { partition with buckets := buckets }

/-- 插入一个 selected literal occurrence。 -/
def insert (index : LiteralDiscriminationIndex) (entry : LiteralOccurrence) :
    LiteralDiscriminationIndex :=
  let key := LiteralDiscriminationKey.ofLiteral entry.literal
  Id.run do
    let mut partitions := #[]
    let mut inserted := false
    for h : i in [:index.partitions.size] do
      let partition := index.partitions[i]
      if !inserted && partition.positive == key.positive &&
          partition.predicate == key.predicate then
        partitions := partitions.push (insertIntoPartition partition entry)
        inserted := true
      else
        partitions := partitions.push partition
    unless inserted do
      let partition : LiteralDiscriminationPartition := {
        positive := key.positive
        predicate := key.predicate
        buckets := #[]
      }
      partitions := partitions.push (insertIntoPartition partition entry)
    return { partitions := partitions }

/-- 查找 polarity/predicate 互补分区。 -/
def complementaryPartition? (index : LiteralDiscriminationIndex)
    (literal : CoreSyntax.Search.Literal) : Option LiteralDiscriminationPartition :=
  index.partitions.find? fun partition =>
    partition.positive != literal.positive && partition.predicate == literal.predicate

/-- 在互补分区中做 root/sort-aware 查询，并允许 visitor 提前停止。 -/
def foldComplementaryUntil {β : Type} (index : LiteralDiscriminationIndex)
    (literal : CoreSyntax.Search.Literal) (initial : β)
    (visit : β → LiteralOccurrence → Data.FoldStep β) : β :=
  match complementaryPartition? index literal with
  | none => initial
  | some partition =>
      (Data.foldArrayUntilStep partition.buckets initial fun out bucket =>
          if LiteralDiscriminationKey.complementaryToLiteral literal bucket.key then
            Data.foldArrayUntilStep bucket.entries out visit
          else
            .next out).value

/-- 在对应互补分区中做 root/sort-aware 折叠查询。 -/
def foldComplementary {β : Type} (index : LiteralDiscriminationIndex)
    (literal : CoreSyntax.Search.Literal) (initial : β)
    (visit : β → LiteralOccurrence → β) : β :=
  index.foldComplementaryUntil literal initial fun state occurrence =>
    .next (visit state occurrence)

/-- 把 root/sort-aware 互补 occurrence 追加到同一个数组。 -/
def appendComplementary (index : LiteralDiscriminationIndex)
    (literal : CoreSyntax.Search.Literal)
    (initial : Array LiteralOccurrence := #[]) : Array LiteralOccurrence :=
  match complementaryPartition? index literal with
  | none => initial
  | some partition =>
      Id.run do
        let mut out := initial
        for bucket in partition.buckets do
          if LiteralDiscriminationKey.complementaryToLiteral literal bucket.key then
            out := Data.appendArray out bucket.entries
        return out

/-- 是否存在可能与 `literal` 互补的 indexed literal，不物化候选数组。 -/
def hasComplementary (index : LiteralDiscriminationIndex)
    (literal : CoreSyntax.Search.Literal) : Bool :=
  match complementaryPartition? index literal with
  | none => false
  | some partition =>
      partition.buckets.any fun bucket =>
        !bucket.entries.isEmpty &&
          LiteralDiscriminationKey.complementaryToLiteral literal bucket.key

/-- 索引是否为空。插入路径不会保留空 partition。 -/
@[inline]
def isEmpty (index : LiteralDiscriminationIndex) : Bool :=
  index.partitions.isEmpty

/-- indexed literal occurrence 数量。 -/
def size (index : LiteralDiscriminationIndex) : Nat :=
  index.partitions.foldl
    (fun count partition =>
      partition.buckets.foldl (fun count bucket => count + bucket.entries.size) count)
    0

end LiteralDiscriminationIndex

/-- Arena 完美判别树词项索引。 -/
abbrev ArenaTermIndex := DiscriminationTree.PerfectDiscriminationTree TermOccurrence

/--
单 backend 词项索引。

索引创建时固定实现，后续插入与查询不再同时维护 bucket/PDT，也不再按调用点重复分派。
-/
inductive TermIndex where
  | bucket (index : BucketTermIndex)
  | discriminationTree (index : ArenaTermIndex)
  deriving Repr, Lean.ToExpr

namespace TermIndex

/-- 按配置创建唯一 backend。 -/
def empty : Redundancy.IndexBackendKind → TermIndex
  | Redundancy.IndexBackendKind.bucket => .bucket BucketTermIndex.empty
  | Redundancy.IndexBackendKind.discriminationTree =>
      .discriminationTree DiscriminationTree.PerfectDiscriminationTree.empty

/-- 插入一个 term occurrence。 -/
def insert (index : TermIndex) (entry : TermOccurrence) : TermIndex :=
  match index with
  | TermIndex.bucket bucketIndex => TermIndex.bucket (bucketIndex.insert entry)
  | TermIndex.discriminationTree treeIndex =>
      TermIndex.discriminationTree (treeIndex.insertTerm entry.term entry)

/-- 折叠近似可合一候选，并允许 visitor 提前停止。 -/
def foldUnifiableApproxUntil {β : Type} (index : TermIndex)
    (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  match index with
  | TermIndex.bucket bucketIndex =>
      bucketIndex.foldUnifiableApproxUntil term initial visit
  | TermIndex.discriminationTree treeIndex =>
      treeIndex.foldUnifiableApproxUntil term initial visit

/-- 折叠近似可合一候选。 -/
def foldUnifiableApprox {β : Type} (index : TermIndex)
    (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldUnifiableApproxUntil term initial fun state occurrence =>
    .next (visit state occurrence)

/-- 折叠可被模式匹配的目标，并允许 visitor 提前停止。 -/
def foldMatchedByUntil {β : Type} (index : TermIndex)
    (pattern : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  match index with
  | TermIndex.bucket bucketIndex =>
      bucketIndex.foldMatchedByUntil pattern initial visit
  | TermIndex.discriminationTree treeIndex =>
      treeIndex.foldMatchedByUntil pattern initial visit

/-- 折叠可被模式匹配的目标。 -/
def foldMatchedBy {β : Type} (index : TermIndex)
    (pattern : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldMatchedByUntil pattern initial fun state occurrence =>
    .next (visit state occurrence)

/-- 折叠可能匹配目标的模式，并允许 visitor 提前停止。 -/
def foldPatternsMatchingUntil {β : Type} (index : TermIndex)
    (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  match index with
  | TermIndex.bucket bucketIndex =>
      bucketIndex.foldPatternsMatchingUntil target initial visit
  | TermIndex.discriminationTree treeIndex =>
      treeIndex.foldPatternsMatchingUntil target initial visit

/-- 折叠可能匹配目标的模式。 -/
def foldPatternsMatching {β : Type} (index : TermIndex)
    (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldPatternsMatchingUntil target initial fun state occurrence =>
    .next (visit state occurrence)

/-- 把近似可合一 occurrence 追加到同一个输出数组。 -/
def appendUnifiableApprox (index : TermIndex) (term : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) : Array TermOccurrence :=
  match index with
  | TermIndex.bucket bucketIndex => bucketIndex.appendUnifiableApprox term initial
  | TermIndex.discriminationTree treeIndex => treeIndex.appendUnifiableApprox term initial

/-- 把可被模式匹配的 occurrence 追加到同一个输出数组。 -/
def appendMatchedBy (index : TermIndex) (pattern : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) : Array TermOccurrence :=
  match index with
  | TermIndex.bucket bucketIndex => bucketIndex.appendMatchedBy pattern initial
  | TermIndex.discriminationTree treeIndex => treeIndex.appendMatchedBy pattern initial

/-- 把可能匹配目标的模式 occurrence 追加到同一个输出数组。 -/
def appendPatternsMatching (index : TermIndex) (target : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) : Array TermOccurrence :=
  match index with
  | TermIndex.bucket bucketIndex => bucketIndex.appendPatternsMatching target initial
  | TermIndex.discriminationTree treeIndex => treeIndex.appendPatternsMatching target initial

/-- 索引是否为空。 -/
@[inline]
def isEmpty (index : TermIndex) : Bool :=
  match index with
  | TermIndex.bucket bucketIndex => bucketIndex.buckets.isEmpty
  | TermIndex.discriminationTree treeIndex => treeIndex.isEmpty

end TermIndex

/-- 在一个字句内部对两个可合一普通文字做一阶 factoring，并记录 MGU。 -/
def sameLiteralAfterSubstitution (subst : CoreSyntax.Search.Substitution)
    (left right : CoreSyntax.Search.Literal) : Bool :=
  decide (CoreSyntax.Search.Substitution.applyLiteral subst left =
    CoreSyntax.Search.Substitution.applyLiteral subst right)

/--
替换后两个文字是否成为严格互补文字。

βη 等价必须由 HOSearch 的显式公理节点进入 persistent arena，不能在 resolution
checker 内隐式归一化，否则 proof journal 会产生 HO-DAG 无法材料化的旁路父边。
-/
def complementaryAfterSubstitution (subst : CoreSyntax.Search.Substitution)
    (left right : CoreSyntax.Search.Literal) : Bool :=
  let left := CoreSyntax.Search.Substitution.applyLiteral subst left
  let right := CoreSyntax.Search.Substitution.applyLiteral subst right
  left.positive != right.positive &&
    decide (left.predicate = right.predicate) &&
      CoreSyntax.Search.termEq left.left right.left &&
        CoreSyntax.Search.termEq left.right right.right

/--
替换后两个项是否结构相同。

非结构性的 βη 等价由独立 β/η 节点证明，再通过普通局部规则消费。
-/
def sameTermAfterSubstitution (subst : CoreSyntax.Search.Substitution)
    (left right : CoreSyntax.Search.Term) : Bool :=
  CoreSyntax.Search.termEq
    (CoreSyntax.Search.Substitution.applyTerm subst left)
    (CoreSyntax.Search.Substitution.applyTerm subst right)

/-- 在一个字句内部对两个可合一普通文字做一阶 factoring，并记录 MGU。 -/
def ordinaryFactoringAt? (clause : Clause) (i j : Nat) : Option (Clause × CoreSyntax.Search.Substitution) :=
  if hi : i < clause.size then
    if hj : j < clause.size then
      if i == j then
        none
      else
        let left := clause[i]
        let right := clause[j]
        if left.positive == right.positive && left.predicate == right.predicate then
          match CoreSyntax.Search.unifyAtom? left right with
          | some subst =>
              if sameLiteralAfterSubstitution subst left right then
                let factored := eraseLiteral (CoreSyntax.Search.Substitution.applyClause subst clause) j
                some (factored, subst)
              else
                none
          | none => none
        else
          none
    else
      none
  else
    none

/-- 构造内部等词文字。 -/
def equalityLiteral (positive : Bool) (left right : CoreSyntax.Search.Term) : CoreSyntax.Search.Literal :=
  {
    positive := positive
    predicate := CoreSyntax.Search.PredicateKind.equal
    left := left
    right := right
  }

/-- 删除列表中的两个文字位置；两个位置相同时只删除该位置一次。 -/
def eraseTwoLiteralsList : List CoreSyntax.Search.Literal → Nat → Nat → List CoreSyntax.Search.Literal
  | [], _, _ => []
  | _ :: rest, 0, 0 => rest
  | _ :: rest, 0, second + 1 => eraseLiteralList rest second
  | _ :: rest, first + 1, 0 => eraseLiteralList rest first
  | literal :: rest, first + 1, second + 1 =>
      literal :: eraseTwoLiteralsList rest first second

/-- 删除字句中的两个文字位置。 -/
def eraseTwoLiterals (clause : Clause) (first second : Nat) : Clause :=
  (eraseTwoLiteralsList clause.toList first second).toArray

/-- 一个正等词文字的一个方向。等词 factoring 会枚举左右两个方向。 -/
structure EqualityOrientation where
  lhs : CoreSyntax.Search.Term
  rhs : CoreSyntax.Search.Term
  deriving Repr, BEq, Lean.ToExpr

/-- 正等词文字的两个可用方向；非正等词没有方向。 -/
def positiveEqualityOrientations (literal : CoreSyntax.Search.Literal) : Array EqualityOrientation :=
  if literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal then
    #[
      { lhs := literal.left, rhs := literal.right },
      { lhs := literal.right, rhs := literal.left }
    ]
  else
    #[]

/-- 正等词文字的有序方向；只有严格大侧可作为 `lhs`。 -/
def orderedPositiveEqualityOrientations (literal : CoreSyntax.Search.Literal) : Array EqualityOrientation :=
  if literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal then
    Id.run do
      let mut out := #[]
      if TermOrdering.gt literal.left literal.right then
        out := out.push { lhs := literal.left, rhs := literal.right }
      if TermOrdering.gt literal.right literal.left then
        out := out.push { lhs := literal.right, rhs := literal.left }
      return out
  else
    #[]

/-- 函数 sort 是否可外延展开。 -/
def arrowSort? (term : CoreSyntax.Search.Term) :
    Option (CoreSyntax.CoreSort × CoreSyntax.CoreSort) := do
  let sort ← term.inferSort?
  sort.arrow?

/-- 给函数等式生成逐点等式参数。 -/
def extensionalPointwiseLiteral? (left right : CoreSyntax.Search.Term) :
    Option CoreSyntax.Search.Literal := do
  let (domain, _codomain) ← arrowSort? left
  let (domain', _codomain') ← arrowSort? right
  if domain == domain' then
    let varId := Nat.max left.maxVarSucc right.maxVarSucc
    let binder := CoreSyntax.Search.Term.fvar domain varId
    let left' := CoreSyntax.Search.Term.apply left binder
    let right' := CoreSyntax.Search.Term.apply right binder
    some (equalityLiteral true left' right')
  else
    none

/-- 对正函数等词两侧应用同一个新鲜参数。 -/
def argumentCongruenceAt? (clause : Clause) (index : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if h : index < clause.size then
    let literal := clause[index]
    if literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal then
      match extensionalPointwiseLiteral? literal.left literal.right with
      | some pointwise =>
          let clause := eraseLiteral clause index ++ #[pointwise]
          some (normalizeClause clause, [])
      | none => none
    else
      none
  else
    none

/-- Bool 等词作为命题等价的规则层入口。当前搜索层用 bool equality literal 承载 iff。 -/
def boolEqualityLiteral? (literal : CoreSyntax.Search.Literal) : Option CoreSyntax.Search.Literal :=
  if literal.predicate == CoreSyntax.Search.PredicateKind.equal then
    match literal.left.inferSort?, literal.right.inferSort? with
    | some CoreSyntax.CoreSort.bool, some CoreSyntax.CoreSort.bool =>
        some literal
    | _, _ => none
  else
    none

/-- Boolean extensionality/propositional equality 的显式规则步。 -/
def booleanExtensionalityAt? (clause : Clause) (index : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if h : index < clause.size then
    match boolEqualityLiteral? clause[index] with
    | some literal =>
        let normalized : CoreSyntax.Search.Literal := {
          literal with
          left := CoreSyntax.Search.normalizeBetaEta literal.left
          right := CoreSyntax.Search.normalizeBetaEta literal.right
        }
        let clause := eraseLiteral clause index ++ #[normalized]
        if normalizeClause clause == normalizeClause clause then
          some (normalizeClause clause, [])
        else
          none
    | none => none
  else
    none

/-- 对一个负等词文字执行 equality/reflexivity resolution。 -/
def equalityResolutionAt? (config : Config) (clause : Clause) (index : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if h : index < clause.size then
    let literal := clause[index]
    if eligibleNegativeEquality config clause index then
      match CoreSyntax.Search.unify? literal.left literal.right with
      | some subst =>
          if sameTermAfterSubstitution subst literal.left literal.right then
            some (CoreSyntax.Search.Substitution.applyClause subst (eraseLiteral clause index), subst)
          else
            none
      | none => none
    else
      none
  else
    none

/-- 对两个有序正等词文字执行 equality factoring。 -/
def equalityFactoringAt? (config : Config) (clause : Clause) (mainIndex otherIndex : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if hMain : mainIndex < clause.size then
    if hOther : otherIndex < clause.size then
      if mainIndex == otherIndex || !selectedForResolution config clause mainIndex then
        none
      else
        let mainLiteral := clause[mainIndex]
        let otherLiteral := clause[otherIndex]
        (orderedPositiveEqualityOrientations mainLiteral).toList.findSome? fun main =>
          (orderedPositiveEqualityOrientations otherLiteral).toList.findSome? fun other =>
            match CoreSyntax.Search.unify? main.lhs other.lhs with
            | some subst =>
                -- checker 显式记录合一后置条件，soundness replay 不信任合一器实现细节。
                if sameTermAfterSubstitution subst main.lhs other.lhs then
                  let rest := CoreSyntax.Search.Substitution.applyClause subst
                    (eraseTwoLiterals clause mainIndex otherIndex)
                  let negative := equalityLiteral false
                    (CoreSyntax.Search.Substitution.applyTerm subst main.rhs)
                    (CoreSyntax.Search.Substitution.applyTerm subst other.rhs)
                  let kept := equalityLiteral true
                    (CoreSyntax.Search.Substitution.applyTerm subst other.lhs)
                    (CoreSyntax.Search.Substitution.applyTerm subst other.rhs)
                  some (#[negative, kept] ++ rest, subst)
                else
                  none
            | none => none
    else
      none
  else
    none

/-- 在已经 standardize-apart 的两个字句上生成 resolvent，并记录所用 MGU。 -/
def resolventAtStandardized? (left right : Clause) (i j : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if hi : i < left.size then
    if hj : j < right.size then
      match complementarySubstitution? left[i] right[j] with
      | some subst =>
          if complementaryAfterSubstitution subst left[i] right[j] then
            let rest := eraseLiteral left i ++ eraseLiteral right j
            some (CoreSyntax.Search.Substitution.applyClause subst rest, subst)
          else
            none
      | none => none
    else
      none
  else
    none

/-- 由两个父字句的第 `i/j` 个互补文字生成 resolvent；内部先标准化变量。 -/
def resolventAt? (left right : Clause) (i j : Nat) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  let (left, right) := CoreSyntax.Search.standardizeApart left right
  resolventAtStandardized? left right i j

/-- 持久 occurrence 的综合索引。每个字段只承担一种推理角色。 -/
structure ClauseIndex where
  positiveEqualities : TermIndex
  negativeEqualityTerms : TermIndex
  complementaryLiterals : LiteralDiscriminationIndex := LiteralDiscriminationIndex.empty
  superpositionTargets : TermIndex
  demodulators : TermIndex
  liveness : Data.StableIdLiveness := {}
  registered : Data.StableIdRegistry := {}
  requiresActiveFilter : Bool := false
  deriving Repr, Lean.ToExpr

namespace ClauseIndex

/-- 空综合索引。 -/
def empty (config : Config) : ClauseIndex := {
  positiveEqualities := TermIndex.empty config.indexBackend
  negativeEqualityTerms := TermIndex.empty config.indexBackend
  superpositionTargets := TermIndex.empty config.indexBackend
  demodulators := TermIndex.empty config.indexBackend
}

@[inline]
def isVisible (index : ClauseIndex) (workspace : Data.GivenWorkspace)
    (clauseId : ClauseId) : Bool :=
  if index.requiresActiveFilter && !workspace.isActive clauseId then
    false
  else if index.liveness.hasTombstones then
    index.liveness.isLive! clauseId
  else
    true

/-- 后续查询必须按当前模型轮的 Active generation 过滤。 -/
@[inline]
def enableActiveFilter (index : ClauseIndex) : ClauseIndex :=
  { index with requiresActiveFilter := true }

/-- 折叠可与给定项合一的 active 目标，并允许 visitor 提前停止。 -/
def foldUnifiableSuperpositionTargetsUntil {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.superpositionTargets.foldUnifiableApproxUntil term initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state

/-- 折叠可与给定项合一的 active 可叠加目标位置。 -/
def foldUnifiableSuperpositionTargets {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldUnifiableSuperpositionTargetsUntil workspace term initial
    fun state occurrence => .next (visit state occurrence)

/-- 追加可与给定项合一的 active 可叠加目标。 -/
def appendUnifiableSuperpositionTargets (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) :
    Array TermOccurrence :=
  index.foldUnifiableSuperpositionTargets workspace term initial Array.push

/-- 折叠可被给定模式匹配的 active 目标，并允许 visitor 提前停止。 -/
def foldMatchedSuperpositionTargetsByUntil {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (pattern : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.superpositionTargets.foldMatchedByUntil pattern initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state

/-- 折叠可被给定模式匹配的 active 可叠加目标位置。 -/
def foldMatchedSuperpositionTargetsBy {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (pattern : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldMatchedSuperpositionTargetsByUntil workspace pattern initial
    fun state occurrence => .next (visit state occurrence)

/-- 追加可被给定模式匹配的 active 可叠加目标。 -/
def appendMatchedSuperpositionTargetsBy (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (pattern : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) :
    Array TermOccurrence :=
  index.foldMatchedSuperpositionTargetsBy workspace pattern initial Array.push

/-- 折叠 active 负等词侧项，并允许 visitor 提前停止。 -/
def foldUnifiableNegativeEqualityTermsUntil {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.negativeEqualityTerms.foldUnifiableApproxUntil term initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state

/-- 折叠 active 中可能与给定负等词侧项合一的负等词侧项。 -/
def foldUnifiableNegativeEqualityTerms {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldUnifiableNegativeEqualityTermsUntil workspace term initial
    fun state occurrence => .next (visit state occurrence)

/-- 追加可与给定项合一的 active 负等词侧项。 -/
def appendUnifiableNegativeEqualityTerms (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) :
    Array TermOccurrence :=
  index.foldUnifiableNegativeEqualityTerms workspace term initial Array.push

/-- 折叠互补 active 文字，并允许 visitor 提前停止。 -/
def foldComplementaryLiteralsUntil {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (literal : CoreSyntax.Search.Literal) (initial : β)
    (visit : β → LiteralOccurrence → Data.FoldStep β) : β :=
  index.complementaryLiterals.foldComplementaryUntil literal initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state

/-- 折叠可能与给定文字互补的 active 文字出现。 -/
def foldComplementaryLiterals {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (literal : CoreSyntax.Search.Literal) (initial : β)
    (visit : β → LiteralOccurrence → β) : β :=
  index.foldComplementaryLiteralsUntil workspace literal initial
    fun state occurrence => .next (visit state occurrence)

/-- 追加可能与给定文字互补的 active 文字。 -/
def appendComplementaryLiterals (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (literal : CoreSyntax.Search.Literal)
    (initial : Array LiteralOccurrence := #[]) :
    Array LiteralOccurrence :=
  index.foldComplementaryLiterals workspace literal initial Array.push

/-- 是否存在可能与给定文字互补的 active 文字，不物化 occurrence 数组。 -/
def hasComplementary (index : ClauseIndex) (workspace : Data.GivenWorkspace)
    (literal : CoreSyntax.Search.Literal) : Bool :=
  index.foldComplementaryLiterals workspace literal false fun _ _ => true

/-- active 互补文字索引是否为空。 -/
@[inline]
def complementaryLiteralsEmpty (index : ClauseIndex) (workspace : Data.GivenWorkspace) : Bool :=
  !index.complementaryLiterals.partitions.any fun partition =>
    partition.buckets.any fun bucket =>
      bucket.entries.any fun occurrence => index.isVisible workspace occurrence.clauseId

/-- active 互补文字 occurrence 数量。 -/
def complementaryLiteralCount (index : ClauseIndex) (workspace : Data.GivenWorkspace) : Nat :=
  index.complementaryLiterals.partitions.foldl
    (fun count partition =>
      partition.buckets.foldl
        (fun count bucket =>
          bucket.entries.foldl
            (fun count occurrence =>
              count + if index.isVisible workspace occurrence.clauseId then 1 else 0)
            count)
        count)
    0

/--
折叠可与给定项合一的 active 定向等词大侧出现。

`positiveEqualities` 只由 `insertPositiveEquality` 写入；该入口会重新调用
`selectedOrientedEqualityAt?`，因此这里返回的 occurrence 已经来自 eligible 的正等词大侧。
-/
def foldUnifiablePositiveEqualitiesUntil {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.positiveEqualities.foldUnifiableApproxUntil term initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state

/-- 折叠可与给定项合一的 active 定向等词大侧出现。 -/
def foldUnifiablePositiveEqualities {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldUnifiablePositiveEqualitiesUntil workspace term initial
    fun state occurrence => .next (visit state occurrence)

/-- 追加可与给定项合一的 active 正等词大侧。 -/
def appendUnifiablePositiveEqualities (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) :
    Array TermOccurrence :=
  index.foldUnifiablePositiveEqualities workspace term initial Array.push

/-- 折叠可能匹配目标的 active 定向等词，并允许 visitor 提前停止。 -/
def foldPatternsMatchingPositiveEqualitiesUntil {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.positiveEqualities.foldPatternsMatchingUntil target initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state

/-- 折叠可能匹配给定目标项的 active 定向等词左端出现。 -/
def foldPatternsMatchingPositiveEqualities {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldPatternsMatchingPositiveEqualitiesUntil workspace target initial
    fun state occurrence => .next (visit state occurrence)

/-- 追加可能匹配给定目标项的 active 正等词模式。 -/
def appendPatternsMatchingPositiveEqualities (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) :
    Array TermOccurrence :=
  index.foldPatternsMatchingPositiveEqualities workspace target initial Array.push

/-- 折叠可能匹配目标的 active demodulator，并允许 visitor 提前停止。 -/
def foldPatternsMatchingDemodulatorsUntil {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → Data.FoldStep β) : β :=
  index.demodulators.foldPatternsMatchingUntil target initial fun state occurrence =>
    if index.isVisible workspace occurrence.clauseId then
      visit state occurrence
    else
      .next state

/-- 折叠可能匹配给定目标项的 active 单位 demodulator 左端出现。 -/
def foldPatternsMatchingDemodulators {β : Type} (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term) (initial : β)
    (visit : β → TermOccurrence → β) : β :=
  index.foldPatternsMatchingDemodulatorsUntil workspace target initial
    fun state occurrence => .next (visit state occurrence)

/-- 追加可能匹配给定目标项的 active 单位 demodulator。 -/
def appendPatternsMatchingDemodulators (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term)
    (initial : Array TermOccurrence := #[]) :
    Array TermOccurrence :=
  index.foldPatternsMatchingDemodulators workspace target initial Array.push

/-- 批量把稳定字句编号标记为索引 tombstone，不改写平坦索引 arena。 -/
def deleteMany (index : ClauseIndex) (ids : Array ClauseId) : ClauseIndex :=
  { index with liveness := index.liveness.deleteMany ids }

/-- 是否存在可与给定项合一的 active 可叠加目标，不物化 occurrence 数组。 -/
def hasUnifiableSuperpositionTarget (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) : Bool :=
  index.foldUnifiableSuperpositionTargets workspace term false fun _ _ => true

/-- 是否存在可被给定模式匹配的 active 可叠加目标，不物化 occurrence 数组。 -/
def hasMatchedSuperpositionTargetBy (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (pattern : CoreSyntax.Search.Term) : Bool :=
  index.foldMatchedSuperpositionTargetsBy workspace pattern false fun _ _ => true

/-- 是否存在可与给定项合一的 active 负等词侧项，不物化 occurrence 数组。 -/
def hasUnifiableNegativeEqualityTerm (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) : Bool :=
  index.foldUnifiableNegativeEqualityTerms workspace term false fun _ _ => true

/-- 是否存在可与给定项合一的 active 正等词大侧，不物化 occurrence 数组。 -/
def hasUnifiablePositiveEquality (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (term : CoreSyntax.Search.Term) : Bool :=
  index.foldUnifiablePositiveEqualities workspace term false fun _ _ => true

/-- 是否存在可能匹配给定目标项的 active 正等词模式。 -/
def hasPatternMatchingPositiveEquality (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term) : Bool :=
  index.foldPatternsMatchingPositiveEqualities workspace target false fun _ _ => true

/-- 是否存在可能匹配给定目标项的 active 单位 demodulator。 -/
def hasPatternMatchingDemodulator (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (target : CoreSyntax.Search.Term) : Bool :=
  index.foldPatternsMatchingDemodulators workspace target false fun _ _ => true

/-- 把一个可叠加目标位置插入 active 目标索引。 -/
def insertSuperpositionTarget
    (index : ClauseIndex) (clauseId : ClauseId) (literalIndex : Nat)
    (position : PositionedTerm) : ClauseIndex :=
  {
    index with
    superpositionTargets := index.superpositionTargets.insert {
      clauseId := clauseId
      literalIndex := literalIndex
      side := position.side
      path := position.path
      term := position.term
    }
  }

/-- 把一个 selected 文字插入 active 互补文字索引。 -/
def insertComplementaryLiteral
    (index : ClauseIndex) (clauseId : ClauseId) (literalIndex : Nat)
    (literal : CoreSyntax.Search.Literal) : ClauseIndex :=
  {
    index with
    complementaryLiterals := index.complementaryLiterals.insert {
      clauseId := clauseId
      literalIndex := literalIndex
      literal := literal
    }
  }

/-- 插入 eligible 的 selected/maximal 正等词大侧，供 ordered superposition 查询。 -/
def insertPositiveEquality
    (index : ClauseIndex) (clauseId : ClauseId) (literalIndex : Nat) (clause : Clause) :
    ClauseIndex :=
  match selectedOrientedEqualityAt? clause literalIndex with
  | some equality =>
      {
        index with
        positiveEqualities := index.positiveEqualities.insert {
          clauseId := clauseId
          literalIndex := literalIndex
          side := LiteralSide.left
          path := []
          term := equality.lhs
        }
      }
  | none => index

/-- 插入 selected 负等词文字的某一侧，供 equality resolution 与负叠加查询。 -/
def insertNegativeEqualitySide
    (index : ClauseIndex) (clauseId : ClauseId) (literalIndex : Nat)
    (side : LiteralSide) (term : CoreSyntax.Search.Term) : ClauseIndex :=
  {
    index with
    negativeEqualityTerms := index.negativeEqualityTerms.insert {
      clauseId := clauseId
      literalIndex := literalIndex
      side := side
      path := []
      term := term
    }
  }

/-- 插入 selected 负等词文字的两侧。 -/
def insertNegativeEquality
    (index : ClauseIndex) (clauseId : ClauseId) (literalIndex : Nat)
    (literal : CoreSyntax.Search.Literal) : ClauseIndex :=
  if !literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal then
    (index.insertNegativeEqualitySide clauseId literalIndex LiteralSide.left literal.left)
      |>.insertNegativeEqualitySide clauseId literalIndex LiteralSide.right literal.right
  else
    index

/-- 插入单位 demodulator，供重写查询。 -/
def insertDemodulator
    (index : ClauseIndex) (clauseId : ClauseId) (equality : OrientedEquality) : ClauseIndex :=
  {
    index with
    demodulators := index.demodulators.insert {
      clauseId := clauseId
      literalIndex := equality.literalIndex
      side := LiteralSide.left
      path := []
      term := equality.lhs
    }
  }

/-- 单条 active 字句索引构建的局部工作状态。 -/
private structure ClauseInsertion where
  index : ClauseIndex
  budget : WorkBudget
  exhausted : Bool := false

/-- 把一个 active 子句登记到综合索引中，并让全部位置枚举服从共享预算。 -/
def insertClauseWithBudget
    (config : Config) (index : ClauseIndex) (clauseId : ClauseId) (clause : Clause)
    (budget : WorkBudget) : WorkResult ClauseIndex :=
  if index.registered.contains clauseId then
    .complete index budget
  else
    let scan :=
      Data.foldNatRangeUntil 0 clause.size
        ({
          index := {
            index with
            registered := index.registered.insert clauseId
          }
          budget := budget
        } : ClauseInsertion)
        fun scan literalIndex =>
          if scan.exhausted then
            .done scan
          else
            match clause[literalIndex]? with
            | none => .next scan
            | some literal =>
                match scan.budget.charge? WorkKind.indexMaintenance with
                | none => .done { scan with exhausted := true }
                | some budget =>
                    let index :=
                      if eligibleResolutionLiteral config clause literalIndex then
                        scan.index.insertComplementaryLiteral clauseId literalIndex literal
                      else
                        scan.index
                    let index :=
                      if eligibleNegativeEquality config clause literalIndex then
                        index.insertNegativeEquality clauseId literalIndex literal
                      else
                        index
                    let scan := { scan with index := index, budget := budget }
                    let scanStep :=
                      if eligibleSuperpositionTarget config clause literalIndex ||
                          literal.predicate != CoreSyntax.Search.PredicateKind.equal then
                        foldLiteralSubtermsUntil literal scan fun scan position =>
                          match
                              (scan.budget.charge? WorkKind.termPosition).bind
                                (·.charge? WorkKind.indexMaintenance) with
                          | none => .done { scan with exhausted := true }
                          | some budget =>
                              .next {
                                scan with
                                index :=
                                  scan.index.insertSuperpositionTarget
                                    clauseId literalIndex position
                                budget := budget
                              }
                      else
                        .next scan
                    match scanStep with
                    | .done scan => .done scan
                    | .next scan =>
                        match scan.budget.charge? WorkKind.indexMaintenance with
                        | none => .done { scan with exhausted := true }
                        | some budget =>
                            .next {
                              scan with
                              index := scan.index.insertPositiveEquality clauseId literalIndex clause
                              budget := budget
                            }
    if scan.exhausted then
      .exhausted scan.budget
    else
      match scan.budget.charge? WorkKind.indexMaintenance with
      | none => .exhausted scan.budget
      | some budget =>
          let index :=
            match orientedUnitEquality? clause with
            | some equality => scan.index.insertDemodulator clauseId equality
            | none => scan.index
          .complete index budget

end ClauseIndex

/-- Superposition 的目标文字极性。正目标是普通正叠加，负目标是负等词叠加。 -/
inductive SuperpositionPolarity where
  | positive
  | negative
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace SuperpositionPolarity

/-- 审计日志中的目标极性标签。 -/
def label : SuperpositionPolarity → String
  | positive => "positive"
  | negative => "negative"

end SuperpositionPolarity

/-- 一次 ordered superposition 的可检查位置证据。 -/
structure SuperpositionSite where
  equalityLiteral : Nat
  targetLiteral : Nat
  targetPosition : PositionedTerm
  orientedLhs : CoreSyntax.Search.Term
  orientedRhs : CoreSyntax.Search.Term
  substitution : CoreSyntax.Search.Substitution
  polarity : SuperpositionPolarity := SuperpositionPolarity.positive
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace SuperpositionSite

/-- 从已定向等词和目标位置构造 site。 -/
def ofPosition
    (equality : OrientedEquality) (targetLiteral : Nat) (position : PositionedTerm)
    (substitution : CoreSyntax.Search.Substitution)
    (polarity : SuperpositionPolarity := SuperpositionPolarity.positive) :
    SuperpositionSite :=
  {
    equalityLiteral := equality.literalIndex
    targetLiteral := targetLiteral
    targetPosition := position
    orientedLhs := equality.lhs
    orientedRhs := equality.rhs
    substitution := substitution
    polarity := polarity
  }

end SuperpositionSite

/-- 按 site 构造 ordered superposition 的 raw 结论字句。 -/
def buildSuperpositionClause?
    (equalityClause targetClause : Clause) (site : SuperpositionSite) : Option Clause :=
  if hTarget : site.targetLiteral < targetClause.size then
    let subst := site.substitution
    let sourceRest := CoreSyntax.Search.Substitution.applyClause subst
      (eraseLiteral equalityClause site.equalityLiteral)
    let targetLiteral :=
      CoreSyntax.Search.Substitution.applyLiteral subst targetClause[site.targetLiteral]
    let targetClause := CoreSyntax.Search.Substitution.applyClause subst targetClause
    let replacement := CoreSyntax.Search.Substitution.applyTerm subst site.orientedRhs
    match replaceLiteralAt? targetLiteral site.targetPosition.side site.targetPosition.path
        replacement with
    | some newLiteral =>
        match replaceClauseLiteralAt? targetClause site.targetLiteral newLiteral with
        | some targetClause => some (sourceRest ++ targetClause)
        | none => none
    | none => none
  else
    none

/-- 检查 superposition 目标文字是否符合规则极性。 -/
def superpositionTargetPolarityOk (literal : CoreSyntax.Search.Literal)
    (polarity : SuperpositionPolarity) : Bool :=
  match polarity with
  | SuperpositionPolarity.positive => literal.positive
  | SuperpositionPolarity.negative =>
      !literal.positive && literal.predicate == CoreSyntax.Search.PredicateKind.equal

/-- 从目标文字形状判断应使用哪一种 superposition 目标极性。 -/
def superpositionPolarityOfTarget? (literal : CoreSyntax.Search.Literal) :
    Option SuperpositionPolarity :=
  if literal.positive then
    some SuperpositionPolarity.positive
  else if literal.predicate == CoreSyntax.Search.PredicateKind.equal then
    some SuperpositionPolarity.negative
  else
    none

/-- 当前配置是否允许某种 superposition 目标极性。 -/
def superpositionPolarityEnabled (config : Config) : SuperpositionPolarity → Bool
  | SuperpositionPolarity.positive => config.enableSuperposition
  | SuperpositionPolarity.negative =>
      config.enableSuperposition && config.enableNegativeSuperposition

/-- 由目标极性选择对应的证书规则。 -/
def superpositionRuleOfPolarity (polarity : SuperpositionPolarity)
    (equality target : ClauseId) : Rule :=
  match polarity with
  | SuperpositionPolarity.positive => Rule.positiveSuperposition equality target
  | SuperpositionPolarity.negative => Rule.negativeSuperposition equality target

/-- 是否属于函数值/高阶位置上的 paramodulation。 -/
def isExtensionalParamodulationSite
    (equality : OrientedEquality) (position : PositionedTerm) : Bool :=
  (arrowSort? equality.lhs).isSome ||
    (arrowSort? position.term).isSome ||
      match position.term with
      | CoreSyntax.Search.Term.apply .. => true
      | CoreSyntax.Search.Term.lam .. => true
      | _ => false

/-- 由目标极性与位置形状选择证书规则。 -/
def superpositionRuleForSite (polarity : SuperpositionPolarity)
    (equality target : ClauseId) (oriented : OrientedEquality) (position : PositionedTerm) : Rule :=
  if polarity == SuperpositionPolarity.positive &&
      isExtensionalParamodulationSite oriented position then
    Rule.extensionalParamodulation equality target
  else
    superpositionRuleOfPolarity polarity equality target

/-- 检查 ordered superposition 的全部 side conditions，并同时确认结论字句。 -/
def checkSuperpositionSideConditions
    (config : Config) (equalityClause targetClause conclusion : Clause)
    (site : SuperpositionSite) : Bool :=
  if hEq : site.equalityLiteral < equalityClause.size then
    if hTarget : site.targetLiteral < targetClause.size then
      match selectedOrientedEqualityAt? equalityClause site.equalityLiteral with
      | some equality =>
            decide (site.orientedLhs = equality.lhs) &&
            decide (site.orientedRhs = equality.rhs) &&
            eligibleSuperpositionTarget config targetClause site.targetLiteral &&
            superpositionTargetPolarityOk targetClause[site.targetLiteral] site.polarity &&
            (match literalTermAt? targetClause[site.targetLiteral] site.targetPosition.side
                site.targetPosition.path with
            | some term => CoreSyntax.Search.termEqBetaEta site.targetPosition.term term
            | none => false) &&
            !CoreSyntax.Search.Term.isVar site.targetPosition.term &&
            TermOrdering.gt site.orientedLhs site.orientedRhs &&
            match CoreSyntax.Search.unify? site.orientedLhs site.targetPosition.term with
            | some subst =>
                decide (subst = site.substitution) &&
                  sameTermAfterSubstitution subst site.orientedLhs site.targetPosition.term &&
                  TermOrdering.gt
                    (CoreSyntax.Search.Substitution.applyTerm subst site.orientedLhs)
                    (CoreSyntax.Search.Substitution.applyTerm subst site.orientedRhs) &&
                  (literalSubterms targetClause[site.targetLiteral]).any
                    (fun position => decide (position = site.targetPosition)) &&
                  match buildSuperpositionClause? equalityClause targetClause site with
                  | some raw => sameRetainedClause raw conclusion
                  | none => false
            | none => false
      | none => false
    else
      false
  else
    false

/-- 对单个 selected 目标文字尝试一次 ordered superposition。 -/
def superpositionAt?
    (config : Config)
    (equalityClause targetClause : Clause) (equality : OrientedEquality)
    (targetIndex : Nat) (position : PositionedTerm)
    (polarity : SuperpositionPolarity := SuperpositionPolarity.positive) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  if _hTarget : targetIndex < targetClause.size then
    if !eligibleSuperpositionTarget config targetClause targetIndex ||
        !superpositionTargetPolarityOk targetClause[targetIndex] polarity ||
        !(match literalTermAt? targetClause[targetIndex] position.side position.path with
        | some term => CoreSyntax.Search.termEqBetaEta position.term term
        | none => false) ||
        CoreSyntax.Search.Term.isVar position.term then
      none
    else
      match CoreSyntax.Search.unify? equality.lhs position.term with
      | some subst =>
          if sameTermAfterSubstitution subst equality.lhs position.term then
            let site := SuperpositionSite.ofPosition equality targetIndex position subst polarity
            match buildSuperpositionClause? equalityClause targetClause site with
            | some raw =>
                if checkSuperpositionSideConditions config equalityClause targetClause
                    (normalizeClause raw) site then
                  some (raw, subst)
                else
                  none
            | none => none
          else
            none
      | none => none
  else
    none

/-- 对单个 selected 正目标文字尝试一次 ordered positive superposition。 -/
def positiveSuperpositionAt?
    (config : Config)
    (equalityClause targetClause : Clause) (equality : OrientedEquality)
    (targetIndex : Nat) (position : PositionedTerm) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  superpositionAt? config equalityClause targetClause equality targetIndex position
    SuperpositionPolarity.positive

/-- 对单个 selected 负等词目标位置尝试一次 ordered negative superposition。 -/
def negativeSuperpositionAt?
    (config : Config)
    (equalityClause targetClause : Clause) (equality : OrientedEquality)
    (targetIndex : Nat) (position : PositionedTerm) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  superpositionAt? config equalityClause targetClause equality targetIndex position
    SuperpositionPolarity.negative

/-- 用已索引的 eligible 等词 occurrence 和目标 occurrence 尝试一次 ordered superposition。 -/
def superpositionAtOccurrences?
    (config : Config) (equalityClause targetClause : Clause)
    (equalityOccurrence targetOccurrence : TermOccurrence)
    (polarity : SuperpositionPolarity := SuperpositionPolarity.positive) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  match selectedOrientedEqualityAt? equalityClause equalityOccurrence.literalIndex with
  | some equality =>
      if CoreSyntax.Search.termEq equality.lhs equalityOccurrence.term then
        superpositionAt? config equalityClause targetClause equality
          targetOccurrence.literalIndex {
            side := targetOccurrence.side
            path := targetOccurrence.path
            term := targetOccurrence.term
          } polarity
      else
        none
  | none => none

/-- 用已索引的 eligible 等词 occurrence 和负等词目标 occurrence 尝试一次 negative superposition。 -/
def negativeSuperpositionAtOccurrences?
    (config : Config) (equalityClause targetClause : Clause)
    (equalityOccurrence targetOccurrence : TermOccurrence) :
    Option (Clause × CoreSyntax.Search.Substitution) :=
  match selectedOrientedEqualityAt? equalityClause equalityOccurrence.literalIndex with
  | some equality =>
      if CoreSyntax.Search.termEq equality.lhs equalityOccurrence.term then
        negativeSuperpositionAt? config equalityClause targetClause equality
          targetOccurrence.literalIndex {
            side := targetOccurrence.side
            path := targetOccurrence.path
            term := targetOccurrence.term
          }
      else
        none
  | none => none

/-- 饱和循环中的一个候选新字句。 -/
structure Candidate where
  rule : Rule
  substitution : CoreSyntax.Search.Substitution := []
  guards : GuardSet := #[]
  clause : Clause
  resource? : Option ResourceTrace.LocalStepWitness := none
  deriving Repr, Lean.ToExpr

namespace Candidate

/-- 把搜索候选投影成最终 local rule checker 消费的 proof step。 -/
def proofStep (candidate : Candidate) : ProofStep := {
  rule := candidate.rule
  substitution := candidate.substitution
  clause := candidate.clause
  resource? := candidate.resource?
}

end Candidate

/-- 单个或多个 generator 运行后的观察统计；不进入 proof checker。 -/
structure GenerationSummary where
  generatedCandidates : Nat := 0
  indexedBatches : Nat := 0
  indexedBatchHits : Nat := 0
  indexedCandidates : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace GenerationSummary

/-- 记录一个 generator 批次实际交给 consumer 的候选。 -/
def record (summary : GenerationSummary) (indexed : Bool) (added : Nat) :
    GenerationSummary := {
  generatedCandidates := summary.generatedCandidates + added
  indexedBatches := summary.indexedBatches + if indexed then 1 else 0
  indexedBatchHits :=
    summary.indexedBatchHits + if indexed && added != 0 then 1 else 0
  indexedCandidates := summary.indexedCandidates + if indexed then added else 0
}

end GenerationSummary

/--
Vampire 风格的惰性候选消费游标。

`value` 由调用方决定，可以是数组，也可以是正在原地风格推进的 saturation `State`。
generator 只持有固定输入快照，通过 consumer 逐候选交付，不观察 consumer 新插入的节点。
-/
structure CandidateFlow (α : Type) where
  value : α
  budget : WorkBudget
  summary : GenerationSummary := {}
  exhausted : Bool := false
  deriving Repr

/-- 单个候选的消费函数。 -/
abbrev CandidateConsumer (α : Type) :=
  CandidateFlow α → Candidate → CandidateFlow α

namespace CandidateFlow

/-- 扣减一个细粒度工作单位；耗尽后游标保持幂等停止。 -/
@[inline]
def charge (flow : CandidateFlow α) (kind : WorkKind) : CandidateFlow α :=
  if flow.exhausted then
    flow
  else
    match flow.budget.charge? kind with
    | some budget => { flow with budget := budget }
    | none => { flow with exhausted := true }

/-- 把游标转换成索引 fold 的继续/停止协议。 -/
@[inline]
def step (flow : CandidateFlow α) : Data.FoldStep (CandidateFlow α) :=
  if flow.exhausted then .done flow else .next flow

/-- 产生一个候选并立即交给 consumer。 -/
@[inline]
def emit (flow : CandidateFlow α) (candidate : Candidate)
    (consume : CandidateConsumer α) : CandidateFlow α :=
  let flow := flow.charge WorkKind.generatedCandidate
  if flow.exhausted then flow else consume flow candidate

end CandidateFlow

/-- 构造资源证书里的轻量父节点引用。 -/
def resourceClauseRef (id : ClauseId) : ResourceTrace.ClauseRef :=
  { id := id }

/-- 一元规则 candidate 的资源 witness。 -/
def unaryResourceWitness (kind : ResourceTrace.UnaryKind) (parent : ClauseId)
    (literalIndex? otherLiteralIndex? : Option Nat)
    (substitution : CoreSyntax.Search.Substitution) (clause : Clause) :
    ResourceTrace.LocalStepWitness :=
  ResourceTrace.LocalStepWitness.unary {
    kind := kind
    parent := resourceClauseRef parent
    literalIndex? := literalIndex?
    otherLiteralIndex? := otherLiteralIndex?
    substitution := substitution
    result := clause
  }

/-- 二元 resolution candidate 的资源 witness。 -/
def resolutionResourceWitness (left right : ClauseId)
    (leftLiteralIndex? rightLiteralIndex? : Option Nat)
    (substitution : CoreSyntax.Search.Substitution) (clause : Clause)
    (standardizeApart? : Option ResourceTrace.StandardizeApartMetadata := none) :
    ResourceTrace.LocalStepWitness :=
  ResourceTrace.LocalStepWitness.resolution {
    left := resourceClauseRef left
    right := resourceClauseRef right
    leftLiteralIndex? := leftLiteralIndex?
    rightLiteralIndex? := rightLiteralIndex?
    standardizeApart? := standardizeApart?
    substitution := substitution
    result := clause
  }

/-- resolution 前 standardize-apart 的显式资源元数据。 -/
def resolutionStandardizeApartMetadata (left right : Clause) :
    ResourceTrace.StandardizeApartMetadata :=
  let offset := CoreSyntax.Search.Clause.maxVarSucc left
  {
    left := {
      original := left
      offset := 0
      renamed := CoreSyntax.Search.Clause.renameVars 0 left
    }
    right := {
      original := right
      offset := offset
      renamed := CoreSyntax.Search.Clause.renameVars offset right
    }
  }

/--
demodulation 的 substitution 来自等词左侧匹配，只能实例化等词父句。

目标父句保持原变量编号；等词父句整体平移到目标变量区间之外，使最终 DAG checker
可以用标准化重写证据准确回放 matcher 语义。
-/
def demodulationStandardizeApartMetadata (equality target : Clause) :
    ResourceTrace.StandardizeApartMetadata :=
  let offset := CoreSyntax.Search.Clause.maxVarSucc target
  {
    left := {
      original := equality
      offset := offset
      renamed := CoreSyntax.Search.Clause.renameVars offset equality
    }
    right := {
      original := target
      offset := 0
      renamed := CoreSyntax.Search.Clause.renameVars 0 target
    }
  }

/-- 超消元目标极性转换成资源证书极性。 -/
def resourceTargetPolarity : SuperpositionPolarity → ResourceTrace.TargetPolarity
  | SuperpositionPolarity.positive => ResourceTrace.TargetPolarity.positive
  | SuperpositionPolarity.negative => ResourceTrace.TargetPolarity.negative

/-- 搜索器内部文字侧映射到稳定资源证书格式。 -/
def resourceLiteralSide : LiteralSide → ResourceTrace.LiteralSide
  | LiteralSide.left => ResourceTrace.LiteralSide.left
  | LiteralSide.right => ResourceTrace.LiteralSide.right

/-- 搜索器内部位置映射到稳定资源证书格式。 -/
def resourcePositionedTerm (position : PositionedTerm) :
    ResourceTrace.PositionedTerm :=
  {
    side := resourceLiteralSide position.side
    path := position.path
    term := position.term
  }

/-- 稳定资源证书位置恢复成搜索器内部位置。 -/
def positionedTermOfResource (position : ResourceTrace.PositionedTerm) :
    PositionedTerm :=
  {
    side :=
      match position.side with
      | ResourceTrace.LiteralSide.left => LiteralSide.left
      | ResourceTrace.LiteralSide.right => LiteralSide.right
    path := position.path
    term := position.term
  }

/-- 从搜索规则标签提取一元规则资源族。 -/
def unaryResourceKind? : Rule → Option ResourceTrace.UnaryKind
  | Rule.ordinaryFactoring .. => some ResourceTrace.UnaryKind.ordinaryFactoring
  | Rule.equalityFactoring .. => some ResourceTrace.UnaryKind.equalityFactoring
  | Rule.equalityResolution .. => some ResourceTrace.UnaryKind.equalityResolution
  | Rule.booleanExtensionality .. => some ResourceTrace.UnaryKind.booleanExtensionality
  | Rule.argumentCongruence .. => some ResourceTrace.UnaryKind.argumentCongruence
  | _ => none

/-- 从搜索规则标签提取重写/叠加资源族。 -/
def rewriteResourceKindOfRule? : Rule → Option ResourceTrace.RewriteKind
  | Rule.demodulation .. => some ResourceTrace.RewriteKind.demodulation
  | Rule.positiveSuperposition .. => some ResourceTrace.RewriteKind.positiveSuperposition
  | Rule.negativeSuperposition .. => some ResourceTrace.RewriteKind.negativeSuperposition
  | Rule.extensionalParamodulation .. => some ResourceTrace.RewriteKind.extensionalParamodulation
  | _ => none

/-- 重写/叠加 candidate 的资源 witness。 -/
def rewriteResourceWitness (kind : ResourceTrace.RewriteKind)
    (equality target : ClauseId) (targetClause : Clause)
    (equalityLiteral targetLiteral : Nat)
    (position : PositionedTerm) (orientedLhs orientedRhs : CoreSyntax.Search.Term)
    (substitution : CoreSyntax.Search.Substitution) (clause : Clause)
    (contextual : Bool := false)
    (targetPolarity? : Option ResourceTrace.TargetPolarity := none)
    (standardizeApart? : Option ResourceTrace.StandardizeApartMetadata := none) :
    ResourceTrace.LocalStepWitness :=
  ResourceTrace.LocalStepWitness.rewrite {
    kind := kind
    equality := resourceClauseRef equality
    target := { id := target, clause? := some targetClause }
    equalityLiteral := equalityLiteral
    targetLiteral := targetLiteral
    targetPosition := resourcePositionedTerm position
    orientedLhs := orientedLhs
    orientedRhs := orientedRhs
    substitution := substitution
    result := clause
    contextual := contextual
    targetPolarity? := targetPolarity?
    standardizeApart? := standardizeApart?
  }

/-- 安全读取字句。 -/
def clauseAt? (clauses : Array Clause) (id : ClauseId) : Option Clause :=
  if h : id < clauses.size then
    some clauses[id]
  else
    none

/-- 围绕 given clause，逐个交付一元规则候选。 -/
def foldIndexedUnaryRuleCandidates
    {α : Type}
    (rule : ClauseId → Rule)
    (ruleAt? : Clause → Nat → Option (Clause × CoreSyntax.Search.Substitution))
    (clauses : Array Clause) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow index =>
        let flow := flow.charge WorkKind.inferenceAttempt
        if flow.exhausted then
          .done flow
        else
          match ruleAt? given index with
          | some (clause, subst) =>
              let ruleValue := rule givenId
              let resource? :=
                (unaryResourceKind? ruleValue).map fun kind =>
                  unaryResourceWitness kind givenId (some index) none subst clause
              (flow.emit {
                rule := ruleValue
                substitution := subst
                clause := clause
                resource? := resource?
              } consume).step
          | none => .next flow
  | none => initial

/-- active 负等词侧项是否已经对应一个可合一的负等词文字。 -/
def negativeEqualityResolutionOccurrence? (config : Config) (clauses : Array Clause)
    (occurrence : TermOccurrence) : Option (Candidate) := do
  let clause ← clauseAt? clauses occurrence.clauseId
  let (clause, subst) ← equalityResolutionAt? config clause occurrence.literalIndex
  some {
    rule := Rule.equalityResolution occurrence.clauseId
    substitution := subst
    clause := clause
    resource? :=
      some <| unaryResourceWitness ResourceTrace.UnaryKind.equalityResolution
        occurrence.clauseId (some occurrence.literalIndex) none subst clause
  }

/-- 围绕 given clause，逐个交付 equality resolution 候选。 -/
def foldIndexedEqualityResolutionCandidates
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if !config.enableEqualityResolution then
    initial
  else
    match clauseAt? clauses givenId with
    | some given =>
        Data.foldNatRangeUntil 0 given.size initial fun flow literalIndex =>
          let flow :=
            (flow.charge WorkKind.inferenceAttempt).charge WorkKind.unification
          if flow.exhausted then
            .done flow
          else
            let flow :=
              match equalityResolutionAt? config given literalIndex with
              | some (clause, subst) =>
                  flow.emit {
                    rule := Rule.equalityResolution givenId
                    substitution := subst
                    clause := clause
                    resource? :=
                      some <| unaryResourceWitness ResourceTrace.UnaryKind.equalityResolution
                        givenId (some literalIndex) none subst clause
                  } consume
              | none => flow
            if flow.exhausted then
              .done flow
            else
              match given[literalIndex]? with
              | some literal =>
                  if eligibleNegativeEquality config given literalIndex then
                    let flow :=
                      index.foldUnifiableNegativeEqualityTermsUntil
                        workspace literal.left flow fun flow occurrence =>
                          let flow :=
                            (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                          if flow.exhausted then
                            .done flow
                          else
                            match negativeEqualityResolutionOccurrence? config clauses occurrence with
                            | some candidate => (flow.emit candidate consume).step
                            | none => .next flow
                    if flow.exhausted then
                      .done flow
                    else
                      let flow :=
                        index.foldUnifiableNegativeEqualityTermsUntil
                          workspace literal.right flow fun flow occurrence =>
                            let flow :=
                              (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                            if flow.exhausted then
                              .done flow
                            else
                              match negativeEqualityResolutionOccurrence? config clauses occurrence with
                              | some candidate => (flow.emit candidate consume).step
                              | none => .next flow
                      flow.step
                  else
                    .next flow
              | none => .next flow
    | none => initial

/-- 围绕 given clause 逐个交付普通一阶 factoring 候选。 -/
def foldIndexedOrdinaryFactoringCandidates
    {α : Type}
    (config : Config) (clauses : Array Clause) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow i =>
        let flow :=
          Data.foldNatRangeUntil 0 given.size flow fun flow j =>
            let flow := flow.charge WorkKind.inferenceAttempt
            if flow.exhausted then
              .done flow
            else if i != j && selectedForResolution config given i then
              let flow := flow.charge WorkKind.unification
              if flow.exhausted then
                .done flow
              else
              match ordinaryFactoringAt? given i j with
              | some (clause, subst) =>
                  (flow.emit {
                    rule := Rule.ordinaryFactoring givenId
                    substitution := subst
                    clause := clause
                    resource? :=
                      some <| unaryResourceWitness ResourceTrace.UnaryKind.ordinaryFactoring
                        givenId (some i) (some j) subst clause
                  } consume).step
              | none => .next flow
            else
              .next flow
        flow.step
  | none => initial

/-- 围绕 given clause 逐个交付 equality factoring 候选。 -/
def foldIndexedEqualityFactoringCandidates
    {α : Type}
    (config : Config) (clauses : Array Clause) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if !config.enableEqualityFactoring then
    initial
  else
    match clauseAt? clauses givenId with
    | some given =>
        Data.foldNatRangeUntil 0 given.size initial fun flow mainIndex =>
          let flow :=
            Data.foldNatRangeUntil 0 given.size flow fun flow otherIndex =>
              let flow := flow.charge WorkKind.inferenceAttempt
              if flow.exhausted then
                .done flow
              else if mainIndex != otherIndex then
                let flow := flow.charge WorkKind.unification
                if flow.exhausted then
                  .done flow
                else
                match equalityFactoringAt? config given mainIndex otherIndex with
                | some (clause, subst) =>
                    (flow.emit {
                      rule := Rule.equalityFactoring givenId
                      substitution := subst
                      clause := clause
                      resource? :=
                        some <| unaryResourceWitness ResourceTrace.UnaryKind.equalityFactoring
                          givenId (some mainIndex) (some otherIndex) subst clause
                    } consume).step
                | none => .next flow
              else
                .next flow
          flow.step
    | none => initial

/-- 围绕 given clause，通过 active 文字索引逐个交付 resolution 候选。 -/
def foldIndexedResolutionCandidates
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow literalIndex =>
        let flow := flow.charge WorkKind.inferenceAttempt
        if flow.exhausted then
          .done flow
        else
          match given[literalIndex]? with
          | some literal =>
              if eligibleResolutionLiteral config given literalIndex then
                let flow :=
                  index.foldComplementaryLiteralsUntil
                    workspace literal flow fun flow occurrence =>
                    let flow :=
                      (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                    if flow.exhausted then
                      .done flow
                    else
                      match clauseAt? clauses occurrence.clauseId with
                      | some active =>
                          match resolventAt? given active literalIndex occurrence.literalIndex with
                          | some (clause, subst) =>
                              (flow.emit {
                                rule := Rule.binaryResolution givenId occurrence.clauseId
                                substitution := subst
                                clause := clause
                                resource? :=
                                  some <| resolutionResourceWitness givenId occurrence.clauseId
                                    (some literalIndex) (some occurrence.literalIndex) subst clause
                                    (some (resolutionStandardizeApartMetadata given active))
                              } consume).step
                          | none => .next flow
                      | none => .next flow
                flow.step
              else
                .next flow
          | none => .next flow
  | none => initial

/-- 逐个交付 given demodulator 重写 active clauses 产生的候选。 -/
def foldIndexedDemodulationFromGivenCandidates
    {α : Type}
    (_config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      match orientedUnitEquality? given with
      | some queryEquality =>
          index.foldMatchedSuperpositionTargetsByUntil
            workspace queryEquality.lhs initial fun flow occurrence =>
            let flow :=
              (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
            if flow.exhausted then
              .done flow
            else
              match clauseAt? clauses occurrence.clauseId with
              | some target =>
                  let metadata := demodulationStandardizeApartMetadata given target
                  match orientedUnitEquality? metadata.left.renamed with
                  | some equality =>
                      match demodulateLiteral? target equality occurrence.literalIndex {
                          side := occurrence.side
                          path := occurrence.path
                          term := occurrence.term
                        } with
                      | some (clause, subst) =>
                          (flow.emit {
                            rule := Rule.demodulation givenId occurrence.clauseId
                            substitution := subst
                            clause := clause
                            resource? :=
                              some <| rewriteResourceWitness
                                ResourceTrace.RewriteKind.demodulation
                                givenId occurrence.clauseId target
                                equality.literalIndex occurrence.literalIndex
                                { side := occurrence.side
                                  path := occurrence.path
                                  term := occurrence.term }
                                equality.lhs equality.rhs subst clause
                                (standardizeApart? := some metadata)
                          } consume).step
                      | none => .next flow
                  | none => .next flow
              | none => .next flow
      | none => initial
  | none => initial

/-- 逐个交付 given 条件等词重写 active clauses 产生的候选。 -/
def foldIndexedContextualDemodulationFromGivenCandidates
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if !config.enableContextualDemodulation then
    initial
  else
    match clauseAt? clauses givenId with
    | some given =>
        Data.foldNatRangeUntil 0 given.size initial fun flow equalityIndex =>
          let flow := flow.charge WorkKind.inferenceAttempt
          if flow.exhausted then
            .done flow
          else
            match selectedOrientedEqualityAt? given equalityIndex with
            | some queryEquality =>
                let flow :=
                  index.foldMatchedSuperpositionTargetsByUntil
                    workspace queryEquality.lhs flow fun flow occurrence =>
                    let flow :=
                      (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                    if flow.exhausted then
                      .done flow
                    else
                  match clauseAt? clauses occurrence.clauseId with
                  | some target =>
                      let metadata := demodulationStandardizeApartMetadata given target
                      match selectedOrientedEqualityAt? metadata.left.renamed equalityIndex with
                      | some equality =>
                          match contextualDemodulateLiteral?
                              metadata.left.renamed target equality occurrence.literalIndex {
                                side := occurrence.side
                                path := occurrence.path
                                term := occurrence.term
                            } with
                          | some (clause, subst) =>
                              (flow.emit {
                                rule := Rule.demodulation givenId occurrence.clauseId
                                substitution := subst
                                clause := clause
                                resource? :=
                                  some <| rewriteResourceWitness
                                    ResourceTrace.RewriteKind.contextualDemodulation
                                    givenId occurrence.clauseId target
                                    equality.literalIndex occurrence.literalIndex
                                    { side := occurrence.side
                                      path := occurrence.path
                                      term := occurrence.term }
                                    equality.lhs equality.rhs subst clause true
                                    (standardizeApart? := some metadata)
                              } consume).step
                          | none => .next flow
                      | none => .next flow
                  | none => .next flow
                flow.step
            | none => .next flow
    | none => initial

/--
给定单位等词对既有 Active 字句执行 backward demodulation。

forward fixpoint 只负责把当前 given 归约到规范形；当规范形本身成为新的 demodulator 时，
仍需保留这条生成路径，避免既有 Active 字句永远看不到新重写规则。
-/
def foldIndexedBackwardDemodulationCandidates
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if !config.enableDemodulation then
    initial
  else
    let out :=
      foldIndexedDemodulationFromGivenCandidates
        config clauses index workspace givenId initial consume
    if out.exhausted then
      out
    else
      foldIndexedContextualDemodulationFromGivenCandidates
        config clauses index workspace givenId out consume

/-- 按目标极性流式枚举可叠加位置，避免先物化完整位置数组。 -/
private def foldSuperpositionTargetPositionsUntil {α : Type}
    (polarity : SuperpositionPolarity) (literal : CoreSyntax.Search.Literal)
    (initial : α) (visit : α → PositionedTerm → Data.FoldStep α) :
    Data.FoldStep α :=
  match polarity with
  | SuperpositionPolarity.negative =>
      Data.foldArrayUntilStep
        #[
          { side := LiteralSide.left, path := [], term := literal.left },
          { side := LiteralSide.right, path := [], term := literal.right }
        ]
        initial visit
  | SuperpositionPolarity.positive =>
      foldLiteralSubtermsUntil literal initial visit

/-- 逐个交付 active 正等词叠加到 given clause 的候选。 -/
def foldIndexedSuperpositionIntoGivenCandidatesWithPolarity
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (polarity : SuperpositionPolarity)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow literalIndex =>
        let flow := flow.charge WorkKind.inferenceAttempt
        if flow.exhausted then
          .done flow
        else
          match given[literalIndex]? with
          | some literal =>
              if eligibleSuperpositionTarget config given literalIndex then
                let flowStep :=
                  foldSuperpositionTargetPositionsUntil polarity literal flow
                    fun flow position =>
                    let flow :=
                      (flow.charge WorkKind.termPosition).charge WorkKind.inferenceAttempt
                    if flow.exhausted then
                      .done flow
                    else if !CoreSyntax.Search.Term.isVar position.term &&
                        superpositionPolarityOfTarget? literal == some polarity &&
                        superpositionPolarityEnabled config polarity then
                      let flow :=
                        index.foldUnifiablePositiveEqualitiesUntil
                          workspace position.term flow fun flow occurrence =>
                          let flow :=
                            (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                          if flow.exhausted then
                            .done flow
                          else
                            match clauseAt? clauses occurrence.clauseId with
                            | some equalityClause =>
                                let targetOccurrence : TermOccurrence := {
                                  clauseId := givenId
                                  literalIndex := literalIndex
                                  side := position.side
                                  path := position.path
                                  term := position.term
                                }
                                match
                                    superpositionAtOccurrences? config equalityClause given occurrence
                                      targetOccurrence polarity with
                                | some (clause, subst) =>
                                    match
                                        selectedOrientedEqualityAt?
                                          equalityClause occurrence.literalIndex with
                                    | some oriented =>
                                        let ruleValue :=
                                          superpositionRuleForSite
                                            polarity occurrence.clauseId givenId oriented position
                                        let resourceKind :=
                                          (rewriteResourceKindOfRule? ruleValue).getD
                                            ResourceTrace.RewriteKind.positiveSuperposition
                                        (flow.emit {
                                          rule := ruleValue
                                          substitution := subst
                                          clause := clause
                                          resource? :=
                                            some <| rewriteResourceWitness resourceKind
                                              occurrence.clauseId givenId given
                                              oriented.literalIndex literalIndex
                                              position oriented.lhs oriented.rhs subst clause false
                                              (some (resourceTargetPolarity polarity))
                                        } consume).step
                                    | none => .next flow
                                | none => .next flow
                            | none => .next flow
                      flow.step
                    else
                      .next flow
                flowStep
              else
                .next flow
          | none => .next flow
  | none => initial

/-- 逐个交付 given 正等词叠加到 active clauses 的候选。 -/
def foldIndexedSuperpositionFromGivenCandidatesWithPolarity
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (polarity : SuperpositionPolarity)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  match clauseAt? clauses givenId with
  | some given =>
      Data.foldNatRangeUntil 0 given.size initial fun flow equalityIndex =>
        let flow := flow.charge WorkKind.inferenceAttempt
        if flow.exhausted then
          .done flow
        else
          match selectedOrientedEqualityAt? given equalityIndex with
          | some equality =>
              let equalityOccurrence : TermOccurrence := {
                clauseId := givenId
                literalIndex := equalityIndex
                side := LiteralSide.left
                path := []
                term := equality.lhs
              }
              if polarity == SuperpositionPolarity.positive &&
                  superpositionPolarityEnabled config SuperpositionPolarity.positive then
                let flow :=
                  index.foldUnifiableSuperpositionTargetsUntil
                    workspace equality.lhs flow fun flow occurrence =>
                    let flow :=
                      (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                    if flow.exhausted then
                      .done flow
                    else
                  match clauseAt? clauses occurrence.clauseId with
                  | some target =>
                      if hTarget : occurrence.literalIndex < target.size then
                        match superpositionPolarityOfTarget? target[occurrence.literalIndex] with
                        | some SuperpositionPolarity.positive =>
                            match superpositionAtOccurrences? config given target
                                equalityOccurrence occurrence SuperpositionPolarity.positive with
                            | some (clause, subst) =>
                                let position : PositionedTerm := {
                                  side := occurrence.side
                                  path := occurrence.path
                                  term := occurrence.term
                                }
                                let ruleValue :=
                                  superpositionRuleForSite SuperpositionPolarity.positive
                                    givenId occurrence.clauseId equality position
                                let resourceKind :=
                                  (rewriteResourceKindOfRule? ruleValue).getD
                                    ResourceTrace.RewriteKind.positiveSuperposition
                                (flow.emit {
                                  rule := ruleValue
                                  substitution := subst
                                  clause := clause
                                  resource? :=
                                    some <| rewriteResourceWitness resourceKind
                                      givenId occurrence.clauseId target equality.literalIndex
                                      occurrence.literalIndex position equality.lhs equality.rhs subst clause
                                      false (some ResourceTrace.TargetPolarity.positive)
                                } consume).step
                            | none => .next flow
                        | _ => .next flow
                      else
                        .next flow
                  | none => .next flow
                if flow.exhausted then
                  .done flow
                else if polarity == SuperpositionPolarity.negative &&
                  superpositionPolarityEnabled config SuperpositionPolarity.negative then
                  let flow :=
                    index.foldUnifiableNegativeEqualityTermsUntil
                      workspace equality.lhs flow fun flow occurrence =>
                      let flow :=
                        (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                      if flow.exhausted then
                        .done flow
                      else
                  match clauseAt? clauses occurrence.clauseId with
                  | some target =>
                      match negativeSuperpositionAtOccurrences? config given target
                          equalityOccurrence occurrence with
                      | some (clause, subst) =>
                          let position : PositionedTerm := {
                            side := occurrence.side
                            path := occurrence.path
                            term := occurrence.term
                          }
                          (flow.emit {
                            rule := Rule.negativeSuperposition givenId occurrence.clauseId
                            substitution := subst
                            clause := clause
                            resource? :=
                              some <| rewriteResourceWitness
                                ResourceTrace.RewriteKind.negativeSuperposition
                                givenId occurrence.clauseId target equality.literalIndex
                                occurrence.literalIndex position equality.lhs equality.rhs subst clause
                                false (some ResourceTrace.TargetPolarity.negative)
                          } consume).step
                      | none => .next flow
                  | none => .next flow
                  flow.step
                else
                  .next flow
              else if polarity == SuperpositionPolarity.negative &&
                  superpositionPolarityEnabled config SuperpositionPolarity.negative then
                let flow :=
                  index.foldUnifiableNegativeEqualityTermsUntil
                    workspace equality.lhs flow fun flow occurrence =>
                    let flow :=
                      (flow.charge WorkKind.indexOccurrence).charge WorkKind.unification
                    if flow.exhausted then
                      .done flow
                    else
                      match clauseAt? clauses occurrence.clauseId with
                      | some target =>
                          match negativeSuperpositionAtOccurrences? config given target
                              equalityOccurrence occurrence with
                          | some (clause, subst) =>
                              let position : PositionedTerm := {
                                side := occurrence.side
                                path := occurrence.path
                                term := occurrence.term
                              }
                              (flow.emit {
                                rule := Rule.negativeSuperposition givenId occurrence.clauseId
                                substitution := subst
                                clause := clause
                                resource? :=
                                  some <| rewriteResourceWitness
                                    ResourceTrace.RewriteKind.negativeSuperposition
                                    givenId occurrence.clauseId target equality.literalIndex
                                    occurrence.literalIndex position equality.lhs equality.rhs subst clause
                                    false (some ResourceTrace.TargetPolarity.negative)
                              } consume).step
                          | none => .next flow
                      | none => .next flow
                flow.step
              else
                .next flow
          | none => .next flow
  | none => initial

/-- 逐个交付 active/given 两侧指定极性的 ordered superposition 候选。 -/
def foldIndexedSuperpositionCandidatesWithPolarity
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (polarity : SuperpositionPolarity)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  if superpositionPolarityEnabled config polarity then
    let out :=
      foldIndexedSuperpositionIntoGivenCandidatesWithPolarity
        config clauses index workspace givenId polarity initial consume
    if out.exhausted then
      out
    else
      foldIndexedSuperpositionFromGivenCandidatesWithPolarity
        config clauses index workspace givenId polarity out consume
  else
    initial

/-- 逐个交付独立的 positive superposition 候选。 -/
def foldIndexedPositiveSuperpositionCandidates
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  foldIndexedSuperpositionCandidatesWithPolarity config clauses index workspace givenId
    SuperpositionPolarity.positive initial consume

/-- 逐个交付独立的 negative superposition 候选。 -/
def foldIndexedNegativeSuperpositionCandidates
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  foldIndexedSuperpositionCandidatesWithPolarity config clauses index workspace givenId
    SuperpositionPolarity.negative initial consume

/-- 一个 given-clause generator 的调度表项。 -/
structure GeneratorSpec where
  label : String
  /-- 该批 generator 是否依赖 Active 索引提供父候选。 -/
  indexed : Bool := false
  generate : ∀ {α : Type}, Config → Array Clause → ClauseIndex →
    Data.GivenWorkspace → ClauseId → CandidateFlow α → CandidateConsumer α →
      CandidateFlow α

/--
运行单个规则 generator。

这里不做规范化、去重或包含判断；索引只提供保守候选，后续 local rule checker 与
retention 阶段分别决定推理是否成立、结论是否入库。
-/
private def runGeneratorSpec
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (flow : CandidateFlow α) (consume : CandidateConsumer α)
    (spec : GeneratorSpec) : CandidateFlow α :=
  if flow.exhausted then
    flow
  else
    let before := flow.budget.stats.generatedCandidates
    let next := spec.generate config clauses index workspace givenId flow consume
    let added := next.budget.stats.generatedCandidates - before
    { next with summary := next.summary.record spec.indexed added }

/-- 顺序运行 given-clause 的生成式规则表。 -/
private def runGenerators
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (generators : Array GeneratorSpec) (initial : CandidateFlow α)
    (consume : CandidateConsumer α) : CandidateFlow α :=
  Data.foldArrayUntil generators initial fun flow generator =>
    (runGeneratorSpec config clauses index workspace givenId flow consume generator).step

/-- 当前 given-clause loop 的规则调度表。 -/
def givenCandidateGenerators : Array GeneratorSpec := #[
  {
    label := "boolean extensionality"
    generate := fun _config clauses _index _workspace givenId initial consume =>
      foldIndexedUnaryRuleCandidates Rule.booleanExtensionality booleanExtensionalityAt?
        clauses givenId initial consume
  },
  {
    label := "backward demodulation"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedBackwardDemodulationCandidates
        config clauses index workspace givenId initial consume
  },
  {
    label := "ordinary factoring"
    generate := fun config clauses _index _workspace givenId initial consume =>
      foldIndexedOrdinaryFactoringCandidates config clauses givenId initial consume
  },
  {
    label := "equality resolution"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedEqualityResolutionCandidates
        config clauses index workspace givenId initial consume
  },
  {
    label := "equality factoring"
    generate := fun config clauses _index _workspace givenId initial consume =>
      foldIndexedEqualityFactoringCandidates config clauses givenId initial consume
  },
  {
    label := "argument congruence"
    generate := fun _config clauses _index _workspace givenId initial consume =>
      foldIndexedUnaryRuleCandidates Rule.argumentCongruence argumentCongruenceAt?
        clauses givenId initial consume
  },
  {
    label := "binary resolution"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedResolutionCandidates config clauses index workspace givenId initial consume
  },
  {
    label := "positive superposition"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedPositiveSuperpositionCandidates
        config clauses index workspace givenId initial consume
  },
  {
    label := "negative superposition"
    indexed := true
    generate := fun config clauses index workspace givenId initial consume =>
      foldIndexedNegativeSuperpositionCandidates
        config clauses index workspace givenId initial consume
  }
]

/-- 围绕 given clause，按固定规则表逐个消费新候选。 -/
def foldGivenCandidates
    {α : Type}
    (config : Config) (clauses : Array Clause) (index : ClauseIndex)
    (workspace : Data.GivenWorkspace) (givenId : ClauseId)
    (initial : CandidateFlow α) (consume : CandidateConsumer α) :
    CandidateFlow α :=
  runGenerators config clauses index workspace givenId
    givenCandidateGenerators initial consume

/-- Passive 集合中的待处理字句。 -/
abbrev PassiveEntry := Data.GivenEntry

/-- 字句权重：文字数加左右项尺寸。 -/
def clauseWeight (clause : Clause) : Nat :=
  clause.foldl
    (fun acc literal =>
      acc + 1 + CoreSyntax.Search.Term.size literal.left +
        CoreSyntax.Search.Term.size literal.right) 0

/-- 只计算一次并与稳定 clause id 对齐缓存的搜索元数据。 -/
def metadataOfClause (clause : Clause) : Data.ClauseMetadata := {
  weight := clauseWeight clause
  subsumption := Data.ClauseSignature.key clause
}

/-- 从字句数据库中读取一组 live clauses。 -/
def liveClausesFrom (clauses : Array Clause) (ids : Array ClauseId) : Array Clause :=
  Id.run do
    let mut out := #[]
    for id in ids do
      match clauseAt? clauses id with
      | some clause => out := out.push clause
      | none => pure ()
    return out

/-- Given clause loop 的 Passive 选择模式。 -/
inductive PassiveSelectionMode where
  | age
  | weight
  deriving Repr, BEq, DecidableEq, Lean.ToExpr

namespace PassiveSelectionMode

/-- 审计日志中的选择模式名。 -/
def label : PassiveSelectionMode → String
  | age => "age"
  | weight => "weight"

end PassiveSelectionMode

/--
Passive 选择策略。

`ageWeightRatio = 5` 表示一个循环周期中第 0 轮选最老字句，接下来 5 轮选最轻字句，
也就是 Age:Weight 约为 1:5。
-/
def passiveSelectionMode (config : Config) (selectionClock : Nat) : PassiveSelectionMode :=
  if config.ageWeightRatio == 0 then
    PassiveSelectionMode.age
  else if selectionClock % (config.ageWeightRatio + 1) == 0 then
    PassiveSelectionMode.age
  else
    PassiveSelectionMode.weight

/-- 后向冗余阶段准备删除的稳定数据库节点。 -/
structure DeletionPlan where
  clauseIds : Array ClauseId := #[]
  deriving Repr, Inhabited, Lean.ToExpr

namespace DeletionPlan

/-- 向删除计划加入一个不重复节点。 -/
def insert (plan : DeletionPlan) (id : ClauseId) : DeletionPlan :=
  if plan.clauseIds.contains id then
    plan
  else
    { clauseIds := plan.clauseIds.push id }

end DeletionPlan

/-- given-clause 生命周期的累计观察统计；不参与证书检查。 -/
structure LifecycleStats where
  generatedCandidates : Nat := 0
  checkedCandidates : Nat := 0
  ruleRejectedCandidates : Nat := 0
  retainedCandidates : Nat := 0
  retentionRejectedCandidates : Nat := 0
  activatedClauses : Nat := 0
  deletedClauses : Nat := 0
  indexedBatches : Nat := 0
  indexedBatchHits : Nat := 0
  indexedCandidates : Nat := 0
  forwardSimplificationSteps : Nat := 0
  forwardSimplifiedGivens : Nat := 0
  forwardDiscardedGivens : Nat := 0
  work : WorkStats := {}
  workExhaustions : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

namespace LifecycleStats

/-- 记录流式 generation 的规则批次结果。 -/
def recordGeneration (stats : LifecycleStats) (generation : GenerationSummary) :
    LifecycleStats := {
  stats with
  generatedCandidates := stats.generatedCandidates + generation.generatedCandidates
  indexedBatches := stats.indexedBatches + generation.indexedBatches
  indexedBatchHits := stats.indexedBatchHits + generation.indexedBatchHits
  indexedCandidates := stats.indexedCandidates + generation.indexedCandidates
}

/-- 同步本轮共享工作预算的累计 profile。 -/
def recordWorkBudget (stats : LifecycleStats) (budget : WorkBudget)
    (exhausted : Bool) : LifecycleStats := {
  stats with
  work := budget.stats
  workExhaustions := stats.workExhaustions + if exhausted then 1 else 0
}

/-- 记录一个由 Active 索引命中且通过 local checker 的 forward simplification 步骤。 -/
def recordForwardSimplificationStep (stats : LifecycleStats) : LifecycleStats := {
  stats with
  generatedCandidates := stats.generatedCandidates + 1
  checkedCandidates := stats.checkedCandidates + 1
  indexedBatches := stats.indexedBatches + 1
  indexedBatchHits := stats.indexedBatchHits + 1
  indexedCandidates := stats.indexedCandidates + 1
  forwardSimplificationSteps := stats.forwardSimplificationSteps + 1
}

/-- 记录一次 given 的 forward simplification 最终状态。 -/
def recordForwardSimplificationResult
    (stats : LifecycleStats) (iterations : Nat) (discarded : Bool) : LifecycleStats := {
  stats with
  forwardSimplifiedGivens :=
    stats.forwardSimplifiedGivens + if iterations == 0 then 0 else 1
  forwardDiscardedGivens :=
    stats.forwardDiscardedGivens + if discarded then 1 else 0
}

end LifecycleStats

/-- 饱和循环状态：Active/Passive given-clause loop。 -/
structure State where
  clauses : Array Clause
  guards : Array GuardSet
  enabled : Array Bool
  clauseMetadata : Data.ClauseMetadataTable
  steps : Array ProofStep := #[]
  active : Array ClauseId := #[]
  givenWorkspace : Data.GivenWorkspace := {}
  modelRoundWorkspace : Data.ModelRoundWorkspace := {}
  index : ClauseIndex
  nextAge : Nat := 0
  selectionClock : Nat := 0
  processed : Nat := 0
  lifecycle : LifecycleStats := {}
  deriving Repr, Lean.ToExpr

namespace State

/-- 从固定的 guarded input arena 与 aligned enable mask 构造搜索状态。 -/
def ofGuardedClausesWithEnabled (config : Config) (inputs : Array GuardedClause)
    (enabled : Array Bool) (enqueueEnabled : Bool) : State :=
  Id.run do
    let mut passiveEntries := #[]
    let clauses := inputs.map (fun input => input.clause)
    let guards := inputs.map (fun input => canonicalGuards input.guards)
    let enabled := inputs.mapIdx fun id _ => enabled.getD id false
    let metadata := clauses.map metadataOfClause
    let mut index := ClauseIndex.empty config
    let mut modelRoundWorkspace : Data.ModelRoundWorkspace := {}
    unless enqueueEnabled do
      index := index.enableActiveFilter
    for id in [:guards.size] do
      modelRoundWorkspace :=
        modelRoundWorkspace.registerClause id (guards[id]!.map (·.var))
    if enqueueEnabled then
      for id in [:clauses.size] do
        if enabled[id]! then
          passiveEntries := passiveEntries.push {
            clauseId := id
            age := id
            weight := metadata[id]!.weight
          }
    let givenWorkspace :=
      if enqueueEnabled then
        ({} : Data.GivenWorkspace).beginRound passiveEntries
      else
        {}
    return {
      clauses := clauses
      guards := guards
      enabled := enabled
      clauseMetadata := Data.ClauseMetadataTable.ofLiveEntries metadata
      givenWorkspace := givenWorkspace
      modelRoundWorkspace := modelRoundWorkspace
      index := index
      nextAge := clauses.size
    }

/-- 从固定的 guarded input arena 构造搜索状态。 -/
def ofGuardedClauses (config : Config) (inputs : Array GuardedClause)
    (enqueueAll : Bool) : State :=
  ofGuardedClausesWithEnabled config inputs
    (List.replicate inputs.size true).toArray enqueueAll

/-- 从普通无 guard 输入构造 Passive 集合，Active 初始为空。 -/
def initial (config : Config) (clauses : Array Clause) : State :=
  ofGuardedClauses config
    (clauses.map fun clause => { clause := clause }) true

/-- 建立 dormant guarded input arena；具体组件由 AVATAR assignment 激活。 -/
def dormant (config : Config) (inputs : Array GuardedClause) : State :=
  ofGuardedClauses config inputs false

/-- 建立带初始关闭槽的 dormant guarded input arena。 -/
def dormantWithEnabled (config : Config) (inputs : Array GuardedClause)
    (enabled : Array Bool) : State :=
  ofGuardedClausesWithEnabled config inputs enabled false

/-- 安全读取一个数据库节点的 canonical support。 -/
def guardsAt? (state : State) (id : ClauseId) : Option GuardSet :=
  state.guards[id]?

/-- 一个稳定 clause slot 是否已经向搜索开放。 -/
def enabledAt (state : State) (id : ClauseId) : Bool :=
  state.enabled.getD id false

/-- 数据库节点是否仍属于永久 retained 集。 -/
def retained (state : State) (id : ClauseId) : Bool :=
  state.clauseMetadata.retained id

/-- 当前已经开放且永久 retained 的 clause id。 -/
def retainedIds (state : State) : Array ClauseId :=
  state.clauseMetadata.retainedIds.filter state.enabledAt

/--
按 assignment delta 更新当前 AVATAR Active/Passive 前沿。

仍受支持的 Active 与未消费 Passive 都保留；只有 changed selector 依赖的字句重新计算
support。新可见字句按稳定 age/weight 插回现有队列；selection clock 与两个队列 cursor
跨模型轮持续前进，不会重新处理上一轮 Active。
-/
def reseed (state : State)
    (assignment : Array (Option Bool)) (supportActive : GuardSet → Bool) :
    State :=
  Id.run do
    let mut index := state.index
    unless index.requiresActiveFilter do
      index := index.enableActiveFilter
    let (modelRoundWorkspace, affectedIds) :=
      state.modelRoundWorkspace.beginAssignment assignment
    let mut modelRoundWorkspace := modelRoundWorkspace
    let mut givenWorkspace := state.givenWorkspace
    let mut deactivated := #[]
    for id in affectedIds do
      let wasVisible := modelRoundWorkspace.isVisible id
      let visible :=
        state.enabledAt id && state.retained id &&
          match state.guardsAt? id with
          | some guards => supportActive guards
          | none => false
      modelRoundWorkspace := modelRoundWorkspace.setVisible id visible
      if visible then
        if !wasVisible && !givenWorkspace.isActive id &&
            !givenWorkspace.isPassive id then
          match state.clauseMetadata.weight? id with
          | some weight =>
              givenWorkspace := givenWorkspace.push {
                clauseId := id
                age := id
                weight := weight
              }
          | none => pure ()
      else
        deactivated := deactivated.push id
    givenWorkspace := givenWorkspace.deactivateMany deactivated
    let active :=
      state.active.filter fun id =>
        state.retained id &&
          modelRoundWorkspace.isVisible id &&
            givenWorkspace.isActive id
    return {
      state with
      active := active
      givenWorkspace := givenWorkspace
      modelRoundWorkspace := modelRoundWorkspace
      index := index
    }

/-- 从规则父节点计算 candidate support。 -/
def ruleGuards? (state : State) (rule : Rule) : Option GuardSet := do
  let mut guards : GuardSet := #[]
  for parent in rule.parents do
    if !state.enabledAt parent then
      none
    let parentGuards ← state.guardsAt? parent
    guards := mergeGuards guards parentGuards
  some guards

/--
把已经通过 checker/retention 的 candidate 追加到永久 clause/proof arena。

该入口只维护稳定编号与对齐 proof journal，不决定新节点是否立即进入 Passive。
-/
def insertDerivedCandidate (state : State)
    (candidate : Candidate) : State × ClauseId :=
  let id := state.clauses.size
  let metadata := metadataOfClause candidate.clause
  let guards := canonicalGuards candidate.guards
  let modelRoundWorkspace :=
    state.modelRoundWorkspace.registerClause id (guards.map (·.var))
  let modelRoundWorkspace :=
    if state.index.requiresActiveFilter && modelRoundWorkspace.initialized then
      modelRoundWorkspace.setVisible id true
    else
      modelRoundWorkspace
  ({
    state with
    clauses := state.clauses.push candidate.clause
    guards := state.guards.push guards
    enabled := state.enabled.push true
    clauseMetadata := state.clauseMetadata.push metadata
    modelRoundWorkspace := modelRoundWorkspace
    index := state.index
    steps := state.steps.push {
      rule := candidate.rule
      substitution := candidate.substitution
      clause := candidate.clause
      resource? := candidate.resource?
    }
    nextAge := state.nextAge + 1
    lifecycle := {
      state.lifecycle with
      retainedCandidates := state.lifecycle.retainedCandidates + 1
      }
  }, id)

/-- 把已经通过 retention 的 candidate 插入永久数据库与 Passive。 -/
def insertPassiveCandidate (state : State) (candidate : Candidate) : State × ClauseId :=
  let age := state.nextAge
  let (state, id) := state.insertDerivedCandidate candidate
  let weight :=
    match state.clauseMetadata.weight? id with
    | some weight => weight
    | none => clauseWeight candidate.clause
  ({
    state with
    givenWorkspace := state.givenWorkspace.push {
      clauseId := id
      age := age
      weight := weight
    }
  }, id)

/--
删除一个尚未进入 Active/索引、也不再位于 Passive 的稳定节点。

forward simplification 的当前 given 已经被弹出 Passive，中间节点也从未入队，因此该入口
只需更新永久 liveness；证明 arena 与父引用保持不变。
-/
def deleteUnindexedClause (state : State) (id : ClauseId) : State :=
  if state.retained id && !state.givenWorkspace.isActive id &&
      !state.givenWorkspace.isPassive id then
    {
      state with
      clauseMetadata := state.clauseMetadata.delete id
      modelRoundWorkspace := state.modelRoundWorkspace.deleteMany #[id]
      index :=
        if state.index.registered.contains id then
          state.index.deleteMany #[id]
        else
          state.index
      lifecycle := {
        state.lifecycle with
        deletedClauses := state.lifecycle.deletedClauses + 1
      }
    }
  else
    state

/--
幂等开放一个已经存在于固定 input prefix 的 clause slot。

开放只改变搜索可见性并加入当前 Passive；canonical clause、guard、stable id 与 proof
journal 都保持不变。
-/
private def enableClauseWith (state : State) (id : ClauseId) (enqueue : Bool) : State :=
  if state.enabledAt id then
    state
  else
    match clauseAt? state.clauses id, state.clauseMetadata.weight? id with
    | some _, some weight =>
        if state.retained id then
          let age := state.nextAge
          let modelRoundWorkspace :=
            if enqueue && state.modelRoundWorkspace.initialized then
              state.modelRoundWorkspace.setVisible id true
            else
              state.modelRoundWorkspace
          let state := {
            state with
            enabled := state.enabled.set! id true
            modelRoundWorkspace := modelRoundWorkspace
            nextAge := age + 1
          }
          if enqueue then
            {
              state with
              givenWorkspace := state.givenWorkspace.push {
                clauseId := id
                age := age
                weight := weight
              }
            }
          else
            state
        else
          state
    | _, _ => state

/-- 幂等开放并立即把一个固定 input slot 加入当前 Passive。 -/
def enableClause (state : State) (id : ClauseId) : State :=
  enableClauseWith state id true

/-- 按 stable id 批量幂等开放固定 input slots。 -/
def enableClauses (state : State) (ids : Array ClauseId) : State :=
  ids.foldl enableClause state

/--
按当前 support predicate 批量开放 guarded input slots。

不满足本轮 assignment 的槽只记录为已开放，不进入本轮 Passive；下一次 `reseed` 会按新
assignment 自动决定是否入队。
-/
def enableClausesSupported (state : State) (ids : Array ClauseId)
    (supportActive : GuardSet → Bool) : State :=
  ids.foldl
    (fun state id =>
      let enqueue :=
        match state.guardsAt? id with
        | some guards => supportActive guards
        | none => false
      enableClauseWith state id enqueue)
    state

/-- 当前状态中的 live clause id。 -/
def liveIds (state : State) : Array ClauseId :=
  Data.appendArray state.active state.givenWorkspace.liveClauseIds

/-- 当前状态中的 live clauses。 -/
def liveClauses (state : State) : Array Clause :=
  liveClausesFrom state.clauses state.liveIds

/-- 带稳定数据库编号的 live residual clause。 -/
structure LiveClause where
  id : ClauseId
  guards : GuardSet
  clause : Clause
  deriving Repr, Lean.ToExpr

/-- 当前状态中的 live residual clause 及其稳定数据库编号。 -/
def liveEntries (state : State) : Array LiveClause := Id.run do
  let mut entries := #[]
  for id in state.liveIds do
    match clauseAt? state.clauses id, state.guardsAt? id with
    | some clause, some guards =>
        entries := entries.push { id := id, guards := guards, clause := clause }
    | _, _ => pure ()
  return entries

/--
在一次 retained 扫描中完成 duplicate 与 forward subsumption 判定。

duplicate 仍然拥有更高优先级：即使先遇到 subsuming clause，也继续扫描直到发现 duplicate
或遍历结束。最终包含判定仍由 `clauseSubsumes` 完整复核。
-/
def supportedRedundancyDecision
    (state : State) (config : Config) (guards : GuardSet) (clause : Clause) :
    RetentionDecision :=
  let target := Data.ClauseSignature.key clause
  state.clauseMetadata.foldForwardCandidatesUntil target config.enableSubsumption .accept
      fun decision id duplicatePossible =>
    if state.enabledAt id then
      match clauseAt? state.clauses id, state.guardsAt? id with
      | some existing, some existingGuards =>
          if guardSubset existingGuards guards then
            if duplicatePossible && CoreSyntax.Search.clauseEq existing clause then
              .done .rejectExistingDuplicate
            else if config.enableSubsumption && clauseSubsumes existing clause then
              .next .rejectForwardSubsumed
            else
              .next decision
          else
            .next decision
      | _, _ => .next decision
    else
      .next decision

/-- 预算化前向冗余扫描的内部状态。 -/
private structure RetentionScan where
  decision : RetentionDecision := .accept
  budget : WorkBudget
  exhausted : Bool := false

/--
带共享预算的 duplicate/forward-subsumption 判定。

signature 索引仍只做必要条件筛选；每个实际 retained 候选与 subsumption 回溯都显式扣费。
-/
def supportedRedundancyDecisionWithBudget
    (state : State) (config : Config) (guards : GuardSet) (clause : Clause)
    (budget : WorkBudget) : WorkResult RetentionDecision :=
  let target := Data.ClauseSignature.key clause
  let scan :=
    state.clauseMetadata.foldForwardCandidatesUntil
      target config.enableSubsumption ({ budget := budget } : RetentionScan)
      fun scan id duplicatePossible =>
        if scan.exhausted then
          .done scan
        else
          match scan.budget.charge? WorkKind.retention with
          | none => .done { scan with exhausted := true }
          | some budget =>
              if state.enabledAt id then
                match clauseAt? state.clauses id, state.guardsAt? id with
                | some existing, some existingGuards =>
                    if guardSubset existingGuards guards then
                      if duplicatePossible && CoreSyntax.Search.clauseEq existing clause then
                        .done {
                          decision := .rejectExistingDuplicate
                          budget := budget
                        }
                      else if config.enableSubsumption then
                        match clauseSubsumesWithBudget existing clause budget with
                        | .exhausted budget =>
                            .done {
                              decision := scan.decision
                              budget := budget
                              exhausted := true
                            }
                        | .complete true budget =>
                            .next {
                              decision := .rejectForwardSubsumed
                              budget := budget
                            }
                        | .complete false budget =>
                            .next { scan with budget := budget }
                      else
                        .next { scan with budget := budget }
                    else
                      .next { scan with budget := budget }
                | _, _ => .next { scan with budget := budget }
              else
                .next { scan with budget := budget }
  if scan.exhausted then
    .exhausted scan.budget
  else
    .complete scan.decision scan.budget

/-- 当前状态下的统一保留判定。返回规范化后的字句和保留结论。 -/
def retentionDecision (state : State) (config : Config) (candidate : Candidate) :
    Clause × RetentionDecision :=
  let clause := normalizeClause candidate.clause
  if !clauseWithinLimits config clause then
    (clause, .rejectLimit)
  else if tautological clause then
    (clause, .rejectTautology)
  else
    (clause, state.supportedRedundancyDecision config candidate.guards clause)

/-- 当前状态下尝试接受一个候选。 -/
def retainCandidate? (state : State) (config : Config) (candidate : Candidate) :
    Option Candidate :=
  let (clause, decision) := state.retentionDecision config candidate
  if decision.accepted then
    some {
      candidate with
      clause := clause
      resource? := candidate.resource?.map (fun witness => witness.withResult clause)
    }
  else
    none

/-- 预算化统一保留判定。 -/
def retentionDecisionWithBudget
    (state : State) (config : Config) (candidate : Candidate)
    (budget : WorkBudget) : WorkResult (Clause × RetentionDecision) :=
  let clause := normalizeClause candidate.clause
  if !clauseWithinLimits config clause then
    .complete (clause, .rejectLimit) budget
  else if tautological clause then
    .complete (clause, .rejectTautology) budget
  else
    (state.supportedRedundancyDecisionWithBudget config candidate.guards clause budget).map
      fun decision => (clause, decision)

/-- 在共享预算下尝试接受并规范化一个候选。 -/
def retainCandidateWithBudget
    (state : State) (config : Config) (candidate : Candidate)
    (budget : WorkBudget) : WorkResult (Option Candidate) :=
  match state.retentionDecisionWithBudget config candidate budget with
  | .exhausted budget => .exhausted budget
  | .complete (clause, decision) budget =>
      if decision.accepted then
        .complete (some {
          candidate with
          clause := clause
          resource? := candidate.resource?.map (fun witness => witness.withResult clause)
        }) budget
      else
        .complete none budget

/--
对一条已经通过 local rule checker 的 inference 执行 guard-aware retention。

该阶段只计算 support、做前向冗余判断并插入 Passive；后向删除由独立 deletion 阶段处理。
-/
def retainInference? (state : State) (config : Config) (candidate : Candidate) :
    Option (State × ClauseId) := do
  let guards ← state.ruleGuards? candidate.rule
  let candidate ← state.retainCandidate? config { candidate with guards := guards }
  some (state.insertPassiveCandidate candidate)

/-- 在共享预算下执行 guard-aware retention。 -/
def retainInferenceWithBudget
    (state : State) (config : Config) (candidate : Candidate)
    (budget : WorkBudget) : WorkResult (Option (State × ClauseId)) :=
  match state.ruleGuards? candidate.rule with
  | none => .complete none budget
  | some guards =>
      match state.retainCandidateWithBudget config { candidate with guards := guards } budget with
      | .exhausted budget => .exhausted budget
      | .complete none budget => .complete none budget
      | .complete (some candidate) budget =>
          .complete (some (state.insertPassiveCandidate candidate)) budget

/--
为一个新 retained 字句计算后向包含删除计划。

只有 `newGuards ⊆ oldGuards` 时，新字句才能取代旧字句，避免把不同 AVATAR 假设下的
同形或更弱字句错误合并。这里只计算稳定节点编号，不修改 State 或索引。
-/
def backwardDeletionPlan
    (config : Config) (state : State) (newId : ClauseId) (newClause : Clause) :
    DeletionPlan :=
  if !config.enableSubsumption then
    {}
  else
    match state.guardsAt? newId with
    | none => {}
    | some newGuards =>
        match state.clauseMetadata.subsumptionKey? newId with
        | none => {}
        | some pattern =>
            state.clauseMetadata.foldBackwardCandidates pattern {} fun plan oldId =>
              if oldId != newId && state.enabledAt oldId then
                match clauseAt? state.clauses oldId, state.guardsAt? oldId with
                | some oldClause, some oldGuards =>
                    if guardSubset newGuards oldGuards &&
                        clauseSubsumes newClause oldClause then
                      plan.insert oldId
                    else
                      plan
                | _, _ => plan
              else
                plan

/-- 预算化后向包含删除扫描的内部状态。 -/
private structure BackwardDeletionScan where
  plan : DeletionPlan := {}
  budget : WorkBudget
  exhausted : Bool := false

/-- 在共享预算下计算后向删除计划。 -/
def backwardDeletionPlanWithBudget
    (config : Config) (state : State) (newId : ClauseId) (newClause : Clause)
    (budget : WorkBudget) : WorkResult DeletionPlan :=
  if !config.enableSubsumption then
    .complete {} budget
  else
    match state.guardsAt? newId, state.clauseMetadata.subsumptionKey? newId with
    | some newGuards, some pattern =>
        let scan :=
          state.clauseMetadata.foldBackwardCandidatesUntil pattern
            ({ budget := budget } : BackwardDeletionScan)
            fun scan oldId =>
              if scan.exhausted then
                .done scan
              else
                match scan.budget.charge? WorkKind.backwardDeletion with
                | none => .done { scan with exhausted := true }
                | some budget =>
                    if oldId != newId && state.enabledAt oldId then
                      match clauseAt? state.clauses oldId, state.guardsAt? oldId with
                      | some oldClause, some oldGuards =>
                          if guardSubset newGuards oldGuards then
                            match clauseSubsumesWithBudget newClause oldClause budget with
                            | .exhausted budget =>
                                .done {
                                  plan := scan.plan
                                  budget := budget
                                  exhausted := true
                                }
                            | .complete true budget =>
                                .next {
                                  plan := scan.plan.insert oldId
                                  budget := budget
                                }
                            | .complete false budget =>
                                .next { scan with budget := budget }
                          else
                            .next { scan with budget := budget }
                      | _, _ => .next { scan with budget := budget }
                    else
                      .next { scan with budget := budget }
        if scan.exhausted then
          .exhausted scan.budget
        else
          .complete scan.plan scan.budget
    | _, _ => .complete {} budget

/-- 应用删除计划，并从 Active/Passive 移除节点；索引载荷通过稳定编号 tombstone 失效。 -/
def applyDeletionPlan (_config : Config) (state : State) (plan : DeletionPlan) : State :=
  if plan.clauseIds.isEmpty then
    state
  else
    Id.run do
      let state := {
        state with
        clauseMetadata := state.clauseMetadata.deleteMany plan.clauseIds
        modelRoundWorkspace := state.modelRoundWorkspace.deleteMany plan.clauseIds
        index := state.index.deleteMany plan.clauseIds
        givenWorkspace := state.givenWorkspace.deleteMany plan.clauseIds
      }
      let active := state.active.filter state.retained
      let state := {
        state with
        active := active
        lifecycle := {
          state.lifecycle with
          deletedClauses := state.lifecycle.deletedClauses + plan.clauseIds.size
        }
      }
      return state

/-- 将一个 given clause 移入 Active，并以原子提交方式完成预算化索引登记。 -/
def activateClauseWithBudget
    (config : Config) (state : State) (clauseId : ClauseId)
    (budget : WorkBudget) : WorkResult State :=
  match clauseAt? state.clauses clauseId with
  | some clause =>
      if state.enabledAt clauseId && state.retained clauseId &&
          !state.givenWorkspace.isActive clauseId then
        match ClauseIndex.insertClauseWithBudget config state.index clauseId clause budget with
        | .exhausted budget => .exhausted budget
        | .complete index budget =>
            .complete {
              state with
              active := state.active.push clauseId
              givenWorkspace := state.givenWorkspace.markActive clauseId
              index := index
              lifecycle := {
                state.lifecycle with
                activatedClauses := state.lifecycle.activatedClauses + 1
              }
            } budget
      else
        .complete state budget
  | none => .complete state budget

/-- 选择下一个 given clause，并从 Passive 中移除。 -/
def selectGiven? (config : Config) (state : State) : Option (PassiveEntry × State) :=
  let mode := passiveSelectionMode config state.selectionClock
  let selected? :=
    match mode with
    | PassiveSelectionMode.age => state.givenWorkspace.popAge?
    | PassiveSelectionMode.weight => state.givenWorkspace.popWeight?
  match selected? with
  | some (given, givenWorkspace) =>
      some (given, {
        state with
        givenWorkspace := givenWorkspace
        selectionClock := state.selectionClock + 1
        processed := state.processed + 1
      })
  | none => none

/-- 某个 retained 节点是否是无 support 的全局空字句。 -/
def globallyEmptyAt (state : State) (id : ClauseId) : Bool :=
  state.enabledAt id && state.retained id &&
    match clauseAt? state.clauses id, state.guardsAt? id with
    | some clause, some guards => clause.isEmpty && guards.isEmpty
    | _, _ => false

/-- 定位当前 retained 数据库中的第一个全局空字句。 -/
def firstGlobalEmptyId? (state : State) : Option ClauseId :=
  state.clauseMetadata.firstRetained? fun id =>
    state.enabledAt id &&
      match clauseAt? state.clauses id, state.guardsAt? id with
      | some clause, some guards => clause.isEmpty && guards.isEmpty
      | _, _ => false

/-- 当前 retained 数据库是否已经推出全局空字句。 -/
def containsGlobalEmpty (state : State) : Bool :=
  state.firstGlobalEmptyId?.isSome

end State

/-- 字句集中是否已经推出空字句。 -/
def containsEmptyClause (clauses : Array Clause) : Bool :=
  clauses.any fun clause => clause.isEmpty

/--
Superposition 内核可调用的 residual 闭合 hook。

probe 读取完整搜索状态，因此外层既能命题化 live clauses，也能保留稳定 clause id，
供新 DAG 抽取所有 residual 父节点的共享祖先切片。
-/
abbrev CdclProbe (α : Type) := State → Option α

/-- 默认不启用 CDCL hook，供纯 superposition 饱和入口使用。 -/
def noCdclProbe : CdclProbe PUnit := fun _ => none

/-- 小型核心输出的唯一 proof chain payload。 -/
structure Payload where
  config : Config
  inputClauses : Array Clause
  proofChain : Array ProofStep
  liveClauses : Array Clause
  status : Status
  stats : Certificate.Stats
  replayHasEmpty : Bool
  deriving Repr, Lean.ToExpr

namespace Rule

/-- 按 proof chain 的局部编号重写父节点。 -/
def remapParents? (inputSize : Nat) (mapping : Array (Option ClauseId)) :
    Rule → Option Rule
  | ordinaryFactoring parent => do
      some (ordinaryFactoring (← remap parent))
  | equalityFactoring parent => do
      some (equalityFactoring (← remap parent))
  | equalityResolution parent => do
      some (equalityResolution (← remap parent))
  | demodulation equality target => do
      some (demodulation (← remap equality) (← remap target))
  | extensionalParamodulation equality target => do
      some (extensionalParamodulation (← remap equality) (← remap target))
  | booleanExtensionality parent => do
      some (booleanExtensionality (← remap parent))
  | argumentCongruence parent => do
      some (argumentCongruence (← remap parent))
  | binaryResolution left right => do
      some (binaryResolution (← remap left) (← remap right))
  | positiveSuperposition equality target => do
      some (positiveSuperposition (← remap equality) (← remap target))
  | negativeSuperposition equality target => do
      some (negativeSuperposition (← remap equality) (← remap target))
where
  remap (id : ClauseId) : Option ClauseId :=
    if id < inputSize then
      some id
    else
      let index := id - inputSize
      if h : index < mapping.size then
        mapping[index]
      else
        none

end Rule

/-- 定位数据库里的第一个空字句。 -/
def firstEmptyClauseId? (clauses : Array Clause) : Option ClauseId :=
  Id.run do
    let mut found : Option ClauseId := none
    for h : id in [:clauses.size] do
      if found.isNone && clauses[id].isEmpty then
        found := some id
    return found

/-- 标记某个原始数据库节点的所有 proof chain 祖先。 -/
def markProofAncestor (inputSize : Nat) (steps : Array ProofStep) :
    Nat → ClauseId → Array Bool → Array Bool
  | 0, _, needed => needed
  | fuel + 1, id, needed =>
      if id < inputSize then
        needed
      else
        let index := id - inputSize
        if h : index < steps.size then
          let needed := needed.set! index true
          steps[index].rule.parents.foldl
            (fun needed parent => markProofAncestor inputSize steps fuel parent needed)
            needed
        else
          needed

/-- 为唯一 proof chain 生成搜索派生节点到局部节点的编号表。 -/
def proofChainMapping (inputSize : Nat) (needed : Array Bool) :
    Array (Option ClauseId) :=
  Id.run do
    let mut mapping : Array (Option ClauseId) := (List.replicate needed.size none).toArray
    let mut nextId := inputSize
    for h : index in [:needed.size] do
      if needed[index] then
        mapping := mapping.set! index (some nextId)
        nextId := nextId + 1
    return mapping

/-- 按 proof slice 的局部编号重写一个数据库字句编号。 -/
def remapProofClauseId? (inputSize : Nat) (mapping : Array (Option ClauseId))
    (id : ClauseId) : Option ClauseId :=
  if id < inputSize then
    some id
  else
    let index := id - inputSize
    if h : index < mapping.size then
      mapping[index]
    else
      none

/-- 从完整搜索数据库裁剪出的共享祖先 proof slice。 -/
structure ProofSlice where
  roots : Array ClauseId
  steps : Array ProofStep
  deriving Repr, Lean.ToExpr

/--
从完整搜索数据库裁剪出覆盖全部指定根节点的共享 proof slice。

输入字句编号保持不变；派生节点按拓扑顺序压紧，从而可以直接接到 canonical source
节点之后。多个 residual 根共享祖先时只保留一份推导。
-/
def extractProofSlice? (inputSize : Nat) (steps : Array ProofStep)
    (roots : Array ClauseId) : Option ProofSlice :=
  let needed :=
    roots.foldl
      (fun needed root =>
        markProofAncestor inputSize steps (steps.size + 1) root needed)
      (List.replicate steps.size false).toArray
  let mapping := proofChainMapping inputSize needed
  Id.run do
    let mut chain : Array ProofStep := #[]
    let mut ok := true
    for _h : index in [:steps.size] do
      match needed[index]? with
      | some true =>
          match steps[index]? with
          | some step =>
              match Rule.remapParents? inputSize mapping step.rule with
              | some rule =>
                  match step.resource? with
                  | none => ok := false
                  | some resource =>
                      match resource.remapParents? inputSize mapping with
                      | some resource =>
                          chain := chain.push { step with rule := rule, resource? := some resource }
                      | none => ok := false
              | none => ok := false
          | none => ok := false
      | _ => pure ()
    if !ok then
      return none
    let roots? := roots.mapM (remapProofClauseId? inputSize mapping)
    return roots?.map fun roots => { roots := roots, steps := chain }

/-- 从完整搜索数据库裁剪出通向指定根节点的唯一线性 proof chain。 -/
def extractProofChain? (inputSize : Nat) (steps : Array ProofStep) (root : ClauseId) :
    Option (Array ProofStep) := do
  let slice ← extractProofSlice? inputSize steps #[root]
  some slice.steps

/-- 资源证书中的父字句引用必须按 id 命中当前数据库；若携带 clause 快照则一并校验。 -/
def clauseForResourceRef? (available : Array Clause) (ref : ResourceTrace.ClauseRef) :
    Option Clause := do
  let clause ← clauseAt? available ref.id
  match ref.clause? with
  | some expected =>
      if CoreSyntax.Search.clauseEq expected clause then
        some clause
      else
        none
  | none => some clause

/-- 直接检查一元规则资源。这里不枚举候选位置，只按 witness 指定位置重算一步。 -/
def checkUnaryResource (config : Config) (available : Array Clause)
    (resource : ResourceTrace.UnaryResource) : Bool :=
  match clauseForResourceRef? available resource.parent with
  | none => false
  | some parent =>
      match resource.kind with
      | ResourceTrace.UnaryKind.ordinaryFactoring =>
          match resource.literalIndex?, resource.otherLiteralIndex? with
          | some i, some j =>
              i != j && selectedForResolution config parent i &&
                match ordinaryFactoringAt? parent i j with
                | some (clause, subst) =>
                    subst == resource.substitution &&
                      sameRetainedClause clause resource.result
                | none => false
          | _, _ => false
      | ResourceTrace.UnaryKind.equalityFactoring =>
          match resource.literalIndex?, resource.otherLiteralIndex? with
          | some mainIndex, some otherIndex =>
              mainIndex != otherIndex &&
                match equalityFactoringAt? config parent mainIndex otherIndex with
                | some (clause, subst) =>
                    subst == resource.substitution &&
                      sameRetainedClause clause resource.result
                | none => false
          | _, _ => false
      | ResourceTrace.UnaryKind.equalityResolution =>
          match resource.literalIndex? with
          | some index =>
              match equalityResolutionAt? config parent index with
              | some (clause, subst) =>
                  subst == resource.substitution && sameRetainedClause clause resource.result
              | none => false
          | none => false
      | ResourceTrace.UnaryKind.booleanExtensionality =>
          match resource.literalIndex? with
          | some index =>
              match booleanExtensionalityAt? parent index with
              | some (clause, subst) =>
                  subst == resource.substitution && sameRetainedClause clause resource.result
              | none => false
          | none => false
      | ResourceTrace.UnaryKind.argumentCongruence =>
          match resource.literalIndex? with
          | some index =>
              match argumentCongruenceAt? parent index with
              | some (clause, subst) =>
                  subst == resource.substitution && sameRetainedClause clause resource.result
              | none => false
          | none => false
      | ResourceTrace.UnaryKind.functionExtensionality =>
          false

/-- `ClauseRef.clause?` 若存在，必须与真实父字句一致。 -/
private def resourceRefSnapshotOk (ref : ResourceTrace.ClauseRef)
    (actual : Clause) : Bool :=
  match ref.clause? with
  | some snapshot => CoreSyntax.Search.clauseEq snapshot actual
  | none => true

/-- 单侧 standardize-apart metadata 必须从真实父字句复算出来。 -/
private def standardizeApartSideOk (ref : ResourceTrace.ClauseRef)
    (actual : Clause) (side : ResourceTrace.StandardizeApartSideMetadata) :
    Bool :=
  resourceRefSnapshotOk ref actual &&
    CoreSyntax.Search.clauseEq side.original actual &&
      CoreSyntax.Search.clauseEq side.renamed
        (CoreSyntax.Search.Clause.renameVars side.offset side.original)

/-- 从资源 metadata 或旧隐式路径取出检查用的 standardize-apart 父字句。 -/
private def standardizedResolutionParents?
    (leftRef rightRef : ResourceTrace.ClauseRef)
    (left right : Clause)
    (metadata? : Option ResourceTrace.StandardizeApartMetadata) :
    Option (Clause × Clause) :=
  match metadata? with
  | some metadata =>
      if standardizeApartSideOk leftRef left metadata.left &&
          standardizeApartSideOk rightRef right metadata.right then
        some (metadata.left.renamed, metadata.right.renamed)
      else
        none
  | none =>
      some (CoreSyntax.Search.standardizeApart left right)

/-- 重写资源使用和 resolution 相同的显式双亲改名复算。 -/
private def standardizedRewriteParents?
    (equalityRef targetRef : ResourceTrace.ClauseRef)
    (equality target : Clause)
    (metadata? : Option ResourceTrace.StandardizeApartMetadata) :
    Option (Clause × Clause) :=
  match metadata? with
  | some metadata =>
      if standardizeApartSideOk equalityRef equality metadata.left &&
          standardizeApartSideOk targetRef target metadata.right then
        some (metadata.left.renamed, metadata.right.renamed)
      else
        none
  | none => some (equality, target)

/-- 直接检查二元 resolution 资源。 -/
def checkResolutionResource (config : Config) (available : Array Clause)
    (resource : ResourceTrace.ResolutionResource) : Bool :=
  match clauseForResourceRef? available resource.left,
      clauseForResourceRef? available resource.right,
      resource.leftLiteralIndex?, resource.rightLiteralIndex? with
  | some left, some right, some i, some j =>
      match standardizedResolutionParents? resource.left resource.right left right
          resource.standardizeApart? with
      | some (left, right) =>
          eligibleResolutionLiteral config left i &&
            eligibleResolutionLiteral config right j &&
            match resolventAtStandardized? left right i j with
            | some (clause, subst) =>
                subst == resource.substitution && sameRetainedClause clause resource.result
            | none => false
      | none => false
  | _, _, _, _ => false

private def orientedResourceMatches (equality : OrientedEquality)
    (resource : ResourceTrace.RewriteResource) : Bool :=
  equality.literalIndex == resource.equalityLiteral &&
    resource.orientedLhs == equality.lhs &&
      resource.orientedRhs == equality.rhs

private def directDemodulationCheck (config : Config) (equalityClause targetClause : Clause)
    (resource : ResourceTrace.RewriteResource) : Bool :=
  let targetPosition := positionedTermOfResource resource.targetPosition
  if !config.enableDemodulation then
    false
  else if resource.contextual then
    if !config.enableContextualDemodulation then
      false
    else
      match selectedOrientedEqualityAt? equalityClause resource.equalityLiteral with
      | some equality =>
          orientedResourceMatches equality resource &&
            match contextualDemodulateLiteral? equalityClause targetClause equality
                resource.targetLiteral targetPosition with
            | some (clause, subst) =>
                subst == resource.substitution && sameRetainedClause clause resource.result
            | none => false
      | none => false
  else
    match orientedUnitEquality? equalityClause with
    | some equality =>
        orientedResourceMatches equality resource &&
          match demodulateLiteral? targetClause equality resource.targetLiteral
              targetPosition with
          | some (clause, subst) =>
              subst == resource.substitution && sameRetainedClause clause resource.result
          | none => false
    | none => false

private def directSuperpositionCheck (config : Config) (equalityClause targetClause : Clause)
    (resource : ResourceTrace.RewriteResource) : Bool :=
  let targetPosition := positionedTermOfResource resource.targetPosition
  match resource.targetPolarity? with
  | none => false
  | some polarity =>
      let polarity' :=
        match polarity with
        | ResourceTrace.TargetPolarity.positive => SuperpositionPolarity.positive
        | ResourceTrace.TargetPolarity.negative => SuperpositionPolarity.negative
      let site : SuperpositionSite := {
        equalityLiteral := resource.equalityLiteral
        targetLiteral := resource.targetLiteral
        targetPosition := targetPosition
        orientedLhs := resource.orientedLhs
        orientedRhs := resource.orientedRhs
        substitution := resource.substitution
        polarity := polarity'
      }
      match selectedOrientedEqualityAt? equalityClause resource.equalityLiteral with
      | some equality =>
          let kindOk :=
            match resource.kind, polarity with
            | ResourceTrace.RewriteKind.positiveSuperposition,
              ResourceTrace.TargetPolarity.positive => true
            | ResourceTrace.RewriteKind.extensionalParamodulation,
              ResourceTrace.TargetPolarity.positive =>
                isExtensionalParamodulationSite equality targetPosition
            | ResourceTrace.RewriteKind.negativeSuperposition,
              ResourceTrace.TargetPolarity.negative =>
                resource.targetPosition.path == []
            | _, _ => false
          kindOk && checkSuperpositionSideConditions config equalityClause targetClause
            resource.result site
      | none => false

/-- 直接检查重写/叠加资源。 -/
def checkRewriteResource (config : Config) (available : Array Clause)
    (resource : ResourceTrace.RewriteResource) : Bool :=
  match clauseForResourceRef? available resource.equality,
      clauseForResourceRef? available resource.target with
  | some equalityClause, some targetClause =>
      match standardizedRewriteParents?
          resource.equality resource.target equalityClause targetClause
            resource.standardizeApart? with
      | some (equalityClause, targetClause) =>
          match resource.kind with
          | ResourceTrace.RewriteKind.demodulation =>
              !resource.contextual &&
                directDemodulationCheck config equalityClause targetClause resource
          | ResourceTrace.RewriteKind.contextualDemodulation =>
              resource.contextual &&
                directDemodulationCheck config equalityClause targetClause resource
          | ResourceTrace.RewriteKind.positiveSuperposition
          | ResourceTrace.RewriteKind.negativeSuperposition
          | ResourceTrace.RewriteKind.extensionalParamodulation =>
              directSuperpositionCheck config equalityClause targetClause resource
      | none => false
  | _, _ => false

/-- 局部 step witness checker：只按证书记录的位置和资源重算当前一步。 -/
def checkLocalStepWitness (config : Config) (available : Array Clause)
    (witness : ResourceTrace.LocalStepWitness) : Bool :=
  match witness with
  | ResourceTrace.LocalStepWitness.unary resource =>
      checkUnaryResource config available resource
  | ResourceTrace.LocalStepWitness.resolution resource =>
      checkResolutionResource config available resource
  | ResourceTrace.LocalStepWitness.rewrite resource =>
      checkRewriteResource config available resource

/-- 资源 witness 是否与 proof step 的规则标签和父节点编号一致。 -/
def proofStepResourceMatches (step : ProofStep) : Bool :=
  match step.resource? with
  | none => true
  | some resource =>
      resource.resultMatches step.clause &&
        match step.rule, resource with
        | Rule.ordinaryFactoring parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.ordinaryFactoring &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.equalityFactoring parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.equalityFactoring &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.equalityResolution parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.equalityResolution &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.booleanExtensionality parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.booleanExtensionality &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.argumentCongruence parent, ResourceTrace.LocalStepWitness.unary witness =>
            witness.kind == ResourceTrace.UnaryKind.argumentCongruence &&
              witness.parent.id == parent && witness.substitution == step.substitution
        | Rule.binaryResolution left right, ResourceTrace.LocalStepWitness.resolution witness =>
            witness.left.id == left && witness.right.id == right &&
              witness.substitution == step.substitution
        | Rule.demodulation equality target, ResourceTrace.LocalStepWitness.rewrite witness =>
            witness.equality.id == equality && witness.target.id == target &&
              witness.substitution == step.substitution &&
                (witness.kind == ResourceTrace.RewriteKind.demodulation ||
                  witness.kind == ResourceTrace.RewriteKind.contextualDemodulation)
        | Rule.extensionalParamodulation equality target,
          ResourceTrace.LocalStepWitness.rewrite witness =>
            witness.equality.id == equality && witness.target.id == target &&
              witness.substitution == step.substitution &&
                witness.kind == ResourceTrace.RewriteKind.extensionalParamodulation
        | Rule.positiveSuperposition equality target, ResourceTrace.LocalStepWitness.rewrite witness =>
            witness.equality.id == equality && witness.target.id == target &&
              witness.substitution == step.substitution &&
                witness.kind == ResourceTrace.RewriteKind.positiveSuperposition &&
                  witness.targetPolarity? == some ResourceTrace.TargetPolarity.positive
        | Rule.negativeSuperposition equality target, ResourceTrace.LocalStepWitness.rewrite witness =>
            witness.equality.id == equality && witness.target.id == target &&
              witness.substitution == step.substitution &&
                witness.kind == ResourceTrace.RewriteKind.negativeSuperposition &&
                  witness.targetPolarity? == some ResourceTrace.TargetPolarity.negative
        | _, _ => false

/-- 正式 proof-step checker：每个派生 step 必须携带局部资源 witness。 -/
def validProofStep (config : Config) (available : Array Clause) (step : ProofStep) :
    Bool :=
  match step.resource? with
  | some resource =>
      proofStepResourceMatches step && checkLocalStepWitness config available resource
  | none => false

namespace State

/-- forward simplification 的良基测度。 -/
structure ForwardSimplificationMeasure where
  literalCount : Nat
  termSize : Nat
  termCode : Nat

/--
计算 forward simplification 测度。

先比较文字数，再比较词项总尺寸，最后比较项序编码总和。equality resolution 严格减少
第一分量；demodulation 在文字数不变时必须严格减少后两分量之一。
-/
def forwardSimplificationMeasure (clause : Clause) : ForwardSimplificationMeasure :=
  clause.foldl
    (fun measure literal =>
      {
        literalCount := measure.literalCount + 1
        termSize := measure.termSize +
          CoreSyntax.Search.Term.size literal.left +
          CoreSyntax.Search.Term.size literal.right
        termCode := measure.termCode +
          TermOrdering.code literal.left +
          TermOrdering.code literal.right
      })
    { literalCount := 0, termSize := 0, termCode := 0 }

/-- 新字句是否沿 forward simplification 测度严格下降。 -/
def forwardSimplificationDecreases (before after : Clause) : Bool :=
  let beforeMeasure := forwardSimplificationMeasure before
  let afterMeasure := forwardSimplificationMeasure after
  afterMeasure.literalCount < beforeMeasure.literalCount ||
    (afterMeasure.literalCount == beforeMeasure.literalCount &&
      (afterMeasure.termSize < beforeMeasure.termSize ||
        (afterMeasure.termSize == beforeMeasure.termSize &&
          afterMeasure.termCode < beforeMeasure.termCode)))

/-- 预算化 forward 冗余扫描的内部状态。 -/
private structure ForwardRedundancyScan where
  found : Bool := false
  budget : WorkBudget
  exhausted : Bool := false

/-- 当前 Active 中是否已有 support 更弱的同形或包含字句。 -/
def forwardRedundantAgainstActiveWithBudget
    (config : Config) (state : State) (guards : GuardSet) (clause : Clause)
    (budget : WorkBudget) : WorkResult Bool :=
  let target := Data.ClauseSignature.key clause
  let scan :=
    Data.foldArrayUntil state.active
      ({ budget := budget } : ForwardRedundancyScan) fun scan id =>
        if scan.found || scan.exhausted then
          .done scan
        else
          match scan.budget.charge? WorkKind.retention with
          | none => .done { scan with exhausted := true }
          | some budget =>
              if state.retained id then
                match state.clauseMetadata.subsumptionKey? id with
                | some existingKey =>
                    let duplicatePossible := existingKey == target
                    let subsumptionPossible :=
                      config.enableSubsumption && existingKey.maySubsume target
                    if duplicatePossible || subsumptionPossible then
                      match clauseAt? state.clauses id, state.guardsAt? id with
                      | some existing, some existingGuards =>
                          if guardSubset existingGuards guards then
                            if duplicatePossible &&
                                CoreSyntax.Search.clauseEq existing clause then
                              .done { found := true, budget := budget }
                            else if subsumptionPossible then
                              match clauseSubsumesWithBudget existing clause budget with
                              | .exhausted budget =>
                                  .done {
                                    found := false
                                    budget := budget
                                    exhausted := true
                                  }
                              | .complete found budget =>
                                  if found then
                                    .done { found := true, budget := budget }
                                  else
                                    .next { scan with budget := budget }
                            else
                              .next { scan with budget := budget }
                          else
                            .next { scan with budget := budget }
                      | _, _ => .next { scan with budget := budget }
                    else
                      .next { scan with budget := budget }
                | none => .next { scan with budget := budget }
              else
                .next { scan with budget := budget }
  if scan.exhausted then
    .exhausted scan.budget
  else
    .complete scan.found scan.budget

/-- forward simplification 候选扫描的内部状态。 -/
private structure ForwardCandidateSearch where
  candidate? : Option Candidate := none
  budget : WorkBudget
  exhausted : Bool := false

/-- 把候选扫描状态转换为早停 fold 的控制结果。 -/
@[inline]
private def ForwardCandidateSearch.foldStep
    (search : ForwardCandidateSearch) : Data.FoldStep ForwardCandidateSearch :=
  if search.exhausted || search.candidate?.isSome then
    .done search
  else
    .next search

/-- 构造第一个 equality resolution 收缩步骤。 -/
def firstForwardEqualityResolutionCandidateWithBudget
    (config : Config) (current : PassiveEntry)
    (clause : Clause) (guards : GuardSet) (budget : WorkBudget) :
    WorkResult (Option Candidate) :=
  if !config.enableEqualityResolution then
    .complete none budget
  else
    let search :=
      Data.foldNatRangeUntil 0 clause.size
        ({ budget := budget } : ForwardCandidateSearch) fun search literalIndex =>
          if search.candidate?.isSome || search.exhausted then
            .done search
          else
            match
                (search.budget.charge? WorkKind.inferenceAttempt).bind
                  (·.charge? WorkKind.unification) with
            | none => .done { search with exhausted := true }
            | some budget =>
                match equalityResolutionAt? config clause literalIndex with
                | some (result, subst) =>
                    let result := normalizeClause result
                    if forwardSimplificationDecreases clause result then
                      .done {
                        candidate? := some {
                          rule := Rule.equalityResolution current.clauseId
                          substitution := subst
                          guards := guards
                          clause := result
                          resource? :=
                            some <| unaryResourceWitness
                              ResourceTrace.UnaryKind.equalityResolution
                              current.clauseId (some literalIndex) none subst result
                        }
                        budget := budget
                      }
                    else
                      .next { search with budget := budget }
                | none => .next { search with budget := budget }
    if search.exhausted then
      .exhausted search.budget
    else
      .complete search.candidate? search.budget

/-- 从指定索引中寻找第一个严格收缩的 forward demodulation。 -/
private def firstForwardDemodulationCandidateWithBudget
    (contextual : Bool) (config : Config) (state : State) (current : PassiveEntry)
    (clause : Clause) (guards : GuardSet) (budget : WorkBudget) :
    WorkResult (Option Candidate) :=
  if !config.enableDemodulation || (contextual && !config.enableContextualDemodulation) then
    .complete none budget
  else
    let search :=
      Data.foldNatRangeUntil 0 clause.size
        ({ budget := budget } : ForwardCandidateSearch) fun search literalIndex =>
          if search.candidate?.isSome || search.exhausted then
            .done search
          else
            match clause[literalIndex]? with
            | none => .next search
            | some literal =>
                let searchStep :=
                  foldLiteralSubtermsUntil literal search fun search position =>
                    if search.candidate?.isSome || search.exhausted then
                      .done search
                    else
                      match
                          (search.budget.charge? WorkKind.termPosition).bind
                            (·.charge? WorkKind.inferenceAttempt) with
                      | none => .done { search with exhausted := true }
                      | some budget =>
                          if CoreSyntax.Search.Term.isVar position.term then
                            .next { search with budget := budget }
                          else
                            let visit :=
                              fun search occurrence =>
                                if search.candidate?.isSome || search.exhausted then
                                  .done search
                                else
                                  match
                                      (search.budget.charge? WorkKind.indexOccurrence).bind
                                        (·.charge? WorkKind.unification) with
                                  | none => .done { search with exhausted := true }
                                  | some budget =>
                                      match clauseAt? state.clauses occurrence.clauseId,
                                          state.guardsAt? occurrence.clauseId with
                                      | some equalityClause, some equalityGuards =>
                                          let metadata :=
                                            demodulationStandardizeApartMetadata
                                              equalityClause clause
                                          let equality? :=
                                            if contextual then
                                              selectedOrientedEqualityAt?
                                                metadata.left.renamed occurrence.literalIndex
                                            else
                                              orientedUnitEquality? metadata.left.renamed
                                          match equality? with
                                          | some equality =>
                                              let result? :=
                                                if contextual then
                                                  contextualDemodulateLiteral?
                                                    metadata.left.renamed clause equality
                                                    literalIndex position
                                                else
                                                  demodulateLiteral?
                                                    clause equality literalIndex position
                                              match result? with
                                              | some (result, subst) =>
                                                  if tautological result ||
                                                      forwardSimplificationDecreases
                                                        clause result then
                                                    .done {
                                                      candidate? := some {
                                                        rule :=
                                                          Rule.demodulation
                                                            occurrence.clauseId current.clauseId
                                                        substitution := subst
                                                        guards :=
                                                          mergeGuards equalityGuards guards
                                                        clause := result
                                                        resource? :=
                                                          some <| rewriteResourceWitness
                                                            (if contextual then
                                                              ResourceTrace.RewriteKind.contextualDemodulation
                                                            else
                                                              ResourceTrace.RewriteKind.demodulation)
                                                            occurrence.clauseId
                                                            current.clauseId clause
                                                            equality.literalIndex literalIndex
                                                            position equality.lhs equality.rhs
                                                            subst result contextual
                                                            (standardizeApart? := some metadata)
                                                      }
                                                      budget := budget
                                                    }
                                                  else
                                                    .next { search with budget := budget }
                                              | none => .next { search with budget := budget }
                                          | none => .next { search with budget := budget }
                                      | _, _ => .next { search with budget := budget }
                            let search :=
                              if contextual then
                                state.index.foldPatternsMatchingPositiveEqualitiesUntil
                                  state.givenWorkspace position.term
                                  { search with budget := budget } visit
                              else
                                state.index.foldPatternsMatchingDemodulatorsUntil
                                  state.givenWorkspace position.term
                                  { search with budget := budget } visit
                            search.foldStep
                searchStep
    if search.exhausted then
      .exhausted search.budget
    else
      .complete search.candidate? search.budget

/-- 按固定优先级寻找当前 given 的第一个收缩步骤。 -/
def firstForwardSimplificationCandidateWithBudget
    (config : Config) (state : State) (current : PassiveEntry)
    (clause : Clause) (guards : GuardSet) (budget : WorkBudget) :
    WorkResult (Option Candidate) :=
  match
      firstForwardEqualityResolutionCandidateWithBudget
        config current clause guards budget with
  | .exhausted budget => .exhausted budget
  | .complete (some candidate) budget => .complete (some candidate) budget
  | .complete none budget =>
      match
          firstForwardDemodulationCandidateWithBudget
            false config state current clause guards budget with
      | .exhausted budget => .exhausted budget
      | .complete (some candidate) budget => .complete (some candidate) budget
      | .complete none budget =>
          firstForwardDemodulationCandidateWithBudget
            true config state current clause guards budget

/-- forward simplification region 中的当前 given。 -/
structure ForwardSimplificationMachine where
  state : State
  current : PassiveEntry
  budget : WorkBudget

/-- 应用一个已经确定为严格收缩的 checked simplification candidate。 -/
def applyForwardSimplificationCandidate
    (config : Config) (machine : ForwardSimplificationMachine) (candidate : Candidate) :
    Data.Fixpoint.Step ForwardSimplificationMachine :=
  let state := machine.state
  match state.guardsAt? machine.current.clauseId with
  | none => Data.Fixpoint.Step.discard machine
  | some currentGuards =>
      match state.ruleGuards? candidate.rule with
      | none => Data.Fixpoint.Step.done machine
      | some ruleGuards =>
          let candidate := {
            candidate with
            guards := ruleGuards
            clause := normalizeClause candidate.clause
            resource? := candidate.resource?.map
              (fun witness => witness.withResult (normalizeClause candidate.clause))
          }
          if !clauseWithinLimits config candidate.clause ||
              !validProofStep config state.clauses candidate.proofStep then
            Data.Fixpoint.Step.done machine
          else
            let state := {
              state with
              lifecycle := state.lifecycle.recordForwardSimplificationStep
            }
            if tautological candidate.clause then
              let state := {
                state with
                lifecycle := {
                  state.lifecycle with
                  retentionRejectedCandidates :=
                    state.lifecycle.retentionRejectedCandidates + 1
                }
              }
              let state :=
                if guardSubset ruleGuards currentGuards then
                  state.deleteUnindexedClause machine.current.clauseId
                else
                  state
              Data.Fixpoint.Step.discard { machine with state := state }
            else
              let state :=
                if guardSubset ruleGuards currentGuards then
                  state.deleteUnindexedClause machine.current.clauseId
                else
                  state
              let (state, id) := state.insertDerivedCandidate candidate
              let weight :=
                match state.clauseMetadata.weight? id with
                | some weight => weight
                | none => clauseWeight candidate.clause
              Data.Fixpoint.Step.next {
                state := state
                current := {
                  clauseId := id
                  age := machine.current.age
                  weight := weight
                }
                budget := machine.budget
              }

/-- forward simplification 的单步状态转换。 -/
def advanceForwardSimplification
    (config : Config) (machine : ForwardSimplificationMachine) :
    Data.Fixpoint.Step ForwardSimplificationMachine :=
  match machine.budget.charge? WorkKind.forwardSimplification with
  | none => Data.Fixpoint.Step.exhausted machine
  | some budget =>
      let machine := { machine with budget := budget }
      match clauseAt? machine.state.clauses machine.current.clauseId,
          machine.state.guardsAt? machine.current.clauseId with
      | some clause, some guards =>
          if tautological clause then
            Data.Fixpoint.Step.discard {
              machine with
              state := machine.state.deleteUnindexedClause machine.current.clauseId
            }
          else
            match
                machine.state.forwardRedundantAgainstActiveWithBudget
                  config guards clause machine.budget with
            | .exhausted budget =>
                Data.Fixpoint.Step.exhausted { machine with budget := budget }
            | .complete true budget =>
                Data.Fixpoint.Step.discard {
                  machine with
                  budget := budget
                  state := machine.state.deleteUnindexedClause machine.current.clauseId
                }
            | .complete false budget =>
                match
                    firstForwardSimplificationCandidateWithBudget
                      config machine.state machine.current clause guards budget with
                | .exhausted budget =>
                    Data.Fixpoint.Step.exhausted { machine with budget := budget }
                | .complete none budget =>
                    Data.Fixpoint.Step.done { machine with budget := budget }
                | .complete (some candidate) budget =>
                    match
                        (budget.charge? WorkKind.localCheck).bind
                          (·.charge? WorkKind.retention) with
                    | none =>
                        Data.Fixpoint.Step.exhausted { machine with budget := budget }
                    | some budget =>
                        applyForwardSimplificationCandidate
                          config { machine with budget := budget } candidate
      | _, _ => Data.Fixpoint.Step.discard machine

/-- forward simplification 的冻结结果。 -/
structure ForwardSimplificationResult where
  state : State
  given? : Option PassiveEntry
  budget : WorkBudget
  complete : Bool

/--
把 given 归约到 forward simplification 不动点。

中间节点只追加到稳定 clause/proof arena，不进入 Passive；最终规范形才返回给生成式规则。
-/
def forwardSimplifyGiven
    (config : Config) (state : State) (given : PassiveEntry)
    (budget : WorkBudget) : ForwardSimplificationResult :=
  let result :=
    Data.Fixpoint.Workspace.run
      { state := state, current := given, budget := budget }
      (advanceForwardSimplification config)
  let discarded := result.outcome == Data.Fixpoint.Outcome.discarded
  let exhausted := result.outcome == Data.Fixpoint.Outcome.exhausted
  let state := {
    result.state.state with
    lifecycle :=
      result.state.state.lifecycle.recordForwardSimplificationResult
        result.iterations discarded
  }
  {
    state := state
    given? := if discarded then none else some result.state.current
    budget := result.state.budget
    complete := !exhausted
  }

/--
处理一个 given clause 的显式状态机，并在最终规范形进入 generation 前运行搜索期 hook。

1. given 先通过 checked forward simplification 归约到不动点；
2. `beforeGeneration` 可开放已经存在的 canonical input slots；
3. generation 只围绕最终规范形借助 Active 索引产生 raw inference；
4. local rule checker 从真实父字句重算每一步；
5. retention 计算 guard、前向冗余并插入 Passive；
6. deletion 独立计算并应用后向包含计划；
7. 最终规范形最后才进入 Active 与索引。
-/
structure ProcessGivenResult where
  state : State
  budget : WorkBudget
  complete : Bool

/-- 逐候选执行 local checker、retention 与 backward deletion。 -/
private def consumeGeneratedCandidate
    (config : Config) (givenId : ClauseId)
    (available : Array Clause) (active : Array ClauseId)
    (flow : CandidateFlow State) (candidate : Candidate) :
    CandidateFlow State :=
  let flow := flow.charge WorkKind.localCheck
  if flow.exhausted then
    flow
  else
    let valid :=
      candidate.rule.parents.all
          (fun parent => parent == givenId || active.contains parent) &&
        validProofStep config available candidate.proofStep
    if !valid then
      {
        flow with
        value := {
          flow.value with
          lifecycle := {
            flow.value.lifecycle with
            ruleRejectedCandidates := flow.value.lifecycle.ruleRejectedCandidates + 1
          }
        }
      }
    else
      let state := {
        flow.value with
        lifecycle := {
          flow.value.lifecycle with
          checkedCandidates := flow.value.lifecycle.checkedCandidates + 1
        }
      }
      let flow := { flow with value := state } |>.charge WorkKind.retention
      if flow.exhausted then
        flow
      else
        match flow.value.retainInferenceWithBudget config candidate flow.budget with
        | .exhausted budget =>
            { flow with budget := budget, exhausted := true }
        | .complete none budget =>
            {
              flow with
              budget := budget
              value := {
                flow.value with
                lifecycle := {
                  flow.value.lifecycle with
                  retentionRejectedCandidates :=
                    flow.value.lifecycle.retentionRejectedCandidates + 1
                }
              }
            }
        | .complete (some (retainedState, newId)) budget =>
            match clauseAt? retainedState.clauses newId with
            | none => { flow with value := retainedState, budget := budget }
            | some retainedClause =>
                match
                    retainedState.backwardDeletionPlanWithBudget
                      config newId retainedClause budget with
                | .exhausted budget =>
                    {
                      flow with
                      value := retainedState
                      budget := budget
                      exhausted := true
                    }
                | .complete plan budget =>
                    {
                      flow with
                      value := retainedState.applyDeletionPlan config plan
                      budget := budget
                    }

/--
Vampire 风格的 given activation：固定生成快照，逐候选消费，并显式返回工作预算状态。
-/
def processGivenWith (config : Config) (state : State) (given : PassiveEntry)
    (budget : WorkBudget)
    (beforeGeneration : State → PassiveEntry → State) : ProcessGivenResult :=
  let forward := state.forwardSimplifyGiven config given budget
  let state := forward.state
  let budget := forward.budget
  if !forward.complete then
    {
      state := {
        state with
        lifecycle := state.lifecycle.recordWorkBudget budget true
      }
      budget := budget
      complete := false
    }
  else
    match forward.given? with
    | none =>
      {
        state := {
          state with
          lifecycle := state.lifecycle.recordWorkBudget budget false
        }
        budget := budget
        complete := true
      }
    | some given =>
        let state := beforeGeneration state given
        let available := state.clauses
        let active := state.active
        let index := state.index
        let workspace := state.givenWorkspace
        let flow :=
          foldGivenCandidates config available index workspace given.clauseId
            {
              value := state
              budget := budget
            }
            (consumeGeneratedCandidate config given.clauseId available active)
        let state := {
          flow.value with
          lifecycle := flow.value.lifecycle.recordGeneration flow.summary
        }
        if flow.exhausted then
          {
            state := {
              state with
              lifecycle := state.lifecycle.recordWorkBudget flow.budget true
            }
            budget := flow.budget
            complete := false
          }
        else
          match state.activateClauseWithBudget config given.clauseId flow.budget with
          | .exhausted budget =>
              {
                state := {
                  state with
                  lifecycle := state.lifecycle.recordWorkBudget budget true
                }
                budget := budget
                complete := false
              }
          | .complete state budget =>
              {
                state := {
                  state with
                  lifecycle := state.lifecycle.recordWorkBudget budget false
                }
                budget := budget
                complete := true
              }

/-- 不带额外 source 开放 hook 的普通 given-clause 转换。 -/
def processGiven (config : Config) (state : State) (given : PassiveEntry)
    (budget : WorkBudget) : ProcessGivenResult :=
  state.processGivenWith config given budget fun state _ => state

end State

/-- 带共享细粒度工作预算的小型饱和循环。 -/
def saturateLoopWithBudget {α : Type} (config : Config) (cdclProbe : CdclProbe α) :
    Nat → WorkBudget → State → State × Status × Option α
  | 0, _, state =>
      if state.containsGlobalEmpty then
        (state, Status.refuted, none)
      else
        match cdclProbe state with
        | some proof => (state, Status.cdclRefuted, some proof)
        | none => (state, Status.fuelExhausted, none)
  | fuel + 1, budget, state =>
      if state.containsGlobalEmpty then
        (state, Status.refuted, none)
      else
        match cdclProbe state with
        | some proof => (state, Status.cdclRefuted, some proof)
        | none =>
            match State.selectGiven? config state with
            | some (given, state) =>
                let step := State.processGiven config state given budget
                if step.complete then
                  saturateLoopWithBudget config cdclProbe fuel step.budget step.state
                else
                  (step.state, Status.fuelExhausted, none)
            | none => (state, Status.saturated, none)

/-- 使用配置工作预算运行小型饱和循环。 -/
def saturateLoop {α : Type} (config : Config) (cdclProbe : CdclProbe α)
    (fuel : Nat) (state : State) : State × Status × Option α :=
  saturateLoopWithBudget config cdclProbe fuel
    (WorkBudget.ofConfig config state.lifecycle.work) state

/-- 按 proof chain 逐步回放，并在同一工作区维护最终数据库摘要。 -/
def replayProofChainSummaryList? (config : Config)
    (workspace : Data.ReplayWorkspace Clause) :
    List ProofStep → Option (Data.ReplaySummary Clause)
  | [] => some workspace.freeze
  | step :: rest =>
      if validProofStep config workspace.items step then
        replayProofChainSummaryList? config
          (workspace.push step.clause (fun clause => clause.size))
          rest
      else
        none

/-- 从输入字句回放唯一 proof chain，并保留完整最终数据库及紧凑摘要。 -/
def replayProofChainSummary? (config : Config) (input : Array Clause)
    (chain : Array ProofStep) : Option (Data.ReplaySummary Clause) :=
  replayProofChainSummaryList? config
    (Data.ReplayWorkspace.fromItems input (fun clause => clause.size))
    chain.toList

/-- 顺序回放唯一 proof chain。保留该接口供冷路径调用。 -/
def replayProofChainList? (config : Config) :
    Array Clause → List ProofStep → Option (Array Clause)
  | available, steps =>
      (replayProofChainSummaryList? config
        (Data.ReplayWorkspace.fromItems available
          (fun clause => clause.size))
        steps).map (·.finalItems)

/-- 从输入字句回放唯一 proof chain。 -/
def replayProofChain (config : Config) (input : Array Clause)
    (chain : Array ProofStep) : Option (Array Clause) :=
  (replayProofChainSummary? config input chain).map (·.finalItems)

namespace Payload

/-- 向规则标签数组加入不重复标签。 -/
def pushCertificateTag (tags : Array Certificate.RuleTag)
    (tag : Certificate.RuleTag) : Array Certificate.RuleTag :=
  if tags.any (fun existing => existing == tag) then tags else tags.push tag

/-- proof chain 中实际出现过的公共规则标签。 -/
def ruleTags (payload : Payload) : Array Certificate.RuleTag :=
  payload.proofChain.foldl
    (fun tags step => pushCertificateTag tags step.rule.certificateTag)
    #[Certificate.RuleTag.firstOrderSuperposition]

/-- 搜索项是否含有原生 lambda/apply/flexible 函数结构。 -/
partial def termHasHOLambdaSyntax : CoreSyntax.Search.Term → Bool
  | CoreSyntax.Search.Term.var _ => false
  | CoreSyntax.Search.Term.bvar .. => true
  | CoreSyntax.Search.Term.fvar sort _ => CoreSyntax.Search.isFlexibleSort sort
  | CoreSyntax.Search.Term.app _ args =>
      args.any termHasHOLambdaSyntax
  | CoreSyntax.Search.Term.apply .. => true
  | CoreSyntax.Search.Term.lam .. => true

/-- 字面量是否含有高阶/lambda 搜索结构。 -/
def literalHasHOLambdaSyntax (literal : CoreSyntax.Search.Literal) : Bool :=
  termHasHOLambdaSyntax literal.left || termHasHOLambdaSyntax literal.right

/-- 字句是否含有高阶/lambda 搜索结构。 -/
def clauseHasHOLambdaSyntax (clause : Clause) : Bool :=
  clause.any literalHasHOLambdaSyntax

/-- 字句数组是否含有高阶/lambda 搜索结构。 -/
def clausesHaveHOLambdaSyntax (clauses : Array Clause) : Bool :=
  clauses.any clauseHasHOLambdaSyntax

/-- proof chain 是否实际使用了 HO/lambda/FOOL 专用规则。 -/
def usesHOLambdaRules (payload : Payload) : Bool :=
  payload.proofChain.any (fun step => step.rule.isHOLambdaRule)

/-- payload 是否属于 HO/lambda superposition 闭合路线。 -/
def usesHOLambdaLayer (payload : Payload) : Bool :=
  usesHOLambdaRules payload ||
    clausesHaveHOLambdaSyntax payload.inputClauses ||
      clausesHaveHOLambdaSyntax payload.liveClauses ||
        clausesHaveHOLambdaSyntax (payload.proofChain.map (fun step => step.clause))

/-- payload 对应的闭合来源。 -/
def closureKind (payload : Payload) : Certificate.ClosureKind :=
  if payload.status == Status.cdclRefuted then
    Certificate.ClosureKind.residualCdcl
  else if payload.usesHOLambdaLayer then
    Certificate.ClosureKind.hoLambdaSuperposition
  else
    Certificate.ClosureKind.firstOrderSuperposition

/-- proof chain 回放后的最终字句数据库。 -/
def finalClauses? (payload : Payload) : Option (Array Clause) :=
  (replayProofChainSummary? payload.config payload.inputClauses payload.proofChain).map
    (·.finalItems)

/-- proof chain 回放后的同一次紧凑摘要。 -/
def replaySummary? (payload : Payload) : Option (Data.ReplaySummary Clause) :=
  replayProofChainSummary? payload.config payload.inputClauses payload.proofChain

/-- checked payload 中的每个派生 step 都必须携带局部资源证书。 -/
def proofChainResourcesComplete (payload : Payload) : Bool :=
  payload.proofChain.all (fun step => step.resource?.isSome)

/-- 反驳状态下，proof chain 回放数据库必须含空字句。 -/
def refutationShapeOkWithSummary (payload : Payload)
    (summary : Data.ReplaySummary Clause) : Bool :=
  match payload.status with
  | Status.refuted => summary.containsEmpty (fun clause => clause.isEmpty)
  | Status.cdclRefuted => true
  | _ => true

/-- 反驳状态下，proof chain 回放数据库必须含空字句。冷路径保留旧接口。 -/
def refutationShapeOk (payload : Payload) : Bool :=
  match payload.status, payload.replaySummary? with
  | Status.refuted, some summary => refutationShapeOkWithSummary payload summary
  | Status.refuted, none => false
  | Status.cdclRefuted, some summary => refutationShapeOkWithSummary payload summary
  | Status.cdclRefuted, none => false
  | _, _ => true

/-- proof chain 回放成功且基本摘要与输出一致。 -/
def check (payload : Payload) : Bool :=
  let replay? := payload.replaySummary?
  clausesArityOk payload.inputClauses &&
    clausesArityOk payload.liveClauses &&
    clausesWithinLimits payload.config payload.inputClauses &&
    clausesWithinLimits payload.config payload.liveClauses &&
    payload.proofChainResourcesComplete &&
    payload.stats.steps == payload.proofChain.size &&
    payload.stats.generated == payload.proofChain.size &&
    payload.stats.verified == payload.proofChain.size &&
    payload.stats.retained == payload.liveClauses.size &&
    payload.stats.fuel == payload.config.fuel &&
    payload.stats.residuals ==
      (if payload.status == Status.refuted || payload.status == Status.cdclRefuted then
        0
      else
        payload.liveClauses.size) &&
    match replay? with
    | some summary =>
        payload.stats.clauses == summary.itemCount &&
          payload.stats.literals == summary.measure &&
          payload.replayHasEmpty == summary.containsEmpty (fun clause => clause.isEmpty) &&
          payload.refutationShapeOkWithSummary summary
    | none => false

/-- checked 且状态为 refuted 时，proof chain 回放数据库含空字句。 -/
theorem containsEmpty_of_check_refuted (payload : Payload)
    (hChecked : Payload.check payload = true)
    (hStatus : payload.status = Status.refuted)
    {finalClauses : Array Clause}
    (hReplay :
      replayProofChain payload.config payload.inputClauses payload.proofChain =
        some finalClauses) :
    containsEmptyClause finalClauses = true := by
  have hSummary : ∃ summary, payload.replaySummary? = some summary := by
    cases hFinal : payload.replaySummary? with
    | none =>
        unfold Payload.check at hChecked
        simp [hFinal] at hChecked
    | some summary =>
        exact ⟨summary, rfl⟩
  rcases hSummary with ⟨summary, hSummary⟩
  have hSummaryReplay :
      replayProofChain payload.config payload.inputClauses payload.proofChain =
        some summary.finalItems := by
    unfold replayProofChain
    change
      (payload.replaySummary?).map (fun summary => summary.finalItems) =
        some summary.finalItems
    rw [hSummary]
    simp
  have hFinalEq : summary.finalItems = finalClauses :=
    Option.some.inj (hSummaryReplay.symm.trans hReplay)
  have hShape : summary.containsEmpty (fun clause => clause.isEmpty) = true := by
    unfold Payload.check at hChecked
    simp [hSummary, hStatus] at hChecked
    have hShape' : payload.refutationShapeOkWithSummary summary = true := hChecked.2.2
    simpa [Payload.refutationShapeOkWithSummary, hStatus] using hShape'
  have hSummaryContains : containsEmptyClause summary.finalItems = true := by
    simpa [Data.ReplaySummary.containsEmpty, containsEmptyClause] using hShape
  simpa [hFinalEq] using hSummaryContains

/-- 从 payload checker 中抽出 proof chain 回放成功的事实。 -/
theorem replayProofChain_isSome (payload : Payload)
    (hChecked : Payload.check payload = true) :
    ∃ finalClauses,
      replayProofChain payload.config payload.inputClauses payload.proofChain =
        some finalClauses := by
  cases hFinal : payload.replaySummary? with
  | some summary =>
      refine ⟨summary.finalItems, ?_⟩
      unfold replayProofChain
      change
        (payload.replaySummary?).map (fun summary => summary.finalItems) =
          some summary.finalItems
      rw [hFinal]
      simp
  | none =>
      unfold Payload.check at hChecked
      simp [hFinal] at hChecked

end Payload

/-- 已通过 checker 的小型超消元结果。 -/
structure Result where
  payload : Payload
  checked : Certificate.Checked Payload Payload.check

namespace Result

/-- 当前叠加核心是否已经推出空字句。 -/
def refuted (result : Result) : Bool :=
  result.payload.status == Status.refuted

/-- 当前叠加核心是否通过内置 CDCL hook 关闭。 -/
def cdclRefuted (result : Result) : Bool :=
  result.payload.status == Status.cdclRefuted

/-- 转成公共证书节点。 -/
def toCoreNode (result : Result) (id : Certificate.NodeId := 0)
    (dependencies : Array Certificate.NodeId := #[]) : Certificate.Node :=
  {
    id := id
    backend :=
      if result.payload.usesHOLambdaLayer then
        Certificate.Backend.hoLambdaSuperposition
      else
        Certificate.Backend.superposition
    phase :=
      if result.payload.usesHOLambdaLayer then
        Certificate.Phase.hoSaturation
      else
        Certificate.Phase.saturation
    label := s!"given-clause superposition saturation ({result.payload.status.label})"
    ruleTags := result.payload.ruleTags
    closureKind? :=
      if result.payload.status == Status.refuted ||
          result.payload.status == Status.cdclRefuted then
        some result.payload.closureKind
      else
        none
    stats := result.payload.stats
    dependencies := dependencies
  }

end Result

/-- 已 checked payload 的 proof chain 回放数据库是否含空字句。 -/
def checkedPayloadContainsEmpty (checked : Certificate.Checked Payload Payload.check) : Bool :=
  checked.payload.replayHasEmpty

/-- 已由唯一 proof chain checker 确认的反驳。 -/
structure CheckedRefutation where
  checked : Certificate.Checked Payload Payload.check
  status_refuted : checked.payload.status = Status.refuted
  replay_empty : checkedPayloadContainsEmpty checked = true

namespace CheckedRefutation

/-- 取出已经通过 `Payload.check` 的底层 payload。 -/
def payload (refutation : CheckedRefutation) : Payload :=
  refutation.checked.payload

/-- 底层 payload 的 checker 证明。 -/
theorem payload_checked (refutation : CheckedRefutation) :
    Payload.check refutation.payload = true :=
  refutation.checked.checked

/-- 已检查反驳证书的输入字句。 -/
def inputClauses (refutation : CheckedRefutation) : Array Clause :=
  refutation.payload.inputClauses

/-- 已检查反驳的唯一 proof chain。 -/
def proofChain (refutation : CheckedRefutation) : Array ProofStep :=
  refutation.payload.proofChain

/-- 已检查反驳的 residual live clauses。 -/
def liveClauses (refutation : CheckedRefutation) : Array Clause :=
  refutation.payload.liveClauses

/-- 已检查反驳的回放数据库。 -/
def finalClauses? (refutation : CheckedRefutation) : Option (Array Clause) :=
  refutation.payload.finalClauses?

/-- 证书状态是否为反驳。 -/
def refuted (refutation : CheckedRefutation) : Bool :=
  refutation.payload.status == Status.refuted

/-- 回放数据库是否含空字句。 -/
def containsEmpty (refutation : CheckedRefutation) : Bool :=
  checkedPayloadContainsEmpty refutation.checked

/-- 已检查反驳证书的状态事实。 -/
theorem status_eq_refuted (refutation : CheckedRefutation) :
    refutation.payload.status = Status.refuted :=
  refutation.status_refuted

/-- 从 checked refutation 中定位回放数据库里的一个实际空字句。 -/
theorem exists_empty_clause (refutation : CheckedRefutation) :
    ∃ finalClauses, ∃ (i : Nat), ∃ hLt : i < finalClauses.size,
      replayProofChain refutation.payload.config refutation.inputClauses
          refutation.proofChain = some finalClauses ∧
        finalClauses[i] = (#[] : Clause) := by
  have hReplay := Payload.replayProofChain_isSome refutation.payload refutation.payload_checked
  rcases hReplay with ⟨finalClauses, hReplay⟩
  have hAny : containsEmptyClause finalClauses = true := by
    exact Payload.containsEmpty_of_check_refuted refutation.payload
      refutation.payload_checked refutation.status_refuted hReplay
  unfold containsEmptyClause at hAny
  rw [Array.any_eq_true] at hAny
  rcases hAny with ⟨i, hLt, hEmpty⟩
  refine ⟨finalClauses, i, hLt, hReplay, ?_⟩
  have hSize : finalClauses[i].size = 0 := by
    simpa using hEmpty
  exact Array.eq_empty_of_size_eq_zero hSize

/-- checked refutation 的 proof chain 回放成功。 -/
theorem replayProofChain_isSome (refutation : CheckedRefutation) :
    ∃ finalClauses,
      replayProofChain refutation.payload.config refutation.inputClauses refutation.proofChain =
        some finalClauses :=
  Payload.replayProofChain_isSome refutation.payload refutation.payload_checked

/-- 从任意已 checked payload 中计算式提取反驳证书。 -/
def ofChecked? (checked : Certificate.Checked Payload Payload.check) :
    Option CheckedRefutation :=
  if hstatus : checked.payload.status = Status.refuted then
    if hempty : checkedPayloadContainsEmpty checked = true then
      some {
        checked := checked
        status_refuted := hstatus
        replay_empty := hempty
      }
    else
      none
  else
    none

/-- 从裸 payload 中计算式构造已检查反驳证书。 -/
def mk? (payload : Payload) : Option CheckedRefutation :=
  match Certificate.Checked.mk? (check := Payload.check) payload with
  | some checked => ofChecked? checked
  | none => none

/-- `mk?` 成功时，得到的 checked refutation 确实封装同一个 payload。 -/
theorem mk?_eq_some_payload {payload : Payload} {cert : CheckedRefutation}
    (h : mk? payload = some cert) :
    cert.payload = payload := by
  unfold mk? at h
  cases hChecked : Certificate.Checked.mk? (check := Payload.check) payload with
  | none =>
      simp [hChecked] at h
  | some checked =>
      unfold ofChecked? at h
      by_cases hStatus : checked.payload.status = Status.refuted
      · by_cases hEmpty : checkedPayloadContainsEmpty checked = true
        · simp [hChecked, hStatus, hEmpty] at h
          cases h
          change checked.payload = payload
          have hCheckedPayload : checked.payload = payload := by
            unfold Certificate.Checked.mk? at hChecked
            split at hChecked <;> simp at hChecked
            cases hChecked
            rfl
          exact hCheckedPayload
        · simp [hChecked, hStatus, hEmpty] at h
      · simp [hChecked, hStatus] at h

end CheckedRefutation

namespace Result

/-- 从普通小型超消元结果中计算式提取已检查反驳证书。 -/
def checkedRefutation? (result : Result) : Option CheckedRefutation :=
  CheckedRefutation.mk? result.payload

end Result

namespace HOLambdaSuperposition

/-!
阶段 7 的 HO/lambda superposition 公共证书 payload。

底层 proof chain 仍由 `Superposition.Payload.check` 回放；这一层只把扩展规则族和闭合
来源暴露给 scheduler/replay bridge，避免后续 soundness 层只能看到“普通 superposition”。
-/

/-- HO/lambda superposition bridge payload。 -/
structure Payload where
  core : Superposition.Payload
  replayChecker : Bool
  deriving Repr, Lean.ToExpr

namespace Payload

/-- 从底层超消元 payload 构造 HO/lambda bridge payload。 -/
def build (core : Superposition.Payload) : Payload :=
  { core := core, replayChecker := Superposition.Payload.check core }

/-- HO/lambda bridge payload 的可计算 checker。 -/
def check (payload : Payload) : Bool :=
  payload.replayChecker &&
    Superposition.Payload.check payload.core &&
      payload.core.usesHOLambdaLayer

/-- 计算式构造 checked HO/lambda bridge payload。 -/
def mk? (core : Superposition.Payload) :
    Option (Certificate.Checked Payload Payload.check) :=
  Certificate.Checked.mk? (check := Payload.check) (build core)

/-- 从普通超消元结果中提取 HO/lambda bridge payload。 -/
def ofResult? (result : Superposition.Result) :
    Option (Certificate.Checked Payload Payload.check) :=
  mk? result.payload

/-- HO/lambda bridge payload 的公共证书节点。 -/
def toCoreNode (payload : Payload) (id : Certificate.NodeId := 0)
    (dependencies : Array Certificate.NodeId := #[])
    (closureKind? : Option Certificate.ClosureKind := some Certificate.ClosureKind.hoLambdaSuperposition) :
    Certificate.Node :=
  {
    id := id
    backend := Certificate.Backend.hoLambdaSuperposition
    phase := Certificate.Phase.hoSaturation
    label := s!"checked HO/lambda superposition ({payload.core.status.label})"
    ruleTags := payload.core.ruleTags
    closureKind? := closureKind?
    stats := payload.core.stats
    dependencies := dependencies
  }

end Payload

end HOLambdaSuperposition

/-- 执行小型超消元饱和，并允许内核在 live residual 上调用 CDCL hook。 -/
def runClausesWithCdclProbe {α : Type}
    (config : Config) (inputClauses : Array Clause) (cdclProbe : CdclProbe α) :
    Except Certificate.Diagnostic (Result × Option α) := do
  let initial : State := State.initial config inputClauses
  let (state, status, cdclResult?) := saturateLoop config cdclProbe config.fuel initial
  let proofChain ←
    if status == Status.refuted then
      match state.firstGlobalEmptyId? with
      | some root =>
          match extractProofChain? inputClauses.size state.steps root with
          | some chain => pure chain
          | none =>
              throw (Certificate.Diagnostic.ofMessage Certificate.Backend.superposition
                Certificate.Phase.backendCheck
                "failed to extract small-superposition proof chain")
      | none =>
          throw (Certificate.Diagnostic.ofMessage Certificate.Backend.superposition
            Certificate.Phase.backendCheck
            "small-superposition refuted status without empty clause")
    else
      pure #[]
  let liveClauses := if status == Status.refuted then #[] else state.liveClauses
  let finalClauseCount :=
    inputClauses.size + proofChain.size
  let finalLiteralCount :=
    clauseLiteralCount inputClauses +
      proofChain.foldl (fun total step => total + step.clause.size) 0
  let replayHasEmpty :=
    containsEmptyClause inputClauses ||
      proofChain.any (fun step => step.clause.isEmpty)
  let stats : Certificate.Stats := {
    steps := proofChain.size
    clauses := finalClauseCount
    literals := finalLiteralCount
    generated := proofChain.size
    retained := liveClauses.size
    verified := proofChain.size
    residuals :=
      if status == Status.refuted || status == Status.cdclRefuted then
        0
      else
        liveClauses.size
    fuel := config.fuel
  }
  let payload : Payload := {
    config := config
    inputClauses := inputClauses
    proofChain := proofChain
    liveClauses := liveClauses
    status := status
    stats := stats
    replayHasEmpty := replayHasEmpty
  }
  match Certificate.Checked.mk? (check := Payload.check) payload with
  | some checked => pure ({ payload := payload, checked := checked }, cdclResult?)
  | none =>
      throw (Certificate.Diagnostic.ofMessage Certificate.Backend.superposition
        Certificate.Phase.backendCheck
        "generated small-superposition payload failed structural check")

/-- 执行小型超消元饱和。 -/
def runClauses (config : Config) (inputClauses : Array Clause) :
    Except Certificate.Diagnostic Result := do
  let (result, _) ← runClausesWithCdclProbe config inputClauses noCdclProbe
  pure result

end Superposition
end Automation
end YesMetaZFC
