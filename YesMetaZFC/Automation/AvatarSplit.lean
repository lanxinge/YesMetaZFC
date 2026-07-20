import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.Resolution

/-!
# AVATAR component splitting 的共享可计算核心

本模块只放搜索层与证书 checker 都需要复算的纯数据算法。它不依赖 SearchDAG 或
大型 DAG，因此两层可信边界可以消费同一套 partition 与 selector 纪律。
-/

namespace YesMetaZFC
namespace Automation
namespace AvatarSplit

abbrev Clause := CoreSyntax.Search.Clause
abbrev GuardSet := PropResolution.Clause

private def pushVariableUnique (values : Array CoreSyntax.Search.Variable)
    (value : CoreSyntax.Search.Variable) : Array CoreSyntax.Search.Variable :=
  if values.contains value then values else values.push value

/-- 一个搜索项中的 typed 自由变量，去重但保留首次出现顺序。 -/
def termVars (term : CoreSyntax.Search.Term) : Array CoreSyntax.Search.Variable :=
  term.variables.foldl pushVariableUnique #[]

/-- 一个 literal 中的 typed 自由变量。 -/
def literalVars (literal : CoreSyntax.Search.Literal) : Array CoreSyntax.Search.Variable :=
  (termVars literal.left).foldl pushVariableUnique (termVars literal.right)

/-- 两个变量集合是否相交。 -/
def varsOverlap (left right : Array CoreSyntax.Search.Variable) : Bool :=
  left.any right.contains

/-- 按索引抽取一个 component clause。越界索引会被丢弃，checker 另行拒绝。 -/
def clauseAtIndices (clause : Clause) (indices : Array Nat) : Clause :=
  indices.filterMap fun index => clause[index]?

/--
检查 literal partitions 是否精确覆盖 `[0, clauseSize)`。

每个 component 必须非空；每个索引必须在范围内且只出现一次；最终不能遗漏任何
literal。空字句唯一允许的 partition 是空数组。
-/
def indexPartitionOk (clauseSize : Nat) (partitions : Array (Array Nat)) : Bool :=
  Id.run do
    if clauseSize == 0 then
      return partitions.isEmpty
    let mut seen := (List.replicate clauseSize false).toArray
    for partition in partitions do
      if partition.isEmpty then
        return false
      for index in partition do
        if h : index < seen.size then
          if seen[index] then
            return false
          else
            seen := seen.set index true h
        else
          return false
    return seen.all id

/--
selector 表必须和 component 数量一致，并由互异正文字组成。

这里保留 component 顺序；SAT skeleton 在外层另行 canonicalize，不能用命题字句排序
破坏 `selectors[index]` 与 partition slot 的对应关系。
-/
def selectorsOk (partitions : Array (Array Nat)) (selectors : GuardSet) : Bool :=
  selectors.size == partitions.size &&
    selectors.all (fun selector => selector.positive) &&
      Id.run do
        let mut seen : GuardSet := #[]
        for selector in selectors do
          if seen.contains selector then
            return false
          else
            seen := seen.push selector
        return true

/-- 读取某个 component 对应的 selector。 -/
def selectorAt? (selectors : GuardSet) (componentIndex : Nat) :
    Option PropResolution.Lit :=
  selectors[componentIndex]?

/--
把一个字句拆成变量连通 components。

ground literal 没有变量，因此各自形成 singleton component；非 ground literal 通过共享
变量的传递闭包归入同一 component。
-/
def splitClause (clause : Clause) : Array (Array Nat × Clause) := Id.run do
  let mut seen := (List.replicate clause.size false).toArray
  let mut components := #[]
  for h : start in [:clause.size] do
    if !seen.getD start false then
      seen := seen.set! start true
      let mut indices := #[start]
      let mut vars := literalVars clause[start]
      let mut changed := true
      while changed do
        changed := false
        for hIndex : index in [:clause.size] do
          if !seen.getD index false then
            let candidateVars := literalVars clause[index]
            if !vars.isEmpty && varsOverlap vars candidateVars then
              seen := seen.set! index true
              indices := indices.push index
              vars := candidateVars.foldl pushVariableUnique vars
              changed := true
      components := components.push (indices, clauseAtIndices clause indices)
  return components

end AvatarSplit
end Automation
end YesMetaZFC
