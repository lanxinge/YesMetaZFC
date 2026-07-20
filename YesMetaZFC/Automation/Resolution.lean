import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.CoreSyntax
import YesMetaZFC.Automation.Data.ClauseArena
import Lean

/-!
# MF1 公共命题 resolution 证书数据

本文件只放 CDCL/resolution 证书的纯数据结构和可计算检查器。它不依赖 Lean `Expr`，
也不直接生成 `Derives` 证明项；后续的 soundness 层会以这里的 checked certificate
作为输入，逐步替换当前 Meta 层的 Hilbert replay。
-/

namespace YesMetaZFC
namespace Automation
namespace PropResolution

/-- 命题 CNF 字句中的文字；`positive = false` 表示负文字。 -/
structure Lit where
  var : Nat
  positive : Bool
  deriving Repr, Inhabited, BEq, ReflBEq, DecidableEq, Lean.ToExpr

/-- 一个字句是文字数组。 -/
abbrev Clause := Array Lit

/-- 单步 resolution：当前字句与 `reason` 以 `pivot` 为主元归结得到 `result`。 -/
structure ResolutionStep where
  pivot : Nat
  reasonIndex : Nat
  reason : Clause
  substitution : CoreSyntax.Search.Substitution := []
  result : Clause
  deriving Repr, Inhabited, Lean.ToExpr

/-- 一条 learned clause 的 resolution 推导。 -/
structure ResolutionDerivation where
  startIndex : Nat
  start : Clause
  steps : Array ResolutionStep
  result : Clause
  deriving Repr, Inhabited, Lean.ToExpr

/-- Tseitin 初始字句的来源。 -/
inductive ClauseOrigin where
  | negForward (root child : Lit)
  | negBackward (root child : Lit)
  | impMain (root left right : Lit)
  | impLeft (root left : Lit)
  | impRight (root right : Lit)
  | rootNegation (root : Lit)
  | residual (index : Nat)
  deriving Repr, Lean.ToExpr

namespace ClauseOrigin

/-- 该初始字句是否为 `¬target` 根假设。 -/
def isRootNegation : ClauseOrigin → Bool
  | rootNegation _ => true
  | _ => false

end ClauseOrigin

/-- 带来源信息的初始字句。 -/
structure InitialClause where
  clause : Clause
  origin : ClauseOrigin
  deriving Repr, Lean.ToExpr

/-!
## 紧凑 CDCL journal

搜索器不再把 decide/propagate/conflict 事件写进核心证书，也不在每个 resolution 步骤
重复保存 reason/result 字句。journal 只保存 ClauseId 和全局步骤 slab 的切片。
-/

/-- journal 中的一步 resolution。 -/
structure CompactResolutionStep where
  pivot : Nat
  /-- 1-based `Data.ClauseId.raw`。 -/
  reason : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 一条 learned clause 的紧凑记录。 -/
structure LearnRecord where
  /-- 1-based learned `Data.ClauseId.raw`。 -/
  clause : Nat
  /-- 1-based conflict-start `Data.ClauseId.raw`。 -/
  start : Nat
  stepsStart : Nat
  stepsLength : Nat
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- learned-only journal。所有 resolution 步骤存放在一个连续 slab 中。 -/
structure LearnJournal where
  steps : Array CompactResolutionStep := #[]
  learns : Array LearnRecord := #[]
  deriving Repr, Inhabited, BEq, Lean.ToExpr

/-- CDCL 搜索器携出的紧凑证明数据。 -/
structure CdclProof where
  arena : Data.ClauseArena
  journal : LearnJournal
  deriving Repr, Inhabited, BEq, Lean.ToExpr

namespace Lit

/-- 文字取反。 -/
def neg (lit : Lit) : Lit :=
  { lit with positive := !lit.positive }

/-- 文字规范序。Lean 的 `Bool` 顺序满足 `false < true`。 -/
def le (left right : Lit) : Bool :=
  left.var < right.var || (left.var == right.var && (!left.positive || right.positive))

/-- 在部分赋值下读取文字真值。 -/
def value? (assignment : Array (Option Bool)) (lit : Lit) : Option Bool :=
  match assignment.getD lit.var none with
  | none => none
  | some value => some (if lit.positive then value else !value)

/-- 让该文字为真所需的变量取值。 -/
def forcedValue (lit : Lit) : Bool :=
  lit.positive

/-- 打包成热路径 literal。 -/
@[inline]
def pack (lit : Lit) : Data.PackedLit :=
  Data.PackedLit.pack lit.var lit.positive

/-- 从热路径 literal 恢复逻辑边界结构。 -/
@[inline]
def ofPacked (lit : Data.PackedLit) : Lit :=
  { var := Data.PackedLit.var lit, positive := Data.PackedLit.positive lit }

/-- 命题 valuation。 -/
abbrev Valuation := Nat → Prop

/-- 命题文字在 valuation 下为真。 -/
def Holds (valuation : Valuation) (lit : Lit) : Prop :=
  if lit.positive then valuation lit.var else ¬ valuation lit.var

end Lit

abbrev Valuation := Lit.Valuation

namespace Clause

/-- 命题字句在 valuation 下为真，即其中至少一个文字为真。 -/
def Satisfies (valuation : Valuation) (clause : Clause) : Prop :=
  ∃ lit, lit ∈ clause.toList ∧ lit.Holds valuation

/-- 空命题字句不可满足。 -/
theorem not_satisfies_empty (valuation : Valuation) :
    ¬ Satisfies valuation (#[] : Clause) := by
  intro h
  rcases h with ⟨lit, hMem, _hLit⟩
  simp at hMem

/-- 字句中的真文字给出字句满足性。 -/
theorem satisfies_of_mem {valuation : Valuation} {clause : Clause} {lit : Lit}
    (hMem : lit ∈ clause.toList) (hLit : lit.Holds valuation) :
    Satisfies valuation clause :=
  ⟨lit, hMem, hLit⟩

end Clause

/-- 命题字句数据库在 valuation 下逐项满足。 -/
def DatabaseSatisfies (valuation : Valuation) (database : Array Clause) : Prop :=
  ∀ clause, clause ∈ database.toList → Clause.Satisfies valuation clause

/-- 数据库满足性在追加一个已满足 learned clause 后保持。 -/
theorem DatabaseSatisfies.push {valuation : Valuation} {database : Array Clause}
    {clause : Clause}
    (hDb : DatabaseSatisfies valuation database)
    (hClause : Clause.Satisfies valuation clause) :
    DatabaseSatisfies valuation (database.push clause) := by
  intro target hMem
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hMem | hEq
  · exact hDb target hMem
  · subst hEq
    exact hClause

/-- 把逻辑边界字句打包成标量数组。 -/
def packClause (clause : Clause) : Array Data.PackedLit :=
  clause.map Lit.pack

/-- 从 packed literal 数组恢复逻辑边界字句。 -/
def unpackClause (clause : Array Data.PackedLit) : Clause :=
  clause.map Lit.ofPacked

/-- 从 arena 物化一个逻辑字句。 -/
def arenaClause (arena : Data.ClauseArena) (id : Data.ClauseId) : Clause :=
  unpackClause (arena.packedClause id)

/-- 直接比较 arena 字句与逻辑边界字句，不构造临时 packed 数组。 -/
def arenaClauseEq (arena : Data.ClauseArena) (id : Data.ClauseId) (clause : Clause) : Bool :=
  match arena.header? id with
  | none => false
  | some header =>
      if header.length != clause.size then
        false
      else
        Id.run do
          for h : position in [:clause.size] do
            if arena.literals[header.start + position]? != some clause[position].pack then
              return false
          return true

namespace LearnJournal

/-- 记录的 resolution-step 切片是否在 slab 范围内。 -/
def stepSliceValid (journal : LearnJournal) (record : LearnRecord) : Bool :=
  record.stepsStart + record.stepsLength <= journal.steps.size

/-- 物化记录对应的紧凑步骤切片。只在 checker/replay 边界使用。 -/
def stepsFor (journal : LearnJournal) (record : LearnRecord) :
    Array CompactResolutionStep :=
  journal.steps.extract record.stepsStart (record.stepsStart + record.stepsLength)

end LearnJournal

/-- 字句中是否包含给定文字。 -/
def clauseContainsLit (clause : Clause) (lit : Lit) : Bool :=
  clause.any fun other => other == lit

/-- 字句成员反射到 `clauseContainsLit`。 -/
theorem clauseContainsLit_of_mem {clause : Clause} {lit : Lit}
    (hMem : lit ∈ clause.toList) : clauseContainsLit clause lit = true := by
  rw [clauseContainsLit]
  exact Array.any_eq_true'.mpr ⟨lit, Array.mem_def.mpr hMem, beq_self_eq_true lit⟩

/-- 字句是否包含某文字的反文字。 -/
def clauseContainsComplement (clause : Clause) (lit : Lit) : Bool :=
  clauseContainsLit clause lit.neg

/-- 原始字句中是否已经出现互补文字。 -/
def clauseTautological (clause : Clause) : Bool :=
  clause.any fun lit => clauseContainsComplement clause lit

/-- 字句中是否包含某个变量的文字。 -/
def clauseContainsVar (clause : Clause) (var : Nat) : Bool :=
  clause.any fun lit => lit.var == var

/-- 指定命题变量和极性的文字。 -/
def pivotLit (pivot : Nat) (positive : Bool) : Lit :=
  { var := pivot, positive := positive }

/-- 字句是否包含指定极性的主元文字。 -/
def clauseContainsPivotSign (clause : Clause) (pivot : Nat) (positive : Bool) : Bool :=
  clauseContainsLit clause (pivotLit pivot positive)

/-- 字句里实际出现的主元文字会反射到对应极性的 pivot 检查。 -/
theorem clauseContainsPivotSign_of_mem_var {clause : Clause} {lit : Lit} {pivot : Nat}
    (hMem : lit ∈ clause.toList) (hVar : lit.var = pivot) :
    clauseContainsPivotSign clause pivot lit.positive = true := by
  subst pivot
  simpa [clauseContainsPivotSign, pivotLit] using
    clauseContainsLit_of_mem (clause := clause) (lit := lit) hMem

/-- resolution 主元在两个父字句中的方向。 -/
inductive ResolutionOrientation where
  | leftPositive
  | leftNegative
  deriving Repr, Inhabited, DecidableEq

namespace ResolutionOrientation

/-- 左父字句中的主元极性。 -/
def leftSign : ResolutionOrientation → Bool
  | leftPositive => true
  | leftNegative => false

/-- 右父字句中的主元极性。 -/
def rightSign : ResolutionOrientation → Bool
  | leftPositive => false
  | leftNegative => true

end ResolutionOrientation

/--
两个父字句是否以 `pivot` 为合法互补主元。

为了让 `resolveClause` 的“删除两个父字句中所有 pivot 文字”具有可靠对象逻辑解释，
这里要求每个父字句只在一个极性上含有该主元，并且两个父字句的极性互补。
-/
def resolutionOrientation? (left right : Clause) (pivot : Nat) :
    Option ResolutionOrientation :=
  let leftPos := clauseContainsPivotSign left pivot true
  let leftNeg := clauseContainsPivotSign left pivot false
  let rightPos := clauseContainsPivotSign right pivot true
  let rightNeg := clauseContainsPivotSign right pivot false
  if leftPos && !leftNeg && rightNeg && !rightPos then
    some ResolutionOrientation.leftPositive
  else if leftNeg && !leftPos && rightPos && !rightNeg then
    some ResolutionOrientation.leftNegative
  else
    none

/-- `leftPositive` 分支暴露的主元极性事实。 -/
theorem resolutionOrientation_leftPositive_facts {left right : Clause} {pivot : Nat}
    (h : resolutionOrientation? left right pivot = some ResolutionOrientation.leftPositive) :
    clauseContainsPivotSign left pivot true = true ∧
      clauseContainsPivotSign left pivot false = false ∧
      clauseContainsPivotSign right pivot false = true ∧
      clauseContainsPivotSign right pivot true = false := by
  unfold resolutionOrientation? at h
  simp at h
  exact h

/-- `leftNegative` 分支暴露的主元极性事实。 -/
theorem resolutionOrientation_leftNegative_facts {left right : Clause} {pivot : Nat}
    (h : resolutionOrientation? left right pivot = some ResolutionOrientation.leftNegative) :
    clauseContainsPivotSign left pivot false = true ∧
      clauseContainsPivotSign left pivot true = false ∧
      clauseContainsPivotSign right pivot true = true ∧
      clauseContainsPivotSign right pivot false = false := by
  unfold resolutionOrientation? at h
  by_cases hFirst : clauseContainsPivotSign left pivot true &&
      !clauseContainsPivotSign left pivot false &&
        clauseContainsPivotSign right pivot false &&
          !clauseContainsPivotSign right pivot true
  · simp [hFirst] at h
  · simp [hFirst] at h
    exact h

/-- 两个父字句是否以 `pivot` 为合法互补主元。 -/
def resolutionCompatible (left right : Clause) (pivot : Nat) : Bool :=
  (resolutionOrientation? left right pivot).isSome

/--
单步归结的可回放计划。

搜索层仍然只保存紧凑的 `ResolutionStep`；soundness/replay 层会先把它展开成
这个结构，再按 `orientation` 选择对象逻辑里的对应归结引理。
-/
structure ResolutionPlan where
  pivot : Nat
  orientation : ResolutionOrientation
  leftRest : Clause
  rightRest : Clause
  result : Clause
  deriving Repr, Inhabited

/-- 向字句中加入文字；若已经存在则保持不变。 -/
def pushLitUnique (clause : Clause) (lit : Lit) : Clause :=
  if clauseContainsLit clause lit then clause else clause.push lit

/-- 插入到已规范排序且无重复的文字列表中。 -/
def insertCanonicalLitList : List Lit → Lit → List Lit
  | [], lit => [lit]
  | current :: rest, lit =>
      if current = lit then
        current :: rest
      else if Lit.le lit current then
        lit :: current :: rest
      else
        current :: insertCanonicalLitList rest lit

/-- 插入到已规范排序且无重复的字句中。 -/
def insertCanonicalLit (clause : Clause) (lit : Lit) : Clause :=
  (insertCanonicalLitList clause.toList lit).toArray

/-- 列表版字句规范化：稳定排序并删除重复文字。 -/
def canonicalClauseList : List Lit → List Lit
  | [] => []
  | lit :: rest => insertCanonicalLitList (canonicalClauseList rest) lit

/-- 子句规范化：稳定排序并删除重复文字。重言式由调用方决定是否丢弃。 -/
def canonicalClause (clause : Clause) : Clause :=
  (canonicalClauseList clause.toList).toArray

/-- 插入规范列表不会丢失旧文字。 -/
theorem mem_insertCanonicalLitList_of_mem {old lit : Lit} :
    ∀ {lits : List Lit}, old ∈ lits → old ∈ insertCanonicalLitList lits lit
  | [], h => by cases h
  | current :: rest, h => by
      by_cases hEq : current = lit
      · simpa [insertCanonicalLitList, hEq] using h
      · by_cases hLe : Lit.le lit current
        · rw [insertCanonicalLitList]
          simp [hEq, hLe]
          rw [List.mem_cons] at h
          rcases h with hOld | hRest
          · exact Or.inr (Or.inl hOld)
          · exact Or.inr (Or.inr hRest)
        · rw [insertCanonicalLitList]
          simp [hEq, hLe]
          rw [List.mem_cons] at h
          rcases h with hOld | hRest
          · exact Or.inl hOld
          · exact Or.inr (mem_insertCanonicalLitList_of_mem hRest)

/-- 插入规范列表后，新文字一定出现。 -/
theorem mem_insertCanonicalLitList_self (lits : List Lit) (lit : Lit) :
    lit ∈ insertCanonicalLitList lits lit := by
  induction lits with
  | nil =>
      simp [insertCanonicalLitList]
  | cons current rest ih =>
      by_cases hEq : current = lit
      · rw [insertCanonicalLitList]
        simp [hEq]
      · by_cases hLe : Lit.le lit current
        · rw [insertCanonicalLitList]
          simp [hEq, hLe]
        · rw [insertCanonicalLitList]
          simp [hEq, hLe]
          exact Or.inr ih

/-- 规范化列表保留原列表中的每个文字。 -/
theorem mem_canonicalClauseList_of_mem {lit : Lit} :
    ∀ {lits : List Lit}, lit ∈ lits → lit ∈ canonicalClauseList lits
  | [], h => by cases h
  | current :: rest, h => by
      rw [List.mem_cons] at h
      rcases h with hHead | hTail
      · subst hHead
        exact mem_insertCanonicalLitList_self (canonicalClauseList rest) lit
      · exact mem_insertCanonicalLitList_of_mem
          (mem_canonicalClauseList_of_mem (lits := rest) hTail)

/-- 规范化字句保留原字句中的每个文字。 -/
theorem mem_canonicalClause_of_mem {clause : Clause} {lit : Lit}
    (hMem : lit ∈ clause.toList) :
    lit ∈ (canonicalClause clause).toList := by
  simpa [canonicalClause] using mem_canonicalClauseList_of_mem hMem

/-- 可保留的规范字句。重言式在 CNF/learned 入库前统一丢弃。 -/
def canonicalClause? (clause : Clause) : Option Clause :=
  if clauseTautological clause then
    none
  else
    some (canonicalClause clause)

namespace ClauseOrigin

/-- `ClauseOrigin` 在 Tseitin 反射证书中承诺生成的原始字句形状。 -/
def rawExpectedClause? : ClauseOrigin → Option Clause
  | negForward root child => some #[root.neg, child.neg]
  | negBackward root child => some #[root, child]
  | impMain root left right => some #[root.neg, left.neg, right]
  | impLeft root left => some #[root, left]
  | impRight root right => some #[root, right.neg]
  | rootNegation root => some #[root.neg]
  | residual _ => none

/-- `ClauseOrigin` 对应的规范字句形状。 -/
def expectedClause? (origin : ClauseOrigin) : Option Clause :=
  origin.rawExpectedClause?.map canonicalClause

end ClauseOrigin

/-- 当前证书检查器采用顺序敏感的字句相等。 -/
def clauseEq (left right : Clause) : Bool :=
  decide (left = right)

/-- 布尔字句相等的反射引理，供 checked payload replay 使用。 -/
theorem clauseEq_eq {left right : Clause} :
    clauseEq left right = true ↔ left = right := by
  simp [clauseEq]

/-- 列表版：删除所有主元文字，保留其他文字的原始顺序。 -/
def erasePivotList (pivot : Nat) : List Lit → List Lit
  | [] => []
  | lit :: rest =>
      if lit.var == pivot then
        erasePivotList pivot rest
      else
        lit :: erasePivotList pivot rest

/-- 删除所有主元文字，保留其他文字的原始顺序。 -/
def erasePivot (clause : Clause) (pivot : Nat) : Clause :=
  (erasePivotList pivot clause.toList).toArray

/-- 按原始数组形态执行一步 resolution。只供 soundness 的结构引理定位 raw 形态。 -/
def resolveClauseRaw (learned reason : Clause) (pivot : Nat) : Clause :=
  erasePivot learned pivot ++ erasePivot reason pivot

/-- 按证书规范形态执行一步 resolution：去主元后立即 canonicalize。 -/
def resolveClause (learned reason : Clause) (pivot : Nat) : Clause :=
  canonicalClause (resolveClauseRaw learned reason pivot)

/-- 从两个父字句计算归结计划。 -/
def resolutionPlan? (left right : Clause) (pivot : Nat) : Option ResolutionPlan :=
  match resolutionOrientation? left right pivot with
  | none => none
  | some orientation =>
      let leftRest := erasePivot left pivot
      let rightRest := erasePivot right pivot
      some {
        pivot := pivot
        orientation := orientation
        leftRest := leftRest
        rightRest := rightRest
        result := canonicalClause (leftRest ++ rightRest)
      }

/-- 归结计划记录的方向正是计算得到的互补方向。 -/
theorem resolutionPlan_orientation {left right : Clause} {pivot : Nat}
    {plan : ResolutionPlan}
    (h : resolutionPlan? left right pivot = some plan) :
    resolutionOrientation? left right pivot = some plan.orientation := by
  cases hOrient : resolutionOrientation? left right pivot with
  | none =>
      simp [resolutionPlan?, hOrient] at h
  | some orientation =>
      simp [resolutionPlan?, hOrient] at h
      cases h
      rfl

/-- 归结计划记录的结果与核心 `resolveClause` 完全一致。 -/
theorem resolutionPlan_result {left right : Clause} {pivot : Nat}
    {plan : ResolutionPlan}
    (h : resolutionPlan? left right pivot = some plan) :
    plan.result = resolveClause left right pivot := by
  cases hOrient : resolutionOrientation? left right pivot with
  | none =>
      simp [resolutionPlan?, hOrient] at h
  | some orientation =>
      simp [resolutionPlan?, hOrient] at h
      cases h
      rfl

/-- 非 pivot 文字在删除 pivot 时保留。 -/
theorem mem_erasePivotList_of_mem_var_ne {pivot : Nat} {lit : Lit} :
    ∀ {lits : List Lit}, lit ∈ lits → lit.var ≠ pivot → lit ∈ erasePivotList pivot lits
  | [], hMem, _ => by cases hMem
  | current :: rest, hMem, hNe => by
      simp [erasePivotList] at hMem ⊢
      by_cases hCurrent : current.var = pivot
      · simp [hCurrent]
        rcases hMem with hHead | hTail
        · subst hHead
          exact (hNe hCurrent).elim
        · exact mem_erasePivotList_of_mem_var_ne hTail hNe
      · simp [hCurrent]
        rcases hMem with hHead | hTail
        · exact Or.inl hHead
        · exact Or.inr (mem_erasePivotList_of_mem_var_ne hTail hNe)

/-- 非 pivot 文字在字句删除 pivot 后保留。 -/
theorem mem_erasePivot_of_mem_var_ne {pivot : Nat} {clause : Clause} {lit : Lit}
    (hMem : lit ∈ clause.toList) (hNe : lit.var ≠ pivot) :
    lit ∈ (erasePivot clause pivot).toList := by
  simpa [erasePivot] using mem_erasePivotList_of_mem_var_ne (pivot := pivot) hMem hNe

/-- 左父字句中的非 pivot 文字会进入归结结果。 -/
theorem mem_resolveClause_left_of_mem_var_ne {pivot : Nat} {left right : Clause}
    {lit : Lit} (hMem : lit ∈ left.toList) (hNe : lit.var ≠ pivot) :
    lit ∈ (resolveClause left right pivot).toList := by
  apply mem_canonicalClause_of_mem
  have hLeft : lit ∈ (erasePivot left pivot).toList :=
    mem_erasePivot_of_mem_var_ne (pivot := pivot) hMem hNe
  have hRaw : lit ∈ (erasePivot left pivot).toList ++ (erasePivot right pivot).toList :=
    List.mem_append_left _ hLeft
  simpa [resolveClause, resolveClauseRaw] using hRaw

/-- 右父字句中的非 pivot 文字会进入归结结果。 -/
theorem mem_resolveClause_right_of_mem_var_ne {pivot : Nat} {left right : Clause}
    {lit : Lit} (hMem : lit ∈ right.toList) (hNe : lit.var ≠ pivot) :
    lit ∈ (resolveClause left right pivot).toList := by
  apply mem_canonicalClause_of_mem
  have hRight : lit ∈ (erasePivot right pivot).toList :=
    mem_erasePivot_of_mem_var_ne (pivot := pivot) hMem hNe
  have hRaw : lit ∈ (erasePivot left pivot).toList ++ (erasePivot right pivot).toList :=
    List.mem_append_right _ hRight
  simpa [resolveClause, resolveClauseRaw] using hRaw

/-- 单步命题 resolution plan 的语义 soundness。 -/
theorem resolutionPlan_sound {valuation : Valuation} {left right : Clause}
    {pivot : Nat} {plan : ResolutionPlan}
    (hPlan : resolutionPlan? left right pivot = some plan)
    (hLeft : Clause.Satisfies valuation left)
    (hRight : Clause.Satisfies valuation right) :
    Clause.Satisfies valuation plan.result := by
  have hPlanResult : plan.result = resolveClause left right pivot :=
    resolutionPlan_result hPlan
  have hOrient := resolutionPlan_orientation hPlan
  rcases hLeft with ⟨leftLit, hLeftMem, hLeftHolds⟩
  rcases hRight with ⟨rightLit, hRightMem, hRightHolds⟩
  cases hOrientation : plan.orientation with
  | leftPositive =>
      simp [hOrientation] at hOrient
      rcases resolutionOrientation_leftPositive_facts hOrient with
        ⟨_hLeftPos, hLeftNeg, _hRightNeg, hRightPos⟩
      by_cases hLeftVar : leftLit.var = pivot
      · have hLeftSign : leftLit.positive = true := by
          cases hSign : leftLit.positive
          · have hContains := clauseContainsPivotSign_of_mem_var hLeftMem hLeftVar
            simp [hSign, hLeftNeg] at hContains
          · rfl
        have hVal : valuation pivot := by
          simpa [Lit.Holds, hLeftVar, hLeftSign] using hLeftHolds
        by_cases hRightVar : rightLit.var = pivot
        · have hRightSign : rightLit.positive = false := by
            cases hSign : rightLit.positive
            · rfl
            · have hContains := clauseContainsPivotSign_of_mem_var hRightMem hRightVar
              simp [hSign, hRightPos] at hContains
          have hNotVal : ¬ valuation pivot := by
            simpa [Lit.Holds, hRightVar, hRightSign] using hRightHolds
          exact (hNotVal hVal).elim
        · have hMem := mem_resolveClause_right_of_mem_var_ne
            (pivot := pivot) (left := left) (right := right) hRightMem hRightVar
          rw [hPlanResult]
          exact Clause.satisfies_of_mem hMem hRightHolds
      · have hMem := mem_resolveClause_left_of_mem_var_ne
          (pivot := pivot) (left := left) (right := right) hLeftMem hLeftVar
        rw [hPlanResult]
        exact Clause.satisfies_of_mem hMem hLeftHolds
  | leftNegative =>
      simp [hOrientation] at hOrient
      rcases resolutionOrientation_leftNegative_facts hOrient with
        ⟨_hLeftNeg, hLeftPos, _hRightPos, hRightNeg⟩
      by_cases hLeftVar : leftLit.var = pivot
      · have hLeftSign : leftLit.positive = false := by
          cases hSign : leftLit.positive
          · rfl
          · have hContains := clauseContainsPivotSign_of_mem_var hLeftMem hLeftVar
            simp [hSign, hLeftPos] at hContains
        have hNotVal : ¬ valuation pivot := by
          simpa [Lit.Holds, hLeftVar, hLeftSign] using hLeftHolds
        by_cases hRightVar : rightLit.var = pivot
        · have hRightSign : rightLit.positive = true := by
            cases hSign : rightLit.positive
            · have hContains := clauseContainsPivotSign_of_mem_var hRightMem hRightVar
              simp [hSign, hRightNeg] at hContains
            · rfl
          have hVal : valuation pivot := by
            simpa [Lit.Holds, hRightVar, hRightSign] using hRightHolds
          exact (hNotVal hVal).elim
        · have hMem := mem_resolveClause_right_of_mem_var_ne
            (pivot := pivot) (left := left) (right := right) hRightMem hRightVar
          rw [hPlanResult]
          exact Clause.satisfies_of_mem hMem hRightHolds
      · have hMem := mem_resolveClause_left_of_mem_var_ne
          (pivot := pivot) (left := left) (right := right) hLeftMem hLeftVar
        rw [hPlanResult]
        exact Clause.satisfies_of_mem hMem hLeftHolds

/-!
## 紧凑 CDCL resolution 检查内核

CDCL journal 直接以 `CompactResolutionStep` 的连续切片作为可信边界。检查器只保留当前
字句和 slab 游标，每一步读取一次 reason、计算一次归结计划，不构造通用
`ResolutionStep`/`ResolutionDerivation` 中间数组。
-/

/-- 从紧凑 step slab 单遍检查一条 resolution 链。 -/
def compactResolutionStepsValidAgainst (database : Array Clause) (journal : LearnJournal) :
    Nat → Nat → Clause → Clause → Bool
  | 0, _, current, target =>
      clauseEq current target
  | remaining + 1, stepIndex, current, target =>
      if hStep : stepIndex < journal.steps.size then
        let step := journal.steps[stepIndex]
        let reasonId : Data.ClauseId := Data.Id.ofNat step.reason
        match reasonId.index? with
        | none => false
        | some reasonIndex =>
            if hReason : reasonIndex < database.size then
              match resolutionPlan? current database[reasonIndex] step.pivot with
              | none => false
              | some plan =>
                  compactResolutionStepsValidAgainst database journal remaining
                    (stepIndex + 1) plan.result target
            else
              false
      else
        false

/--
检查一条紧凑 resolution step，并返回下一条当前字句。

这个单步视图只用于把大型 journal replay 拆成可共享的局部内核等式；原有递归 checker
仍是最终可信边界。
-/
def compactResolutionStep? (database : Array Clause) (journal : LearnJournal)
    (stepIndex : Nat) (current : Clause) : Option Clause :=
  if hStep : stepIndex < journal.steps.size then
    let step := journal.steps[stepIndex]
    let reasonId : Data.ClauseId := Data.Id.ofNat step.reason
    match reasonId.index? with
    | none => none
    | some reasonIndex =>
        if hReason : reasonIndex < database.size then
          match resolutionPlan? current database[reasonIndex] step.pivot with
          | none => none
          | some plan => some plan.result
        else
          none
  else
    none

/-- 递归 checker 的非空分支等于一次单步检查再继续。 -/
theorem compactResolutionStepsValidAgainst_succ
    (database : Array Clause) (journal : LearnJournal)
    (remaining stepIndex : Nat) (current target : Clause) :
    compactResolutionStepsValidAgainst database journal (remaining + 1)
        stepIndex current target =
      match compactResolutionStep? database journal stepIndex current with
      | some next =>
          compactResolutionStepsValidAgainst database journal remaining
            (stepIndex + 1) next target
      | none => false := by
  by_cases hStep : stepIndex < journal.steps.size
  · let step := journal.steps[stepIndex]
    cases hReasonIndex :
        (Data.Id.ofNat step.reason : Data.ClauseId).index? with
    | none =>
        simp [compactResolutionStepsValidAgainst, compactResolutionStep?,
          hStep, step, hReasonIndex]
    | some reasonIndex =>
        by_cases hReason : reasonIndex < database.size
        · cases hPlan : resolutionPlan? current database[reasonIndex] step.pivot with
          | none =>
              simp [compactResolutionStepsValidAgainst, compactResolutionStep?,
                hStep, step, hReasonIndex, hReason, hPlan]
          | some plan =>
              simp [compactResolutionStepsValidAgainst, compactResolutionStep?,
                hStep, step, hReasonIndex, hReason, hPlan]
        · simp [compactResolutionStepsValidAgainst, compactResolutionStep?,
            hStep, step, hReasonIndex, hReason]
  · simp [compactResolutionStepsValidAgainst, compactResolutionStep?, hStep]

/-- 逐 step 携带紧凑 resolution checker 的局部状态转移证明。 -/
inductive CheckedCompactResolutionTrace
    (database : Array Clause) (journal : LearnJournal) (target : Clause) :
    Nat → Nat → Clause → Prop where
  | done {stepIndex current}
      (hTarget : clauseEq current target = true) :
      CheckedCompactResolutionTrace database journal target 0 stepIndex current
  | step {remaining stepIndex current next}
      (hNext : compactResolutionStep? database journal stepIndex current = some next)
      (tail :
        CheckedCompactResolutionTrace database journal target remaining
          (stepIndex + 1) next) :
      CheckedCompactResolutionTrace database journal target (remaining + 1)
        stepIndex current

namespace CheckedCompactResolutionTrace

/-- 逐 step 状态转移证明线性合成原递归 resolution checker。 -/
theorem check_eq_true
    {database : Array Clause} {journal : LearnJournal} {target : Clause}
    {remaining stepIndex : Nat} {current : Clause}
    (trace :
      CheckedCompactResolutionTrace database journal target remaining stepIndex current) :
    compactResolutionStepsValidAgainst database journal remaining stepIndex current target =
      true := by
  induction trace with
  | done hTarget =>
      simpa [compactResolutionStepsValidAgainst] using hTarget
  | step hNext _ ih =>
      rw [compactResolutionStepsValidAgainst_succ, hNext]
      exact ih

end CheckedCompactResolutionTrace

/--
检查单条 learned record。

`learnedIndex = database.size` 保证 arena 与顺序数据库同构；reason 只允许引用当前数据库
中的既有字句，因此不必在每个 resolution 步骤重复比较 arena 字句。
-/
def compactLearnRecordValidAgainst (database : Array Clause) (proof : CdclProof)
    (record : LearnRecord) : Bool :=
  let startId : Data.ClauseId := Data.Id.ofNat record.start
  let learnedId : Data.ClauseId := Data.Id.ofNat record.clause
  match startId.index?, learnedId.index? with
  | some startIndex, some learnedIndex =>
      if hStart : startIndex < database.size then
        learnedIndex == database.size &&
          proof.journal.stepSliceValid record &&
          compactResolutionStepsValidAgainst database proof.journal record.stepsLength
            record.stepsStart database[startIndex] (arenaClause proof.arena learnedId)
      else
        false
  | _, _ => false

/-- 单条 learned record 的头部检查与逐 step trace 合成原 checker。 -/
theorem compactLearnRecordValidAgainst_eq_true_of_trace
    {database : Array Clause} {proof : CdclProof} {record : LearnRecord}
    {startIndex learnedIndex : Nat} {startClause : Clause}
    (hStartId :
      (Data.Id.ofNat record.start : Data.ClauseId).index? = some startIndex)
    (hLearnedId :
      (Data.Id.ofNat record.clause : Data.ClauseId).index? = some learnedIndex)
    (hStartClause : database[startIndex]? = some startClause)
    (hLearnedIndex : learnedIndex = database.size)
    (hSlice : proof.journal.stepSliceValid record = true)
    (trace :
      CheckedCompactResolutionTrace database proof.journal
        (arenaClause proof.arena (Data.Id.ofNat record.clause))
        record.stepsLength record.stepsStart startClause) :
    compactLearnRecordValidAgainst database proof record = true := by
  have hStart : startIndex < database.size :=
    (Array.getElem?_eq_some_iff.mp hStartClause).1
  have hStartGet : database[startIndex] = startClause :=
    (Array.getElem?_eq_some_iff.mp hStartClause).2
  have hSteps := trace.check_eq_true
  simp [compactLearnRecordValidAgainst, hStartId, hLearnedId, hStart,
    hStartGet, hLearnedIndex, hSlice, hSteps]

/-- 紧凑 resolution step slab 的语义 soundness。 -/
theorem compactResolutionStepsValidAgainst_sound {valuation : Valuation}
    {database : Array Clause} {journal : LearnJournal}
    (hDb : DatabaseSatisfies valuation database) :
    ∀ {remaining stepIndex current target},
      Clause.Satisfies valuation current →
      compactResolutionStepsValidAgainst database journal remaining stepIndex current target = true →
      Clause.Satisfies valuation target
  | 0, _stepIndex, current, target, hCurrent, hValid => by
      have hEq : current = target :=
        clauseEq_eq.mp (by simpa [compactResolutionStepsValidAgainst] using hValid)
      simpa [hEq] using hCurrent
  | remaining + 1, stepIndex, current, target, hCurrent, hValid => by
      by_cases hStep : stepIndex < journal.steps.size
      · simp [compactResolutionStepsValidAgainst, hStep] at hValid
        cases hReasonId :
            (Data.Id.ofNat (journal.steps[stepIndex]).reason : Data.ClauseId).index? with
        | none =>
            simp [hReasonId] at hValid
        | some reasonIndex =>
            simp [hReasonId] at hValid
            rcases hValid with ⟨hReason, hValid⟩
            cases hPlan : resolutionPlan? current database[reasonIndex]
                (journal.steps[stepIndex]).pivot with
            | none =>
                simp [hPlan] at hValid
            | some plan =>
                simp [hPlan] at hValid
                have hReasonSat : Clause.Satisfies valuation database[reasonIndex] :=
                  hDb database[reasonIndex] (Array.getElem_mem_toList hReason)
                have hNext : Clause.Satisfies valuation plan.result :=
                  resolutionPlan_sound hPlan hCurrent hReasonSat
                exact compactResolutionStepsValidAgainst_sound hDb hNext hValid
      · simp [compactResolutionStepsValidAgainst, hStep] at hValid

/-- 单条 learned record 通过 checker 时，其 learned arena 字句语义成立。 -/
theorem compactLearnRecordValidAgainst_sound {valuation : Valuation}
    {database : Array Clause} {proof : CdclProof} {record : LearnRecord}
    (hDb : DatabaseSatisfies valuation database)
    (hValid : compactLearnRecordValidAgainst database proof record = true) :
    Clause.Satisfies valuation
      (arenaClause proof.arena (Data.Id.ofNat record.clause : Data.ClauseId)) := by
  unfold compactLearnRecordValidAgainst at hValid
  cases hStartId : (Data.Id.ofNat record.start : Data.ClauseId).index? with
  | none =>
      simp [hStartId] at hValid
  | some startIndex =>
      simp [hStartId] at hValid
      cases hLearnedId : (Data.Id.ofNat record.clause : Data.ClauseId).index? with
      | none =>
          simp [hLearnedId] at hValid
      | some learnedIndex =>
          by_cases hStart : startIndex < database.size
          · simp [hLearnedId, hStart] at hValid
            rcases hValid with ⟨⟨_hLearnedIndex, _hSlice⟩, hSteps⟩
            have hStartSat : Clause.Satisfies valuation database[startIndex] :=
              hDb database[startIndex] (Array.getElem_mem_toList hStart)
            exact compactResolutionStepsValidAgainst_sound hDb hStartSat hSteps
          · simp [hLearnedId, hStart] at hValid

/-- 检查单步 resolution，并返回后续 replay 可直接消费的计划。 -/
def resolutionStepPlan? (current reason : Clause) (step : ResolutionStep) :
    Option ResolutionPlan :=
  if step.substitution == [] && clauseEq reason step.reason then
    match resolutionPlan? current reason step.pivot with
    | none => none
    | some plan =>
        if clauseEq plan.result step.result then
          some plan
        else
          none
  else
    none

/-- 单步计划检查通过时，证书记录的 `reason` 与数据库中的父字句一致。 -/
theorem resolutionStepPlan_reason {current reason : Clause} {step : ResolutionStep}
    {plan : ResolutionPlan}
    (h : resolutionStepPlan? current reason step = some plan) :
    reason = step.reason := by
  unfold resolutionStepPlan? at h
  simp at h
  exact clauseEq_eq.mp h.1.2

/-- 单步计划检查通过时，计划方向正是父字句的互补方向。 -/
theorem resolutionStepPlan_orientation {current reason : Clause} {step : ResolutionStep}
    {plan : ResolutionPlan}
    (h : resolutionStepPlan? current reason step = some plan) :
    resolutionOrientation? current reason step.pivot = some plan.orientation := by
  unfold resolutionStepPlan? at h
  simp at h
  rcases h with ⟨_, hPlan⟩
  cases hRawPlan : resolutionPlan? current reason step.pivot with
  | none =>
      simp [hRawPlan] at hPlan
  | some rawPlan =>
      simp [hRawPlan] at hPlan
      rcases hPlan with ⟨_, hEq⟩
      cases hEq
      exact resolutionPlan_orientation hRawPlan

/-- 单步计划检查通过时，计划结果与证书记录的结果一致。 -/
theorem resolutionStepPlan_result {current reason : Clause} {step : ResolutionStep}
    {plan : ResolutionPlan}
    (h : resolutionStepPlan? current reason step = some plan) :
    plan.result = step.result := by
  unfold resolutionStepPlan? at h
  simp at h
  rcases h with ⟨_, hPlan⟩
  cases hRawPlan : resolutionPlan? current reason step.pivot with
  | none =>
      simp [hRawPlan] at hPlan
  | some rawPlan =>
      simp [hRawPlan] at hPlan
      rcases hPlan with ⟨hResult, hEq⟩
      cases hEq
      exact clauseEq_eq.mp hResult

/-- 单步计划检查通过时，核心归结函数得到的结果就是证书记录的结果。 -/
theorem resolutionStepPlan_resolveResult {current reason : Clause} {step : ResolutionStep}
    {plan : ResolutionPlan}
    (h : resolutionStepPlan? current reason step = some plan) :
    resolveClause current reason step.pivot = step.result := by
  unfold resolutionStepPlan? at h
  simp at h
  rcases h with ⟨_, hPlan⟩
  cases hRawPlan : resolutionPlan? current reason step.pivot with
  | none =>
      simp [hRawPlan] at hPlan
  | some rawPlan =>
      simp [hRawPlan] at hPlan
      rcases hPlan with ⟨hResult, hEq⟩
      cases hEq
      exact (resolutionPlan_result hRawPlan).symm.trans (clauseEq_eq.mp hResult)

/-- 检查单步 resolution 是否满足 soundness 层需要的所有局部条件。 -/
def resolutionStepValid (current reason : Clause) (step : ResolutionStep) : Bool :=
  (resolutionStepPlan? current reason step).isSome

/-- 单步 resolution checker 的语义 soundness。 -/
theorem resolutionStepValid_sound {valuation : Valuation} {current reason : Clause}
    {step : ResolutionStep}
    (hValid : resolutionStepValid current reason step = true)
    (hCurrent : Clause.Satisfies valuation current)
    (hReason : Clause.Satisfies valuation reason) :
    Clause.Satisfies valuation step.result := by
  have hSubst : step.substitution = [] := by
    by_cases hSubst : step.substitution = []
    · exact hSubst
    · have hTmp := hValid
      simp [resolutionStepValid, resolutionStepPlan?, hSubst] at hTmp
  have hReasonEq : clauseEq reason step.reason = true := by
    by_cases hReason : clauseEq reason step.reason = true
    · exact hReason
    · have hTmp := hValid
      simp [resolutionStepValid, resolutionStepPlan?, hSubst, hReason] at hTmp
  have hPlan : ∃ plan, resolutionStepPlan? current reason step = some plan := by
    exact Option.isSome_iff_exists.mp (by simpa [resolutionStepValid] using hValid)
  rcases hPlan with ⟨plan, hPlan⟩
  have hRaw : resolutionPlan? current reason step.pivot = some plan ∧
      clauseEq plan.result step.result = true := by
    unfold resolutionStepPlan? at hPlan
    simp [hSubst, hReasonEq] at hPlan
    cases hRawPlan : resolutionPlan? current reason step.pivot with
    | none =>
        simp [hRawPlan] at hPlan
    | some rawPlan =>
        simp [hRawPlan] at hPlan
        rcases hPlan with ⟨hResult, hEq⟩
        cases hEq
        exact ⟨rfl, hResult⟩
  have hSound : Clause.Satisfies valuation plan.result :=
    resolutionPlan_sound hRaw.1 hCurrent hReason
  simpa [clauseEq_eq.mp hRaw.2] using hSound

/-- 递归检查一串 resolution 步骤。 -/
def resolutionStepsValidAgainst (database : Array Clause) :
    Clause → List ResolutionStep → Clause → Bool
  | current, [], target =>
      clauseEq current target
  | current, step :: rest, target =>
      if h : step.reasonIndex < database.size then
        let reason := database[step.reasonIndex]
        resolutionStepValid current reason step &&
          resolutionStepsValidAgainst database step.result rest target
      else
        false

/-- 检查一条 resolution 推导是否确实从已有数据库推出目标字句。 -/
def resolutionDerivationValidAgainst
    (database : Array Clause) (derivation : ResolutionDerivation) (target : Clause) : Bool :=
  if h : derivation.startIndex < database.size then
    let start := database[derivation.startIndex]
    clauseEq start derivation.start &&
      resolutionStepsValidAgainst database derivation.start derivation.steps.toList target &&
      clauseEq derivation.result target
  else
    false

/-- resolution checker 的通用 payload。 -/
structure ResolutionPayload where
  database : Array Clause
  derivation : ResolutionDerivation
  target : Clause
  deriving Repr, Inhabited

namespace ResolutionPayload

/-- 检查 payload 中的 resolution 推导。 -/
def check (payload : ResolutionPayload) : Bool :=
  resolutionDerivationValidAgainst payload.database payload.derivation payload.target

end ResolutionPayload

/--
已经通过 checker 的 resolution 推导。

这个结构目前只封装计算检查结果；后续 soundness 层会证明：
若数据库中的字句都可由对象逻辑推出，则 `target` 对应的字句公式也可推出。
-/
structure CheckedResolutionDerivation where
  database : Array Clause
  derivation : ResolutionDerivation
  target : Clause
  checked : resolutionDerivationValidAgainst database derivation target = true

namespace CheckedResolutionDerivation

/-- 计算式构造 checked resolution 推导。 -/
def mk? (database : Array Clause) (derivation : ResolutionDerivation) (target : Clause) :
    Option CheckedResolutionDerivation :=
  if h : resolutionDerivationValidAgainst database derivation target = true then
    some {
      database := database
      derivation := derivation
      target := target
      checked := h
    }
  else
    none

/-- 转成公共 checked payload。 -/
def toCoreChecked (cert : CheckedResolutionDerivation) :
    Certificate.Checked ResolutionPayload ResolutionPayload.check :=
  {
    payload := {
      database := cert.database
      derivation := cert.derivation
      target := cert.target
    }
    checked := cert.checked
  }

end CheckedResolutionDerivation

/-- 初始字句数据库，去掉来源标签。 -/
def initialClauseDatabase (initialClauses : Array InitialClause) : Array Clause :=
  initialClauses.map fun initial => initial.clause

/-- 带来源 initial clause 的满足性可转成裸 clause database 满足性。 -/
theorem initialClauseDatabase_satisfies {valuation : Valuation}
    {initialClauses : Array InitialClause}
    (hInitial : ∀ initial, initial ∈ initialClauses.toList →
      Clause.Satisfies valuation initial.clause) :
    DatabaseSatisfies valuation (initialClauseDatabase initialClauses) := by
  intro clause hMem
  simp [initialClauseDatabase] at hMem
  rcases hMem with ⟨initial, hInitialMem, hEq⟩
  subst hEq
  exact hInitial initial (Array.mem_def.mp hInitialMem)

/-- CDCL journal 中的 learned clause 数、已验证数和 resolution 步数。 -/
structure ResolutionStats where
  learned : Nat
  verified : Nat
  steps : Nat
  deriving Repr, Inhabited

namespace ResolutionStats

/-- 映射到公共证书摘要。 -/
def toCertificateStats (stats : ResolutionStats) : Certificate.Stats :=
  {
    steps := stats.steps
    clauses := stats.learned
    generated := stats.learned
    retained := stats.learned
    verified := stats.verified
  }

end ResolutionStats

/-- arena 初始前缀中一个槽位是否与带来源字句完全同步。 -/
def initialArenaClauseChecked (proof : CdclProof)
    (index : Nat) (initial : InitialClause) : Bool :=
  arenaClauseEq proof.arena (Data.Id.ofIndex index) initial.clause

/-- arena 的初始前缀是否与带来源的初始字句完全同步。 -/
def initialArenaValid (initialClauses : Array InitialClause) (proof : CdclProof) : Bool :=
  proof.arena.size == initialClauses.size + proof.journal.learns.size &&
    (initialClauses.mapIdx fun index initial =>
      initialArenaClauseChecked proof index initial).all fun ok => ok

/-- 逐槽位携带 initial arena 对齐证明。 -/
inductive CheckedInitialArenaClauses (proof : CdclProof) :
    Nat → List InitialClause → Prop where
  | nil {start} :
      CheckedInitialArenaClauses proof start []
  | cons {start head tail} :
      initialArenaClauseChecked proof start head = true →
        CheckedInitialArenaClauses proof (start + 1) tail →
          CheckedInitialArenaClauses proof start (head :: tail)

namespace CheckedInitialArenaClauses

/-- 逐槽位证明合成 initial arena 的 `mapIdx/all` 检查。 -/
theorem mapIdx_all_eq_true
    {proof : CdclProof} {start : Nat} {initialClauses : List InitialClause}
    (checked : CheckedInitialArenaClauses proof start initialClauses) :
    (initialClauses.mapIdx fun offset initial =>
      initialArenaClauseChecked proof (start + offset) initial).all id = true := by
  induction checked with
  | nil =>
      rfl
  | cons hHead _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Bool.and_eq_true_iff.mpr ⟨hHead, ih⟩

end CheckedInitialArenaClauses

/-- arena 尺寸与逐槽位证明合成 initial arena checker。 -/
theorem initialArenaValid_eq_true_of_clauses
    (initialClauses : Array InitialClause) (proof : CdclProof)
    (hSize :
      (proof.arena.size == initialClauses.size + proof.journal.learns.size) = true)
    (checked :
      CheckedInitialArenaClauses proof 0 initialClauses.toList) :
    initialArenaValid initialClauses proof = true := by
  unfold initialArenaValid
  rw [hSize]
  simp only [Bool.true_and]
  rw [← Array.all_toList, Array.toList_mapIdx]
  simpa using checked.mapIdx_all_eq_true

/-- journal 中 learned 空字句的数量。 -/
def emptyLearnedClauseCount (proof : CdclProof) : Nat :=
  Id.run do
    let mut count := 0
    for record in proof.journal.learns do
      if proof.arena.clauseIsEmpty (Data.Id.ofNat record.clause) then
        count := count + 1
    return count

/-- CDCL UNSAT checker 的单遍状态。 -/
structure UnsatCheckState where
  database : Array Clause
  ok : Bool
  foundEmpty : Bool
  nextStep : Nat
  learned : Nat
  verified : Nat
  steps : Nat
  deriving Repr, Inhabited, Lean.ToExpr

namespace UnsatCheckState

/-- 已验证初始 arena 后使用的共享初态。 -/
def acceptedInitial (database : Array Clause) : UnsatCheckState :=
  {
    database := database
    ok := true
    foundEmpty := false
    nextStep := 0
    learned := 0
    verified := 0
    steps := 0
  }

/-- 初始 UNSAT 检查状态。 -/
def initial (initialClauses : Array InitialClause) (proof : CdclProof) : UnsatCheckState :=
  {
    database := initialClauseDatabase initialClauses
    ok := initialArenaValid initialClauses proof
    foundEmpty := false
    nextStep := 0
    learned := 0
    verified := 0
    steps := 0
  }

/-- 初始数据库等式与 arena checker 合成共享初态等式。 -/
theorem initial_eq_acceptedInitial
    {initialClauses : Array InitialClause} {proof : CdclProof}
    {database : Array Clause}
    (hDatabase : initialClauseDatabase initialClauses = database)
    (hArena : initialArenaValid initialClauses proof = true) :
    initial initialClauses proof = acceptedInitial database := by
  simp [initial, acceptedInitial, hDatabase, hArena]

/--
消费一条 learned journal 记录。step slab 必须按记录顺序连续分区，不能重叠、跳过或
留下未审计的尾部步骤。
-/
def step (proof : CdclProof) (state : UnsatCheckState)
    (record : LearnRecord) : UnsatCheckState :=
  let learnedId : Data.ClauseId := Data.Id.ofNat record.clause
  let clause := arenaClause proof.arena learnedId
  let checked :=
    record.stepsStart == state.nextStep &&
      compactLearnRecordValidAgainst state.database proof record
  {
    database := state.database.push clause
    ok := state.ok && checked
    foundEmpty := state.foundEmpty || clause.isEmpty
    nextStep := state.nextStep + record.stepsLength
    learned := state.learned + 1
    verified := state.verified + if checked then 1 else 0
    steps := state.steps + record.stepsLength
  }

/-- 已验证 learned record 后使用的共享后继状态。 -/
def acceptedStep (proof : CdclProof) (state : UnsatCheckState)
    (record : LearnRecord) : UnsatCheckState :=
  let learnedId : Data.ClauseId := Data.Id.ofNat record.clause
  let clause := arenaClause proof.arena learnedId
  {
    database := state.database.push clause
    ok := state.ok
    foundEmpty := state.foundEmpty || clause.isEmpty
    nextStep := state.nextStep + record.stepsLength
    learned := state.learned + 1
    verified := state.verified + 1
    steps := state.steps + record.stepsLength
  }

/-- record 起点与内容检查通过时，通用 step 等于共享后继状态。 -/
theorem step_eq_acceptedStep
    {proof : CdclProof} {state : UnsatCheckState} {record : LearnRecord}
    (hStart : record.stepsStart = state.nextStep)
    (hRecord : compactLearnRecordValidAgainst state.database proof record = true) :
    state.step proof record = acceptedStep proof state record := by
  simp [step, acceptedStep, hStart, hRecord]

end UnsatCheckState

/-- 逐 learned record 携带 UNSAT checker 的状态转移证明。 -/
inductive CheckedUnsatTrace (proof : CdclProof) :
    List LearnRecord → UnsatCheckState → UnsatCheckState → Prop where
  | nil {state} :
      CheckedUnsatTrace proof [] state state
  | cons {record rest state next final}
      (hStep : state.step proof record = next)
      (tail : CheckedUnsatTrace proof rest next final) :
      CheckedUnsatTrace proof (record :: rest) state final

/-- 列表版单遍 CDCL UNSAT checker，和 soundness replay 的递归结构保持一致。 -/
def runUnsatCheckList (proof : CdclProof) :
    List LearnRecord → UnsatCheckState → UnsatCheckState
  | [], state => state
  | record :: rest, state => runUnsatCheckList proof rest (state.step proof record)

namespace CheckedUnsatTrace

/-- 逐 record 状态转移证明线性合成原 journal checker 的最终状态。 -/
theorem run_eq
    {proof : CdclProof} {records : List LearnRecord}
    {initial final : UnsatCheckState}
    (trace : CheckedUnsatTrace proof records initial final) :
    runUnsatCheckList proof records initial = final := by
  induction trace with
  | nil =>
      rfl
  | cons hStep _ ih =>
      simpa [runUnsatCheckList, hStep] using ih

end CheckedUnsatTrace

/-- `ok = false` 在后续 checker 运行中保持为 false。 -/
theorem runUnsatCheckList_ok_false (proof : CdclProof) (records : List LearnRecord)
    {state : UnsatCheckState}
    (h : state.ok = false) :
    (runUnsatCheckList proof records state).ok = false := by
  induction records generalizing state with
  | nil =>
      simpa [runUnsatCheckList] using h
  | cons record rest ih =>
      apply ih
      simp [UnsatCheckState.step, h]

/-- 如果一段非空 journal 最终 `ok = true`，那么第一条记录之后也必须 `ok = true`。 -/
theorem step_ok_of_runUnsatCheckList_cons_ok
    {proof : CdclProof} {record : LearnRecord} {rest : List LearnRecord}
    {state : UnsatCheckState}
    (h : (runUnsatCheckList proof (record :: rest) state).ok = true) :
    (state.step proof record).ok = true := by
  cases hStep : (state.step proof record).ok with
  | false =>
      have hFalse := runUnsatCheckList_ok_false proof rest hStep
      simp [runUnsatCheckList, hFalse] at h
  | true =>
      rfl

/-- journal 最终 `ok = true` 时，起始状态也必须已经 `ok = true`。 -/
theorem runUnsatCheckList_initial_ok {proof : CdclProof} :
    ∀ {records : List LearnRecord} {state : UnsatCheckState},
      (runUnsatCheckList proof records state).ok = true → state.ok = true
  | [], state, h => by
      simpa [runUnsatCheckList] using h
  | record :: rest, state, h => by
      have hStepOk : (state.step proof record).ok = true :=
        step_ok_of_runUnsatCheckList_cons_ok h
      have hBoth : state.ok = true ∧
          record.stepsStart = state.nextStep ∧
            compactLearnRecordValidAgainst state.database proof record = true := by
        simpa [UnsatCheckState.step] using hStepOk
      exact hBoth.1

/-- journal checker `ok = true` 时，数据库满足性沿 learned record 逐步保持。 -/
theorem runUnsatCheckList_database_satisfies {valuation : Valuation}
    {proof : CdclProof} :
    ∀ {records : List LearnRecord} {state : UnsatCheckState},
      DatabaseSatisfies valuation state.database →
      state.ok = true →
      (runUnsatCheckList proof records state).ok = true →
      DatabaseSatisfies valuation (runUnsatCheckList proof records state).database
  | [], state, hDb, _hStateOk, _hRunOk => by
      simpa [runUnsatCheckList] using hDb
  | record :: rest, state, hDb, hStateOk, hRunOk => by
      have hStepOk : (state.step proof record).ok = true :=
        step_ok_of_runUnsatCheckList_cons_ok hRunOk
      have hRecordValid : compactLearnRecordValidAgainst state.database proof record = true := by
        have hStepValid : record.stepsStart = state.nextStep ∧
            compactLearnRecordValidAgainst state.database proof record = true := by
          simpa [UnsatCheckState.step, hStateOk] using hStepOk
        exact hStepValid.2
      have hLearnedSat : Clause.Satisfies valuation
          (arenaClause proof.arena (Data.Id.ofNat record.clause : Data.ClauseId)) :=
        compactLearnRecordValidAgainst_sound hDb hRecordValid
      have hStepDb : DatabaseSatisfies valuation (state.step proof record).database := by
        simpa [UnsatCheckState.step] using
          DatabaseSatisfies.push hDb hLearnedSat
      have hTailOk : (runUnsatCheckList proof rest (state.step proof record)).ok = true := by
        simpa [runUnsatCheckList] using hRunOk
      exact runUnsatCheckList_database_satisfies
        (records := rest) (state := state.step proof record) hStepDb hStepOk hTailOk

/-- 单步 `foundEmpty` 反射：若标记为真，则当前数据库中真的有空字句。 -/
theorem step_foundEmpty_mem {proof : CdclProof} {state : UnsatCheckState}
    {record : LearnRecord}
    (hState : state.foundEmpty = true →
      ∃ clause, clause ∈ state.database.toList ∧ clause.isEmpty = true)
    (hFound : (state.step proof record).foundEmpty = true) :
    ∃ clause, clause ∈ (state.step proof record).database.toList ∧ clause.isEmpty = true := by
  simp [UnsatCheckState.step] at hFound
  rcases hFound with hOld | hNew
  · rcases hState hOld with ⟨clause, hMem, hEmpty⟩
    refine ⟨clause, ?_, hEmpty⟩
    simp only [UnsatCheckState.step, Array.toList_push, List.mem_append, List.mem_singleton]
    exact Or.inl hMem
  · refine ⟨arenaClause proof.arena (Data.Id.ofNat record.clause : Data.ClauseId), ?_, ?_⟩
    · simp [UnsatCheckState.step]
    · simp [hNew]

/-- journal 运行结束时的 `foundEmpty` 标记反射到最终数据库中的空字句。 -/
theorem runUnsatCheckList_foundEmpty_mem {proof : CdclProof} :
    ∀ {records : List LearnRecord} {state : UnsatCheckState},
      (state.foundEmpty = true →
        ∃ clause, clause ∈ state.database.toList ∧ clause.isEmpty = true) →
      (runUnsatCheckList proof records state).foundEmpty = true →
      ∃ clause,
        clause ∈ (runUnsatCheckList proof records state).database.toList ∧
          clause.isEmpty = true
  | [], state, hState, hFound => by
      simpa [runUnsatCheckList] using hState hFound
  | record :: rest, state, hState, hFound => by
      have hTailFound :
          (runUnsatCheckList proof rest (state.step proof record)).foundEmpty = true := by
        simpa [runUnsatCheckList] using hFound
      exact runUnsatCheckList_foundEmpty_mem
        (records := rest) (state := state.step proof record)
        (step_foundEmpty_mem hState) hTailFound

/-- 运行单遍 CDCL UNSAT checker。 -/
def runUnsatCheck (initialClauses : Array InitialClause) (proof : CdclProof) :
    UnsatCheckState :=
  runUnsatCheckList proof proof.journal.learns.toList
    (UnsatCheckState.initial initialClauses proof)

/-- 初态等式与逐 record trace 合成原 UNSAT checker 的最终状态。 -/
theorem runUnsatCheck_eq_of_trace
    {initialClauses : Array InitialClause} {proof : CdclProof}
    {initial final : UnsatCheckState}
    (hInitial : UnsatCheckState.initial initialClauses proof = initial)
    (trace : CheckedUnsatTrace proof proof.journal.learns.toList initial final) :
    runUnsatCheck initialClauses proof = final := by
  unfold runUnsatCheck
  rw [hInitial]
  exact trace.run_eq

/-- 统计 journal 中 learned clause 的紧凑 checker 通过情况。 -/
def learnedResolutionStats
    (initialClauses : Array InitialClause) (proof : CdclProof) : ResolutionStats :=
  let finalState := runUnsatCheck initialClauses proof
  {
    learned := finalState.learned
    verified := finalState.verified
    steps := finalState.steps
  }

/-- 整条 CDCL UNSAT 证书的可计算检查。 -/
def checkedUnsat (initialClauses : Array InitialClause) (proof : CdclProof) : Bool :=
  let finalState := runUnsatCheck initialClauses proof
  finalState.ok && finalState.foundEmpty &&
    finalState.nextStep == proof.journal.steps.size

/-- 已证明的最终状态及其三个终止字段合成整条 CDCL UNSAT checker。 -/
theorem checkedUnsat_eq_true_of_run
    {initialClauses : Array InitialClause} {proof : CdclProof}
    {final : UnsatCheckState}
    (hRun : runUnsatCheck initialClauses proof = final)
    (hOk : final.ok = true)
    (hFoundEmpty : final.foundEmpty = true)
    (hNextStep : (final.nextStep == proof.journal.steps.size) = true) :
    checkedUnsat initialClauses proof = true := by
  simp [checkedUnsat, hRun, hOk, hFoundEmpty, hNextStep]

/--
Checked CDCL UNSAT 证书的语义消费接口。

如果所有 initial prop clauses 在同一个 valuation 下都成立，那么一个通过
`checkedUnsat` 的 learned-only CDCL 证书会推出矛盾。
-/
theorem checkedUnsat_sound {valuation : Valuation}
    {initialClauses : Array InitialClause} {proof : CdclProof}
    (hInitial : ∀ initial, initial ∈ initialClauses.toList →
      Clause.Satisfies valuation initial.clause)
    (hChecked : checkedUnsat initialClauses proof = true) : False := by
  have hCheckedParts : (runUnsatCheck initialClauses proof).ok = true ∧
      (runUnsatCheck initialClauses proof).foundEmpty = true := by
    simp [checkedUnsat] at hChecked
    exact ⟨hChecked.1.1, hChecked.1.2⟩
  let state0 := UnsatCheckState.initial initialClauses proof
  have hDb0 : DatabaseSatisfies valuation state0.database := by
    simpa [state0, UnsatCheckState.initial] using
      initialClauseDatabase_satisfies (valuation := valuation)
        (initialClauses := initialClauses) hInitial
  have hStateOk0 : state0.ok = true := by
    exact runUnsatCheckList_initial_ok
      (records := proof.journal.learns.toList) (state := state0) hCheckedParts.1
  have hDbFinal : DatabaseSatisfies valuation
      (runUnsatCheckList proof proof.journal.learns.toList state0).database :=
    runUnsatCheckList_database_satisfies
      (records := proof.journal.learns.toList) (state := state0)
      hDb0 hStateOk0 hCheckedParts.1
  have hEmptyExists : ∃ clause,
      clause ∈ (runUnsatCheckList proof proof.journal.learns.toList state0).database.toList ∧
        clause.isEmpty = true := by
    exact runUnsatCheckList_foundEmpty_mem
      (records := proof.journal.learns.toList) (state := state0)
      (by intro h; simp [state0, UnsatCheckState.initial] at h)
      hCheckedParts.2
  rcases hEmptyExists with ⟨clause, hMem, hEmpty⟩
  have hSat : Clause.Satisfies valuation clause := hDbFinal clause hMem
  have hEq : clause = #[] := by simpa using hEmpty
  subst hEq
  exact Clause.not_satisfies_empty valuation hSat

/-- CDCL UNSAT checker 的通用 payload。 -/
structure UnsatPayload where
  initialClauses : Array InitialClause
  proof : CdclProof
  deriving Repr, Inhabited

namespace UnsatPayload

/-- 检查 payload 是否给出 UNSAT 证书。 -/
def check (payload : UnsatPayload) : Bool :=
  checkedUnsat payload.initialClauses payload.proof

end UnsatPayload

/-- 已通过 checker 的 CDCL UNSAT 证书。 -/
structure CheckedUnsatCertificate where
  initialClauses : Array InitialClause
  proof : CdclProof
  checked : checkedUnsat initialClauses proof = true
  deriving Repr

namespace CheckedUnsatCertificate

/-- 计算式构造 checked UNSAT 证书。 -/
def mk? (initialClauses : Array InitialClause) (proof : CdclProof) :
    Option CheckedUnsatCertificate :=
  if h : checkedUnsat initialClauses proof = true then
    some {
      initialClauses := initialClauses
      proof := proof
      checked := h
    }
  else
    none

/-- `mk?` 成功时，证书字段等于传入的初始字句与紧凑证明。 -/
theorem mk?_eq_some_fields
    {initialClauses : Array InitialClause} {proof : CdclProof}
    {cert : CheckedUnsatCertificate}
    (h : mk? initialClauses proof = some cert) :
    cert.initialClauses = initialClauses ∧ cert.proof = proof := by
  unfold mk? at h
  by_cases hChecked : checkedUnsat initialClauses proof = true
  · simp [hChecked] at h
    cases h
    exact ⟨rfl, rfl⟩
  · simp [hChecked] at h

/-- checked certificate 对象形式的语义消费接口。 -/
theorem sound (cert : CheckedUnsatCertificate) {valuation : Valuation}
    (hInitial : ∀ initial, initial ∈ cert.initialClauses.toList →
      Clause.Satisfies valuation initial.clause) : False :=
  checkedUnsat_sound hInitial cert.checked

/-- learned clause 统计。 -/
def learnedResolutionStats (cert : CheckedUnsatCertificate) : ResolutionStats :=
  {
    learned := cert.proof.journal.learns.size
    verified := cert.proof.journal.learns.size
    steps := cert.proof.journal.steps.size
  }

/-- learned 空字句数量。 -/
def emptyLearnedClauseCount (cert : CheckedUnsatCertificate) : Nat :=
  PropResolution.emptyLearnedClauseCount cert.proof

/-- 转成公共 checked payload。 -/
def toCoreChecked (cert : CheckedUnsatCertificate) :
    Certificate.Checked UnsatPayload UnsatPayload.check :=
  {
    payload := {
      initialClauses := cert.initialClauses
      proof := cert.proof
    }
    checked := cert.checked
  }

/-- CDCL 证书对应的公共证书节点。 -/
def toCoreNode (cert : CheckedUnsatCertificate)
    (id : Certificate.NodeId := 0) : Certificate.Node :=
  Certificate.Node.leaf id Certificate.Backend.propositionalCdcl Certificate.Phase.backendCheck
    "checked CDCL UNSAT"
    (cert.learnedResolutionStats.toCertificateStats)

/-- 单节点组合证书视图。 -/
def toCoreComposite (cert : CheckedUnsatCertificate)
    (id : Certificate.NodeId := 0) : Certificate.Composite :=
  { root := id, nodes := #[cert.toCoreNode id] }

end CheckedUnsatCertificate


end PropResolution
end Automation
end YesMetaZFC
