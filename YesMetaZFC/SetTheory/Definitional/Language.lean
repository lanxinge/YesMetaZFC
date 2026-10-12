import YesMetaZFC.SetTheory.Binding
/-!
# 带定义原子的集合论语言
本层是未来集合论主语法核。公式可以引用带层级的定义原子；每个原子的定义体只能引用
严格更低层的原子，因此定义依赖天然形成有向无环图。
旧纯 `∈` 语法不进入本模块。完全展开与保守性证明位于独立的
`YesMetaZFC.SetTheory.Definitional.Audit`。
-/
namespace YesMetaZFC
namespace SetTheory
namespace Definitional
universe u
/-- 定义原子签名。所有原子层级都严格小于公开公式使用的 `maxStage`。 -/
structure AtomSignature where
  Symbol : Type u
  arity : Symbol → Nat
  stage : Symbol → Nat
  maxStage : Nat
  stage_lt_maxStage : ∀ symbol, stage symbol < maxStage
/-- 新核中深度为 `depth` 的 locally nameless 集合论项。 -/
inductive Term (depth : Nat) where
  | bound : Fin depth → Term depth
  | free : FreeVarId → Term depth
  deriving Repr, BEq, DecidableEq, Hashable
namespace Term
/-- 按 substitution 替换 bound 变量。 -/
def bind {sourceDepth targetDepth : Nat} (substitution : Fin sourceDepth → Term targetDepth) :
    Term sourceDepth → Term targetDepth
  | .bound entry => substitution entry
  | .free id => .free id
/-- 按 `Fin` 映射重命名 bound 变量。 -/
def rename {sourceDepth targetDepth : Nat} (indexMap : Fin sourceDepth → Fin targetDepth) (term : Term sourceDepth) : Term targetDepth :=
  term.bind (.bound ∘ indexMap)
/-- 在上下文顶部加入一个新 binder。 -/
def weaken {depth : Nat} (term : Term depth) : Term (depth + 1) :=
  term.rename Fin.succ
/-- 当前上下文顶部最新引入的 bound 变量。 -/
def newest {depth : Nat} : Term (depth + 1) :=
  .bound ⟨0, Nat.zero_lt_succ _⟩
/-- substitution 穿过一个 binder 时的 lifting。 -/
def liftSubstitution {sourceDepth targetDepth : Nat} (substitution : Fin sourceDepth → Term targetDepth) :
    Fin (sourceDepth + 1) → Term (targetDepth + 1) :=
  fin_cases newest fun entry => (substitution entry).weaken
/-- 项中出现的自由变量编号。 -/
def freeSupport {depth : Nat} : Term depth → List FreeVarId
  | .bound _ => []
  | .free id => [id]
@[simp] theorem freeSupport_bound {depth : Nat} (entry : Fin depth) : (Term.bound entry).freeSupport = [] :=
  rfl
@[simp] theorem freeSupport_free {depth : Nat} (id : FreeVarId) : (Term.free id : Term depth).freeSupport = [id] :=
  rfl
@[simp] theorem freeSupport_newest {depth : Nat} : (newest : Term (depth + 1)).freeSupport = [] :=
  rfl
@[simp] theorem freeSupport_rename {sourceDepth targetDepth : Nat} (indexMap : Fin sourceDepth → Fin targetDepth) (term : Term sourceDepth) :
    (term.rename indexMap).freeSupport = term.freeSupport := by
  cases term <;> rfl
@[simp] theorem freeSupport_weaken {depth : Nat} (term : Term depth) :
    term.weaken.freeSupport = term.freeSupport :=
  freeSupport_rename Fin.succ term
/-- 不引入自由变量的 substitution 保持项的自由变量支持。 -/
theorem freeSupport_bind_of_closed {sourceDepth targetDepth : Nat} (substitution : Fin sourceDepth → Term targetDepth)
    (hClosed : ∀ entry, (substitution entry).freeSupport = []) (term : Term sourceDepth) : (term.bind substitution).freeSupport = term.freeSupport := by
  cases term with
  | bound entry =>
      exact hClosed entry
  | free id =>
      rfl
/-- lifting 保持“不引入自由变量”合同。 -/
theorem liftSubstitution_closed {sourceDepth targetDepth : Nat} (substitution : Fin sourceDepth → Term targetDepth)
    (hClosed : ∀ entry, (substitution entry).freeSupport = []) :
    ∀ entry, (liftSubstitution substitution entry).freeSupport = [] := by
  intro entry
  refine fin_cases ?_ (fun previous => ?_) entry
  · rfl
  · exact (freeSupport_weaken (substitution previous)).trans (hClosed previous)
end Term
/-- 固定长度、可结构比较和哈希的定义原子参数。 -/
structure TermVector (count depth : Nat) where
  terms : Array (Term depth)
  size_eq : terms.size = count
  deriving Repr
namespace TermVector
/-- 从逐项构造函数建立规范的固定长度参数数组。 -/
def ofFn {count depth : Nat} (terms : Fin count → Term depth) :
    TermVector count depth where
  -- 先按有限下标构造列表；其读取定理不依赖元层选择，再无损转为参数数组。
  terms := (List.ofFn terms).toArray
  size_eq := by simp only [List.size_toArray, List.length_ofFn]
/-- 按有界下标读取一个参数。 -/
def get {count depth : Nat} (terms : TermVector count depth) (entry : Fin count) : Term depth :=
  terms.terms[entry.val]' (terms.size_eq.symm ▸ entry.isLt)
@[simp] theorem get_ofFn {count depth : Nat} (terms : Fin count → Term depth) (entry : Fin count) : (ofFn terms).get entry = terms entry := by
  simp only [get, ofFn, List.getElem_toArray, List.getElem_ofFn]
instance {count depth : Nat} : CoeFun (TermVector count depth) (fun _ => Fin count → Term depth) :=
  ⟨get⟩
instance {count depth : Nat} : BEq (TermVector count depth) where
  beq left right := left.terms == right.terms
instance {count depth : Nat} : Hashable (TermVector count depth) where
  hash terms := hash terms.terms
/-- 空参数向量。 -/
def empty {depth : Nat} : TermVector 0 depth where
  terms := #[]
  size_eq := rfl
/-- 单参数向量。 -/
def singleton {depth : Nat} (term : Term depth) : TermVector 1 depth :=
  ofFn fun _ => term
/--
取当前上下文末尾的 `parameterCount` 个 bound 变量作为参数向量。
最内侧的 `localCount` 个位置留给局部量词，schema 参数从 index `localCount` 开始。
-/
def boundParameters (parameterCount localCount : Nat) :
    TermVector parameterCount (parameterCount + localCount) :=
  ofFn fun parameter =>
    .bound ⟨parameter.val + localCount, by omega⟩
/-- 参数遍历的长度证书由结构归纳产生，不调用数组外延性。 -/
private theorem tv_map_length {α β : Type _} (f : α → β) :
    ∀ xs : List α, (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (tv_map_length f xs)

private theorem tv_map_get {α β : Type _} (f : α → β) (xs : List α)
    (i : Nat) (h : i < xs.length) :
    (xs.map f)[i]' ((tv_map_length f xs).symm ▸ h) = f (xs[i]) := by
  induction xs generalizing i with
  | nil => exact (Nat.not_lt_zero i h).elim
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ h)

/-- 按 substitution 替换参数向量；底层列表遍历仍返回原数组接口。 -/
def bind {count sourceDepth targetDepth : Nat} (substitution : Fin sourceDepth → Term targetDepth) (terms : TermVector count sourceDepth) :
    TermVector count targetDepth where
  terms := ⟨terms.terms.toList.map (Term.bind substitution)⟩
  size_eq := (tv_map_length _ _).trans terms.size_eq
@[simp] theorem get_bind {count sourceDepth targetDepth : Nat} (substitution : Fin sourceDepth → Term targetDepth)
    (terms : TermVector count sourceDepth) (entry : Fin count) : (terms.bind substitution) entry = (terms entry).bind substitution := by
  exact tv_map_get (Term.bind substitution) terms.terms.toList entry.val
    (Eq.mp (congrArg (fun n => entry.val < n) terms.size_eq.symm) entry.isLt)
/-- 按 `Fin` 映射重命名参数向量中的 bound 变量。 -/
def rename {count sourceDepth targetDepth : Nat} (indexMap : Fin sourceDepth → Fin targetDepth) (terms : TermVector count sourceDepth) :
    TermVector count targetDepth :=
  terms.bind (.bound ∘ indexMap)
/-- 所有参数同时穿过一个新 binder。 -/
def weaken {count depth : Nat} (terms : TermVector count depth) :
    TermVector count (depth + 1) :=
  terms.rename Fin.succ
@[simp] theorem get_weaken {count depth : Nat} (terms : TermVector count depth) (entry : Fin count) :
    terms.weaken entry = (terms entry).weaken := by
  simp [weaken, rename, Term.weaken, Term.rename]
@[simp] theorem empty_weaken {depth : Nat} : (empty : TermVector 0 depth).weaken = empty := by
  simp [empty, weaken, rename, bind]
/-- 参数向量没有自由变量。 -/
def FreeClosed {count depth : Nat} (terms : TermVector count depth) : Prop :=
  ∀ entry, (terms entry).freeSupport = []
@[simp] theorem ofFn_freeClosed {count depth : Nat} (terms : Fin count → Term depth) :
    (ofFn terms).FreeClosed ↔ ∀ entry, (terms entry).freeSupport = [] := by
  simp [FreeClosed]
@[simp] theorem singleton_freeClosed {depth : Nat} (term : Term depth) :
    (singleton term).FreeClosed ↔ term.freeSupport = [] := by
  simp [singleton]
/-- 空参数向量自由闭合。 -/
@[simp] theorem empty_freeClosed {depth : Nat} : (empty : TermVector 0 depth).FreeClosed := by
  intro entry
  exact Fin.elim0 entry
/-- 由当前 bound 上下文取得的参数向量没有自由变量。 -/
@[simp] theorem boundParameters_freeClosed (parameterCount localCount : Nat) : (boundParameters parameterCount localCount).FreeClosed := by
  intro entry
  simp [boundParameters]
instance {count depth : Nat} (terms : TermVector count depth) :
    Decidable terms.FreeClosed := by
  unfold FreeClosed
  infer_instance
/-- 不引入自由变量的 substitution 不改变参数向量的自由闭合性。 -/
@[simp] theorem freeClosed_bind_iff_of_closed
    {count sourceDepth targetDepth : Nat} (substitution : Fin sourceDepth → Term targetDepth) (hClosed : ∀ entry, (substitution entry).freeSupport = [])
    (terms : TermVector count sourceDepth) : (terms.bind substitution).FreeClosed ↔ terms.FreeClosed := by
  have e i := (congrArg Term.freeSupport (get_bind substitution terms i)).trans
    (Term.freeSupport_bind_of_closed substitution hClosed (terms i))
  exact ⟨fun h i => e i ▸ h i, fun h i => (e i).symm ▸ h i⟩
/-- bound-variable 重命名不改变参数向量的自由闭合性。 -/
@[simp] theorem freeClosed_rename {count sourceDepth targetDepth : Nat} (indexMap : Fin sourceDepth → Fin targetDepth) (terms : TermVector count sourceDepth) :
    (terms.rename indexMap).FreeClosed ↔ terms.FreeClosed := by
  apply freeClosed_bind_iff_of_closed
  intro entry
  rfl
/-- 参数向量穿过 binder 时保持自由闭合性。 -/
@[simp] theorem freeClosed_weaken {count depth : Nat} (terms : TermVector count depth) :
    terms.weaken.FreeClosed ↔ terms.FreeClosed :=
  freeClosed_rename Fin.succ terms
/-- 参数向量的项节点数。集合论项只有变量节点，因此等于参数数量。 -/
def size {count depth : Nat} (_terms : TermVector count depth) : Nat :=
  count
end TermVector
/--
带定义原子的分层公式。
处在 `availableStage` 的公式只能引用层级严格低于它的原子。普通逻辑构造子保持当前
层级；进入原子定义体时层级严格下降。
-/
inductive Formula (σ : AtomSignature.{u}) : (availableStage depth : Nat) → Type u where
  | falsum {availableStage depth : Nat} : Formula σ availableStage depth
  | truth {availableStage depth : Nat} : Formula σ availableStage depth
  | mem {availableStage depth : Nat} :
      Term depth → Term depth → Formula σ availableStage depth
  | atom {availableStage depth : Nat} (symbol : σ.Symbol) (hStage : σ.stage symbol < availableStage) (arguments : TermVector (σ.arity symbol) depth) :
      Formula σ availableStage depth
  | neg {availableStage depth : Nat} :
      Formula σ availableStage depth → Formula σ availableStage depth
  | conj {availableStage depth : Nat} :
      Formula σ availableStage depth → Formula σ availableStage depth →
        Formula σ availableStage depth
  | disj {availableStage depth : Nat} :
      Formula σ availableStage depth → Formula σ availableStage depth →
        Formula σ availableStage depth
  | imp {availableStage depth : Nat} :
      Formula σ availableStage depth → Formula σ availableStage depth →
        Formula σ availableStage depth
  | iff {availableStage depth : Nat} :
      Formula σ availableStage depth → Formula σ availableStage depth →
        Formula σ availableStage depth
  | forallE {availableStage depth : Nat} :
      Formula σ availableStage (depth + 1) → Formula σ availableStage depth
  | existsE {availableStage depth : Nat} :
      Formula σ availableStage (depth + 1) → Formula σ availableStage depth
/-- 可以引用签名中全部定义原子的公开公式。 -/
abbrev RootFormula (σ : AtomSignature.{u}) (depth : Nat) :=
  Formula σ σ.maxStage depth
/-- 没有外层 bound 变量的公开公式。 -/
abbrev OpenFormula (σ : AtomSignature.{u}) :=
  RootFormula σ 0
namespace Formula
/-- 新核公式没有自由变量。定义原子的参数必须全部自由闭合。 -/
def FreeClosed {σ : AtomSignature.{u}} {availableStage : Nat} :
    {depth : Nat} → Formula σ availableStage depth → Prop
  | _, .falsum => True
  | _, .truth => True
  | _, .mem left right =>
      left.freeSupport = [] ∧ right.freeSupport = []
  | _, .atom _ _ arguments =>
      arguments.FreeClosed
  | _, .neg formula => FreeClosed formula
  | _, .conj left right
  | _, .disj left right
  | _, .imp left right
  | _, .iff left right =>
      FreeClosed left ∧ FreeClosed right
  | _, .forallE body
  | _, .existsE body =>
      FreeClosed body
termination_by structural _ formula => formula
@[reducible] instance instDecidableFreeClosed {σ : AtomSignature.{u}} {availableStage : Nat} :
    {depth : Nat} → (formula : Formula σ availableStage depth) →
        Decidable formula.FreeClosed
  | _, .falsum => by
      simp only [FreeClosed]
      infer_instance
  | _, .truth => by
      simp only [FreeClosed]
      infer_instance
  | _, .mem left right => by
      simp only [FreeClosed]
      infer_instance
  | _, .atom _ _ arguments => by
      simp only [FreeClosed]
      infer_instance
  | _, .neg formula => by
      simp only [FreeClosed]
      exact instDecidableFreeClosed formula
  | _, .conj left right
  | _, .disj left right
  | _, .imp left right
  | _, .iff left right => by
      simp only [FreeClosed]
      letI := instDecidableFreeClosed left
      letI := instDecidableFreeClosed right
      exact inferInstance
  | _, .forallE body
  | _, .existsE body => by
      simp only [FreeClosed]
      exact instDecidableFreeClosed body
termination_by structural _ formula => formula
/-- 按 substitution 替换公式中的 bound 变量。 -/
def bind {σ : AtomSignature.{u}} {availableStage sourceDepth targetDepth : Nat} (substitution : Fin sourceDepth → Term targetDepth) :
    Formula σ availableStage sourceDepth → Formula σ availableStage targetDepth
  | .falsum => .falsum
  | .truth => .truth
  | .mem left right => .mem (left.bind substitution) (right.bind substitution)
  | .atom symbol hStage arguments =>
      .atom symbol hStage (arguments.bind substitution)
  | .neg formula => .neg (bind substitution formula)
  | .conj left right => .conj (bind substitution left) (bind substitution right)
  | .disj left right => .disj (bind substitution left) (bind substitution right)
  | .imp left right => .imp (bind substitution left) (bind substitution right)
  | .iff left right => .iff (bind substitution left) (bind substitution right)
  | .forallE body => .forallE (bind (Term.liftSubstitution substitution) body)
  | .existsE body => .existsE (bind (Term.liftSubstitution substitution) body)
termination_by structural formula => formula
/-- 不引入自由变量的 substitution 不改变公式的自由闭合性。 -/
@[simp] theorem freeClosed_bind_iff_of_closed
    {σ : AtomSignature.{u}} {availableStage sourceDepth targetDepth : Nat} (substitution : Fin sourceDepth → Term targetDepth)
    (hClosed : ∀ entry, (substitution entry).freeSupport = []) (formula : Formula σ availableStage sourceDepth) :
    (formula.bind substitution).FreeClosed ↔ formula.FreeClosed := by
  induction formula generalizing targetDepth with
  | falsum | truth => exact Iff.rfl
  | mem left right =>
      have h := Term.freeSupport_bind_of_closed substitution hClosed left
      have k := Term.freeSupport_bind_of_closed substitution hClosed right
      exact ⟨fun e => ⟨h ▸ e.1, k ▸ e.2⟩, fun e => ⟨h.symm ▸ e.1, k.symm ▸ e.2⟩⟩
  | atom symbol hStage arguments =>
      exact TermVector.freeClosed_bind_iff_of_closed substitution hClosed arguments
  | neg formula ih => exact ih substitution hClosed
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      exact and_congr (ihLeft substitution hClosed) (ihRight substitution hClosed)
  | forallE body ih
  | existsE body ih =>
      exact ih (Term.liftSubstitution substitution) (Term.liftSubstitution_closed substitution hClosed)
/-- 按 `Fin` 映射重命名公式中的 bound 变量。 -/
def rename {σ : AtomSignature.{u}}
    {availableStage sourceDepth targetDepth : Nat} (indexMap : Fin sourceDepth → Fin targetDepth) (formula : Formula σ availableStage sourceDepth) :
    Formula σ availableStage targetDepth :=
  formula.bind (.bound ∘ indexMap)
/-- bound-variable 重命名不改变公式的自由闭合性。 -/
@[simp] theorem freeClosed_rename {σ : AtomSignature.{u}}
    {availableStage sourceDepth targetDepth : Nat} (indexMap : Fin sourceDepth → Fin targetDepth) (formula : Formula σ availableStage sourceDepth) :
    (formula.rename indexMap).FreeClosed ↔ formula.FreeClosed := by
  apply freeClosed_bind_iff_of_closed
  intro entry
  rfl
/-- 在上下文顶部加入一个新 binder。 -/
def weaken {σ : AtomSignature.{u}} {availableStage depth : Nat} (formula : Formula σ availableStage depth) :
    Formula σ availableStage (depth + 1) :=
  formula.rename Fin.succ
/-- 公式穿过 binder 时保持自由闭合性。 -/
@[simp] theorem freeClosed_weaken {σ : AtomSignature.{u}}
    {availableStage depth : Nat} (formula : Formula σ availableStage depth) :
    formula.weaken.FreeClosed ↔ formula.FreeClosed :=
  freeClosed_rename Fin.succ formula
/-- 用一个项实例化公式最顶部的 bound 变量。 -/
def instantiateTop {σ : AtomSignature.{u}} {availableStage depth : Nat} (replacement : Term depth) (body : Formula σ availableStage (depth + 1)) :
    Formula σ availableStage depth :=
  body.bind <| Fin.cases replacement Term.bound
/-- 依次全称闭合当前全部 bound 参数。 -/
def forallClosure {σ : AtomSignature.{u}} {availableStage : Nat} : (depth : Nat) → Formula σ availableStage depth → Formula σ availableStage 0
  | 0, formula => formula
  | depth + 1, formula => forallClosure depth (.forallE formula)
termination_by structural depth _ => depth
/-- 全称闭合不改变公式的自由闭合性。 -/
@[simp] theorem freeClosed_forallClosure {σ : AtomSignature.{u}}
    {availableStage depth : Nat} (formula : Formula σ availableStage depth) : (forallClosure depth formula).FreeClosed ↔ formula.FreeClosed := by
  induction depth with
  | zero =>
      rfl
  | succ depth ih => exact ih (.forallE formula)
/-- 公式的粗略节点数；定义原子只计自身和参数，不展开定义体。 -/
def size {σ : AtomSignature.{u}} :
    {availableStage depth : Nat} → Formula σ availableStage depth → Nat
  | _, _, .falsum => 1
  | _, _, .truth => 1
  | _, _, .mem _ _ => 3
  | _, _, .atom _ _ arguments => arguments.size + 1
  | _, _, .neg formula => size formula + 1
  | _, _, .conj left right
  | _, _, .disj left right
  | _, _, .imp left right
  | _, _, .iff left right =>
      size left + size right + 1
  | _, _, .forallE body
  | _, _, .existsE body =>
      size body + 1
end Formula
/-- 每个定义原子的定义体只能引用更低层原子，并且不能引入自由变量。 -/
structure Definitions (σ : AtomSignature.{u}) where
  body : (symbol : σ.Symbol) →
      Formula σ (σ.stage symbol) (σ.arity symbol)
  bodyFreeClosed :
    ∀ symbol, Formula.FreeClosed (body symbol)
/-- 新核中的 Jech 句子。 -/
structure Sentence (σ : AtomSignature.{u}) where
  formula : OpenFormula σ
  freeClosed : formula.FreeClosed
/- 闭合证书在隐式参数匹配时保持可归约。 -/
attribute [implicit_reducible] Formula.FreeClosed
end Definitional
end SetTheory
end YesMetaZFC
