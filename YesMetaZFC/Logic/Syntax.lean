import YesMetaZFC.Logic.Signature

/-!
# 内在良构的一阶语法核

本模块只允许构造排序正确、元数正确且作用域正确的项和公式。

* bound 与 free 变量分别由有限排序上下文索引；
* 函数和关系的参数由签名中的排序列表索引；
* 等式两端在类型上具有同一排序；
* 量词体直接处于扩展后的 bound 上下文；
* 重命名与替换统一表达为上下文之间的保排序映射。

因此本层不存在 raw AST、良构谓词、作用域谓词、合法性 Bool 检查器或 checked
包装。稳定自然数变量编号属于后续序列化层，不进入语法核。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

/-- 排序上下文。列表头表示最近引入的变量。 -/
abbrev SortContext (σ : Signature.{u, v, w}) := List σ.SortSymbol

/--
排序上下文中的变量。构造子同时证明变量存在于上下文并具有指定排序。
-/
inductive Variable {S : Type u} : List S → S → Type u where
  | here {Γ : List S} {s : S} : Variable (s :: Γ) s
  | there {Γ : List S} {s t : S} : Variable Γ s → Variable (t :: Γ) s

namespace Variable

/-- 变量的 de Bruijn 位置，仅供后续序列化使用。 -/
def index {S : Type u} {Γ : List S} {s : S} : Variable Γ s → Nat
  | .here => 0
  | .there entry => entry.index + 1

/-- 变量位置严格落在其上下文长度内。 -/
theorem index_lt_length {S : Type u} {Γ : List S} {s : S}
    (entry : Variable Γ s) : entry.index < Γ.length := by
  induction entry with
  | here =>
      simp [index]
  | there previous ih =>
      simpa [index] using Nat.succ_lt_succ ih

/-- 变量在有限上下文中的位置。 -/
def position {S : Type u} {Γ : List S} {s : S}
    (entry : Variable Γ s) : Fin Γ.length :=
  ⟨entry.index, entry.index_lt_length⟩

/-- 在上下文头部加入一个变量后，原变量仍然可用。 -/
def weaken {S : Type u} {Γ : List S} {s : S} (introduced : S) :
    Variable Γ s → Variable (introduced :: Γ) s :=
  .there

/-- 扩展上下文中新引入的规范变量。 -/
def newest {S : Type u} {Γ : List S} {s : S} :
    Variable (s :: Γ) s :=
  .here

/-- 在上下文尾部加入变量后，原变量保持原有 de Bruijn 位置。 -/
def appendRight {S : Type u} {Γ : List S} {s : S}
    (introduced : S) : Variable Γ s → Variable (Γ ++ [introduced]) s
  | .here => .here
  | .there previous => .there (appendRight introduced previous)

/-- 尾扩展不改变既有变量的 de Bruijn 位置。 -/
@[simp] theorem index_appendRight {S : Type u} {Γ : List S} {s : S}
    (introduced : S) (entry : Variable Γ s) :
    (appendRight introduced entry).index = entry.index := by
  induction entry <;> simp [appendRight, index, *]

/-- 上下文尾部新加入的变量。 -/
def last {S : Type u} (Γ : List S) (s : S) : Variable (Γ ++ [s]) s :=
  match Γ with
  | [] => .here
  | _ :: tail => .there (last tail s)

/-- 尾部新变量的 de Bruijn 位置恰为原上下文长度。 -/
@[simp] theorem index_last {S : Type u} (Γ : List S) (s : S) :
    (last Γ s).index = Γ.length := by
  induction Γ with
  | nil => rfl
  | cons head tail ih =>
      simp [last, index, ih]

end Variable

/-- 两个排序上下文之间的保排序变量映射。 -/
abbrev VariableRenaming {S : Type u} (source target : List S) :=
  {s : S} → Variable source s → Variable target s

namespace VariableRenaming

/-- 恒等变量映射。 -/
def id {S : Type u} {Γ : List S} : VariableRenaming Γ Γ :=
  fun entry => entry

/-- 从空上下文到任意上下文的唯一重命名。 -/
def empty {S : Type u} {Γ : List S} : VariableRenaming [] Γ :=
  fun entry => nomatch entry

/-- 将整个源上下文嵌入扩展后的上下文。 -/
def weaken {S : Type u} {Γ : List S} (introduced : S) :
    VariableRenaming Γ (introduced :: Γ) :=
  fun entry => .there entry

/-- 将整个源上下文嵌入其尾扩展。 -/
def appendRight {S : Type u} {Γ : List S} (introduced : S) :
    VariableRenaming Γ (Γ ++ [introduced]) :=
  Variable.appendRight introduced

/-- 在变量映射头部指定一个像，其余变量沿用既有映射。 -/
def cons {S : Type u} {source target : List S} {sort : S}
    (head : Variable target sort) (tail : VariableRenaming source target) :
    VariableRenaming (sort :: source) target :=
  fun entry =>
    match entry with
    | .here => head
    | .there previous => tail previous

/-- 交换 free 上下文顶部的两个变量。 -/
def swapTop {S : Type u} {Γ : List S} {first second : S} :
    VariableRenaming (first :: second :: Γ) (second :: first :: Γ) :=
  fun entry =>
    match entry with
    | .here => .there .here
    | .there .here => .here
    | .there (.there previous) => .there (.there previous)

/-- 重命名穿过同一个新 binder。 -/
def lift {S : Type u} {source target : List S} {introduced : S}
    (ρ : VariableRenaming source target) :
    VariableRenaming (introduced :: source) (introduced :: target) :=
  fun entry =>
    match entry with
    | .here => .here
    | .there previous => .there (ρ previous)

/-- 重命名的复合。 -/
def comp {S : Type u} {source middle target : List S}
    (outer : VariableRenaming middle target)
    (inner : VariableRenaming source middle) :
    VariableRenaming source target :=
  fun entry => outer (inner entry)

end VariableRenaming

/--
同时作用于 bound/free 上下文的重命名。`.id` 是显式快路径，不把恒等性藏在函数
外延等式里。
-/
inductive Renaming (σ : Signature.{u, v, w}) :
    SortContext σ → SortContext σ → SortContext σ → SortContext σ →
      Type (max u v w) where
  | id {bound free : SortContext σ} : Renaming σ bound free bound free
  | map {sourceBound sourceFree targetBound targetFree : SortContext σ} :
      VariableRenaming sourceBound targetBound →
      VariableRenaming sourceFree targetFree →
      Renaming σ sourceBound sourceFree targetBound targetFree

namespace Renaming

/-- 仅改变 bound 上下文。 -/
def bound {σ : Signature.{u, v, w}}
    {sourceBound targetBound free : SortContext σ}
    (ρ : VariableRenaming sourceBound targetBound) :
    Renaming σ sourceBound free targetBound free :=
  .map ρ VariableRenaming.id

/-- 仅改变 free 上下文。 -/
def free {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree) :
    Renaming σ bound sourceFree bound targetFree :=
  .map VariableRenaming.id ρ

/-- 在 bound 上下文头部加入一个变量。 -/
def weakenBound {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    Renaming σ bound free (introduced :: bound) free :=
  .bound (VariableRenaming.weaken introduced)

/-- 在 free 上下文头部加入一个变量。 -/
def weakenFree {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    Renaming σ bound free bound (introduced :: free) :=
  .free (VariableRenaming.weaken introduced)

/-- 将空 free 上下文嵌入任意 free 上下文。 -/
def emptyFree {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    Renaming σ bound [] bound free :=
  match free with
  | [] => .id
  | _ :: _ => .free VariableRenaming.empty

/-- 重命名穿过同一个新 binder；恒等重命名保持 `.id`。 -/
def liftBound {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol) :
    Renaming σ sourceBound sourceFree targetBound targetFree →
      Renaming σ (introduced :: sourceBound) sourceFree
        (introduced :: targetBound) targetFree
  | .id => .id
  | .map boundRenaming freeRenaming =>
      .map (VariableRenaming.lift boundRenaming) freeRenaming

/-- 重命名复合；任一侧为恒等时不创建新的映射节点。 -/
def comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Renaming σ middleBound middleFree targetBound targetFree)
    (inner : Renaming σ sourceBound sourceFree middleBound middleFree) :
    Renaming σ sourceBound sourceFree targetBound targetFree :=
  match outer, inner with
  | .id, inner => inner
  | outer, .id => outer
  | .map outerBound outerFree, .map innerBound innerFree =>
      .map (VariableRenaming.comp outerBound innerBound)
        (VariableRenaming.comp outerFree innerFree)

end Renaming

mutual

/-- 内在排序的一阶项。 -/
inductive Term (σ : Signature.{u, v, w})
    (bound free : SortContext σ) : σ.SortSymbol → Type (max u v w) where
  | bvar {sort : σ.SortSymbol} :
      Variable bound sort → Term σ bound free sort
  | fvar {sort : σ.SortSymbol} :
      Variable free sort → Term σ bound free sort
  | app (function : σ.FuncSymbol) :
      Arguments σ bound free (σ.funcDomain function) →
        Term σ bound free (σ.funcCodomain function)

/-- 由排序列表索引的异质参数列。 -/
inductive Arguments (σ : Signature.{u, v, w})
    (bound free : SortContext σ) : List σ.SortSymbol →
    Type (max u v w) where
  | nil : Arguments σ bound free []
  | cons {sort : σ.SortSymbol} {sorts : List σ.SortSymbol} :
      Term σ bound free sort → Arguments σ bound free sorts →
        Arguments σ bound free (sort :: sorts)

end

/-- 只沿参数列归纳；各头项的性质可直接复用既有项定理。 -/
@[elab_as_elim] theorem Arguments.listRec {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    {motive : {sorts : List σ.SortSymbol} → Arguments σ bound free sorts → Prop}
    (nil : motive .nil)
    (cons : ∀ {sort sorts} (head : Term σ bound free sort)
      (tail : Arguments σ bound free sorts),
      motive tail → motive (.cons head tail)) :
    ∀ {sorts} (arguments : Arguments σ bound free sorts), motive arguments
  | _, .nil => nil
  | _, .cons head tail => cons head tail (Arguments.listRec nil cons tail)

/-- 内在排序且内在作用域正确的一阶公式。 -/
inductive Formula (σ : Signature.{u, v, w}) :
    SortContext σ → SortContext σ → Type (max u v w) where
  | falsum {bound free : SortContext σ} : Formula σ bound free
  | truth {bound free : SortContext σ} : Formula σ bound free
  | rel {bound free : SortContext σ} (relation : σ.RelSymbol) :
      Arguments σ bound free (σ.relDomain relation) → Formula σ bound free
  | equal {bound free : SortContext σ} {sort : σ.SortSymbol} :
      Term σ bound free sort → Term σ bound free sort → Formula σ bound free
  | neg {bound free : SortContext σ} :
      Formula σ bound free → Formula σ bound free
  | conj {bound free : SortContext σ} :
      Formula σ bound free → Formula σ bound free → Formula σ bound free
  | disj {bound free : SortContext σ} :
      Formula σ bound free → Formula σ bound free → Formula σ bound free
  | imp {bound free : SortContext σ} :
      Formula σ bound free → Formula σ bound free → Formula σ bound free
  | iff {bound free : SortContext σ} :
      Formula σ bound free → Formula σ bound free → Formula σ bound free
  | forallE {bound free : SortContext σ} (sort : σ.SortSymbol) :
      Formula σ (sort :: bound) free → Formula σ bound free
  | existsE {bound free : SortContext σ} (sort : σ.SortSymbol) :
      Formula σ (sort :: bound) free → Formula σ bound free

/-- 没有外层 bound 变量的项。 -/
abbrev OpenTerm (σ : Signature.{u, v, w})
    (free : SortContext σ) (sort : σ.SortSymbol) :=
  Term σ [] free sort

/-- 没有外层 bound 变量的公式。 -/
abbrev OpenFormula (σ : Signature.{u, v, w})
    (free : SortContext σ) :=
  Formula σ [] free

/-- 没有 bound 或 free 变量的闭句。 -/
abbrev Sentence (σ : Signature.{u, v, w}) :=
  Formula σ [] []

mutual

/-- 执行非恒等项重命名。公共入口 `Term.rename` 负责恒等快路径。 -/
def Term.renameMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree) :
    {sort : σ.SortSymbol} →
      Term σ sourceBound sourceFree sort → Term σ targetBound targetFree sort
  | _, .bvar entry => .bvar (boundRenaming entry)
  | _, .fvar entry => .fvar (freeRenaming entry)
  | _, .app function arguments =>
      .app function
        (Arguments.renameMapped boundRenaming freeRenaming arguments)

/-- 执行非恒等参数列重命名。 -/
def Arguments.renameMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree) :
    {sorts : List σ.SortSymbol} →
      Arguments σ sourceBound sourceFree sorts →
        Arguments σ targetBound targetFree sorts
  | _, .nil => .nil
  | _, .cons term rest =>
      .cons (term.renameMapped boundRenaming freeRenaming)
        (Arguments.renameMapped boundRenaming freeRenaming rest)

end

/-- 同时重命名项的 bound 与 free 变量；恒等情形在根节点直接返回。 -/
def Term.rename {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    Term σ targetBound targetFree sort :=
  match ρ with
  | .id => term
  | .map boundRenaming freeRenaming =>
      term.renameMapped boundRenaming freeRenaming

/-- 同时重命名参数列的 bound 与 free 变量；恒等情形在根节点直接返回。 -/
def Arguments.rename {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    Arguments σ targetBound targetFree sorts :=
  match ρ with
  | .id => arguments
  | .map boundRenaming freeRenaming =>
      arguments.renameMapped boundRenaming freeRenaming

/-- 项穿过一个新 binder。 -/
def Term.weakenBound {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (introduced : σ.SortSymbol) (term : Term σ bound free sort) :
    Term σ (introduced :: bound) free sort :=
  term.rename (Renaming.weakenBound introduced)

/-- 参数列穿过一个新 binder。 -/
def Arguments.weakenBound {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (introduced : σ.SortSymbol)
    (arguments : Arguments σ bound free sorts) :
    Arguments σ (introduced :: bound) free sorts :=
  arguments.rename (Renaming.weakenBound introduced)

/-- 无 bound 变量的项可规范嵌入任意 binder 上下文。 -/
def Term.embedBoundClosed {σ : Signature.{u, v, w}}
    {free : SortContext σ} {sort : σ.SortSymbol} :
    (targetBound : SortContext σ) →
      Term σ [] free sort → Term σ targetBound free sort
  | [], term => term
  | introduced :: rest, term =>
      (term.embedBoundClosed rest).weakenBound introduced

/-- 无 bound 变量的参数列可规范嵌入任意 binder 上下文。 -/
def Arguments.embedBoundClosed {σ : Signature.{u, v, w}}
    {free : SortContext σ} {sorts : List σ.SortSymbol} :
    (targetBound : SortContext σ) →
      Arguments σ [] free sorts → Arguments σ targetBound free sorts
  | [], arguments => arguments
  | introduced :: rest, arguments =>
      (arguments.embedBoundClosed rest).weakenBound introduced

/-- 按保排序映射改变项的 free 上下文。 -/
def Term.renameFree {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    {sort : σ.SortSymbol} (term : Term σ bound sourceFree sort) :
    Term σ bound targetFree sort :=
  term.rename (Renaming.free ρ)

/-- 按保排序映射改变参数列的 free 上下文。 -/
def Arguments.renameFree {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound sourceFree sorts) :
    Arguments σ bound targetFree sorts :=
  arguments.rename (Renaming.free ρ)

/-- 扩展 free 上下文中新引入的规范自由变量项。 -/
def Term.newestFree {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (sort : σ.SortSymbol) :
    Term σ bound (sort :: free) sort :=
  .fvar .here

/-- 项穿过一个新 free 变量。 -/
def Term.weakenFree {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (introduced : σ.SortSymbol) (term : Term σ bound free sort) :
    Term σ bound (introduced :: free) sort :=
  term.rename (Renaming.weakenFree introduced)

/-- 参数列穿过一个新 free 变量。 -/
def Arguments.weakenFree {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (introduced : σ.SortSymbol)
    (arguments : Arguments σ bound free sorts) :
    Arguments σ bound (introduced :: free) sorts :=
  arguments.rename (Renaming.weakenFree introduced)

namespace Formula

/-- 执行非恒等公式重命名。公共入口 `Formula.rename` 负责恒等快路径。 -/
def renameMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree) :
    Formula σ sourceBound sourceFree → Formula σ targetBound targetFree
  | .falsum => .falsum
  | .truth => .truth
  | .rel relation arguments =>
      .rel relation
        (Arguments.renameMapped boundRenaming freeRenaming arguments)
  | .equal left right =>
      .equal (left.renameMapped boundRenaming freeRenaming)
        (right.renameMapped boundRenaming freeRenaming)
  | .neg body => .neg (renameMapped boundRenaming freeRenaming body)
  | .conj left right =>
      .conj (renameMapped boundRenaming freeRenaming left)
        (renameMapped boundRenaming freeRenaming right)
  | .disj left right =>
      .disj (renameMapped boundRenaming freeRenaming left)
        (renameMapped boundRenaming freeRenaming right)
  | .imp left right =>
      .imp (renameMapped boundRenaming freeRenaming left)
        (renameMapped boundRenaming freeRenaming right)
  | .iff left right =>
      .iff (renameMapped boundRenaming freeRenaming left)
        (renameMapped boundRenaming freeRenaming right)
  | .forallE sort body =>
      .forallE sort
        (renameMapped (VariableRenaming.lift boundRenaming)
          freeRenaming body)
  | .existsE sort body =>
      .existsE sort
        (renameMapped (VariableRenaming.lift boundRenaming)
          freeRenaming body)

/-- 同时重命名公式的 bound 与 free 变量；恒等情形在根节点直接返回。 -/
def rename {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (ρ : Renaming σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    Formula σ targetBound targetFree :=
  match ρ with
  | .id => formula
  | .map boundRenaming freeRenaming =>
      renameMapped boundRenaming freeRenaming formula

/-- 公式穿过一个新 binder。 -/
def weakenBound {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (formula : Formula σ bound free) :
    Formula σ (introduced :: bound) free :=
  formula.rename (Renaming.weakenBound introduced)

/-- 按保排序映射改变公式的 free 上下文。 -/
def renameFree {σ : Signature.{u, v, w}}
    {bound sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    (formula : Formula σ bound sourceFree) :
    Formula σ bound targetFree :=
  formula.rename (Renaming.free ρ)

/-- 公式穿过一个新 free 变量。新变量在结果中按构造不可出现。 -/
def weakenFree {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (formula : Formula σ bound free) :
    Formula σ bound (introduced :: free) :=
  formula.rename (Renaming.weakenFree introduced)

/-- 交换公式 free 上下文顶部的两个变量。 -/
def swapFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {first second : σ.SortSymbol}
    (body : Formula σ bound (first :: second :: free)) :
    Formula σ bound (second :: first :: free) :=
  body.renameFree VariableRenaming.swapTop

/-- 将闭句嵌入任意 free 上下文。 -/
def fromSentence {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sentence : Sentence σ) :
    OpenFormula σ free :=
  sentence.rename Renaming.emptyFree

/-- 右结合有限合取；空列表解释为真。 -/
def conjunctionList {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    List (Formula σ bound free) → Formula σ bound free
  | [] => .truth
  | [formula] => formula
  | formula :: rest => .conj formula (conjunctionList rest)

/-- 右结合有限析取；空列表解释为假。 -/
def disjunctionList {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    List (Formula σ bound free) → Formula σ bound free
  | [] => .falsum
  | [formula] => formula
  | formula :: rest => .disj formula (disjunctionList rest)

end Formula

mutual

/--
尝试删除 free 上下文顶部变量。成功时返回处于较小上下文中的同一项；失败表示该
变量确实在项中出现。
-/
def Term.strengthenFreeTop? {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sort : σ.SortSymbol} →
      Term σ bound (introduced :: free) sort →
        Option (Term σ bound free sort)
  | _, .bvar entry => some (.bvar entry)
  | _, .fvar .here => none
  | _, .fvar (.there previous) => some (.fvar previous)
  | _, .app function arguments =>
      match Arguments.strengthenFreeTop? introduced arguments with
      | some strengthened => some (.app function strengthened)
      | none => none

/-- 参数列的可计算 free-context strengthening。 -/
def Arguments.strengthenFreeTop? {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sorts : List σ.SortSymbol} →
      Arguments σ bound (introduced :: free) sorts →
        Option (Arguments σ bound free sorts)
  | _, .nil => some .nil
  | _, .cons term rest =>
      match term.strengthenFreeTop? introduced,
          Arguments.strengthenFreeTop? introduced rest with
      | some strengthenedTerm, some strengthenedRest =>
          some (.cons strengthenedTerm strengthenedRest)
      | _, _ => none

end


/-- 公式的可计算 free-context strengthening。 -/
def Formula.strengthenFreeTop? {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    Formula σ bound (introduced :: free) → Option (Formula σ bound free)
  | .falsum => some .falsum
  | .truth => some .truth
  | .rel relation arguments =>
      match Arguments.strengthenFreeTop? introduced arguments with
      | some strengthened => some (.rel relation strengthened)
      | none => none
  | .equal left right =>
      match left.strengthenFreeTop? introduced,
          right.strengthenFreeTop? introduced with
      | some strengthenedLeft, some strengthenedRight =>
          some (.equal strengthenedLeft strengthenedRight)
      | _, _ => none
  | .neg body =>
      match body.strengthenFreeTop? introduced with
      | some strengthened => some (.neg strengthened)
      | none => none
  | .conj left right =>
      match left.strengthenFreeTop? introduced,
          right.strengthenFreeTop? introduced with
      | some strengthenedLeft, some strengthenedRight =>
          some (.conj strengthenedLeft strengthenedRight)
      | _, _ => none
  | .disj left right =>
      match left.strengthenFreeTop? introduced,
          right.strengthenFreeTop? introduced with
      | some strengthenedLeft, some strengthenedRight =>
          some (.disj strengthenedLeft strengthenedRight)
      | _, _ => none
  | .imp left right =>
      match left.strengthenFreeTop? introduced,
          right.strengthenFreeTop? introduced with
      | some strengthenedLeft, some strengthenedRight =>
          some (.imp strengthenedLeft strengthenedRight)
      | _, _ => none
  | .iff left right =>
      match left.strengthenFreeTop? introduced,
          right.strengthenFreeTop? introduced with
      | some strengthenedLeft, some strengthenedRight =>
          some (.iff strengthenedLeft strengthenedRight)
      | _, _ => none
  | .forallE sort body =>
      match body.strengthenFreeTop? introduced with
      | some strengthened => some (.forallE sort strengthened)
      | none => none
  | .existsE sort body =>
      match body.strengthenFreeTop? introduced with
      | some strengthened => some (.existsE sort strengthened)
      | none => none

/-- 将一个变量上下文解释为目标上下文中的同排序项。 -/
abbrev VariableSubstitution (σ : Signature.{u, v, w})
    (source targetBound targetFree : SortContext σ) :=
  {sort : σ.SortSymbol} →
    Variable source sort → Term σ targetBound targetFree sort

namespace VariableSubstitution

/-- 从空变量上下文到任意项上下文的唯一替换。 -/
def empty {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    VariableSubstitution σ [] bound free :=
  fun entry => nomatch entry

/-- 在变量替换头部指定一个项像，其余变量沿用既有替换。 -/
def cons {σ : Signature.{u, v, w}}
    {source bound free : SortContext σ} {sort : σ.SortSymbol}
    (head : Term σ bound free sort)
    (tail : VariableSubstitution σ source bound free) :
    VariableSubstitution σ (sort :: source) bound free :=
  fun entry =>
    match entry with
    | .here => head
    | .there previous => tail previous

/-- free 替换穿过同一个规范新变量。 -/
def liftFree {σ : Signature.{u, v, w}}
    {source bound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution : VariableSubstitution σ source bound targetFree) :
    VariableSubstitution σ (introduced :: source) bound
      (introduced :: targetFree) :=
  fun entry =>
    match entry with
    | .here => .fvar .here
    | .there previous =>
        (substitution previous).weakenFree introduced

/-- bound 变量的恒等替换。 -/
def boundId {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    VariableSubstitution σ bound bound free :=
  fun entry => .bvar entry

/-- free 变量的恒等替换。 -/
def freeId {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    VariableSubstitution σ free bound free :=
  fun entry => .fvar entry

/-- 替换结果整体穿过一个新 binder。 -/
def weakenBound {σ : Signature.{u, v, w}}
    {source targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution : VariableSubstitution σ source targetBound targetFree) :
    VariableSubstitution σ source (introduced :: targetBound) targetFree :=
  fun entry => (substitution entry).weakenBound introduced

/-- bound-closed 的替换像整体嵌入任意 binder 上下文。 -/
def embedBoundClosed {σ : Signature.{u, v, w}}
    {source targetFree : SortContext σ}
    (targetBound : SortContext σ)
    (substitution : VariableSubstitution σ source [] targetFree) :
    VariableSubstitution σ source targetBound targetFree :=
  fun entry => (substitution entry).embedBoundClosed targetBound

@[simp] theorem embedBoundClosed_nil {σ : Signature.{u, v, w}}
    {source targetFree : SortContext σ}
    (substitution : VariableSubstitution σ source [] targetFree) :
    @embedBoundClosed σ source targetFree [] substitution =
      (fun {sort} (entry : Variable source sort) => substitution entry) :=
  rfl

@[simp] theorem embedBoundClosed_cons {σ : Signature.{u, v, w}}
    {source targetFree : SortContext σ}
    (introduced : σ.SortSymbol) (rest : SortContext σ)
    (substitution : VariableSubstitution σ source [] targetFree) :
    @embedBoundClosed σ source targetFree (introduced :: rest) substitution =
      @weakenBound σ source rest targetFree introduced
        (@embedBoundClosed σ source targetFree rest substitution) :=
  rfl

/-- bound 替换穿过同一个新 binder。 -/
def liftBound {σ : Signature.{u, v, w}}
    {source targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (substitution : VariableSubstitution σ source targetBound targetFree) :
    VariableSubstitution σ (introduced :: source)
      (introduced :: targetBound) targetFree :=
  fun entry =>
    match entry with
    | .here => .bvar .here
    | .there previous =>
        (substitution previous).weakenBound introduced

/-- 用一个项实例化上下文顶部的 bound 变量。 -/
def instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    VariableSubstitution σ (sort :: bound) bound free :=
  fun entry =>
    match entry with
    | .here => replacement
    | .there previous => .bvar previous

/-- 用一个项实例化 free 上下文顶部变量。 -/
def instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    VariableSubstitution σ (sort :: free) bound free
  | _, .here => replacement
  | _, .there previous => .fvar previous

/-- 原 bound 变量在引入新 binder 后整体后移。 -/
def abstractBound {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    VariableSubstitution σ bound (introduced :: bound) free
  | _, entry => .bvar (.there entry)

/-- free 上下文顶部变量转为最新 binder，其余 free 变量保持不变。 -/
def abstractFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    VariableSubstitution σ (sort :: free) (sort :: bound) free
  | _, .here => .bvar .here
  | _, .there previous => .fvar previous

end VariableSubstitution

/--
同时作用于 bound/free 变量的替换。`.id` 使恒等替换无需检查语法树根节点以下内容。
-/
inductive Substitution (σ : Signature.{u, v, w}) :
    SortContext σ → SortContext σ → SortContext σ → SortContext σ →
      Type (max u v w) where
  | id {bound free : SortContext σ} :
      Substitution σ bound free bound free
  | map {sourceBound sourceFree targetBound targetFree : SortContext σ} :
      VariableSubstitution σ sourceBound targetBound targetFree →
      VariableSubstitution σ sourceFree targetBound targetFree →
      Substitution σ sourceBound sourceFree targetBound targetFree

namespace Substitution

/-- 替换穿过同一个新 binder；恒等替换保持 `.id`。 -/
def liftBound {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol) :
    Substitution σ sourceBound sourceFree targetBound targetFree →
      Substitution σ (introduced :: sourceBound) sourceFree
        (introduced :: targetBound) targetFree
  | .id => .id
  | .map boundSubstitution freeSubstitution =>
      .map (VariableSubstitution.liftBound introduced boundSubstitution)
        (VariableSubstitution.weakenBound introduced freeSubstitution)

/-- 用一个项实例化上下文顶部的 bound 变量。 -/
def instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    Substitution σ (sort :: bound) free bound free :=
  .map (VariableSubstitution.instantiateTop replacement)
    VariableSubstitution.freeId

/-- 用一个项实例化 free 上下文顶部变量。 -/
def instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort) :
    Substitution σ bound (sort :: free) bound free :=
  .map VariableSubstitution.boundId
    (VariableSubstitution.instantiateFreeTop replacement)

/-- free 上下文顶部变量转为最新 binder。 -/
def abstractFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    Substitution σ bound (sort :: free) (sort :: bound) free :=
  .map (VariableSubstitution.abstractBound sort)
    VariableSubstitution.abstractFreeTop

end Substitution

mutual

/-- 执行非恒等项替换。公共入口 `Term.substitute` 负责恒等快路径。 -/
def Term.substituteMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    {sort : σ.SortSymbol} →
      Term σ sourceBound sourceFree sort → Term σ targetBound targetFree sort
  | _, .bvar entry => boundSubstitution entry
  | _, .fvar entry => freeSubstitution entry
  | _, .app function arguments =>
      .app function
        (Arguments.substituteMapped boundSubstitution freeSubstitution arguments)

/-- 执行非恒等参数列替换。 -/
def Arguments.substituteMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    {sorts : List σ.SortSymbol} →
      Arguments σ sourceBound sourceFree sorts →
        Arguments σ targetBound targetFree sorts
  | _, .nil => .nil
  | _, .cons term rest =>
      .cons (term.substituteMapped boundSubstitution freeSubstitution)
        (Arguments.substituteMapped boundSubstitution freeSubstitution rest)

end

/-- 同时替换项的 bound 与 free 变量；恒等情形在根节点直接返回。 -/
def Term.substitute {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    Term σ targetBound targetFree sort :=
  match τ with
  | .id => term
  | .map boundSubstitution freeSubstitution =>
      term.substituteMapped boundSubstitution freeSubstitution

/-- 同时替换参数列的 bound 与 free 变量；恒等情形在根节点直接返回。 -/
def Arguments.substitute {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    Arguments σ targetBound targetFree sorts :=
  match τ with
  | .id => arguments
  | .map boundSubstitution freeSubstitution =>
      arguments.substituteMapped boundSubstitution freeSubstitution

/-- 用同排序项实例化项最外层的 binder。 -/
def Term.instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (body : Term σ (sort :: bound) free resultSort)
    (replacement : Term σ bound free sort) :
    Term σ bound free resultSort :=
  body.substitute (Substitution.instantiateTop replacement)

/-- 用同排序项实例化异质参数列最外层的 binder。 -/
def Arguments.instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ (sort :: bound) free sorts)
    (replacement : Term σ bound free sort) :
    Arguments σ bound free sorts :=
  arguments.substitute (Substitution.instantiateTop replacement)

/-- 用同排序项实例化项 free 上下文顶部变量。 -/
def Term.instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort resultSort : σ.SortSymbol}
    (body : Term σ bound (sort :: free) resultSort)
    (replacement : Term σ bound free sort) :
    Term σ bound free resultSort :=
  body.substitute (Substitution.instantiateFreeTop replacement)

/-- 用同排序项实例化参数列 free 上下文顶部变量。 -/
def Arguments.instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound (sort :: free) sorts)
    (replacement : Term σ bound free sort) :
    Arguments σ bound free sorts :=
  arguments.substitute (Substitution.instantiateFreeTop replacement)

namespace Substitution

/--
替换的 Kleisli 复合。恒等情形直接返回原对象；两个非恒等替换只复合变量像，不在
此处遍历待替换 AST。
-/
def comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree) :
    Substitution σ sourceBound sourceFree targetBound targetFree :=
  match outer, inner with
  | .id, inner => inner
  | outer, .id => outer
  | .map outerBound outerFree, .map innerBound innerFree =>
      .map
        (fun entry => (innerBound entry).substituteMapped
          outerBound outerFree)
        (fun entry => (innerFree entry).substituteMapped
          outerBound outerFree)

end Substitution

namespace Formula

/-- 执行非恒等公式替换。公共入口 `Formula.substitute` 负责恒等快路径。 -/
def substituteMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    Formula σ sourceBound sourceFree → Formula σ targetBound targetFree
  | .falsum => .falsum
  | .truth => .truth
  | .rel relation arguments =>
      .rel relation
        (Arguments.substituteMapped boundSubstitution freeSubstitution arguments)
  | .equal left right =>
      .equal (left.substituteMapped boundSubstitution freeSubstitution)
        (right.substituteMapped boundSubstitution freeSubstitution)
  | .neg body =>
      .neg (substituteMapped boundSubstitution freeSubstitution body)
  | .conj left right =>
      .conj (substituteMapped boundSubstitution freeSubstitution left)
        (substituteMapped boundSubstitution freeSubstitution right)
  | .disj left right =>
      .disj (substituteMapped boundSubstitution freeSubstitution left)
        (substituteMapped boundSubstitution freeSubstitution right)
  | .imp left right =>
      .imp (substituteMapped boundSubstitution freeSubstitution left)
        (substituteMapped boundSubstitution freeSubstitution right)
  | .iff left right =>
      .iff (substituteMapped boundSubstitution freeSubstitution left)
        (substituteMapped boundSubstitution freeSubstitution right)
  | .forallE sort body =>
      .forallE sort
        (substituteMapped
          (VariableSubstitution.liftBound sort boundSubstitution)
          (VariableSubstitution.weakenBound sort freeSubstitution)
          body)
  | .existsE sort body =>
      .existsE sort
        (substituteMapped
          (VariableSubstitution.liftBound sort boundSubstitution)
          (VariableSubstitution.weakenBound sort freeSubstitution)
          body)

/-- 同时替换公式的 bound 与 free 变量；恒等情形在根节点直接返回。 -/
def substitute {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (τ : Substitution σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    Formula σ targetBound targetFree :=
  match τ with
  | .id => formula
  | .map boundSubstitution freeSubstitution =>
      substituteMapped boundSubstitution freeSubstitution formula

/-- 用同排序项实例化公式体最外层的 binder。 -/
def instantiateTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ (sort :: bound) free) :
    Formula σ bound free :=
  body.substitute (Substitution.instantiateTop replacement)

/-- 用同排序项实例化公式 free 上下文顶部变量。 -/
def instantiateFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (replacement : Term σ bound free sort)
    (body : Formula σ bound (sort :: free)) :
    Formula σ bound free :=
  body.substitute (Substitution.instantiateFreeTop replacement)

/--
把 free 上下文顶部变量转为最新 binder。该操作不需要 freshness 或自然数避让证明。
-/
def abstractFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (body : Formula σ bound (sort :: free)) :
    Formula σ (sort :: bound) free :=
  body.substitute Substitution.abstractFreeTop

/-- 量化 free 上下文顶部变量。 -/
def forallFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (sort : σ.SortSymbol)
    (body : Formula σ bound (sort :: free)) :
    Formula σ bound free :=
  .forallE sort body.abstractFreeTop

/-- 存在量化 free 上下文顶部变量。 -/
def existsFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (sort : σ.SortSymbol)
    (body : Formula σ bound (sort :: free)) :
    Formula σ bound free :=
  .existsE sort body.abstractFreeTop

end Formula

mutual

/-- 项的结构节点数。 -/
def Term.size {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol} :
    Term σ bound free sort → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .app _ arguments => arguments.size + 1

/-- 参数列中所有项的结构节点数。 -/
def Arguments.size {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    {sorts : List σ.SortSymbol} → Arguments σ bound free sorts → Nat
  | _, .nil => 0
  | _, .cons term rest => term.size + rest.size

end

namespace Formula

/-- 公式及其项参数的结构节点数。 -/
def size {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} : Formula σ bound free → Nat
  | .falsum => 1
  | .truth => 1
  | .rel _ arguments => arguments.size + 1
  | .equal left right => left.size + right.size + 1
  | .neg body => body.size + 1
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right => left.size + right.size + 1
  | .forallE _ body
  | .existsE _ body => body.size + 1

end Formula

namespace VariableRenaming

/-- 顶部交换是自身的逆。 -/
@[simp] theorem swapTop_swapTop {S : Type u} {Γ : List S}
    {first second resultSort : S}
    (entry : Variable (first :: second :: Γ) resultSort) :
    (swapTop : VariableRenaming (second :: first :: Γ)
      (first :: second :: Γ))
      ((swapTop : VariableRenaming (first :: second :: Γ)
        (second :: first :: Γ)) entry) = entry := by
  cases entry with
  | here => rfl
  | there previous =>
      cases previous <;> rfl

/-- 恒等变量映射穿过 binder 后仍与恒等映射外延相等。 -/
@[simp] theorem lift_id {S : Type u} {Γ : List S} {introduced : S} :
    (lift (introduced := introduced) (id (Γ := Γ)) :
      VariableRenaming (introduced :: Γ) (introduced :: Γ)) =
      (id : VariableRenaming (introduced :: Γ) (introduced :: Γ)) := by
  funext sort entry
  cases entry <;> rfl

/-- 提升保持变量映射复合。 -/
@[simp] theorem lift_comp {S : Type u}
    {source middle target : List S} {introduced : S}
    (outer : VariableRenaming middle target)
    (inner : VariableRenaming source middle) :
    (lift (introduced := introduced) (comp outer inner) :
      VariableRenaming (introduced :: source) (introduced :: target)) =
      (comp (lift outer) (lift inner) :
        VariableRenaming (introduced :: source) (introduced :: target)) := by
  funext sort entry
  cases entry <;> rfl

end VariableRenaming

/-!
## 局部归约方程

这些方程只展开一个语法构造子。后续证明使用它们，而不把完整重命名执行器加入
`simp` 展开集。
-/

@[simp] theorem Term.weakenBound_bvar {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (entry : Variable bound sort) :
    (Term.bvar entry : Term σ bound free sort).weakenBound introduced =
      .bvar (.there entry) :=
  rfl

@[simp] theorem Term.weakenBound_fvar {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (entry : Variable free sort) :
    (Term.fvar entry : Term σ bound free sort).weakenBound introduced =
      .fvar entry :=
  rfl

@[simp] theorem Term.weakenBound_app {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (function : σ.FuncSymbol)
    (arguments : Arguments σ bound free (σ.funcDomain function)) :
    (Term.app function arguments).weakenBound introduced =
      .app function (arguments.weakenBound introduced) :=
  rfl

@[simp] theorem Arguments.weakenBound_nil {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol} :
    (Arguments.nil : Arguments σ bound free []).weakenBound introduced =
      .nil :=
  rfl

@[simp] theorem Arguments.weakenBound_cons {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    {sorts : List σ.SortSymbol} (term : Term σ bound free sort)
    (rest : Arguments σ bound free sorts) :
    (Arguments.cons term rest).weakenBound introduced =
      .cons (term.weakenBound introduced) (rest.weakenBound introduced) :=
  rfl

@[simp] theorem Term.embedBoundClosed_fvar {σ : Signature.{u, v, w}}
    {free : SortContext σ} {sort : σ.SortSymbol}
    (targetBound : SortContext σ) (entry : Variable free sort) :
    (Term.fvar entry : Term σ [] free sort).embedBoundClosed targetBound =
      .fvar entry := by
  induction targetBound with
  | nil => rfl
  | cons introduced rest ih =>
      simp [Term.embedBoundClosed, ih]

@[simp] theorem Term.embedBoundClosed_app {σ : Signature.{u, v, w}}
    {free : SortContext σ} (targetBound : SortContext σ)
    (function : σ.FuncSymbol)
    (arguments : Arguments σ [] free (σ.funcDomain function)) :
    (Term.app function arguments).embedBoundClosed targetBound =
      .app function (arguments.embedBoundClosed targetBound) := by
  induction targetBound with
  | nil => rfl
  | cons introduced rest ih =>
      simp [Term.embedBoundClosed, Arguments.embedBoundClosed, ih]

@[simp] theorem Arguments.embedBoundClosed_nil {σ : Signature.{u, v, w}}
    {free : SortContext σ} (targetBound : SortContext σ) :
    (Arguments.nil : Arguments σ [] free []).embedBoundClosed targetBound =
      .nil := by
  induction targetBound with
  | nil => rfl
  | cons introduced rest ih =>
      simp [Arguments.embedBoundClosed, ih]

@[simp] theorem Arguments.embedBoundClosed_cons {σ : Signature.{u, v, w}}
    {free : SortContext σ} {sort : σ.SortSymbol}
    {sorts : List σ.SortSymbol} (targetBound : SortContext σ)
    (term : Term σ [] free sort) (rest : Arguments σ [] free sorts) :
    (Arguments.cons term rest).embedBoundClosed targetBound =
      .cons (term.embedBoundClosed targetBound)
        (rest.embedBoundClosed targetBound) := by
  induction targetBound with
  | nil => rfl
  | cons introduced targetBound ih =>
      simp [Arguments.embedBoundClosed, Term.embedBoundClosed, ih]

/-- bound 变量不受 free weakening 影响。 -/
@[simp] theorem Term.weakenFree_bvar {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (entry : Variable bound sort) :
    (Term.bvar entry : Term σ bound free sort).weakenFree introduced =
      .bvar entry :=
  rfl

/-- 旧 free 变量在扩展后后移一位。 -/
@[simp] theorem Term.weakenFree_fvar {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (entry : Variable free sort) :
    (Term.fvar entry : Term σ bound free sort).weakenFree introduced =
      .fvar (.there entry) :=
  rfl

/-- free weakening 在函数应用上只递归一层。 -/
@[simp] theorem Term.weakenFree_app {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (function : σ.FuncSymbol)
    (arguments : Arguments σ bound free (σ.funcDomain function)) :
    (Term.app function arguments).weakenFree introduced =
      .app function (arguments.weakenFree introduced) :=
  rfl

/-- 显式 free 弱化重命名直接恢复专用快路径。 -/
theorem Term.renameMapped_id_weaken {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    term.renameMapped VariableRenaming.id
        (VariableRenaming.weaken introduced) =
      term.weakenFree introduced :=
  rfl

@[simp] theorem Arguments.weakenFree_nil {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol} :
    (Arguments.nil : Arguments σ bound free []).weakenFree introduced =
      .nil :=
  rfl

@[simp] theorem Arguments.weakenFree_cons {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    {sorts : List σ.SortSymbol} (term : Term σ bound free sort)
    (rest : Arguments σ bound free sorts) :
    (Arguments.cons term rest).weakenFree introduced =
      .cons (term.weakenFree introduced) (rest.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_falsum {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol} :
    (Formula.falsum : Formula σ bound free).weakenFree introduced = .falsum :=
  rfl

@[simp] theorem Formula.weakenFree_truth {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol} :
    (Formula.truth : Formula σ bound free).weakenFree introduced = .truth :=
  rfl

@[simp] theorem Formula.weakenFree_rel {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (relation : σ.RelSymbol)
    (arguments : Arguments σ bound free (σ.relDomain relation)) :
    (Formula.rel relation arguments).weakenFree introduced =
      .rel relation (arguments.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_equal {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort introduced : σ.SortSymbol}
    (left right : Term σ bound free sort) :
    (Formula.equal left right).weakenFree introduced =
      .equal (left.weakenFree introduced) (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_neg {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (body : Formula σ bound free) :
    body.neg.weakenFree introduced = (body.weakenFree introduced).neg :=
  rfl

@[simp] theorem Formula.weakenFree_conj {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (left right : Formula σ bound free) :
    (left.conj right).weakenFree introduced =
      (left.weakenFree introduced).conj (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_disj {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (left right : Formula σ bound free) :
    (left.disj right).weakenFree introduced =
      (left.weakenFree introduced).disj (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_imp {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (left right : Formula σ bound free) :
    (left.imp right).weakenFree introduced =
      (left.weakenFree introduced).imp (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_iff {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced : σ.SortSymbol}
    (left right : Formula σ bound free) :
    (left.iff right).weakenFree introduced =
      (left.weakenFree introduced).iff (right.weakenFree introduced) :=
  rfl

@[simp] theorem Formula.weakenFree_forallE {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (body : Formula σ (sort :: bound) free) :
    (Formula.forallE sort body).weakenFree introduced =
      .forallE sort (body.weakenFree introduced) :=
  by
    simp [Formula.weakenFree, Formula.rename, Renaming.weakenFree,
      Renaming.free, Formula.renameMapped]

@[simp] theorem Formula.weakenFree_existsE {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {introduced sort : σ.SortSymbol}
    (body : Formula σ (sort :: bound) free) :
    (Formula.existsE sort body).weakenFree introduced =
      .existsE sort (body.weakenFree introduced) :=
  by
    simp [Formula.weakenFree, Formula.rename, Renaming.weakenFree,
      Renaming.free, Formula.renameMapped]

/-!
## 基础代数律

这些定律只依赖语法结构，在内核中统一证明；下游不再为每一种对象公式重复恢复
重命名与替换的恒等性。
-/

namespace Renaming

/-- 恒等重命名穿过 binder 后仍由同一个 `.id` 构造子表示。 -/
@[simp] theorem liftBound_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    liftBound introduced
        (Renaming.id : Renaming σ bound free bound free) =
      (Renaming.id :
        Renaming σ (introduced :: bound) free (introduced :: bound) free) :=
  rfl

end Renaming

/-- 项上的恒等重命名在根节点命中快路径。 -/
@[simp] theorem Term.rename_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    term.rename Renaming.id = term :=
  rfl

/-- 参数列上的恒等重命名在根节点命中快路径。 -/
@[simp] theorem Arguments.rename_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    arguments.rename Renaming.id = arguments :=
  rfl

/-- 公式上的恒等重命名在根节点命中快路径。 -/
@[simp] theorem Formula.rename_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (formula : Formula σ bound free) :
    formula.rename Renaming.id = formula :=
  rfl

mutual

/-- 两次非恒等项重命名可合并为一次遍历。 -/
@[simp] theorem Term.renameMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableRenaming middleBound targetBound)
    (outerFree : VariableRenaming middleFree targetFree)
    (innerBound : VariableRenaming sourceBound middleBound)
    (innerFree : VariableRenaming sourceFree middleFree) :
    {sort : σ.SortSymbol} → (term : Term σ sourceBound sourceFree sort) →
      (term.renameMapped innerBound innerFree).renameMapped
          outerBound outerFree =
        term.renameMapped
          (VariableRenaming.comp outerBound innerBound)
          (VariableRenaming.comp outerFree innerFree)
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments => by
      simp [Term.renameMapped, Arguments.renameMapped_comp]

/-- 两次非恒等参数列重命名可合并为一次遍历。 -/
@[simp] theorem Arguments.renameMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableRenaming middleBound targetBound)
    (outerFree : VariableRenaming middleFree targetFree)
    (innerBound : VariableRenaming sourceBound middleBound)
    (innerFree : VariableRenaming sourceFree middleFree) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ sourceBound sourceFree sorts) →
        (arguments.renameMapped innerBound innerFree).renameMapped
            outerBound outerFree =
          arguments.renameMapped
            (VariableRenaming.comp outerBound innerBound)
            (VariableRenaming.comp outerFree innerFree)
  | _, .nil => rfl
  | _, .cons term rest => by
      simp [Arguments.renameMapped, Term.renameMapped_comp,
        Arguments.renameMapped_comp]

end

/-- 两次非恒等公式重命名可合并为一次遍历。 -/
@[simp] theorem Formula.renameMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableRenaming middleBound targetBound)
    (outerFree : VariableRenaming middleFree targetFree)
    (innerBound : VariableRenaming sourceBound middleBound)
    (innerFree : VariableRenaming sourceFree middleFree) :
    (formula : Formula σ sourceBound sourceFree) →
      (formula.renameMapped innerBound innerFree).renameMapped
          outerBound outerFree =
        formula.renameMapped
          (VariableRenaming.comp outerBound innerBound)
          (VariableRenaming.comp outerFree innerFree)
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments => by
      simp [Formula.renameMapped]
  | .equal left right => by
      simp [Formula.renameMapped]
  | .neg body => by
      simp [Formula.renameMapped, Formula.renameMapped_comp]
  | .conj left right => by
      simp [Formula.renameMapped, Formula.renameMapped_comp]
  | .disj left right => by
      simp [Formula.renameMapped, Formula.renameMapped_comp]
  | .imp left right => by
      simp [Formula.renameMapped, Formula.renameMapped_comp]
  | .iff left right => by
      simp [Formula.renameMapped, Formula.renameMapped_comp]
  | .forallE sort body => by
      simp [Formula.renameMapped, Formula.renameMapped_comp]
  | .existsE sort body => by
      simp [Formula.renameMapped, Formula.renameMapped_comp]

/-- 连续项重命名先复合变换对象，因此只需一次 AST 遍历。 -/
@[simp] theorem Term.rename_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Renaming σ middleBound middleFree targetBound targetFree)
    (inner : Renaming σ sourceBound sourceFree middleBound middleFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    (term.rename inner).rename outer = term.rename (Renaming.comp outer inner) := by
  cases outer <;> cases inner <;>
    simp [Term.rename, Renaming.comp]

/-- 连续参数列重命名先复合变换对象，因此只需一次 AST 遍历。 -/
@[simp] theorem Arguments.rename_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Renaming σ middleBound middleFree targetBound targetFree)
    (inner : Renaming σ sourceBound sourceFree middleBound middleFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    (arguments.rename inner).rename outer =
      arguments.rename (Renaming.comp outer inner) := by
  cases outer <;> cases inner <;>
    simp [Arguments.rename, Renaming.comp]

/-- 连续公式重命名先复合变换对象，因此只需一次 AST 遍历。 -/
@[simp] theorem Formula.rename_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Renaming σ middleBound middleFree targetBound targetFree)
    (inner : Renaming σ sourceBound sourceFree middleBound middleFree)
    (formula : Formula σ sourceBound sourceFree) :
    (formula.rename inner).rename outer =
      formula.rename (Renaming.comp outer inner) := by
  cases outer <;> cases inner <;>
    simp [Formula.rename, Renaming.comp]

mutual

/-- 两次非恒等项替换可合并为一次遍历。 -/
@[simp] theorem Term.substituteMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (innerBound : VariableSubstitution σ sourceBound middleBound middleFree)
    (innerFree : VariableSubstitution σ sourceFree middleBound middleFree) :
    {sort : σ.SortSymbol} → (term : Term σ sourceBound sourceFree sort) →
      (term.substituteMapped innerBound innerFree).substituteMapped
          outerBound outerFree =
        term.substituteMapped
          (fun entry => (innerBound entry).substituteMapped
            outerBound outerFree)
          (fun entry => (innerFree entry).substituteMapped
            outerBound outerFree)
  | _, .bvar _ => rfl
  | _, .fvar _ => rfl
  | _, .app function arguments => by
      simp [Term.substituteMapped, Arguments.substituteMapped_comp]

/-- 两次非恒等参数列替换可合并为一次遍历。 -/
@[simp] theorem Arguments.substituteMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (innerBound : VariableSubstitution σ sourceBound middleBound middleFree)
    (innerFree : VariableSubstitution σ sourceFree middleBound middleFree) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ sourceBound sourceFree sorts) →
        (arguments.substituteMapped innerBound innerFree).substituteMapped
            outerBound outerFree =
          arguments.substituteMapped
            (fun entry => (innerBound entry).substituteMapped
              outerBound outerFree)
            (fun entry => (innerFree entry).substituteMapped
              outerBound outerFree)
  | _, .nil => rfl
  | _, .cons term rest => by
      simp [Arguments.substituteMapped, Term.substituteMapped_comp,
        Arguments.substituteMapped_comp]

end

mutual

/-- 非恒等项替换与 bound weakening 交换。 -/
@[simp] theorem Term.substituteMapped_weakenBound
    {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    {sort : σ.SortSymbol} → (term : Term σ sourceBound sourceFree sort) →
      (term.weakenBound introduced).substituteMapped
          (VariableSubstitution.liftBound introduced boundSubstitution)
          (VariableSubstitution.weakenBound introduced freeSubstitution) =
        (term.substituteMapped boundSubstitution freeSubstitution).weakenBound
          introduced
  | _, .bvar entry => by
      simp [Term.substituteMapped, VariableSubstitution.liftBound]
  | _, .fvar entry => by
      simp [Term.substituteMapped, VariableSubstitution.weakenBound]
  | _, .app function arguments => by
      simp [Term.substituteMapped,
        Arguments.substituteMapped_weakenBound]

/-- 非恒等参数列替换与 bound weakening 交换。 -/
@[simp] theorem Arguments.substituteMapped_weakenBound
    {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ sourceBound sourceFree sorts) →
        (arguments.weakenBound introduced).substituteMapped
            (VariableSubstitution.liftBound introduced boundSubstitution)
            (VariableSubstitution.weakenBound introduced freeSubstitution) =
          (arguments.substituteMapped boundSubstitution
            freeSubstitution).weakenBound introduced
  | _, .nil => rfl
  | _, .cons term rest => by
      simp [Arguments.substituteMapped,
        Term.substituteMapped_weakenBound,
        Arguments.substituteMapped_weakenBound]

end

/-- 连续项替换先复合变量像，因此只需一次 AST 遍历。 -/
@[simp] theorem Term.substitute_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    (term.substitute inner).substitute outer =
      term.substitute (Substitution.comp outer inner) := by
  cases outer <;> cases inner <;>
    simp [Term.substitute, Substitution.comp]

/-- 连续参数列替换先复合变量像，因此只需一次 AST 遍历。 -/
@[simp] theorem Arguments.substitute_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ sourceBound sourceFree sorts) :
    (arguments.substitute inner).substitute outer =
      arguments.substitute (Substitution.comp outer inner) := by
  cases outer <;> cases inner <;>
    simp [Arguments.substitute, Substitution.comp]

namespace VariableSubstitution

/-- bound 恒等替换穿过 binder 后仍是恒等替换。 -/
@[simp] theorem liftBound_boundId {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (liftBound introduced (boundId (bound := bound) (free := free)) :
      VariableSubstitution σ (introduced :: bound)
        (introduced :: bound) free) =
      (boundId (bound := introduced :: bound) (free := free) :
        VariableSubstitution σ (introduced :: bound)
          (introduced :: bound) free) := by
  funext sort entry
  cases entry <;>
    simp [liftBound, boundId, Term.weakenBound, Term.rename,
      Renaming.weakenBound, Renaming.bound, Term.renameMapped,
      VariableRenaming.weaken]

/-- free 恒等替换的结果穿过 binder 后仍是 free 恒等替换。 -/
@[simp] theorem weakenBound_freeId {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (weakenBound introduced (freeId (bound := bound) (free := free)) :
      VariableSubstitution σ free (introduced :: bound) free) =
      (freeId (bound := introduced :: bound) (free := free) :
        VariableSubstitution σ free (introduced :: bound) free) := by
  funext sort entry
  simp [weakenBound, freeId, Term.weakenBound, Term.rename,
    Renaming.weakenBound, Renaming.bound, Term.renameMapped,
    VariableRenaming.id]

/-- 顶部 free 实例化穿过 binder 时，只需提升替换项。 -/
@[simp] theorem weakenBound_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (introduced : σ.SortSymbol)
    (replacement : Term σ bound free sort) :
    (weakenBound introduced (instantiateFreeTop replacement) :
      VariableSubstitution σ (sort :: free) (introduced :: bound) free) =
      (instantiateFreeTop (replacement.weakenBound introduced) :
        VariableSubstitution σ (sort :: free) (introduced :: bound) free) := by
  funext resultSort entry
  cases entry <;>
    simp [weakenBound, instantiateFreeTop, Term.weakenBound, Term.rename,
      Renaming.weakenBound, Renaming.bound, Term.renameMapped,
      VariableRenaming.id]

/-- lifted 变量替换保持非恒等替换复合。 -/
@[simp] theorem liftBound_substituteMapped
    {σ : Signature.{u, v, w}}
    {source middleBound middleFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (inner : VariableSubstitution σ source middleBound middleFree) :
    (liftBound introduced
        (fun {sort} (entry : Variable source sort) =>
          (inner entry).substituteMapped outerBound outerFree) :
      VariableSubstitution σ (introduced :: source)
        (introduced :: targetBound) targetFree) =
      (fun {sort} (entry : Variable (introduced :: source) sort) =>
        (liftBound introduced inner entry).substituteMapped
          (liftBound introduced outerBound)
          (weakenBound introduced outerFree) :
        VariableSubstitution σ (introduced :: source)
          (introduced :: targetBound) targetFree) := by
  funext sort entry
  cases entry with
  | here => rfl
  | there previous =>
      simp [liftBound, Term.substituteMapped_weakenBound]

/-- weakened 变量替换保持非恒等替换复合。 -/
@[simp] theorem weakenBound_substituteMapped
    {σ : Signature.{u, v, w}}
    {source middleBound middleFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (inner : VariableSubstitution σ source middleBound middleFree) :
    (weakenBound introduced
        (fun {sort} (entry : Variable source sort) =>
          (inner entry).substituteMapped outerBound outerFree) :
      VariableSubstitution σ source (introduced :: targetBound) targetFree) =
      (fun {sort} (entry : Variable source sort) =>
        (weakenBound introduced inner entry).substituteMapped
          (liftBound introduced outerBound)
          (weakenBound introduced outerFree) :
        VariableSubstitution σ source (introduced :: targetBound) targetFree) := by
  funext sort entry
  simp [weakenBound, Term.substituteMapped_weakenBound]

end VariableSubstitution

/-- 两次非恒等公式替换可合并为一次遍历。 -/
@[simp] theorem Formula.substituteMapped_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outerBound : VariableSubstitution σ middleBound targetBound targetFree)
    (outerFree : VariableSubstitution σ middleFree targetBound targetFree)
    (innerBound : VariableSubstitution σ sourceBound middleBound middleFree)
    (innerFree : VariableSubstitution σ sourceFree middleBound middleFree) :
    (formula : Formula σ sourceBound sourceFree) →
      (formula.substituteMapped innerBound innerFree).substituteMapped
          outerBound outerFree =
        formula.substituteMapped
          (fun entry => (innerBound entry).substituteMapped
            outerBound outerFree)
          (fun entry => (innerFree entry).substituteMapped
            outerBound outerFree)
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments => by
      simp [Formula.substituteMapped]
  | .equal left right => by
      simp [Formula.substituteMapped]
  | .neg body => by
      simp [Formula.substituteMapped, Formula.substituteMapped_comp]
  | .conj left right => by
      simp [Formula.substituteMapped, Formula.substituteMapped_comp]
  | .disj left right => by
      simp [Formula.substituteMapped, Formula.substituteMapped_comp]
  | .imp left right => by
      simp [Formula.substituteMapped, Formula.substituteMapped_comp]
  | .iff left right => by
      simp [Formula.substituteMapped, Formula.substituteMapped_comp]
  | .forallE sort body => by
      simp [Formula.substituteMapped, Formula.substituteMapped_comp]
  | .existsE sort body => by
      simp [Formula.substituteMapped, Formula.substituteMapped_comp]

/-- 连续公式替换先复合变量像，因此只需一次 AST 遍历。 -/
@[simp] theorem Formula.substitute_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree)
    (formula : Formula σ sourceBound sourceFree) :
    (formula.substitute inner).substitute outer =
      formula.substitute (Substitution.comp outer inner) := by
  cases outer <;> cases inner <;>
    simp [Formula.substitute, Substitution.comp]

namespace Substitution

/-- binder 提升保持替换复合，组合节点不会在量词下重新展开成两次遍历。 -/
@[simp] theorem liftBound_comp {σ : Signature.{u, v, w}}
    {sourceBound sourceFree middleBound middleFree targetBound targetFree :
      SortContext σ}
    (introduced : σ.SortSymbol)
    (outer : Substitution σ middleBound middleFree targetBound targetFree)
    (inner : Substitution σ sourceBound sourceFree middleBound middleFree) :
    liftBound introduced (comp outer inner) =
      comp (liftBound introduced outer) (liftBound introduced inner) := by
  cases outer <;> cases inner <;>
    simp [liftBound, comp]

/-- 恒等替换穿过 binder 后仍由同一个 `.id` 构造子表示。 -/
@[simp] theorem liftBound_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    liftBound introduced
        (Substitution.id : Substitution σ bound free bound free) =
      (Substitution.id :
        Substitution σ (introduced :: bound) free
          (introduced :: bound) free) :=
  rfl

/-- 顶部 free 实例化穿过 binder 时保持捆绑替换形态。 -/
@[simp] theorem liftBound_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (introduced : σ.SortSymbol)
    (replacement : Term σ bound free sort) :
    liftBound introduced (instantiateFreeTop replacement) =
      instantiateFreeTop (replacement.weakenBound introduced) := by
  simp [liftBound, instantiateFreeTop]

end Substitution

/-- 项上的恒等替换在根节点命中快路径。 -/
@[simp] theorem Term.substitute_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (term : Term σ bound free sort) :
    term.substitute Substitution.id = term :=
  rfl

/-- 参数列上的恒等替换在根节点命中快路径。 -/
@[simp] theorem Arguments.substitute_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    arguments.substitute Substitution.id = arguments :=
  rfl

/-- 公式上的恒等替换在根节点命中快路径。 -/
@[simp] theorem Formula.substitute_id {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (formula : Formula σ bound free) :
    formula.substitute Substitution.id = formula :=
  rfl

mutual

/-- 非恒等执行器对 weakened 旧项实例化顶部 free 变量时恢复原项。 -/
@[simp] theorem Term.substituteMapped_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced) :
    {sort : σ.SortSymbol} → (term : Term σ bound free sort) →
      (term.weakenFree introduced).substituteMapped
          VariableSubstitution.boundId
          (VariableSubstitution.instantiateFreeTop replacement) = term
  | _, .bvar _ => by
      simp [Term.substituteMapped, VariableSubstitution.boundId]
  | _, .fvar _ => by
      simp [Term.substituteMapped,
        VariableSubstitution.instantiateFreeTop]
  | _, .app function arguments => by
      simp [Term.substituteMapped,
        Arguments.substituteMapped_weakenFree_instantiateFreeTop]

/-- 非恒等执行器对 weakened 旧参数列实例化顶部 free 变量时恢复原参数列。 -/
@[simp] theorem Arguments.substituteMapped_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ bound free sorts) →
        (arguments.weakenFree introduced).substituteMapped
            VariableSubstitution.boundId
            (VariableSubstitution.instantiateFreeTop replacement) = arguments
  | _, .nil => by
      simp [Arguments.substituteMapped]
  | _, .cons term rest => by
      simp [Arguments.substituteMapped,
        Term.substituteMapped_weakenFree_instantiateFreeTop,
        Arguments.substituteMapped_weakenFree_instantiateFreeTop]

end

/-- 公共替换入口对 weakened 旧项实例化顶部 free 变量时恢复原项。 -/
@[simp] theorem Term.substitute_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced)
    {sort : σ.SortSymbol} (term : Term σ bound free sort) :
    (term.weakenFree introduced).substitute
        (Substitution.instantiateFreeTop replacement) = term := by
  simp [Substitution.instantiateFreeTop, Term.substitute]

/-- 公共替换入口对 weakened 旧参数列实例化顶部 free 变量时恢复原参数列。 -/
@[simp] theorem Arguments.substitute_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) :
    (arguments.weakenFree introduced).substitute
        (Substitution.instantiateFreeTop replacement) = arguments := by
  simp [Substitution.instantiateFreeTop, Arguments.substitute]


/--
规范新自由变量不出现在旧公式中，因此用任意同排序项实例化它都是严格空操作。
-/
@[simp] theorem Formula.instantiateFreeTop_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (formula : Formula σ bound free) →
      (replacement : Term σ bound free introduced) →
        (formula.weakenFree introduced).instantiateFreeTop replacement =
          formula := by
  intro formula
  induction formula <;> intro replacement <;>
    simp_all [Formula.instantiateFreeTop, Formula.substitute,
      Formula.substituteMapped, Substitution.instantiateFreeTop,
      Term.substituteMapped_weakenFree_instantiateFreeTop,
      Arguments.substituteMapped_weakenFree_instantiateFreeTop]

/-- 非恒等执行器对 weakened 旧公式实例化顶部 free 变量时恢复原公式。 -/
@[simp] theorem Formula.substituteMapped_weakenFree_instantiateFreeTop
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol)
    (replacement : Term σ bound free introduced)
    (formula : Formula σ bound free) :
    (formula.weakenFree introduced).substituteMapped
        VariableSubstitution.boundId
        (VariableSubstitution.instantiateFreeTop replacement) = formula := by
  change (formula.weakenFree introduced).instantiateFreeTop replacement =
    formula
  exact Formula.instantiateFreeTop_weakenFree introduced formula replacement

/-!
## 结构化新鲜性

free 上下文扩展本身就是新鲜性证书：旧对象通过 `weakenFree` 嵌入，新变量由
`newestFree` 唯一表示。以下定律说明可计算 strengthening 精确恢复这种嵌入。
-/

/-- 规范新自由变量不能降回扩展前的上下文。 -/
@[simp] theorem Term.strengthenFreeTop?_newestFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (sort : σ.SortSymbol) :
    Term.strengthenFreeTop? sort
        (Term.newestFree (σ := σ) (bound := bound) (free := free) sort) =
      none :=
  rfl

mutual

/-- 项穿过新 free 变量后，strengthening 精确恢复原项。 -/
@[simp] theorem Term.strengthenFreeTop?_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sort : σ.SortSymbol} → (term : Term σ bound free sort) →
      (term.weakenFree introduced).strengthenFreeTop? introduced = some term
  | _, .bvar _ => by
      simp [Term.strengthenFreeTop?]
  | _, .fvar _ => by
      simp [Term.strengthenFreeTop?]
  | _, .app function arguments => by
      simp [Term.strengthenFreeTop?,
        Arguments.strengthenFreeTop?_weakenFree]

/-- 参数列穿过新 free 变量后，strengthening 精确恢复原参数列。 -/
@[simp] theorem Arguments.strengthenFreeTop?_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sorts : List σ.SortSymbol} →
      (arguments : Arguments σ bound free sorts) →
        (arguments.weakenFree introduced).strengthenFreeTop? introduced =
          some arguments
  | _, .nil => by
      simp [Arguments.strengthenFreeTop?]
  | _, .cons term rest => by
      simp [Arguments.strengthenFreeTop?,
        Term.strengthenFreeTop?_weakenFree,
        Arguments.strengthenFreeTop?_weakenFree]

end


/-- 公式穿过新 free 变量后，strengthening 精确恢复原公式。 -/
@[simp] theorem Formula.strengthenFreeTop?_weakenFree
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (formula : Formula σ bound free) →
      (formula.weakenFree introduced).strengthenFreeTop? introduced =
        some formula := by
  intro formula
  induction formula <;>
    simp_all [Formula.strengthenFreeTop?]

mutual

/-- 项 strengthening 成功时，其结果重新 weakening 后等于原项。 -/
theorem Term.weakenFree_of_strengthenFreeTop?_eq_some
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sort : σ.SortSymbol} →
      (expanded : Term σ bound (introduced :: free) sort) →
      (strengthened : Term σ bound free sort) →
      expanded.strengthenFreeTop? introduced = some strengthened →
        strengthened.weakenFree introduced = expanded
  | _, .bvar entry, strengthened, h => by
      simp [Term.strengthenFreeTop?] at h
      subst strengthened
      simp
  | _, .fvar .here, _, h => by
      simp [Term.strengthenFreeTop?] at h
  | _, .fvar (.there entry), strengthened, h => by
      simp [Term.strengthenFreeTop?] at h
      subst strengthened
      simp
  | _, .app function arguments, strengthened, h => by
      cases hArguments :
          Arguments.strengthenFreeTop? introduced arguments with
      | none =>
          simp [Term.strengthenFreeTop?, hArguments] at h
      | some reducedArguments =>
          simp [Term.strengthenFreeTop?, hArguments] at h
          subst strengthened
          simp [Arguments.weakenFree_of_strengthenFreeTop?_eq_some
              introduced arguments reducedArguments hArguments]

/-- 参数列 strengthening 成功时，其结果重新 weakening 后等于原参数列。 -/
theorem Arguments.weakenFree_of_strengthenFreeTop?_eq_some
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    {sorts : List σ.SortSymbol} →
      (expanded : Arguments σ bound (introduced :: free) sorts) →
      (strengthened : Arguments σ bound free sorts) →
      expanded.strengthenFreeTop? introduced = some strengthened →
        strengthened.weakenFree introduced = expanded
  | _, .nil, strengthened, h => by
      simp [Arguments.strengthenFreeTop?] at h
      subst strengthened
      simp
  | _, .cons term rest, strengthened, h => by
      cases hTerm : term.strengthenFreeTop? introduced with
      | none =>
          simp [Arguments.strengthenFreeTop?, hTerm] at h
      | some reducedTerm =>
          cases hRest : rest.strengthenFreeTop? introduced with
          | none =>
              simp [Arguments.strengthenFreeTop?, hTerm, hRest] at h
          | some reducedRest =>
              simp [Arguments.strengthenFreeTop?, hTerm, hRest] at h
              subst strengthened
              simp [Term.weakenFree_of_strengthenFreeTop?_eq_some
                  introduced term reducedTerm hTerm,
                Arguments.weakenFree_of_strengthenFreeTop?_eq_some
                  introduced rest reducedRest hRest]

end


/-- 公式 strengthening 成功时，其结果重新 weakening 后等于原公式。 -/
theorem Formula.weakenFree_of_strengthenFreeTop?_eq_some
    {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (introduced : σ.SortSymbol) :
    (expanded : Formula σ bound (introduced :: free)) →
    (strengthened : Formula σ bound free) →
    expanded.strengthenFreeTop? introduced = some strengthened →
      strengthened.weakenFree introduced = expanded := by
  intro expanded strengthened h
  fun_induction Formula.strengthenFreeTop? introduced expanded <;>
    cases h <;>
    simp_all
  all_goals
    first
    | solve_by_elim [Arguments.weakenFree_of_strengthenFreeTop?_eq_some]
    | constructor <;>
        solve_by_elim [Term.weakenFree_of_strengthenFreeTop?_eq_some]

end FirstOrder
end Logic
end YesMetaZFC
