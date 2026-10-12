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
  | here => exact Nat.zero_lt_succ _
  | there previous ih => exact Nat.succ_lt_succ ih

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
  induction entry with
  | here => rfl
  | there previous ih => exact congrArg Nat.succ ih

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
  | cons head tail ih => exact congrArg Nat.succ ih

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
  | formula :: rest =>
      match rest with
      | [] => formula
      | _ :: _ => .conj formula (conjunctionList rest)

/-- 右结合有限析取；空列表解释为假。 -/
def disjunctionList {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} :
    List (Formula σ bound free) → Formula σ bound free
  | [] => .falsum
  | formula :: rest =>
      match rest with
      | [] => formula
      | _ :: _ => .disj formula (disjunctionList rest)

end Formula

end FirstOrder
end Logic
end YesMetaZFC
