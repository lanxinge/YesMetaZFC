import YesMetaZFC.Logic.Theory.Basic

/-!
# 内在类型公式的 Hilbert 编译

本模块把丰富的一阶公式编译到仅使用原子式、等式、否定、蕴含与全称量词的
Hilbert 片段。编译保持 bound/free 上下文索引，因此不需要作用域、排序、闭合性
或新鲜性证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

namespace Formula

/-- 只用 Hilbert 片段构造子的恒真式。 -/
def hilbert_truth {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (anchorSort : σ.SortSymbol) :
    Formula σ bound free :=
  .forallE anchorSort
    (.equal (.bvar .here) (.bvar .here))

/-- Hilbert 片段中的假式定义为恒真式的否定。 -/
def hilbert_falsum {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (anchorSort : σ.SortSymbol) :
    Formula σ bound free :=
  .neg (hilbert_truth anchorSort)

/-- Hilbert 编码合取：`¬(φ → ¬ψ)`。 -/
def hilbert_conj {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    (left right : Formula σ bound free) :
    Formula σ bound free :=
  .neg (.imp left (.neg right))

/-- Hilbert 编码双条件：两个方向蕴含的编码合取。 -/
def hilbert_iff {σ : Signature.{u, v, w}}
    {bound free : SortContext σ}
    (left right : Formula σ bound free) :
    Formula σ bound free :=
  hilbert_conj (.imp left right) (.imp right left)

/-- 把丰富公式归约到 `¬/→/∀/=/原子` Hilbert 片段。 -/
def hilbertize {σ : Signature.{u, v, w}}
    (anchorSort : σ.SortSymbol) :
    {bound free : SortContext σ} →
      Formula σ bound free → Formula σ bound free
  | _, _, .falsum => hilbert_falsum anchorSort
  | _, _, .truth => hilbert_truth anchorSort
  | _, _, .rel relation arguments => .rel relation arguments
  | _, _, .equal left right => .equal left right
  | _, _, .neg body => .neg (hilbertize anchorSort body)
  | _, _, .conj left right =>
      hilbert_conj
        (hilbertize anchorSort left)
        (hilbertize anchorSort right)
  | _, _, .disj left right =>
      .imp (.neg (hilbertize anchorSort left))
        (hilbertize anchorSort right)
  | _, _, .imp antecedent consequent =>
      .imp (hilbertize anchorSort antecedent)
        (hilbertize anchorSort consequent)
  | _, _, .iff left right =>
      hilbert_iff
        (hilbertize anchorSort left)
        (hilbertize anchorSort right)
  | _, _, .forallE sort body =>
      .forallE sort (hilbertize anchorSort body)
  | _, _, .existsE sort body =>
      .neg (.forallE sort (.neg (hilbertize anchorSort body)))

@[simp] theorem hilbertize_truth {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (anchorSort : σ.SortSymbol) :
    hilbertize anchorSort (.truth : Formula σ bound free) =
      hilbert_truth anchorSort :=
  rfl

@[simp] theorem hilbertize_falsum {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (anchorSort : σ.SortSymbol) :
    hilbertize anchorSort (.falsum : Formula σ bound free) =
      hilbert_falsum anchorSort :=
  rfl

/-- Hilbert 编译是变量替换的结构同态。 -/
@[simp] theorem hilbertize_substituteMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (anchorSort : σ.SortSymbol)
    (boundSubstitution :
      VariableSubstitution σ sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution σ sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    hilbertize anchorSort
        (formula.substituteMapped boundSubstitution freeSubstitution) =
      (hilbertize anchorSort formula).substituteMapped
        boundSubstitution freeSubstitution := by
  induction formula generalizing targetBound targetFree <;>
    simp_all [hilbertize, hilbert_truth, hilbert_falsum,
      hilbert_conj, hilbert_iff, Formula.substituteMapped,
      Term.substituteMapped, VariableSubstitution.liftBound]

/-- Hilbert 编译与任意变量替换交换。 -/
@[simp] theorem hilbertize_substitute {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (anchorSort : σ.SortSymbol)
    (substitution :
      Substitution σ sourceBound sourceFree targetBound targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    hilbertize anchorSort (formula.substitute substitution) =
      (hilbertize anchorSort formula).substitute substitution := by
  cases substitution with
  | id => rfl
  | map boundSubstitution freeSubstitution =>
      exact hilbertize_substituteMapped anchorSort
        boundSubstitution freeSubstitution formula

/-- Hilbert 编译与顶部 bound 槽实例化交换。 -/
@[simp] theorem hilbertize_instantiateTop {σ : Signature.{u, v, w}}
    {free : SortContext σ} {sort : σ.SortSymbol}
    (anchorSort : σ.SortSymbol)
    (replacement : Term σ [] free sort)
    (formula : Formula σ [sort] free) :
    hilbertize anchorSort (formula.instantiateTop replacement) =
      (hilbertize anchorSort formula).instantiateTop replacement := by
  simp [Formula.instantiateTop]

/-- Hilbert 编译与顶部自由变量抽象交换。 -/
@[simp] theorem hilbertize_abstractFreeTop {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    (anchorSort : σ.SortSymbol)
    (formula : Formula σ bound (sort :: free)) :
    hilbertize anchorSort formula.abstractFreeTop =
      (hilbertize anchorSort formula).abstractFreeTop := by
  simp [Formula.abstractFreeTop]

/-- Hilbert 编译在其像上幂等。 -/
@[simp] theorem hilbertize_idempotent {σ : Signature.{u, v, w}}
    {bound free : SortContext σ} (anchorSort : σ.SortSymbol)
    (formula : Formula σ bound free) :
    hilbertize anchorSort (hilbertize anchorSort formula) =
      hilbertize anchorSort formula := by
  induction formula <;>
    simp_all [hilbertize, hilbert_truth, hilbert_falsum,
      hilbert_conj, hilbert_iff]


/-- Hilbert 编译与类型化重命名交换。 -/
@[simp] theorem hilbertize_renameMapped {σ : Signature.{u, v, w}}
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (anchorSort : σ.SortSymbol)
    (boundRenaming : VariableRenaming sourceBound targetBound)
    (freeRenaming : VariableRenaming sourceFree targetFree)
    (formula : Formula σ sourceBound sourceFree) :
    hilbertize anchorSort (formula.renameMapped boundRenaming freeRenaming) =
      (hilbertize anchorSort formula).renameMapped boundRenaming freeRenaming := by
  induction formula generalizing targetBound targetFree <;>
    simp_all [hilbertize, hilbert_truth, hilbert_falsum, hilbert_conj, hilbert_iff,
      Formula.renameMapped, Term.renameMapped, VariableRenaming.lift]

/-- 编译像上的归纳只需五种原始构造；真、假与派生联结词统一在这里展开。 -/
@[elab_as_elim] theorem hilbertize_induction {σ : Signature.{u, v, w}}
    (anchorSort : σ.SortSymbol)
    {motive : {bound free : SortContext σ} → Formula σ bound free → Prop}
    (relation : ∀ {bound free} (r : σ.RelSymbol)
      (args : Arguments σ bound free (σ.relDomain r)), motive (.rel r args))
    (equality : ∀ {bound free sort} (left right : Term σ bound free sort),
      motive (.equal left right))
    (negation : ∀ {bound free} (body : Formula σ bound free),
      motive body → motive (.neg body))
    (implication : ∀ {bound free} (left right : Formula σ bound free),
      motive left → motive right → motive (.imp left right))
    (universal : ∀ {bound free} (sort : σ.SortSymbol)
      (body : Formula σ (sort :: bound) free), motive body → motive (.forallE sort body))
    {bound free} (formula : Formula σ bound free) : motive (hilbertize anchorSort formula) := by
  have truth {bound free} : motive (hilbert_truth (bound := bound) (free := free) anchorSort) :=
    universal anchorSort _ (equality (.bvar .here) (.bvar .here))
  induction formula with
  | falsum => exact negation _ truth
  | truth => exact truth
  | rel r args => exact relation r args
  | equal left right => exact equality left right
  | neg body ih => exact negation _ ih
  | conj left right ihLeft ihRight =>
      exact negation _ (implication _ _ ihLeft (negation _ ihRight))
  | disj left right ihLeft ihRight =>
      exact implication _ _ (negation _ ihLeft) ihRight
  | imp left right ihLeft ihRight => exact implication _ _ ihLeft ihRight
  | iff left right ihLeft ihRight =>
      exact negation _ (implication _ _ (implication _ _ ihLeft ihRight)
        (negation _ (implication _ _ ihRight ihLeft)))
  | forallE sort body ih => exact universal sort _ ih
  | existsE sort body ih => exact negation _ (universal sort _ (negation _ ih))

end Formula

namespace Theory

/-- 理论逐闭句执行 Hilbert 编译后的像。 -/
def hilbertize {σ : Signature.{u, v, w}}
    (anchorSort : σ.SortSymbol) (theory : Theory σ) :
    Theory σ :=
  fun encoded =>
    ∃ source, theory source ∧
      encoded = Formula.hilbertize anchorSort source

/-- 原理论成员进入其 Hilbert 编译像。 -/
theorem hilbertize_mem {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ}
    {formula : Sentence σ} (hTheory : theory formula) :
    Theory.hilbertize anchorSort theory
      (Formula.hilbertize anchorSort formula) :=
  ⟨formula, hTheory, rfl⟩

/-- 二次 Hilbert 编译理论包含于一次编译像。 -/
theorem hilbertize_idempotent_subset {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ} :
    Theory.Extends
      (Theory.hilbertize anchorSort theory)
      (Theory.hilbertize anchorSort
        (Theory.hilbertize anchorSort theory)) := by
  intro formula hFormula
  rcases hFormula with ⟨middle, ⟨source, hSource, rfl⟩, rfl⟩
  exact ⟨source, hSource,
    Formula.hilbertize_idempotent anchorSort source⟩

/-- 一次 Hilbert 编译像包含于二次编译理论。 -/
theorem hilbertize_subset_idempotent {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ} :
    Theory.Extends
      (Theory.hilbertize anchorSort
        (Theory.hilbertize anchorSort theory))
      (Theory.hilbertize anchorSort theory) := by
  intro formula hFormula
  rcases hFormula with ⟨source, hSource, rfl⟩
  exact ⟨Formula.hilbertize anchorSort source,
    ⟨source, hSource, rfl⟩,
    (Formula.hilbertize_idempotent anchorSort source).symm⟩

end Theory
end FirstOrder
end Logic
end YesMetaZFC
