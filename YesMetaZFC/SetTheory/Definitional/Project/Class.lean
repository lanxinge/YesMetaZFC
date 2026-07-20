import YesMetaZFC.SetTheory.Definitional.Project

/-!
# 项目原子核中的 Jech 风格类

类不是对象语言中的新对象。语法侧仍由一个额外 bound 位置的项目公式表示；语义侧是
对象域上的谓词。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

universe u

/-- 带 `depth` 个外层 bound 参数的可定义类。 -/
abbrev DefinableClass (depth : Nat) := Formula 1 (depth + 1)

namespace DefinableClass

/-- 类公式中代表当前元素的项。 -/
def element {depth : Nat} : Term (depth + 1) :=
  Term.newest

/-- 把一个集合项视为由其元素定义的类。 -/
def ofSet {depth : Nat} (set : Term depth) : DefinableClass depth :=
  .mem element set.weaken

/-- 全类。 -/
def universal {depth : Nat} : DefinableClass depth :=
  Formula.extensionalEq element element

/-- 类的补。 -/
def complement {depth : Nat} (collection : DefinableClass depth) :
    DefinableClass depth :=
  .neg collection

/-- 类的交。 -/
def inter {depth : Nat} (left right : DefinableClass depth) :
    DefinableClass depth :=
  .conj left right

/-- 类的并。 -/
def union {depth : Nat} (left right : DefinableClass depth) :
    DefinableClass depth :=
  .disj left right

/-- 类的差。 -/
def diff {depth : Nat} (left right : DefinableClass depth) :
    DefinableClass depth :=
  .conj left (.neg right)

/-- 一个项属于公式定义的类。 -/
def contains {depth : Nat} (collection : DefinableClass depth)
    (term : Term depth) : Formula 1 depth :=
  collection.instantiateTop term

/-- 两个类逐点等价。 -/
def equal {depth : Nat} (left right : DefinableClass depth) :
    Formula 1 depth :=
  .forallE (.iff left right)

/-- 类包含。 -/
def subset {depth : Nat} (left right : DefinableClass depth) :
    Formula 1 depth :=
  .forallE (.imp left right)

private def atInnermost {depth : Nat} (collection : DefinableClass depth) :
    Formula 1 ((depth + 1) + 1) :=
  collection.bind <| Fin.cases Term.newest fun parameter =>
    .bound parameter.succ.succ

/-- Jech 的并类。 -/
def sUnion {depth : Nat} (collection : DefinableClass depth) :
    DefinableClass depth :=
  .existsE <|
    .conj (.mem element.weaken Term.newest)
      collection.atInnermost

end DefinableClass

/-- 一个对象域上的类。 -/
abbrev Class (α : Type u) := α → Prop

namespace Class

def Equal {α : Type u} (left right : Class α) : Prop :=
  ∀ value, left value ↔ right value

def Subset {α : Type u} (left right : Class α) : Prop :=
  ∀ value, left value → right value

def universal {α : Type u} : Class α :=
  fun _ => True

def complement {α : Type u} (collection : Class α) : Class α :=
  fun value => ¬ collection value

def inter {α : Type u} (left right : Class α) : Class α :=
  fun value => left value ∧ right value

def union {α : Type u} (left right : Class α) : Class α :=
  fun value => left value ∨ right value

def diff {α : Type u} (left right : Class α) : Class α :=
  fun value => left value ∧ ¬ right value

def ofSet (ℳ : Structure.{u}) (set : ℳ.Domain) : Class ℳ.Domain :=
  fun value => ℳ.mem value set

def sUnion (ℳ : Structure.{u}) (collection : Class ℳ.Domain) :
    Class ℳ.Domain :=
  fun value => ∃ set, ℳ.mem value set ∧ collection set

theorem ext {α : Type u} {left right : Class α}
    (hEqual : Equal left right) : left = right :=
  funext fun value => propext (hEqual value)

theorem equal_iff {α : Type u} {left right : Class α} :
    Equal left right ↔ left = right := by
  constructor
  · exact ext
  · intro h
    cases h
    intro value
    rfl

end Class

namespace DefinableClass

/-- 公式定义类在给定结构和参数环境中的语义。 -/
def denote {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (collection : DefinableClass depth) :
    Class ℳ.Domain :=
  fun value => Formula.satisfies (env.push value) collection

theorem denote_universal {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) :
    denote env (universal : DefinableClass depth) = Class.universal := by
  funext value
  apply propext
  simp only [denote, universal, Class.universal]
  rw [Formula.satisfies_extensionalEq_iff]
  simp

theorem denote_inter {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (left right : DefinableClass depth) :
    denote env (inter left right) =
      Class.inter (denote env left) (denote env right) := by
  funext value
  apply propext
  simp only [denote, inter, Class.inter]
  deep_rfl

theorem denote_union {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (left right : DefinableClass depth) :
    denote env (union left right) =
      Class.union (denote env left) (denote env right) := by
  funext value
  apply propext
  simp only [denote, union, Class.union]
  deep_rfl

theorem denote_diff {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (left right : DefinableClass depth) :
    denote env (diff left right) =
      Class.diff (denote env left) (denote env right) := by
  funext value
  apply propext
  simp only [denote, diff, Class.diff]
  deep_rfl

theorem denote_ofSet {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (set : Term depth) :
    denote env (ofSet set) =
      Class.ofSet ℳ (Definitional.Term.eval env set) := by
  funext value
  apply propext
  simp only [denote, ofSet, element, Class.ofSet, Formula.satisfies_mem_iff]
  change ℳ.mem (Definitional.Term.eval (env.push value) Term.newest)
      (Definitional.Term.eval (env.push value) set.weaken) ↔
    ℳ.mem value (Definitional.Term.eval env set)
  rw [Definitional.Term.eval_weaken]
  rfl

theorem satisfies_equal_iff {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (left right : DefinableClass depth) :
    Formula.satisfies env (equal left right) ↔
      Class.Equal (denote env left) (denote env right) := by
  simp only [equal, Class.Equal, denote]
  deep_rfl

theorem satisfies_subset_iff {ℳ : Structure.{u}} {depth : Nat}
    (env : Env ℳ depth) (left right : DefinableClass depth) :
    Formula.satisfies env (subset left right) ↔
      Class.Subset (denote env left) (denote env right) := by
  simp only [subset, Class.Subset, denote]
  deep_rfl

end DefinableClass

end Project
end Definitional
end SetTheory
end YesMetaZFC
