import YesMetaZFC.SetTheory.Definitional.Project
import YesMetaZFC.SetTheory.Definitional.Project.Class.Syntax
/-!
# 项目原子核中的 Jech 风格类
本模块只补充对象域谓词与可定义类的语义解释；纯语法构造位于 `Project.Class.Syntax`。
-/
namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project
universe u
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
theorem ext {α : Type u} {left right : Class α} (hEqual : Equal left right) : left = right :=
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
def denote {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth) (collection : DefinableClass depth) :
    Class ℳ.Domain :=
  fun value => Formula.satisfies (env.push value) collection
theorem denote_universal {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth) :
    denote env (universal : DefinableClass depth) = Class.universal := by
  funext value
  apply propext
  simp only [denote, universal, Class.universal]
  rw [Formula.satisfies_extensionalEq_iff]
  simp
theorem denote_inter {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth) (left right : DefinableClass depth) :
    denote env (inter left right) =
      Class.inter (denote env left) (denote env right) := by
  funext value
  apply propext
  simp only [denote, inter, Class.inter]
  deep_rfl
theorem denote_union {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth) (left right : DefinableClass depth) :
    denote env (union left right) =
      Class.union (denote env left) (denote env right) := by
  funext value
  apply propext
  simp only [denote, union, Class.union]
  deep_rfl
theorem denote_diff {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth) (left right : DefinableClass depth) :
    denote env (diff left right) =
      Class.diff (denote env left) (denote env right) := by
  funext value
  apply propext
  simp only [denote, diff, Class.diff]
  deep_rfl
theorem denote_ofSet {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth) (set : Term depth) :
    denote env (ofSet set) =
      Class.ofSet ℳ (Definitional.Term.eval env set) := by
  funext value
  apply propext
  simp only [denote, ofSet, element, Class.ofSet, Formula.satisfies_mem_iff]
  change ℳ.mem (Definitional.Term.eval (env.push value) Term.newest) (Definitional.Term.eval (env.push value) set.weaken) ↔
    ℳ.mem value (Definitional.Term.eval env set)
  rw [Definitional.Term.eval_weaken]
  rfl
theorem satisfies_equal_iff {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth) (left right : DefinableClass depth) :
    Formula.satisfies env (equal left right) ↔
      Class.Equal (denote env left) (denote env right) := by
  simp only [equal, Class.Equal, denote]
  deep_rfl
theorem satisfies_subset_iff {ℳ : Structure.{u}} {depth : Nat} (env : Env ℳ depth) (left right : DefinableClass depth) :
    Formula.satisfies env (subset left right) ↔
      Class.Subset (denote env left) (denote env right) := by
  simp only [subset, Class.Subset, denote]
  deep_rfl
end DefinableClass
end Project
end Definitional
end SetTheory
end YesMetaZFC
