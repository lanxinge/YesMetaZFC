import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Language
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Algebra
import YesMetaZFC.Logic.FirstOrder.FreshVariable
import YesMetaZFC.Logic.FirstOrder.LevyHierarchy

/-!
# 内在公式模板

公式条件不再以任意的“项到公式”函数出现，而是由固定 free 槽位中的公式模板
通过类型化替换生成。这样条件天然穿过 bound/free 替换，不需要为每个 verifier
重复证明运输合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 没有 bound 槽位、具有固定 free 槽位的内在公式模板。 -/
structure FormulaTemplate (templateFree : SetContext) where
  body : SetFormula [] templateFree

namespace FormulaTemplate

/-- 将模板的 free 槽位一次性映射到目标上下文。 -/
def instantiate
    {templateFree bound free : SetContext}
    (template : FormulaTemplate templateFree)
    (substitution : VariableSubstitution signature templateFree bound free) :
    SetFormula bound free :=
  template.body.substituteMapped
    VariableSubstitution.empty substitution

/-- 模板 body 的 `Delta0` 分类沿类型化实例化直接保持。 -/
theorem instantiate_delta0
    {templateFree bound free : SetContext}
    {ℬ : Formula.LevyBound signature}
    (template : FormulaTemplate templateFree)
    (hBody : Formula.IsDelta0 ℬ template.body)
    (substitution :
      VariableSubstitution signature templateFree bound free) :
    Formula.IsDelta0 ℬ
      (template.instantiate substitution) := by
  exact Formula.IsDelta0.substituteMapped
    (boundSubstitution := VariableSubstitution.empty)
    (freeSubstitution := substitution)
    hBody

/-- 模板实例化再做任意替换时，直接复合槽位项而不重复遍历模板树。 -/
@[simp] theorem instantiate_substituteMapped
    {templateFree sourceBound sourceFree targetBound targetFree : SetContext}
    (template : FormulaTemplate templateFree)
    (substitution :
      VariableSubstitution signature templateFree sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    (template.instantiate substitution).substituteMapped
        boundSubstitution freeSubstitution =
      template.instantiate
        (VariableSubstitution.postcompose boundSubstitution freeSubstitution substitution) := by
  change
    (template.body.substituteMapped
      VariableSubstitution.empty substitution).substituteMapped
        boundSubstitution freeSubstitution =
      template.body.substituteMapped VariableSubstitution.empty
        (fun {sort} entry =>
          (substitution entry).substituteMapped
            boundSubstitution freeSubstitution)
  rw [Formula.substituteMapped_comp]
  congr
  funext sort entry
  exact nomatch entry

/-- 模板实例化与顶部 bound 替换交换，公式树只遍历一次。 -/
@[simp] theorem instantiate_top
    {templateFree bound free : SetContext}
    (template : FormulaTemplate templateFree)
    (substitution :
      VariableSubstitution signature templateFree
        (SetSort.set :: bound) free)
    (replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
      (template.instantiate substitution) =
      template.instantiate
        (fun {_sort} entry =>
          (substitution entry).substituteMapped
            (VariableSubstitution.instantiateTop replacement)
            VariableSubstitution.freeId) := by
  exact instantiate_substituteMapped template substitution _ _


/-- 模板实例化与规范 bound 打开交换，公式树只遍历一次。 -/
@[simp] theorem instantiate_openBoundTop
    {templateFree free : SetContext}
    (template : FormulaTemplate templateFree)
    (substitution :
      VariableSubstitution signature templateFree [SetSort.set] free) :
    Formula.openBoundTop (σ := signature) SetSort.set
        (template.instantiate substitution) =
      template.instantiate
        (fun {_sort} entry =>
          Term.openBoundTop (σ := signature) SetSort.set
            (substitution entry)) := by
  exact instantiate_substituteMapped template substitution _ _


/-- 顶部实例化的映射表示直接恢复穿过 binder 的项。 -/
@[simp] theorem term_substituteMapped_instantiateTop_weakenBound
    {bound free : SetContext}
    (term replacement : SetTerm bound free) :
    (term.weakenBound SetSort.set).substituteMapped
        (VariableSubstitution.instantiateTop replacement)
        VariableSubstitution.freeId = term := by
  change (term.weakenBound SetSort.set).instantiateTop replacement = term
  exact Term.instantiateTop_weakenBound replacement term

/-- 两层 binder 下替换外层槽位时，内层弱化保持并直接恢复原项。 -/
@[simp] theorem term_substituteMapped_liftBound_instantiateTop_two_weakenBound
    {bound free : SetContext}
    {outerSort innerSort resultSort : SetSort}
    (term : Term signature bound free resultSort)
    (replacement : Term signature bound free outerSort) :
    ((term.weakenBound outerSort).weakenBound innerSort).substituteMapped
        (VariableSubstitution.liftBound innerSort
          (VariableSubstitution.instantiateTop replacement))
        VariableSubstitution.freeId =
      term.weakenBound innerSort := by
  calc
    _ = ((term.weakenBound outerSort).substituteMapped
          (VariableSubstitution.instantiateTop replacement)
          VariableSubstitution.freeId).weakenBound innerSort := by
        simpa [VariableSubstitution.weakenBound,
          VariableSubstitution.freeId] using
          (Term.substituteMapped_weakenBound
            (σ := signature) innerSort
            (VariableSubstitution.instantiateTop replacement)
            (VariableSubstitution.freeId :
              VariableSubstitution signature free bound free)
            (term.weakenBound outerSort))
    _ = term.weakenBound innerSort := by
      congr 1
      change (term.weakenBound outerSort).instantiateTop replacement = term
      exact Term.instantiateTop_weakenBound replacement term

abbrev Unary := FormulaTemplate [SetSort.set]
abbrev Binary := FormulaTemplate [SetSort.set, SetSort.set]
abbrev Ternary :=
  FormulaTemplate
    [SetSort.set, SetSort.set, SetSort.set]
abbrev Quaternary :=
  FormulaTemplate
    [SetSort.set, SetSort.set, SetSort.set, SetSort.set]

/-- 单参数模板的类型化应用。 -/
def apply_one
    (template : Unary)
    {bound free : SetContext}
    (term : SetTerm bound free) :
    SetFormula bound free :=
  template.instantiate
    (VariableSubstitution.cons term VariableSubstitution.empty)

/-- 双参数模板的类型化应用。 -/
def apply_two
    (template : Binary)
    {bound free : SetContext}
    (left right : SetTerm bound free) :
    SetFormula bound free :=
  template.instantiate
    (VariableSubstitution.cons left
      (VariableSubstitution.cons right VariableSubstitution.empty))

/-! 三参数模板为 schema 条件保留 formula、certificate、base 三个槽位。 -/

def apply_three
    (template : Ternary)
    {bound free : SetContext}
    (first second third : SetTerm bound free) :
    SetFormula bound free :=
  template.instantiate
    (VariableSubstitution.cons first
      (VariableSubstitution.cons second
        (VariableSubstitution.cons third VariableSubstitution.empty)))

/-- 四参数模板的类型化应用。 -/
def apply_four
    (template : Quaternary)
    {bound free : SetContext}
    (first second third fourth : SetTerm bound free) :
    SetFormula bound free :=
  template.instantiate
    (VariableSubstitution.cons first
      (VariableSubstitution.cons second
        (VariableSubstitution.cons third
          (VariableSubstitution.cons fourth VariableSubstitution.empty))))

/-- 单参数模板的实例化与后续替换交换。 -/
@[simp] theorem apply_one_substituteMapped
    (template : Unary)
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (term : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    (template.apply_one term).substituteMapped
        boundSubstitution freeSubstitution =
      template.apply_one
        (term.substituteMapped boundSubstitution freeSubstitution) := by
  simp only [apply_one, instantiate_substituteMapped,
    VariableSubstitution.map_cons, VariableSubstitution.map_empty]


/-- 双参数模板的实例化与后续替换交换。 -/
@[simp] theorem apply_two_substituteMapped
    (template : Binary)
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (left right : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    (template.apply_two left right).substituteMapped
        boundSubstitution freeSubstitution =
      template.apply_two
        (left.substituteMapped boundSubstitution freeSubstitution)
        (right.substituteMapped boundSubstitution freeSubstitution) := by
  simp only [apply_two, instantiate_substituteMapped,
    VariableSubstitution.map_cons, VariableSubstitution.map_empty]


/-- 单参数模板沿 free 上下文顶部弱化。 -/
@[simp] theorem apply_one_weakenFree
    (template : Unary)
    {bound free : SetContext}
    (introduced : SetSort)
    (term : SetTerm bound free) :
    (template.apply_one term).weakenFree introduced =
      template.apply_one (term.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  rw [← Formula.substituteMapped_of_renaming]
  rw [apply_one_substituteMapped]
  congr 1
  exact Term.substituteMapped_of_renaming
    (VariableRenaming.weaken introduced) term

/-- 双参数模板沿 free 上下文顶部弱化。 -/
@[simp] theorem apply_two_weakenFree
    (template : Binary)
    {bound free : SetContext}
    (introduced : SetSort)
    (left right : SetTerm bound free) :
    (template.apply_two left right).weakenFree introduced =
      template.apply_two (left.weakenFree introduced)
        (right.weakenFree introduced) := by
  rw [Formula.weakenFree_eq_renameMapped]
  rw [← Formula.substituteMapped_of_renaming]
  rw [apply_two_substituteMapped]
  congr 1
  · exact Term.substituteMapped_of_renaming
      (VariableRenaming.weaken introduced) left
  · exact Term.substituteMapped_of_renaming
      (VariableRenaming.weaken introduced) right

/-- 单参数模板以顶部 bound 变量为参数时直接执行 β 归约。 -/
@[simp] theorem apply_one_instantiateTop_bvar
    (template : Unary)
    {free : SetContext}
    (replacement : SetOpenTerm free) :
    Formula.instantiateTop replacement
        (template.apply_one (.bvar .here)) =
      template.apply_one replacement := by
  exact apply_one_substituteMapped template (.bvar .here)
    (VariableSubstitution.instantiateTop replacement) VariableSubstitution.freeId


/-- 双参数模板的首参数为顶部 bound 变量时直接执行 β 归约。 -/
@[simp] theorem apply_two_instantiateTop_bvar
    (template : Binary)
    {free : SetContext}
    (right replacement : SetOpenTerm free) :
    Formula.instantiateTop replacement
        (template.apply_two (.bvar .here)
          (right.weakenBound SetSort.set)) =
      template.apply_two replacement right := by
  change (template.apply_two (.bvar .here) (right.weakenBound SetSort.set)).substituteMapped
    (VariableSubstitution.instantiateTop replacement) VariableSubstitution.freeId = _
  simp only [apply_two_substituteMapped, Term.substituteMapped,
    VariableSubstitution.instantiateTop, term_substituteMapped_instantiateTop_weakenBound]


/-- 三参数模板的实例化与后续替换交换。 -/
@[simp] theorem apply_three_substituteMapped
    (template : Ternary)
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (first second third : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    (template.apply_three first second third).substituteMapped
        boundSubstitution freeSubstitution =
      template.apply_three
        (first.substituteMapped boundSubstitution freeSubstitution)
        (second.substituteMapped boundSubstitution freeSubstitution)
        (third.substituteMapped boundSubstitution freeSubstitution) := by
  simp only [apply_three, instantiate_substituteMapped,
    VariableSubstitution.map_cons, VariableSubstitution.map_empty]


/-- 四参数模板的实例化与后续替换交换。 -/
@[simp] theorem apply_four_substituteMapped
    (template : Quaternary)
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (first second third fourth : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    (template.apply_four first second third fourth).substituteMapped
        boundSubstitution freeSubstitution =
      template.apply_four
        (first.substituteMapped boundSubstitution freeSubstitution)
        (second.substituteMapped boundSubstitution freeSubstitution)
        (third.substituteMapped boundSubstitution freeSubstitution)
        (fourth.substituteMapped boundSubstitution freeSubstitution) := by
  simp only [apply_four, instantiate_substituteMapped,
    VariableSubstitution.map_cons, VariableSubstitution.map_empty]

instance unary_coe_fun : CoeFun Unary
    (fun _ => ∀ {bound free : SetContext},
      SetTerm bound free → SetFormula bound free) where
  coe template := fun {_ _} term => template.apply_one term

instance binary_coe_fun : CoeFun Binary
    (fun _ => ∀ {bound free : SetContext},
      SetTerm bound free → SetTerm bound free → SetFormula bound free) where
  coe template := fun {_ _} left right => template.apply_two left right

instance ternary_coe_fun : CoeFun Ternary
    (fun _ => ∀ {bound free : SetContext},
      SetTerm bound free → SetTerm bound free → SetTerm bound free →
        SetFormula bound free) where
  coe template := fun {_ _} first second third =>
    template.apply_three first second third

instance quaternary_coe_fun : CoeFun Quaternary
    (fun _ => ∀ {bound free : SetContext},
      SetTerm bound free → SetTerm bound free → SetTerm bound free →
        SetTerm bound free → SetFormula bound free) where
  coe template := fun {_ _} first second third fourth =>
    template.apply_four first second third fourth

/-- 四参数模板与任意顶部 bound 实例化交换。 -/
@[simp] theorem apply_four_instantiateTop_arguments
    (template : Quaternary)
    {bound free : SetContext}
    (first second third fourth :
      SetTerm (SetSort.set :: bound) free)
    (replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
        (template first second third fourth) =
      template
        (first.instantiateTop replacement)
        (second.instantiateTop replacement)
        (third.instantiateTop replacement)
        (fourth.instantiateTop replacement) := by
  exact apply_four_substituteMapped template first second third fourth _ _


/-- 三参数模板与任意顶部 bound 实例化交换。 -/
@[simp] theorem apply_three_instantiateTop_arguments
    (template : Ternary)
    {bound free : SetContext}
    (first second third : SetTerm (SetSort.set :: bound) free)
    (replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
        (template first second third) =
      template
        (first.instantiateTop replacement)
        (second.instantiateTop replacement)
        (third.instantiateTop replacement) := by
  exact apply_three_substituteMapped template first second third _ _


/-- 三参数模板直接穿过规范 bound 打开。 -/
@[simp] theorem apply_three_openBoundTop_arguments
    (template : Ternary)
    {free : SetContext}
    (first second third : SetTerm [SetSort.set] free) :
    Formula.openBoundTop (σ := signature) SetSort.set
        (template first second third) =
      template
        (Term.openBoundTop (σ := signature) SetSort.set first)
        (Term.openBoundTop (σ := signature) SetSort.set second)
        (Term.openBoundTop (σ := signature) SetSort.set third) := by
  exact apply_three_substituteMapped template first second third _ _


/-- 四参数模板直接穿过规范 bound 打开。 -/
@[simp] theorem apply_four_openBoundTop_arguments
    (template : Quaternary)
    {free : SetContext}
    (first second third fourth : SetTerm [SetSort.set] free) :
    Formula.openBoundTop (σ := signature) SetSort.set
        (template first second third fourth) =
      template
        (Term.openBoundTop (σ := signature) SetSort.set first)
        (Term.openBoundTop (σ := signature) SetSort.set second)
        (Term.openBoundTop (σ := signature) SetSort.set third)
        (Term.openBoundTop (σ := signature) SetSort.set fourth) := by
  exact apply_four_substituteMapped template first second third fourth _ _


/-- 单参数模板穿过一个新 bound 槽位后直接顶部实例化。 -/
@[simp] theorem apply_one_instantiateTop
    (template : Unary)
    {bound free : SetContext}
    (term replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
      (template
        (term.weakenBound SetSort.set ·ₘ (.bvar .here))) =
      template (term ·ₘ replacement) := by
  change (template.apply_one (term.weakenBound SetSort.set ·ₘ (.bvar .here))).substituteMapped
    (VariableSubstitution.instantiateTop replacement) VariableSubstitution.freeId =
      template.apply_one (term ·ₘ replacement)
  simp only [apply_one_substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    term_substituteMapped_instantiateTop_weakenBound, VariableSubstitution.instantiateTop]

 /-- 单参数模板的底层替换表示同样直接恢复。 -/
@[simp] theorem apply_one_substituteMapped_instantiateTop
    (template : Unary)
    {bound free : SetContext}
    (term replacement : SetTerm bound free) :
    Formula.substituteMapped
        (VariableSubstitution.instantiateTop replacement)
        VariableSubstitution.freeId
        (template
          (term.weakenBound SetSort.set ·ₘ (.bvar .here))) =
      template (term ·ₘ replacement) := by
  change
    Formula.instantiateTop replacement
      (template
        (term.weakenBound SetSort.set ·ₘ (.bvar .here))) =
      template (term ·ₘ replacement)
  exact apply_one_instantiateTop template term replacement

/-- 双参数模板穿过一个新 bound 槽位后直接顶部实例化。 -/
@[simp] theorem apply_two_instantiateTop
    (template : Binary)
    {bound free : SetContext}
    (left right replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
      (template
        (left.weakenBound SetSort.set ·ₘ (.bvar .here))
        (right.weakenBound SetSort.set ·ₘ (.bvar .here))) =
      template (left ·ₘ replacement) (right ·ₘ replacement) := by
  change (template.apply_two (left.weakenBound SetSort.set ·ₘ (.bvar .here)) (right.weakenBound SetSort.set ·ₘ (.bvar .here))).substituteMapped
    (VariableSubstitution.instantiateTop replacement) VariableSubstitution.freeId =
      template.apply_two (left ·ₘ replacement) (right ·ₘ replacement)
  simp only [apply_two_substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    term_substituteMapped_instantiateTop_weakenBound, VariableSubstitution.instantiateTop]


/-- 四参数模板穿过一个新 bound 槽位后直接顶部实例化。 -/
@[simp] theorem apply_four_instantiateTop
    (template : Quaternary)
    {bound free : SetContext}
    (first second third fourth replacement : SetTerm bound free) :
    Formula.instantiateTop replacement
      (template
        (first.weakenBound SetSort.set ·ₘ (.bvar .here))
        (second.weakenBound SetSort.set ·ₘ (.bvar .here))
        (third.weakenBound SetSort.set ·ₘ (.bvar .here))
        (fourth.weakenBound SetSort.set ·ₘ (.bvar .here))) =
      template (first ·ₘ replacement) (second ·ₘ replacement)
        (third ·ₘ replacement) (fourth ·ₘ replacement) := by
  change (template.apply_four (first.weakenBound SetSort.set ·ₘ (.bvar .here)) (second.weakenBound SetSort.set ·ₘ (.bvar .here)) (third.weakenBound SetSort.set ·ₘ (.bvar .here)) (fourth.weakenBound SetSort.set ·ₘ (.bvar .here))).substituteMapped
    (VariableSubstitution.instantiateTop replacement) VariableSubstitution.freeId =
      template.apply_four (first ·ₘ replacement) (second ·ₘ replacement) (third ·ₘ replacement) (fourth ·ₘ replacement)
  simp only [apply_four_substituteMapped, Term.substituteMapped, Arguments.substituteMapped,
    term_substituteMapped_instantiateTop_weakenBound, VariableSubstitution.instantiateTop]

end FormulaTemplate

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
