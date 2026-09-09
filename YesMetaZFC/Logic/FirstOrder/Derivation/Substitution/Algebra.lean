import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Basic

/-! # 类型化替换的槽位代数

替换组合只计算变量像；槽位扩展只处理首项与尾映射。具体模板不再按参数个数
重做语法归纳，也不需要展开函数、关系或 quotation 的定义。
-/
namespace YesMetaZFC.Logic.FirstOrder

universe u v w
variable {σ : Signature.{u, v, w}}

namespace VariableSubstitution

/-- 对槽位中的项做后续替换，显式保留组合边界供局部重写使用。 -/
def postcompose
    {slots sourceBound sourceFree targetBound targetFree : SortContext σ}
    (b : VariableSubstitution σ sourceBound targetBound targetFree)
    (f : VariableSubstitution σ sourceFree targetBound targetFree)
    (substitution : VariableSubstitution σ slots sourceBound sourceFree) :
    VariableSubstitution σ slots targetBound targetFree :=
  fun entry => (substitution entry).substituteMapped b f

/-- 空槽位映射经任何项变换仍为空映射。 -/
theorem map_empty
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (b : VariableSubstitution σ sourceBound targetBound targetFree)
    (f : VariableSubstitution σ sourceFree targetBound targetFree) :
    (postcompose b f empty : VariableSubstitution σ [] targetBound targetFree) =
      (empty : VariableSubstitution σ [] targetBound targetFree) := by
  funext sort entry
  exact nomatch entry

/-- 替换复合沿类型化槽位列逐项分配，参数个数任意。 -/
theorem map_cons
    {slots sourceBound sourceFree targetBound targetFree : SortContext σ}
    {sort : σ.SortSymbol} (head : Term σ sourceBound sourceFree sort)
    (tail : VariableSubstitution σ slots sourceBound sourceFree)
    (b : VariableSubstitution σ sourceBound targetBound targetFree)
    (f : VariableSubstitution σ sourceFree targetBound targetFree) :
    (postcompose b f (cons head tail) : VariableSubstitution σ (sort :: slots) targetBound targetFree) =
      (cons (head.substituteMapped b f) (postcompose b f tail) :
          VariableSubstitution σ (sort :: slots) targetBound targetFree) := by
  funext resultSort entry
  cases entry <;> rfl

end VariableSubstitution

/-- 弱化后再替换，只读取替换映射的尾部，允许同时改变 bound 上下文。 -/
theorem Term.substituteMapped_weakenFree_tail
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (b : VariableSubstitution σ sourceBound targetBound targetFree)
    (f : VariableSubstitution σ (introduced :: sourceFree) targetBound targetFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    (term.weakenFree introduced).substituteMapped b f =
      term.substituteMapped b (fun entry => f (.there entry)) := by
  change (term.renameMapped VariableRenaming.id
    (VariableRenaming.weaken introduced)).substituteMapped b f = _
  rw [← Term.substituteMapped_of_renaming, Term.substituteMapped_comp]
  rfl

/-- 参数列弱化后再替换，同样只读取自由替换的尾部。 -/
theorem Arguments.substituteMapped_weakenFree_tail
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (b : VariableSubstitution σ sourceBound targetBound targetFree)
    (f : VariableSubstitution σ (introduced :: sourceFree) targetBound targetFree)
    {sorts : List σ.SortSymbol} (arguments : Arguments σ sourceBound sourceFree sorts) :
    (arguments.weakenFree introduced).substituteMapped b f =
      arguments.substituteMapped b (fun entry => f (.there entry)) := by
  change (arguments.renameMapped VariableRenaming.id
    (VariableRenaming.weaken introduced)).substituteMapped b f = _
  rw [← Arguments.substituteMapped_of_renaming, Arguments.substituteMapped_comp]
  rfl

/-- bound 弱化与替换复合时忽略新槽，允许同时改变 free 上下文。 -/
theorem Term.substituteMapped_weakenBound_tail
    {sourceBound sourceFree targetBound targetFree : SortContext σ}
    (introduced : σ.SortSymbol)
    (b : VariableSubstitution σ (introduced :: sourceBound) targetBound targetFree)
    (f : VariableSubstitution σ sourceFree targetBound targetFree)
    {sort : σ.SortSymbol} (term : Term σ sourceBound sourceFree sort) :
    (term.weakenBound introduced).substituteMapped b f =
      term.substituteMapped (fun entry => b (.there entry)) f := by
  change (term.renameMapped (VariableRenaming.weaken introduced)
    VariableRenaming.id).substituteMapped b f = _
  rw [← Term.substituteMapped_of_bound_renaming, Term.substituteMapped_comp]
  rfl

/-- 没有自由槽的项不受自由变量替换影响。 -/
theorem Term.substituteMapped_emptyFree
    {bound : SortContext σ} {sort : σ.SortSymbol}
    (f : VariableSubstitution σ [] bound []) (term : Term σ bound [] sort) :
    term.substituteMapped VariableSubstitution.boundId f = term := by
  have hf : @f = (VariableSubstitution.freeId : VariableSubstitution σ [] bound []) := by
    funext sort entry
    exact nomatch entry
  rw [hf, Term.substituteMapped_id]

/-- 多次自由替换先复合槽位，公式结构只遍历一次。 -/
theorem Formula.substituteFree_comp
    {bound sourceFree middleFree targetFree : SortContext σ}
    (outer : VariableSubstitution σ middleFree bound targetFree)
    (inner : VariableSubstitution σ sourceFree bound middleFree)
    (body : Formula σ bound sourceFree) :
    (body.substituteFree inner).substituteFree outer =
      body.substituteFree (VariableSubstitution.postcompose
        VariableSubstitution.boundId outer inner) := by
  exact Formula.substituteMapped_comp _ _ _ _ body

end YesMetaZFC.Logic.FirstOrder
