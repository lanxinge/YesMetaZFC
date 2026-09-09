import YesMetaZFC.Logic.FirstOrder.Completeness.MaximalTheory

/-!
# Henkin 完成理论的内在类型典范模型

每个排序的载体直接由该排序闭项按完成候选中的等词取商。函数与关系解释只接收
签名索引指定的异质参数列，因此旧单域实现中的 sort 谓词、dummy 点、良构证书和
参数排序恢复义务全部消失。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin
namespace CanonicalModel

open HenkinSignature

universe u v w

variable {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
variable {T : Theory (HSignature σ)} {background : Background T}

/-! ## 逐排序闭项商 -/

/-- 同排序闭项等价，当且仅当其等词属于完成候选。 -/
def Equivalent (result : Result background) {sort : σ.SortSymbol}
    (left right : OpenTerm (HSignature σ) [] sort) : Prop :=
  result.candidate (.equal left right)

omit [DecidableEq σ.SortSymbol] in
theorem equivalent_refl (result : Result background)
    {sort : σ.SortSymbol} (term : OpenTerm (HSignature σ) [] sort) :
    Equivalent result term term :=
  result.equal_mem_refl term

omit [DecidableEq σ.SortSymbol] in
theorem equivalent_symm (result : Result background)
    {sort : σ.SortSymbol} {left right : OpenTerm (HSignature σ) [] sort}
    (h : Equivalent result left right) : Equivalent result right left :=
  result.equal_mem_symm h

omit [DecidableEq σ.SortSymbol] in
theorem equivalent_trans (result : Result background)
    {sort : σ.SortSymbol}
    {left middle right : OpenTerm (HSignature σ) [] sort}
    (h₁ : Equivalent result left middle)
    (h₂ : Equivalent result middle right) : Equivalent result left right :=
  result.equal_mem_trans h₁ h₂

/-- 完成候选等词在每个排序上诱导 setoid。 -/
def term_setoid (result : Result background) (sort : σ.SortSymbol) :
    Setoid (OpenTerm (HSignature σ) [] sort) where
  r := Equivalent result
  iseqv :=
    ⟨equivalent_refl result,
      fun h => equivalent_symm result h,
      fun h₁ h₂ => equivalent_trans result h₁ h₂⟩

/-- 典范模型中指定排序的载体。 -/
abbrev Carrier (result : Result background) (sort : σ.SortSymbol) :=
  Quotient (term_setoid result sort)

/-- 闭项的典范等价类。 -/
def classOf (result : Result background) {sort : σ.SortSymbol}
    (term : OpenTerm (HSignature σ) [] sort) : Carrier result sort :=
  Quotient.mk (term_setoid result sort) term

/-- 为定义结构解释固定商类代表。选择不进入任何公开数学前提。 -/
noncomputable def representative (result : Result background)
    {sort : σ.SortSymbol} (value : Carrier result sort) :
    OpenTerm (HSignature σ) [] sort :=
  Classical.choose (Quotient.exists_rep value)

omit [DecidableEq σ.SortSymbol] in
/-- 所选代表回到原商类。 -/
theorem classOf_representative (result : Result background)
    {sort : σ.SortSymbol} (value : Carrier result sort) :
    classOf result (representative result value) = value :=
  Classical.choose_spec (Quotient.exists_rep value)

omit [DecidableEq σ.SortSymbol] in
/-- 所选代表与任意给定代表候选等价。 -/
theorem representative_equivalent (result : Result background)
    {sort : σ.SortSymbol} (term : OpenTerm (HSignature σ) [] sort) :
    Equivalent result (representative result (classOf result term)) term :=
  Quotient.exact (classOf_representative result (classOf result term))

/-! ## 类型化参数拉链 -/

/--
`Prefix whole rest` 是一个参数列拉链：填入 `rest` 参数后得到完整的 `whole`
参数列。递归合同证明用它记录已经处理的前缀，而不做列表排序强制转换。
-/
inductive Prefix (τ : Signature.{u, v, w})
    (bound free : SortContext τ) :
    List τ.SortSymbol → List τ.SortSymbol → Type (max u v w) where
  | hole {sorts : List τ.SortSymbol} : Prefix τ bound free sorts sorts
  | fixed {whole : List τ.SortSymbol} {sort : τ.SortSymbol}
      {sorts : List τ.SortSymbol} :
      Prefix τ bound free whole (sort :: sorts) →
      Term τ bound free sort → Prefix τ bound free whole sorts

namespace Prefix

/-- 用参数尾填满拉链。 -/
def fill {τ : Signature.{u, v, w}} {bound free : SortContext τ} :
    {whole rest : List τ.SortSymbol} →
      Prefix τ bound free whole rest →
      Arguments τ bound free rest → Arguments τ bound free whole
  | _, _, .hole, arguments => arguments
  | _, _, .fixed frame head, arguments =>
      frame.fill (.cons head arguments)

/-- 参数拉链穿过一个新 binder。 -/
def weakenBound {τ : Signature.{u, v, w}}
    {bound free : SortContext τ} {whole rest : List τ.SortSymbol}
    (introduced : τ.SortSymbol) :
    Prefix τ bound free whole rest →
      Prefix τ (introduced :: bound) free whole rest
  | .hole => .hole
  | .fixed frame head =>
      .fixed (frame.weakenBound introduced) (head.weakenBound introduced)

@[simp] theorem instantiateTop_fill_weakenBound
    {τ : Signature.{u, v, w}}
    {bound free : SortContext τ} {whole rest : List τ.SortSymbol}
    {introduced : τ.SortSymbol}
    (replacement : Term τ bound free introduced)
    (frame : Prefix τ bound free whole rest)
    (arguments : Arguments τ (introduced :: bound) free rest) :
    ((frame.weakenBound introduced).fill arguments).instantiateTop replacement =
      frame.fill (arguments.instantiateTop replacement) := by
  induction frame with
  | hole => simp [weakenBound, fill]
  | fixed frame head ih =>
      simp [weakenBound, fill, ih]

end Prefix

/-! ## 参数逐项等词合同 -/

/-- 两列内在类型参数逐项属于同一个候选等词类。 -/
inductive EquivalentArguments (result : Result background) :
    {sorts : List σ.SortSymbol} →
      Arguments (HSignature σ) [] [] sorts →
      Arguments (HSignature σ) [] [] sorts → Prop where
  | nil : EquivalentArguments result .nil .nil
  | cons {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
      {left right : OpenTerm (HSignature σ) [] sort}
      {lefts rights : Arguments (HSignature σ) [] [] sorts}
      (hHead : Equivalent result left right)
      (hTail : EquivalentArguments result lefts rights) :
      EquivalentArguments result (.cons left lefts) (.cons right rights)

namespace EquivalentArguments

omit [DecidableEq σ.SortSymbol] in
theorem symm {result : Result background} {sorts : List σ.SortSymbol}
    {left right : Arguments (HSignature σ) [] [] sorts}
    (h : EquivalentArguments result left right) :
    EquivalentArguments result right left := by
  induction h with
  | nil => exact .nil
  | cons hHead _ ih => exact .cons (equivalent_symm result hHead) ih

end EquivalentArguments

omit [DecidableEq σ.SortSymbol] in
/-- 在函数应用的当前参数位置执行一次 Leibniz 替换。 -/
private theorem app_replace_head (result : Result background)
    (function : (HSignature σ).FuncSymbol)
    {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (frame : Prefix (HSignature σ) [] []
      ((HSignature σ).funcDomain function) (sort :: sorts))
    {left right : OpenTerm (HSignature σ) [] sort}
    (suffix : Arguments (HSignature σ) [] [] sorts)
    (hEquality : Equivalent result left right) :
    Equivalent result
      (.app function (frame.fill (.cons left suffix)))
      (.app function (frame.fill (.cons right suffix))) := by
  let source : OpenTerm (HSignature σ) []
      ((HSignature σ).funcCodomain function) :=
    .app function (frame.fill (.cons left suffix))
  let body : Formula (HSignature σ) [sort] [] :=
    .equal (Term.weakenBound (σ := HSignature σ) sort source)
      (.app function
        ((Prefix.weakenBound (τ := HSignature σ) sort frame).fill
          (.cons (.bvar .here)
            (Arguments.weakenBound (σ := HSignature σ) sort suffix))))
  have hSource : result.candidate (body.instantiateTop left) := by
    simpa [body, source] using result.equal_mem_refl source
  have hTarget :=
    result.substitute_mem_of_equal_mem
      (body := body) hEquality hSource
  simpa [body, source] using! hTarget

omit [DecidableEq σ.SortSymbol] in
/-- 函数符号对候选等词逐参数合同，拉链记录已处理前缀。 -/
private theorem app_mem_congr_prefix (result : Result background)
    (function : (HSignature σ).FuncSymbol)
    {sorts : List σ.SortSymbol}
    (frame : Prefix (HSignature σ) [] []
      ((HSignature σ).funcDomain function) sorts)
    {left right : Arguments (HSignature σ) [] [] sorts}
    (hArguments : EquivalentArguments result left right) :
    Equivalent result (.app function (frame.fill left))
      (.app function (frame.fill right)) := by
  induction hArguments with
  | nil =>
      exact result.equal_mem_refl (.app function (frame.fill .nil))
  | @cons sort sorts left right lefts rights hHead hTail ih =>
      have hFirst :=
        app_replace_head result function frame lefts hHead
      have hRest := ih (.fixed frame right)
      simpa [Prefix.fill] using!
        result.equal_mem_trans hFirst (by
          simpa [Prefix.fill] using! hRest)

omit [DecidableEq σ.SortSymbol] in
/-- 函数符号对候选等词逐参数合同。 -/
theorem app_mem_congr (result : Result background)
    (function : (HSignature σ).FuncSymbol)
    {left right : Arguments (HSignature σ) [] []
      ((HSignature σ).funcDomain function)}
    (hArguments : EquivalentArguments result left right) :
    Equivalent result (.app function left) (.app function right) := by
  simpa [Prefix.fill] using
    app_mem_congr_prefix result function (.hole) hArguments

omit [DecidableEq σ.SortSymbol] in
/-- 在关系原子的当前参数位置执行一次 Leibniz 替换。 -/
private theorem rel_replace_head (result : Result background)
    (relation : (HSignature σ).RelSymbol)
    {sort : σ.SortSymbol} {sorts : List σ.SortSymbol}
    (frame : Prefix (HSignature σ) [] []
      ((HSignature σ).relDomain relation) (sort :: sorts))
    {left right : OpenTerm (HSignature σ) [] sort}
    (suffix : Arguments (HSignature σ) [] [] sorts)
    (hEquality : Equivalent result left right)
    (hSource : result.candidate
      (.rel relation (frame.fill (.cons left suffix)))) :
    result.candidate (.rel relation (frame.fill (.cons right suffix))) := by
  let body : Formula (HSignature σ) [sort] [] :=
    .rel relation
      ((Prefix.weakenBound (τ := HSignature σ) sort frame).fill
        (.cons (.bvar .here)
          (Arguments.weakenBound (σ := HSignature σ) sort suffix)))
  have hSource' : result.candidate (body.instantiateTop left) := by
    simpa [body] using hSource
  have hTarget :=
    result.substitute_mem_of_equal_mem
      (body := body) hEquality hSource'
  simpa [body] using hTarget

omit [DecidableEq σ.SortSymbol] in
/-- 关系原子在逐参数候选等词下保持成员关系。 -/
private theorem rel_mem_congr_prefix (result : Result background)
    (relation : (HSignature σ).RelSymbol)
    {sorts : List σ.SortSymbol}
    (frame : Prefix (HSignature σ) [] []
      ((HSignature σ).relDomain relation) sorts)
    {left right : Arguments (HSignature σ) [] [] sorts}
    (hArguments : EquivalentArguments result left right)
    (hSource : result.candidate (.rel relation (frame.fill left))) :
    result.candidate (.rel relation (frame.fill right)) := by
  induction hArguments with
  | nil => exact hSource
  | @cons sort sorts left right lefts rights hHead hTail ih =>
      have hMiddle :=
        rel_replace_head result relation frame lefts hHead hSource
      simpa [Prefix.fill] using
        ih (.fixed frame right) (by
          simpa [Prefix.fill] using hMiddle)

omit [DecidableEq σ.SortSymbol] in
/-- 关系原子的候选成员关系只依赖参数等词类。 -/
theorem rel_mem_congr_iff (result : Result background)
    (relation : (HSignature σ).RelSymbol)
    {left right : Arguments (HSignature σ) [] []
      ((HSignature σ).relDomain relation)}
    (hArguments : EquivalentArguments result left right) :
    result.candidate (.rel relation left) ↔
      result.candidate (.rel relation right) := by
  constructor
  · simpa [Prefix.fill] using
      rel_mem_congr_prefix result relation (.hole) hArguments
  · simpa [Prefix.fill] using
      rel_mem_congr_prefix result relation (.hole) hArguments.symm

/-! ## 典范结构与求值 -/

/-- 从异质商值列中提取固定代表。 -/
noncomputable def selectArguments (result : Result background) :
    {sorts : List σ.SortSymbol} → Values (Carrier (σ := σ) result) sorts →
      Arguments (HSignature σ) [] [] sorts
  | _, .nil => .nil
  | _, .cons value rest =>
      .cons (representative (σ := σ) result value)
        (selectArguments result rest)

/-- 典范函数解释。 -/
noncomputable def funcInterp (result : Result background)
    (function : (HSignature σ).FuncSymbol)
    (values : Values (Carrier (σ := σ) result)
      ((HSignature σ).funcDomain function)) :
    Carrier (σ := σ) result ((HSignature σ).funcCodomain function) :=
  classOf (σ := σ) result
    (.app function (selectArguments (σ := σ) result values))

/-- 典范关系解释。 -/
noncomputable def relInterp (result : Result background)
    (relation : (HSignature σ).RelSymbol)
    (values : Values (Carrier (σ := σ) result)
      ((HSignature σ).relDomain relation)) : Prop :=
  result.candidate
    (.rel relation (selectArguments (σ := σ) result values))

/-- 完成候选诱导的内在多排序典范结构。 -/
noncomputable def model (result : Result background) :
    Structure.{u, max u v, w, max v w} (HSignature σ) where
  Carrier := Carrier (σ := σ) result
  nonempty := fun sort =>
    ⟨classOf (σ := σ) result (witnessTerm (σ := σ) sort 0)⟩
  funcInterp := funcInterp (σ := σ) result
  relInterp := relInterp (σ := σ) result

/-- 闭句典范模型使用唯一的空环境。 -/
noncomputable def canonical_env (result : Result background) :
    Env (model (σ := σ) result) [] [] :=
  Env.empty

omit [DecidableEq σ.SortSymbol] in
mutual

/--
闭项求值等于自身商类；参数分支同时记录所选代表与原参数逐项候选等价。
-/
theorem eval_eq_classOf (result : Result background)
    {sort : σ.SortSymbol} (term : OpenTerm (HSignature σ) [] sort) :
    Term.eval (canonical_env (σ := σ) result) term =
      classOf (σ := σ) result term := by

  match term with
  | .bvar entry | .fvar entry => nomatch entry
  | .app function arguments =>
      change funcInterp (σ := σ) result function
          (Arguments.eval (canonical_env (σ := σ) result) arguments) =
        classOf (σ := σ) result (.app function arguments)
      exact Quotient.sound (app_mem_congr result function
        (eval_arguments_equivalent result arguments))

/-- 闭项实参求值后，固定代表与原实参逐项候选等价。 -/
theorem eval_arguments_equivalent (result : Result background)
    {sorts : List σ.SortSymbol}
    (arguments : Arguments (HSignature σ) [] [] sorts) :
    EquivalentArguments result
      (selectArguments (σ := σ) result
        (Arguments.eval (canonical_env (σ := σ) result) arguments))
      arguments := by

  match arguments with
  | .nil => exact .nil
  | .cons head tail =>
      change EquivalentArguments result
        (.cons (representative (σ := σ) result
          (Term.eval (canonical_env (σ := σ) result) head))
          (selectArguments (σ := σ) result
            (Arguments.eval (canonical_env (σ := σ) result) tail))) (.cons head tail)
      rw [eval_eq_classOf]
      exact .cons (representative_equivalent (σ := σ) result head)
        (eval_arguments_equivalent result tail)

end

end CanonicalModel
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
