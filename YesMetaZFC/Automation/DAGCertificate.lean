import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.LogicSoundness
import YesMetaZFC.Automation.Resolution
import YesMetaZFC.Logic.FreeVariableSupport

/-!
# 零层级大型 DAG 证书

本文件是新 `Logic` 语义核上的 DAG 证书数据层。它不导入旧 LCF replay，也不携带
Lean `Expr`；搜索层后续只需要把自己的轨迹落成这里的节点、父边和可检查 payload。

当前模块同时定义结构 checker 与整图 soundness：

* 节点编号采用 dense array id：`node.id = index`；
* 每条父边必须指向更早节点；
* source 节点只能引用 `ClauseProblem.initialClauses` 的显式索引；
* residual CDCL 携带 checked propositional UNSAT payload；
* 根节点必须是空字句。

soundness 在这些结构条件上做统一拓扑归纳；公式级问题只在最终出口编译为初始字句。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate

universe x

open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.Automation.LogicSoundness

abbrev Signature := LogicSoundness.SetLevel.Signature
abbrev Term (σ : Signature) := LogicSoundness.SetLevel.Term σ
abbrev Formula (σ : Signature) := LogicSoundness.SetLevel.Formula σ
abbrev DeepProblem (σ : Signature) := LogicSoundness.SetLevel.DeepProblem σ
abbrev NodeId := Certificate.NodeId

/-! ## Clause view -/

namespace StructuralEq

open _root_.YesMetaZFC.Logic.FirstOrder

mutual
  /-- 项的局部结构比较。 -/
  def term {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] :
      Term σ → Term σ → Bool
    | .var value => fun right =>
        match value, right with
        | .bvar sort index, .var (.bvar otherSort otherIndex) =>
            decide (sort = otherSort) && index == otherIndex
        | .fvar sort index, .var (.fvar otherSort otherIndex) =>
            decide (sort = otherSort) && index == otherIndex
        | _, _ => false
    | .app function arguments => fun right =>
        match right with
        | .app otherFunction otherArguments =>
            decide (function = otherFunction) &&
              termList arguments otherArguments
        | _ => false

  /-- 项列表的局部结构比较。 -/
  def termList {σ : Signature} [DecidableEq σ.SortSymbol]
      [DecidableEq σ.FuncSymbol] : List (Term σ) → List (Term σ) → Bool
    | [] => fun right =>
        match right with
        | [] => true
        | _ => false
    | head :: tail => fun right =>
        match right with
        | otherHead :: otherTail =>
            term head otherHead && termList tail otherTail
        | _ => false
end

/-- 公式的局部结构比较。 -/
def formula {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] : Formula σ → Formula σ → Bool
  | .falsum => fun right =>
      match right with
      | .falsum => true
      | _ => false
  | .truth => fun right =>
      match right with
      | .truth => true
      | _ => false
  | .rel relation arguments => fun right =>
      match right with
      | .rel otherRelation otherArguments =>
          decide (relation = otherRelation) &&
            termList arguments otherArguments
      | _ => false
  | .equal left right => fun other =>
      match other with
      | .equal otherLeft otherRight =>
          term left otherLeft && term right otherRight
      | _ => false
  | .neg body => fun right =>
      match right with
      | .neg otherBody => formula body otherBody
      | _ => false
  | .conj left right => fun other =>
      match other with
      | .conj otherLeft otherRight =>
          formula left otherLeft && formula right otherRight
      | _ => false
  | .disj left right => fun other =>
      match other with
      | .disj otherLeft otherRight =>
          formula left otherLeft && formula right otherRight
      | _ => false
  | .imp left right => fun other =>
      match other with
      | .imp otherLeft otherRight =>
          formula left otherLeft && formula right otherRight
      | _ => false
  | .iff left right => fun other =>
      match other with
      | .iff otherLeft otherRight =>
          formula left otherLeft && formula right otherRight
      | _ => false
  | .forallE sort body => fun right =>
      match right with
      | .forallE otherSort otherBody =>
          decide (sort = otherSort) && formula body otherBody
      | _ => false
  | .existsE sort body => fun right =>
      match right with
      | .existsE otherSort otherBody =>
          decide (sort = otherSort) && formula body otherBody
      | _ => false

mutual
  /-- 项与自身的结构比较为真。 -/
  theorem term_refl {σ : Signature} [DecidableEq σ.SortSymbol]
      [DecidableEq σ.FuncSymbol] (input : Term σ) :
      term input input = true := by
    cases input with
    | var value =>
        cases value <;> simp [term]
    | app function arguments =>
        simp [term, termList_refl arguments]

  /-- 项列表与自身的结构比较为真。 -/
  theorem termList_refl {σ : Signature} [DecidableEq σ.SortSymbol]
      [DecidableEq σ.FuncSymbol] (input : List (Term σ)) :
      termList input input = true := by
    cases input with
    | nil => simp [termList]
    | cons head tail =>
        simp [termList, term_refl head, termList_refl tail]
end

/-- 公式与自身的结构比较为真。 -/
theorem formula_refl {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (input : Formula σ) : formula input input = true := by
  induction input with
  | falsum => simp [formula]
  | truth => simp [formula]
  | rel relation arguments => simp [formula, termList_refl arguments]
  | equal left right => simp [formula, term_refl left, term_refl right]
  | neg body ih => simpa [formula] using ih
  | conj left right ihLeft ihRight => simp [formula, ihLeft, ihRight]
  | disj left right ihLeft ihRight => simp [formula, ihLeft, ihRight]
  | imp left right ihLeft ihRight => simp [formula, ihLeft, ihRight]
  | iff left right ihLeft ihRight => simp [formula, ihLeft, ihRight]
  | forallE sort body ih => simp [formula, ih]
  | existsE sort body ih => simp [formula, ih]

/-- 相等项的结构比较为真。 -/
theorem term_eq_true_of_eq {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] {left right : Term σ} (equality : left = right) :
    term left right = true := by
  cases equality
  exact term_refl left

/-- 相等项列表的结构比较为真。 -/
theorem termList_eq_true_of_eq {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] {left right : List (Term σ)} (equality : left = right) :
    termList left right = true := by
  cases equality
  exact termList_refl left

/-- 相等公式的结构比较为真。 -/
theorem formula_eq_true_of_eq {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {left right : Formula σ} (equality : left = right) :
    formula left right = true := by
  cases equality
  exact formula_refl left

/-- 项结构比较为真时，两侧项实际相等。 -/
theorem term_sound {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    (left : Term σ) : ∀ right : Term σ, term left right = true → left = right := by
  refine Term.rec
    (motive_1 := fun left => ∀ right, term left right = true → left = right)
    (motive_2 := fun lefts => ∀ right, termList lefts right = true → lefts = right)
    ?_ ?_ ?_ ?_ left
  · intro v right h
    cases right <;> simp [term] at h
    case var other =>
      cases v <;> cases other <;> simp at h
      all_goals
        rcases h with ⟨hSort, hIndex⟩
        cases hSort
        cases hIndex
        rfl
  · intro f args ihArgs right h
    cases right <;> simp [term] at h
    case app otherFunction otherArgs =>
      rcases h with ⟨hFunction, hArgs⟩
      cases hFunction
      exact congrArg (Term.app f) (ihArgs _ hArgs)
  · intro right h
    cases right with
    | nil => rfl
    | cons _ _ => simp [termList] at h
  · intro head tail ihHead ihTail right h
    cases right <;> simp [termList] at h
    case cons otherHead otherTail =>
      rcases h with ⟨hHead, hTail⟩
      have hHeadEq := ihHead _ hHead
      have hTailEq := ihTail _ hTail
      cases hHeadEq
      cases hTailEq
      rfl

/-- 项列表结构比较为真时，两侧列表实际相等。 -/
theorem termList_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] (left : List (Term σ)) :
    ∀ right : List (Term σ), termList left right = true → left = right := by
  refine Term.rec_1
    (motive_1 := fun left => ∀ right, term left right = true → left = right)
    (motive_2 := fun lefts => ∀ right, termList lefts right = true → lefts = right)
    ?_ ?_ ?_ ?_ left
  · intro v right h
    cases right <;> simp [term] at h
    case var other =>
      cases v <;> cases other <;> simp at h
      all_goals
        rcases h with ⟨hSort, hIndex⟩
        cases hSort
        cases hIndex
        rfl
  · intro f args ihArgs right h
    cases right <;> simp [term] at h
    case app otherFunction otherArgs =>
      rcases h with ⟨hFunction, hArgs⟩
      cases hFunction
      exact congrArg (Term.app f) (ihArgs _ hArgs)
  · intro right h
    cases right with
    | nil => rfl
    | cons _ _ => simp [termList] at h
  · intro head tail ihHead ihTail right h
    cases right <;> simp [termList] at h
    case cons otherHead otherTail =>
      rcases h with ⟨hHead, hTail⟩
      have hHeadEq := ihHead _ hHead
      have hTailEq := ihTail _ hTail
      cases hHeadEq
      cases hTailEq
      rfl

/-- 公式结构比较为真时，两侧公式实际相等。 -/
theorem formula_sound {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (left : Formula σ) :
    ∀ right : Formula σ, formula left right = true → left = right := by
  refine Formula.rec
    (motive := fun left => ∀ right, formula left right = true → left = right)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro right h
    cases right <;> simp [formula] at h
    · rfl
  · intro right h
    cases right <;> simp [formula] at h
    · rfl
  · intro relation args right h
    cases right <;> simp [formula] at h
    case rel otherRelation otherArgs =>
      rcases h with ⟨hRelation, hArgs⟩
      cases hRelation
      exact congrArg (Formula.rel relation) (termList_sound args _ hArgs)
  · intro leftTerm rightTerm right h
    cases right <;> simp [formula] at h
    case equal otherLeft otherRight =>
      rcases h with ⟨hLeft, hRight⟩
      have hLeftEq := term_sound leftTerm _ hLeft
      have hRightEq := term_sound rightTerm _ hRight
      cases hLeftEq
      cases hRightEq
      rfl
  · intro φ ih right h
    cases right <;> simp [formula] at h
    case neg ψ =>
      exact congrArg Formula.neg (ih _ h)
  · intro φ ψ ihφ ihψ right h
    cases right <;> simp [formula] at h
    case conj φ' ψ' =>
      rcases h with ⟨hφ, hψ⟩
      have hφEq := ihφ _ hφ
      have hψEq := ihψ _ hψ
      cases hφEq
      cases hψEq
      rfl
  · intro φ ψ ihφ ihψ right h
    cases right <;> simp [formula] at h
    case disj φ' ψ' =>
      rcases h with ⟨hφ, hψ⟩
      have hφEq := ihφ _ hφ
      have hψEq := ihψ _ hψ
      cases hφEq
      cases hψEq
      rfl
  · intro φ ψ ihφ ihψ right h
    cases right <;> simp [formula] at h
    case imp φ' ψ' =>
      rcases h with ⟨hφ, hψ⟩
      have hφEq := ihφ _ hφ
      have hψEq := ihψ _ hψ
      cases hφEq
      cases hψEq
      rfl
  · intro φ ψ ihφ ihψ right h
    cases right <;> simp [formula] at h
    case iff φ' ψ' =>
      rcases h with ⟨hφ, hψ⟩
      have hφEq := ihφ _ hφ
      have hψEq := ihψ _ hψ
      cases hφEq
      cases hψEq
      rfl
  · intro sort body ih right h
    cases right <;> simp [formula] at h
    case forallE otherSort otherBody =>
      rcases h with ⟨hSort, hBody⟩
      cases hSort
      exact congrArg (Formula.forallE sort) (ih _ hBody)
  · intro sort body ih right h
    cases right <;> simp [formula] at h
    case existsE otherSort otherBody =>
      rcases h with ⟨hSort, hBody⟩
      cases hSort
      exact congrArg (Formula.existsE sort) (ih _ hBody)

end StructuralEq

/-- 一阶 DAG 里的有限项替换。当前只替换 free variable，bound variable 保持不变。 -/
abbrev TermSubstitution (σ : Signature) := List (σ.SortSymbol × Nat × Term σ)

namespace TermSubstitution

/-- 空替换。 -/
def empty {σ : Signature} : TermSubstitution σ := []

/-- 查找一个带 sort 的 free variable 绑定。 -/
def lookup {σ : Signature} [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) (sort : σ.SortSymbol) (id : Nat) :
    Option (Term σ) :=
  match subst with
  | [] => none
  | (entrySort, entryId, term) :: rest =>
      if entrySort = sort && entryId == id then
        some term
      else
        lookup rest sort id

end TermSubstitution

namespace Term

mutual
  /-- 将有限替换作用到 DAG 项。 -/
  def applySubstitution {σ : Signature} [DecidableEq σ.SortSymbol]
      (subst : TermSubstitution σ) : Term σ → Term σ
    | .var (.fvar sort id) =>
        match TermSubstitution.lookup subst sort id with
        | some term => term
        | none => .var (.fvar sort id)
    | .var (.bvar sort index) => .var (.bvar sort index)
    | .app function arguments =>
        .app function (applySubstitutionList subst arguments)

  /-- 将有限替换作用到 DAG 参数列表。 -/
  def applySubstitutionList {σ : Signature} [DecidableEq σ.SortSymbol]
      (subst : TermSubstitution σ) : List (Term σ) → List (Term σ)
    | [] => []
    | head :: tail =>
        applySubstitution subst head :: applySubstitutionList subst tail
end

/-- 显式参数列表递归与原有 `List.map` 视图一致。 -/
theorem applySubstitutionList_eq_map {σ : Signature} [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) :
    ∀ input : List (Term σ),
      applySubstitutionList subst input = input.map (applySubstitution subst)
  | [] => rfl
  | head :: tail => by
      rw [applySubstitutionList, List.map, applySubstitutionList_eq_map]

mutual
  /-- 空 substitution 保持项不变。 -/
  theorem applySubstitution_empty {σ : Signature} [DecidableEq σ.SortSymbol]
      (input : Term σ) : applySubstitution [] input = input := by
    cases input with
    | var value =>
        cases value <;> simp [applySubstitution, TermSubstitution.lookup]
    | app function arguments =>
        simp [applySubstitution, applySubstitutionList_empty arguments]

  /-- 空 substitution 保持参数列表不变。 -/
  theorem applySubstitutionList_empty {σ : Signature}
      [DecidableEq σ.SortSymbol] (input : List (Term σ)) :
      applySubstitutionList [] input = input := by
    cases input with
    | nil => rfl
    | cons head tail =>
        simp [applySubstitutionList, applySubstitution_empty head,
          applySubstitutionList_empty tail]
end

/-- substitution 被证明为空时，施加替换保持项不变。 -/
theorem applySubstitution_eq_self_of_eq_empty {σ : Signature}
    [DecidableEq σ.SortSymbol] (input : Term σ) (subst : TermSubstitution σ)
    (hSubst : subst = []) : applySubstitution subst input = input := by
  cases hSubst
  exact applySubstitution_empty input

mutual
  /-- 将 free variable 编号整体平移；bound variable 保持不变。 -/
  def renameFreeVars (offset : Nat) : Term σ → Term σ
    | .var (.fvar sort id) => .var (.fvar sort (id + offset))
    | .var (.bvar sort index) => .var (.bvar sort index)
    | .app function arguments =>
        .app function (renameFreeVarsList offset arguments)

  /-- 将参数列表中的 free variable 编号整体平移。 -/
  def renameFreeVarsList (offset : Nat) : List (Term σ) → List (Term σ)
    | [] => []
    | head :: tail =>
        renameFreeVars offset head :: renameFreeVarsList offset tail
end

/-- 显式参数列表递归与原有 `List.map` 视图一致。 -/
theorem renameFreeVarsList_eq_map (offset : Nat) :
    ∀ input : List (Term σ),
      renameFreeVarsList offset input = input.map (renameFreeVars offset)
  | [] => rfl
  | head :: tail => by
      rw [renameFreeVarsList, List.map, renameFreeVarsList_eq_map]

mutual
  /-- 零偏移自由变量重命名保持项不变。 -/
  theorem renameFreeVars_zero (input : Term σ) :
      renameFreeVars 0 input = input := by
    cases input with
    | var value =>
        cases value <;> simp [renameFreeVars]
    | app function arguments =>
        simp [renameFreeVars, renameFreeVarsList_zero arguments]

  /-- 零偏移自由变量重命名保持项列表不变。 -/
  theorem renameFreeVarsList_zero (input : List (Term σ)) :
      renameFreeVarsList 0 input = input := by
    cases input with
    | nil => rfl
    | cons head tail =>
        simp [renameFreeVarsList, renameFreeVars_zero head,
          renameFreeVarsList_zero tail]
end

/-- 偏移被证明为零时，项等于其自由变量重命名结果。 -/
theorem eq_renameFreeVars_of_offset_eq_zero
    (input : Term σ) (offset : Nat) (hOffset : offset = 0) :
    input = renameFreeVars offset input := by
  cases hOffset
  exact (renameFreeVars_zero input).symm

mutual
  /-- 可计算检查：项是否具有给定 sort。 -/
  def checkWellSorted {σ : Signature} [DecidableEq σ.SortSymbol]
      (sort : σ.SortSymbol) : Term σ → Bool
    | .var (.bvar s _) => decide (s = sort)
    | .var (.fvar s _) => decide (s = sort)
    | .app f args =>
        decide (σ.funcCodomain f = sort) &&
          checkArgsWellSorted args (σ.funcDomain f)

  /-- 可计算检查：参数列表是否逐项匹配 sort 列表。 -/
  def checkArgsWellSorted {σ : Signature} [DecidableEq σ.SortSymbol] :
      List (Term σ) → List σ.SortSymbol → Bool
    | [], [] => true
    | term :: terms, sort :: sorts =>
        checkWellSorted sort term && checkArgsWellSorted terms sorts
    | _, _ => false
end

mutual
  /-- `checkWellSorted` 通过时得到新语义核的 sort 正确性证明。 -/
  theorem checkWellSorted_sound {σ : Signature} [DecidableEq σ.SortSymbol]
      {sort : σ.SortSymbol} {term : Term σ}
      (hCheck : checkWellSorted sort term = true) :
      Logic.FirstOrder.TermWellSorted term sort := by
    cases term with
    | var var =>
        cases var with
        | bvar s idx =>
            have hSort : s = sort := by
              simpa [checkWellSorted] using hCheck
            cases hSort
            exact Logic.FirstOrder.TermWellSorted.bvar sort idx
        | fvar s id =>
            have hSort : s = sort := by
              simpa [checkWellSorted] using hCheck
            cases hSort
            exact Logic.FirstOrder.TermWellSorted.fvar sort id
    | app f args =>
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hCodomain, hArgs⟩
        have hSort : σ.funcCodomain f = sort := of_decide_eq_true hCodomain
        cases hSort
        exact Logic.FirstOrder.TermWellSorted.app f
          (checkArgsWellSorted_sound hArgs)

  /-- `checkArgsWellSorted` 通过时得到参数列表 sort 正确性证明。 -/
  theorem checkArgsWellSorted_sound {σ : Signature} [DecidableEq σ.SortSymbol]
      {args : List (Term σ)} {sorts : List σ.SortSymbol}
      (hCheck : checkArgsWellSorted args sorts = true) :
      Logic.FirstOrder.ArgsWellSorted args sorts := by
    cases args with
    | nil =>
        cases sorts with
        | nil => exact Logic.FirstOrder.ArgsWellSorted.nil
        | cons _ _ => simp [checkArgsWellSorted] at hCheck
    | cons term terms =>
        cases sorts with
        | nil => simp [checkArgsWellSorted] at hCheck
        | cons sort sorts =>
            rcases Bool.and_eq_true_iff.mp hCheck with ⟨hTerm, hRest⟩
            exact Logic.FirstOrder.ArgsWellSorted.cons
              (checkWellSorted_sound hTerm)
              (checkArgsWellSorted_sound hRest)
end

/-- 项不含 bound variable。用于避免 substitution 穿过量词体时发生捕获。 -/
def BoundClosed {σ : Signature} : Term σ → Prop
  | .var (.bvar ..) => False
  | .var (.fvar ..) => True
  | .app _ args => ∀ term ∈ args, BoundClosed term

mutual
  /-- 可计算检查：项不含 bound variable。 -/
  def checkBoundClosed {σ : Signature} : Term σ → Bool
    | .var (.bvar ..) => false
    | .var (.fvar ..) => true
    | .app _ args => checkBoundClosedList args

  /-- 可计算检查：项列表中每个项都不含 bound variable。 -/
  def checkBoundClosedList {σ : Signature} : List (Term σ) → Bool
    | [] => true
    | term :: rest => checkBoundClosed term && checkBoundClosedList rest
end

mutual
  /-- `checkBoundClosed` 通过时得到 Prop 版 bound-closed 合同。 -/
  theorem checkBoundClosed_sound {σ : Signature} :
      ∀ {term : Term σ}, checkBoundClosed term = true → BoundClosed term
    | .var (.bvar ..), hCheck => by
        simp [checkBoundClosed] at hCheck
    | .var (.fvar ..), _hCheck => by
        simp [BoundClosed]
    | .app _ args, hCheck => by
        have hList : checkBoundClosedList args = true := by
          simpa [checkBoundClosed] using hCheck
        simpa [BoundClosed] using checkBoundClosedList_sound hList

  /-- `checkBoundClosedList` 通过时得到列表版 bound-closed 合同。 -/
  theorem checkBoundClosedList_sound {σ : Signature} :
      ∀ {terms : List (Term σ)}, checkBoundClosedList terms = true →
        ∀ term, term ∈ terms → BoundClosed term
    | [], _hCheck, term, hMem => by
        cases hMem
    | head :: tail, hCheck, term, hMem => by
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hTail⟩
        rcases List.mem_cons.mp hMem with hEq | hTailMem
        · cases hEq
          exact checkBoundClosed_sound hHead
        · exact checkBoundClosedList_sound hTail term hTailMem
end

/-- 项不含 free variable。用于确认 problem 背景不依赖替换环境。 -/
def FreeClosed {σ : Signature} : Term σ → Prop
  | .var (.bvar ..) => True
  | .var (.fvar ..) => False
  | .app _ args => ∀ term ∈ args, FreeClosed term

mutual
  /-- 可计算检查：项不含 free variable。 -/
  def checkFreeClosed {σ : Signature} : Term σ → Bool
    | .var (.bvar ..) => true
    | .var (.fvar ..) => false
    | .app _ args => checkFreeClosedList args

  /-- 可计算检查：项列表中每个项都不含 free variable。 -/
  def checkFreeClosedList {σ : Signature} : List (Term σ) → Bool
    | [] => true
    | term :: rest => checkFreeClosed term && checkFreeClosedList rest
end

mutual
  /-- `checkFreeClosed` 通过时得到 Prop 版 free-closed 合同。 -/
  theorem checkFreeClosed_sound {σ : Signature} :
      ∀ {term : Term σ}, checkFreeClosed term = true → FreeClosed term
    | .var (.bvar ..), _hCheck => by
        simp [FreeClosed]
    | .var (.fvar ..), hCheck => by
        simp [checkFreeClosed] at hCheck
    | .app _ args, hCheck => by
        have hList : checkFreeClosedList args = true := by
          simpa [checkFreeClosed] using hCheck
        simpa [FreeClosed] using checkFreeClosedList_sound hList

  /-- `checkFreeClosedList` 通过时得到列表版 free-closed 合同。 -/
  theorem checkFreeClosedList_sound {σ : Signature} :
      ∀ {terms : List (Term σ)}, checkFreeClosedList terms = true →
        ∀ term, term ∈ terms → FreeClosed term
    | [], _hCheck, term, hMem => by
        cases hMem
    | head :: tail, hCheck, term, hMem => by
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hTail⟩
        rcases List.mem_cons.mp hMem with hEq | hTailMem
        · cases hEq
          exact checkFreeClosed_sound hHead
        · exact checkFreeClosedList_sound hTail term hTailMem
end

/-- bound-closed 项在压入新的 bound 值后解释不变。 -/
theorem eval_pushBound_of_boundClosed {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {term : Term σ} (hClosed : BoundClosed term)
    (sort : σ.SortSymbol) (value : M.Domain)
    (hValue : M.sortInterp sort value) :
    Logic.FirstOrder.Term.eval (env.pushBound sort value hValue) term =
      Logic.FirstOrder.Term.eval env term := by
  exact Logic.FirstOrder.Term.rec
    (motive_1 := fun term =>
      BoundClosed term →
        Logic.FirstOrder.Term.eval (env.pushBound sort value hValue) term =
          Logic.FirstOrder.Term.eval env term)
    (motive_2 := fun terms =>
      (∀ term, term ∈ terms → BoundClosed term) →
        terms.map (Logic.FirstOrder.Term.eval (env.pushBound sort value hValue)) =
          terms.map (Logic.FirstOrder.Term.eval env))
    (fun v hClosed => by
      cases v <;>
        simp [BoundClosed, Logic.FirstOrder.Term.eval,
          Logic.FirstOrder.Env.pushBound] at hClosed ⊢)
    (fun f args ihArgs hClosed => by
      simpa [Logic.FirstOrder.Term.eval] using
        congrArg (M.funcInterp f) (ihArgs (by simpa [BoundClosed] using hClosed)))
    (fun _hClosed => rfl)
    (fun head tail ihHead ihTail hClosed => by
      simp [ihHead (hClosed head (by simp)),
        ihTail (fun term hMem => hClosed term (by simp [hMem]))])
    term hClosed

/-- free-closed 项的解释只依赖 bound stack。 -/
theorem eval_eq_of_freeClosed_of_boundVal_eq {σ : Signature}
    {M : SetLevel.StructureAt.{x} σ} {env targetEnv : SetLevel.EnvAt.{x} M}
    (hBound : ∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index) :
    ∀ term : Term σ, FreeClosed term →
      Logic.FirstOrder.Term.eval targetEnv term =
        Logic.FirstOrder.Term.eval env term
  | .var (.bvar sort index), _hClosed => by
      simpa [Logic.FirstOrder.Term.eval] using hBound sort index
  | .var (.fvar ..), hClosed => by
      simp [FreeClosed] at hClosed
  | .app f args, hClosed => by
      have hArgsClosed : ∀ term, term ∈ args → FreeClosed term := by
        simpa [FreeClosed] using hClosed
      simp [Logic.FirstOrder.Term.eval]
      apply congrArg (M.funcInterp f)
      exact List.map_congr_left fun term hMem =>
        eval_eq_of_freeClosed_of_boundVal_eq hBound term (hArgsClosed term hMem)

end Term

namespace TermSubstitution

/-- 替换中所有右侧项都不含 bound variable。 -/
def BoundClosed {σ : Signature} [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) : Prop :=
  ∀ sort id replacement,
    lookup subst sort id = some replacement → Term.BoundClosed replacement

/-- 替换中所有右侧项都与登记 sort 相匹配。 -/
def WellSorted {σ : Signature} [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) : Prop :=
  ∀ sort id replacement,
    lookup subst sort id = some replacement →
      Logic.FirstOrder.TermWellSorted replacement sort

/-- 替换的可计算检查：右侧项不含 bound variable。 -/
def checkBoundClosed {σ : Signature} : TermSubstitution σ → Bool
  | [] => true
  | (_, _, term) :: rest => Term.checkBoundClosed term && checkBoundClosed rest

/-- `checkBoundClosed` 通过时得到 `BoundClosed`。 -/
theorem checkBoundClosed_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {subst : TermSubstitution σ} :
    checkBoundClosed subst = true → BoundClosed subst := by
  induction subst with
  | nil =>
      intro _hCheck sort id replacement hLookup
      simp [lookup] at hLookup
  | cons entry rest ih =>
      rcases entry with ⟨entrySort, entryId, term⟩
      intro hCheck sort id replacement hLookup
      rcases Bool.and_eq_true_iff.mp (by simpa [checkBoundClosed] using hCheck) with
        ⟨hHead, hRest⟩
      by_cases hSort : entrySort = sort
      · by_cases hId : entryId = id
        · have hLookupHead : term = replacement := by
            simpa [lookup, hSort, hId] using hLookup
          cases hLookupHead
          exact Term.checkBoundClosed_sound hHead
        · have hLookupRest : lookup rest sort id = some replacement := by
            simpa [lookup, hSort, hId] using hLookup
          exact ih hRest sort id replacement hLookupRest
      · have hLookupRest : lookup rest sort id = some replacement := by
          simpa [lookup, hSort] using hLookup
        exact ih hRest sort id replacement hLookupRest

/-- 替换的可计算检查：右侧项的 sort 与登记 sort 匹配。 -/
def checkWellSorted {σ : Signature} [DecidableEq σ.SortSymbol] :
    TermSubstitution σ → Bool
  | [] => true
  | (sort, _, term) :: rest => Term.checkWellSorted sort term && checkWellSorted rest

/-- `checkWellSorted` 通过时得到 `WellSorted`。 -/
theorem checkWellSorted_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {subst : TermSubstitution σ} :
    checkWellSorted subst = true → WellSorted subst := by
  induction subst with
  | nil =>
      intro _hCheck sort id replacement hLookup
      simp [lookup] at hLookup
  | cons entry rest ih =>
      rcases entry with ⟨entrySort, entryId, term⟩
      intro hCheck sort id replacement hLookup
      rcases Bool.and_eq_true_iff.mp (by simpa [checkWellSorted] using hCheck) with
        ⟨hHead, hRest⟩
      by_cases hSort : entrySort = sort
      · by_cases hId : entryId = id
        · have hLookupHead : term = replacement := by
            simpa [lookup, hSort, hId] using hLookup
          cases hLookupHead
          cases hSort
          exact Term.checkWellSorted_sound hHead
        · have hLookupRest : lookup rest sort id = some replacement := by
            simpa [lookup, hSort, hId] using hLookup
          exact ih hRest sort id replacement hLookupRest
      · have hLookupRest : lookup rest sort id = some replacement := by
          simpa [lookup, hSort] using hLookup
        exact ih hRest sort id replacement hLookupRest

/-- 替换的联合可计算检查。 -/
def checkAdmissible {σ : Signature} [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) : Bool :=
  checkBoundClosed subst && checkWellSorted subst

/-- `checkAdmissible` 通过时得到 substitution 的语义合同。 -/
theorem checkAdmissible_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {subst : TermSubstitution σ} (hCheck : checkAdmissible subst = true) :
    BoundClosed subst ∧ WellSorted subst := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hClosed, hWell⟩
  exact ⟨checkBoundClosed_sound hClosed, checkWellSorted_sound hWell⟩

/--
`targetEnv` 是把 `subst` 作用到 `env` 的语义环境：
bound 栈保持一致，free 变量按 substitution 更新；没有命中的 free 变量保持原值。
-/
def EnvMatches {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (subst : TermSubstitution σ)
  (env targetEnv : SetLevel.EnvAt.{x} M) : Prop :=
  (∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index) ∧
    ∀ sort id,
      targetEnv.freeVal sort id =
        match lookup subst sort id with
        | some replacement => Logic.FirstOrder.Term.eval env replacement
        | none => env.freeVal sort id

/-- 由一个可采纳 substitution 和原始环境构造语义目标环境。 -/
def semanticEnv {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (subst : TermSubstitution σ)
    (env : SetLevel.EnvAt.{x} M) (hAdmissible : WellSorted subst) : SetLevel.EnvAt.{x} M where
  boundVal := env.boundVal
  freeVal := fun sort id =>
    match lookup subst sort id with
    | some replacement => Logic.FirstOrder.Term.eval env replacement
    | none => env.freeVal sort id
  boundSort := env.boundSort
  freeSort := by
    intro sort id
    cases hLookup : lookup subst sort id with
    | none =>
        simpa [hLookup] using env.freeSort sort id
    | some replacement =>
        simpa [hLookup] using
          Logic.FirstOrder.Term.eval_sort_of_wellSorted
            (env := env) (term := replacement)
            (hAdmissible sort id replacement hLookup)

/-- `semanticEnv` 正是 substitution 对自由变量环境的语义作用。 -/
theorem semanticEnv_matches {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {subst : TermSubstitution σ}
    {env : SetLevel.EnvAt.{x} M} (hAdmissible : WellSorted subst) :
    EnvMatches subst env (semanticEnv subst env hAdmissible) := by
  constructor
  · intro sort index
    rfl
  · intro sort id
    rfl

namespace EnvMatches

/-- 语义环境匹配在同一个 bound 值入栈后保持。 -/
theorem pushBound {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {subst : TermSubstitution σ}
    {env targetEnv : SetLevel.EnvAt.{x} M}
    (hClosed : BoundClosed subst)
    (hEnv : EnvMatches subst env targetEnv)
    (sort : σ.SortSymbol) (value : M.Domain)
    (hValue : M.sortInterp sort value) :
    EnvMatches subst (env.pushBound sort value hValue)
      (targetEnv.pushBound sort value hValue) := by
  constructor
  · intro target index
    by_cases hTarget : target = sort
    · cases index with
      | zero =>
          simp [Logic.FirstOrder.Env.pushBound, hTarget]
      | succ previous =>
          simpa [Logic.FirstOrder.Env.pushBound, hTarget] using hEnv.1 target previous
    · simpa [Logic.FirstOrder.Env.pushBound, hTarget] using hEnv.1 target index
  · intro target id
    have hFree := hEnv.2 target id
    cases hLookup : lookup subst target id with
    | none =>
        simpa [Logic.FirstOrder.Env.pushBound, hLookup] using hFree
    | some replacement =>
        have hStable :
            Logic.FirstOrder.Term.eval (env.pushBound sort value hValue) replacement =
              Logic.FirstOrder.Term.eval env replacement :=
          Term.eval_pushBound_of_boundClosed
            (env := env) (term := replacement)
            (hClosed target id replacement hLookup) sort value hValue
        simpa [Logic.FirstOrder.Env.pushBound, hLookup, hStable.symm] using hFree

end EnvMatches

end TermSubstitution

namespace FreeVarRenaming

/--
`targetEnv` 是从 `sourceEnv` 按 `offset` 投影得到的自由变量环境。
bound 栈保持一致，目标环境中的 `id` 对应源环境中的 `id + offset`。
-/
def EnvMatches {σ : Signature} {M : SetLevel.StructureAt.{x} σ} (offset : Nat)
    (sourceEnv targetEnv : SetLevel.EnvAt.{x} M) : Prop :=
  (∀ sort index, targetEnv.boundVal sort index = sourceEnv.boundVal sort index) ∧
    ∀ sort id, targetEnv.freeVal sort id = sourceEnv.freeVal sort (id + offset)

/-- 从偏移后的源环境构造原编号可消费的投影环境。 -/
def semanticEnv {σ : Signature} {M : SetLevel.StructureAt.{x} σ} (offset : Nat)
    (sourceEnv : SetLevel.EnvAt.{x} M) : SetLevel.EnvAt.{x} M where
  boundVal := sourceEnv.boundVal
  freeVal := fun sort id => sourceEnv.freeVal sort (id + offset)
  boundSort := sourceEnv.boundSort
  freeSort := fun sort id => sourceEnv.freeSort sort (id + offset)

/-- `semanticEnv` 满足自由变量重索引关系。 -/
theorem semanticEnv_matches {σ : Signature} {M : SetLevel.StructureAt.{x} σ}
    {offset : Nat} {sourceEnv : SetLevel.EnvAt.{x} M} :
    EnvMatches offset sourceEnv (semanticEnv offset sourceEnv) := by
  constructor <;> intro sort index <;> rfl

namespace EnvMatches

/-- 自由变量重索引关系在两侧压入同一个 bound 值后保持。 -/
theorem pushBound {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {offset : Nat}
    {sourceEnv targetEnv : SetLevel.EnvAt.{x} M}
    (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv)
    (sort : σ.SortSymbol) (value : M.Domain)
    (hValue : M.sortInterp sort value) :
    FreeVarRenaming.EnvMatches offset
      (sourceEnv.pushBound sort value hValue)
      (targetEnv.pushBound sort value hValue) := by
  constructor
  · intro target index
    by_cases hTarget : target = sort
    · cases index with
      | zero =>
          simp [Logic.FirstOrder.Env.pushBound, hTarget]
      | succ previous =>
          simpa [Logic.FirstOrder.Env.pushBound, hTarget] using hEnv.1 target previous
    · simpa [Logic.FirstOrder.Env.pushBound, hTarget] using hEnv.1 target index
  · intro target id
    simpa [Logic.FirstOrder.Env.pushBound] using hEnv.2 target id

end EnvMatches

end FreeVarRenaming

namespace Term

/-- 项替换的语义：语法替换等价于更新自由变量环境。 -/
theorem eval_applySubstitution_eq_of_envMatches {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {subst : TermSubstitution σ} {env targetEnv : SetLevel.EnvAt.{x} M}
    (hEnv : TermSubstitution.EnvMatches subst env targetEnv) :
    ∀ term : Term σ,
      Logic.FirstOrder.Term.eval env (applySubstitution subst term) =
        Logic.FirstOrder.Term.eval targetEnv term
  | .var (.bvar sort index) => by
      simpa [applySubstitution, Logic.FirstOrder.Term.eval] using
        (hEnv.1 sort index).symm
  | .var (.fvar sort id) => by
      cases hLookup : TermSubstitution.lookup subst sort id with
      | none =>
          simpa [applySubstitution, Logic.FirstOrder.Term.eval, hLookup] using
            (hEnv.2 sort id).symm
      | some replacement =>
          simpa [applySubstitution, Logic.FirstOrder.Term.eval, hLookup] using
            (hEnv.2 sort id).symm
  | .app f args => by
      simp only [applySubstitution, Logic.FirstOrder.Term.eval]
      apply congrArg (M.funcInterp f)
      rw [applySubstitutionList_eq_map, List.map_map]
      exact List.map_congr_left fun term _ =>
        eval_applySubstitution_eq_of_envMatches (subst := subst)
          (env := env) (targetEnv := targetEnv) hEnv term

/-- 自由变量平移的语义：语法编号平移等价于投影自由变量环境。 -/
theorem eval_renameFreeVars_eq_of_envMatches {σ : Signature}
    {M : SetLevel.StructureAt.{x} σ} {offset : Nat}
    {sourceEnv targetEnv : SetLevel.EnvAt.{x} M}
    (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) :
    ∀ term : Term σ,
      Logic.FirstOrder.Term.eval sourceEnv (renameFreeVars offset term) =
        Logic.FirstOrder.Term.eval targetEnv term
  | .var (.bvar sort index) => by
      simpa [renameFreeVars, Logic.FirstOrder.Term.eval] using
        (hEnv.1 sort index).symm
  | .var (.fvar sort id) => by
      simpa [renameFreeVars, Logic.FirstOrder.Term.eval] using
        (hEnv.2 sort id).symm
  | .app f args => by
      simp only [renameFreeVars, Logic.FirstOrder.Term.eval]
      apply congrArg (M.funcInterp f)
      rw [renameFreeVarsList_eq_map, List.map_map]
      exact List.map_congr_left fun term _ =>
        eval_renameFreeVars_eq_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv term

end Term

namespace Formula

/-- 将有限替换作用到 DAG 公式。 -/
def applySubstitution {σ : Signature} [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) : Formula σ → Formula σ
  | .falsum => .falsum
  | .truth => .truth
  | .rel r args => .rel r (args.map (Term.applySubstitution subst))
  | .equal left right =>
      .equal (Term.applySubstitution subst left) (Term.applySubstitution subst right)
  | .neg φ => .neg (applySubstitution subst φ)
  | .conj φ ψ => .conj (applySubstitution subst φ) (applySubstitution subst ψ)
  | .disj φ ψ => .disj (applySubstitution subst φ) (applySubstitution subst ψ)
  | .imp φ ψ => .imp (applySubstitution subst φ) (applySubstitution subst ψ)
  | .iff φ ψ => .iff (applySubstitution subst φ) (applySubstitution subst ψ)
  | .forallE sort body => .forallE sort (applySubstitution subst body)
  | .existsE sort body => .existsE sort (applySubstitution subst body)

/-- 将公式中的 free variable 编号整体平移。 -/
def renameFreeVars {σ : Signature} (offset : Nat) : Formula σ → Formula σ
  | .falsum => .falsum
  | .truth => .truth
  | .rel r args => .rel r (args.map (Term.renameFreeVars offset))
  | .equal left right =>
      .equal (Term.renameFreeVars offset left) (Term.renameFreeVars offset right)
  | .neg φ => .neg (renameFreeVars offset φ)
  | .conj φ ψ => .conj (renameFreeVars offset φ) (renameFreeVars offset ψ)
  | .disj φ ψ => .disj (renameFreeVars offset φ) (renameFreeVars offset ψ)
  | .imp φ ψ => .imp (renameFreeVars offset φ) (renameFreeVars offset ψ)
  | .iff φ ψ => .iff (renameFreeVars offset φ) (renameFreeVars offset ψ)
  | .forallE sort body => .forallE sort (renameFreeVars offset body)
  | .existsE sort body => .existsE sort (renameFreeVars offset body)

/-- 项中没有 free variable 时，公式的满足性只依赖 bound stack。 -/
def FreeClosed {σ : Signature} : Formula σ → Prop
  | .falsum => True
  | .truth => True
  | .rel _ args => ∀ term, term ∈ args → Term.FreeClosed term
  | .equal left right => Term.FreeClosed left ∧ Term.FreeClosed right
  | .neg φ => FreeClosed φ
  | .conj φ ψ => FreeClosed φ ∧ FreeClosed ψ
  | .disj φ ψ => FreeClosed φ ∧ FreeClosed ψ
  | .imp φ ψ => FreeClosed φ ∧ FreeClosed ψ
  | .iff φ ψ => FreeClosed φ ∧ FreeClosed ψ
  | .forallE _ body => FreeClosed body
  | .existsE _ body => FreeClosed body

/-- 可计算检查：公式中没有 free variable。 -/
def checkFreeClosed {σ : Signature} [DecidableEq σ.SortSymbol] :
    Formula σ → Bool
  | .falsum => true
  | .truth => true
  | .rel _ args => args.all Term.checkFreeClosed
  | .equal left right => Term.checkFreeClosed left && Term.checkFreeClosed right
  | .neg φ => checkFreeClosed φ
  | .conj φ ψ => checkFreeClosed φ && checkFreeClosed ψ
  | .disj φ ψ => checkFreeClosed φ && checkFreeClosed ψ
  | .imp φ ψ => checkFreeClosed φ && checkFreeClosed ψ
  | .iff φ ψ => checkFreeClosed φ && checkFreeClosed ψ
  | .forallE _ body => checkFreeClosed body
  | .existsE _ body => checkFreeClosed body

/-- `checkFreeClosed` 通过时得到 Prop 版 free-closed 合同。 -/
theorem checkFreeClosed_sound {σ : Signature} [DecidableEq σ.SortSymbol] :
    ∀ {φ : Formula σ}, checkFreeClosed φ = true → FreeClosed φ := by
  intro φ
  induction φ with
  | falsum =>
      intro _hCheck
      simp [FreeClosed]
  | truth =>
      intro _hCheck
      simp [FreeClosed]
  | rel _ args =>
      intro hCheck term hMem
      have hAll : ∀ term, term ∈ args → Term.checkFreeClosed term = true := by
        exact List.all_eq_true.mp (by simpa [checkFreeClosed] using hCheck)
      exact Term.checkFreeClosed_sound (hAll term hMem)
  | equal left right =>
      intro hCheck
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
      exact ⟨Term.checkFreeClosed_sound hLeft, Term.checkFreeClosed_sound hRight⟩
  | neg φ ih =>
      intro hCheck
      exact ih hCheck
  | conj φ ψ ihφ ihψ =>
      intro hCheck
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hφ, hψ⟩
      exact ⟨ihφ hφ, ihψ hψ⟩
  | disj φ ψ ihφ ihψ =>
      intro hCheck
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hφ, hψ⟩
      exact ⟨ihφ hφ, ihψ hψ⟩
  | imp φ ψ ihφ ihψ =>
      intro hCheck
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hφ, hψ⟩
      exact ⟨ihφ hφ, ihψ hψ⟩
  | iff φ ψ ihφ ihψ =>
      intro hCheck
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hφ, hψ⟩
      exact ⟨ihφ hφ, ihψ hψ⟩
  | forallE _ body ih =>
      intro hCheck
      exact ih hCheck
  | existsE _ body ih =>
      intro hCheck
      exact ih hCheck

/-- free-closed 公式的满足性只依赖 bound stack。 -/
theorem satisfies_iff_of_freeClosed_of_boundVal_eq {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {env targetEnv : SetLevel.EnvAt.{x} M}
    (hBound : ∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index)
    (φ : Formula σ) (hClosed : FreeClosed φ) :
      Logic.FirstOrder.Formula.satisfies targetEnv φ ↔
        Logic.FirstOrder.Formula.satisfies env φ := by
  induction φ generalizing env targetEnv with
  | falsum =>
      simp [Logic.FirstOrder.Formula.satisfies]
  | truth =>
      simp [Logic.FirstOrder.Formula.satisfies]
  | rel r args =>
      have hArgsClosed : ∀ term, term ∈ args → Term.FreeClosed term := by
        simpa [FreeClosed] using hClosed
      have hArgs :
          args.map (Logic.FirstOrder.Term.eval targetEnv) =
            args.map (Logic.FirstOrder.Term.eval env) := by
        exact List.map_congr_left fun term hMem =>
          Term.eval_eq_of_freeClosed_of_boundVal_eq hBound term
            (hArgsClosed term hMem)
      simp [Logic.FirstOrder.Formula.satisfies, hArgs]
  | equal left right =>
      have hClosed' : Term.FreeClosed left ∧ Term.FreeClosed right := by
        simpa [FreeClosed] using hClosed
      rcases hClosed' with ⟨hLeft, hRight⟩
      simp [Logic.FirstOrder.Formula.satisfies,
        Term.eval_eq_of_freeClosed_of_boundVal_eq hBound left hLeft,
        Term.eval_eq_of_freeClosed_of_boundVal_eq hBound right hRight]
  | neg φ ih =>
      simpa [Logic.FirstOrder.Formula.satisfies] using
        not_congr (ih hBound hClosed)
  | conj φ ψ ihφ ihψ =>
      have hClosed' : FreeClosed φ ∧ FreeClosed ψ := by
        simpa [FreeClosed] using hClosed
      rcases hClosed' with ⟨hφ, hψ⟩
      simp [Logic.FirstOrder.Formula.satisfies,
        ihφ hBound hφ, ihψ hBound hψ]
  | disj φ ψ ihφ ihψ =>
      have hClosed' : FreeClosed φ ∧ FreeClosed ψ := by
        simpa [FreeClosed] using hClosed
      rcases hClosed' with ⟨hφ, hψ⟩
      simp [Logic.FirstOrder.Formula.satisfies,
        ihφ hBound hφ, ihψ hBound hψ]
  | imp φ ψ ihφ ihψ =>
      have hClosed' : FreeClosed φ ∧ FreeClosed ψ := by
        simpa [FreeClosed] using hClosed
      rcases hClosed' with ⟨hφ, hψ⟩
      simp [Logic.FirstOrder.Formula.satisfies,
        ihφ hBound hφ, ihψ hBound hψ]
  | iff φ ψ ihφ ihψ =>
      have hClosed' : FreeClosed φ ∧ FreeClosed ψ := by
        simpa [FreeClosed] using hClosed
      rcases hClosed' with ⟨hφ, hψ⟩
      simp [Logic.FirstOrder.Formula.satisfies,
        ihφ hBound hφ, ihψ hBound hψ]
  | forallE qsort body ih =>
      constructor
      · intro h value hValue
        have hBound' :
            ∀ sort' index,
              (targetEnv.pushBound qsort value hValue).boundVal sort' index =
                (env.pushBound qsort value hValue).boundVal sort' index := by
          intro sort' index
          by_cases hSort : sort' = qsort
          · subst hSort
            cases index with
            | zero => simp [Logic.FirstOrder.Env.pushBound]
            | succ prev =>
                simp [Logic.FirstOrder.Env.pushBound, hBound sort' prev]
          · simp [Logic.FirstOrder.Env.pushBound, hSort, hBound sort' index]
        exact
          (ih hBound' hClosed).mp (h value hValue)
      · intro h value hValue
        have hBound' :
            ∀ sort' index,
              (targetEnv.pushBound qsort value hValue).boundVal sort' index =
                (env.pushBound qsort value hValue).boundVal sort' index := by
          intro sort' index
          by_cases hSort : sort' = qsort
          · subst hSort
            cases index with
            | zero => simp [Logic.FirstOrder.Env.pushBound]
            | succ prev =>
                simp [Logic.FirstOrder.Env.pushBound, hBound sort' prev]
          · simp [Logic.FirstOrder.Env.pushBound, hSort, hBound sort' index]
        exact
          (ih hBound' hClosed).mpr (h value hValue)
  | existsE qsort body ih =>
      constructor
      · intro h
        rcases h with ⟨value, hValue, hBody⟩
        have hBound' :
            ∀ sort' index,
              (targetEnv.pushBound qsort value hValue).boundVal sort' index =
                (env.pushBound qsort value hValue).boundVal sort' index := by
          intro sort' index
          by_cases hSort : sort' = qsort
          · subst hSort
            cases index with
            | zero => simp [Logic.FirstOrder.Env.pushBound]
            | succ prev =>
                simp [Logic.FirstOrder.Env.pushBound, hBound sort' prev]
          · simp [Logic.FirstOrder.Env.pushBound, hSort, hBound sort' index]
        exact ⟨value, hValue,
          (ih hBound' hClosed).mp hBody⟩
      · intro h
        rcases h with ⟨value, hValue, hBody⟩
        have hBound' :
            ∀ sort' index,
              (targetEnv.pushBound qsort value hValue).boundVal sort' index =
                (env.pushBound qsort value hValue).boundVal sort' index := by
          intro sort' index
          by_cases hSort : sort' = qsort
          · subst hSort
            cases index with
            | zero => simp [Logic.FirstOrder.Env.pushBound]
            | succ prev =>
                simp [Logic.FirstOrder.Env.pushBound, hBound sort' prev]
          · simp [Logic.FirstOrder.Env.pushBound, hSort, hBound sort' index]
        exact ⟨value, hValue,
          (ih hBound' hClosed).mpr hBody⟩

/-- 公式替换的语义：语法替换等价于更新自由变量环境。 -/
theorem satisfies_applySubstitution_iff_of_envMatches {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {subst : TermSubstitution σ} {env targetEnv : SetLevel.EnvAt.{x} M}
    (hClosed : TermSubstitution.BoundClosed subst)
    (hEnv : TermSubstitution.EnvMatches subst env targetEnv) :
    ∀ φ : Formula σ,
      Logic.FirstOrder.Formula.satisfies env (applySubstitution subst φ) ↔
        Logic.FirstOrder.Formula.satisfies targetEnv φ
  | .falsum => by
      simp [applySubstitution, Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [applySubstitution, Logic.FirstOrder.Formula.satisfies]
  | .rel r args => by
      have hArgs :
          (args.map (Term.applySubstitution subst)).map
              (Logic.FirstOrder.Term.eval env) =
            args.map (Logic.FirstOrder.Term.eval targetEnv) := by
        simp [List.map_map,
          Term.eval_applySubstitution_eq_of_envMatches
            (subst := subst) (env := env) (targetEnv := targetEnv) hEnv]
      simp [applySubstitution, Logic.FirstOrder.Formula.satisfies, hArgs]
  | .equal left right => by
      simp [applySubstitution, Logic.FirstOrder.Formula.satisfies,
        Term.eval_applySubstitution_eq_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hEnv]
  | .neg φ => by
      simp [applySubstitution, Logic.FirstOrder.Formula.satisfies,
        satisfies_applySubstitution_iff_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv φ]
  | .conj φ ψ => by
      simp [applySubstitution, Logic.FirstOrder.Formula.satisfies,
        satisfies_applySubstitution_iff_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv φ,
        satisfies_applySubstitution_iff_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv ψ]
  | .disj φ ψ => by
      simp [applySubstitution, Logic.FirstOrder.Formula.satisfies,
        satisfies_applySubstitution_iff_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv φ,
        satisfies_applySubstitution_iff_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv ψ]
  | .imp φ ψ => by
      simp [applySubstitution, Logic.FirstOrder.Formula.satisfies,
        satisfies_applySubstitution_iff_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv φ,
        satisfies_applySubstitution_iff_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv ψ]
  | .iff φ ψ => by
      simp [applySubstitution, Logic.FirstOrder.Formula.satisfies,
        satisfies_applySubstitution_iff_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv φ,
        satisfies_applySubstitution_iff_of_envMatches
          (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv ψ]
  | .forallE sort body => by
      constructor
      · intro h value hValue
        have hEnv' :=
          TermSubstitution.EnvMatches.pushBound
            (subst := subst) hClosed hEnv sort value hValue
        exact
          (satisfies_applySubstitution_iff_of_envMatches
              (subst := subst)
              (env := env.pushBound sort value hValue)
              (targetEnv := targetEnv.pushBound sort value hValue)
              hClosed hEnv' body).mp (h value hValue)
      · intro h value hValue
        have hEnv' :=
          TermSubstitution.EnvMatches.pushBound
            (subst := subst) hClosed hEnv sort value hValue
        exact
          (satisfies_applySubstitution_iff_of_envMatches
              (subst := subst)
              (env := env.pushBound sort value hValue)
              (targetEnv := targetEnv.pushBound sort value hValue)
              hClosed hEnv' body).mpr (h value hValue)
  | .existsE sort body => by
      constructor
      · intro h
        rcases h with ⟨value, hValue, hBody⟩
        have hEnv' :=
          TermSubstitution.EnvMatches.pushBound
            (subst := subst) hClosed hEnv sort value hValue
        exact ⟨value, hValue,
          (satisfies_applySubstitution_iff_of_envMatches
              (subst := subst)
              (env := env.pushBound sort value hValue)
              (targetEnv := targetEnv.pushBound sort value hValue)
              hClosed hEnv' body).mp hBody⟩
      · intro h
        rcases h with ⟨value, hValue, hBody⟩
        have hEnv' :=
          TermSubstitution.EnvMatches.pushBound
            (subst := subst) hClosed hEnv sort value hValue
        exact ⟨value, hValue,
          (satisfies_applySubstitution_iff_of_envMatches
              (subst := subst)
              (env := env.pushBound sort value hValue)
              (targetEnv := targetEnv.pushBound sort value hValue)
              hClosed hEnv' body).mpr hBody⟩

/-- 自由变量平移的语义：语法编号平移等价于投影自由变量环境。 -/
theorem satisfies_renameFreeVars_iff_of_envMatches {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {offset : Nat} {sourceEnv targetEnv : SetLevel.EnvAt.{x} M}
    (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) :
    ∀ φ : Formula σ,
      Logic.FirstOrder.Formula.satisfies sourceEnv (renameFreeVars offset φ) ↔
        Logic.FirstOrder.Formula.satisfies targetEnv φ
  | .falsum => by
      simp [renameFreeVars, Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [renameFreeVars, Logic.FirstOrder.Formula.satisfies]
  | .rel r args => by
      have hArgs :
          (args.map (Term.renameFreeVars offset)).map
              (Logic.FirstOrder.Term.eval sourceEnv) =
            args.map (Logic.FirstOrder.Term.eval targetEnv) := by
        simp [List.map_map,
          Term.eval_renameFreeVars_eq_of_envMatches
            (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv]
      simp [renameFreeVars, Logic.FirstOrder.Formula.satisfies, hArgs]
  | .equal left right => by
      simp [renameFreeVars, Logic.FirstOrder.Formula.satisfies,
        Term.eval_renameFreeVars_eq_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv]
  | .neg φ => by
      simp [renameFreeVars, Logic.FirstOrder.Formula.satisfies,
        satisfies_renameFreeVars_iff_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv φ]
  | .conj φ ψ => by
      simp [renameFreeVars, Logic.FirstOrder.Formula.satisfies,
        satisfies_renameFreeVars_iff_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv φ,
        satisfies_renameFreeVars_iff_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv ψ]
  | .disj φ ψ => by
      simp [renameFreeVars, Logic.FirstOrder.Formula.satisfies,
        satisfies_renameFreeVars_iff_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv φ,
        satisfies_renameFreeVars_iff_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv ψ]
  | .imp φ ψ => by
      simp [renameFreeVars, Logic.FirstOrder.Formula.satisfies,
        satisfies_renameFreeVars_iff_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv φ,
        satisfies_renameFreeVars_iff_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv ψ]
  | .iff φ ψ => by
      simp [renameFreeVars, Logic.FirstOrder.Formula.satisfies,
        satisfies_renameFreeVars_iff_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv φ,
        satisfies_renameFreeVars_iff_of_envMatches
          (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv ψ]
  | .forallE sort body => by
      constructor
      · intro h value hValue
        have hEnv' :=
          FreeVarRenaming.EnvMatches.pushBound hEnv sort value hValue
        exact
          (satisfies_renameFreeVars_iff_of_envMatches
              (offset := offset)
              (sourceEnv := sourceEnv.pushBound sort value hValue)
              (targetEnv := targetEnv.pushBound sort value hValue)
              hEnv' body).mp (h value hValue)
      · intro h value hValue
        have hEnv' :=
          FreeVarRenaming.EnvMatches.pushBound hEnv sort value hValue
        exact
          (satisfies_renameFreeVars_iff_of_envMatches
              (offset := offset)
              (sourceEnv := sourceEnv.pushBound sort value hValue)
              (targetEnv := targetEnv.pushBound sort value hValue)
              hEnv' body).mpr (h value hValue)
  | .existsE sort body => by
      constructor
      · intro h
        rcases h with ⟨value, hValue, hBody⟩
        have hEnv' :=
          FreeVarRenaming.EnvMatches.pushBound hEnv sort value hValue
        exact ⟨value, hValue,
          (satisfies_renameFreeVars_iff_of_envMatches
              (offset := offset)
              (sourceEnv := sourceEnv.pushBound sort value hValue)
              (targetEnv := targetEnv.pushBound sort value hValue)
              hEnv' body).mp hBody⟩
      · intro h
        rcases h with ⟨value, hValue, hBody⟩
        have hEnv' :=
          FreeVarRenaming.EnvMatches.pushBound hEnv sort value hValue
        exact ⟨value, hValue,
          (satisfies_renameFreeVars_iff_of_envMatches
              (offset := offset)
              (sourceEnv := sourceEnv.pushBound sort value hValue)
              (targetEnv := targetEnv.pushBound sort value hValue)
              hEnv' body).mpr hBody⟩

end Formula

namespace DeepProblem

/-- problem 背景不含 free variable。substitution replay 需要用它切换自由变量环境。 -/
def FreeClosed {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) : Prop :=
  Formula.FreeClosed problem.target ∧
    ∀ premise, premise ∈ problem.premises → Formula.FreeClosed premise

/-- 可计算检查：problem 的所有前提和目标都不含 free variable。 -/
def freeClosed {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) : Bool :=
  Formula.checkFreeClosed problem.target &&
    problem.premises.all Formula.checkFreeClosed

/-- `freeClosed` 通过时得到 Prop 版 problem 闭合合同。 -/
theorem freeClosed_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (hCheck : problem.freeClosed = true) :
    FreeClosed problem := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hTarget, hPremises⟩
  constructor
  · exact Formula.checkFreeClosed_sound hTarget
  · intro premise hMem
    have hAll :
        ∀ premise, premise ∈ problem.premises →
          Formula.checkFreeClosed premise = true :=
      List.all_eq_true.mp hPremises
    exact Formula.checkFreeClosed_sound (hAll premise hMem)

/-- free-closed problem 的理论模型性可在相同 bound stack 的环境间转移。 -/
theorem models_of_freeClosed_of_boundVal_eq {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {problem : DeepProblem σ} {env targetEnv : SetLevel.EnvAt.{x} M}
    (hClosed : FreeClosed problem)
    (hBound : ∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index)
    (hModels : Logic.FirstOrder.Theory.Models problem.theory env) :
    Logic.FirstOrder.Theory.Models problem.theory targetEnv := by
  intro premise hMem
  exact
    (Formula.satisfies_iff_of_freeClosed_of_boundVal_eq hBound
      premise (hClosed.2 premise hMem)).mpr (hModels premise hMem)

/-- free-closed problem 的目标假性可在相同 bound stack 的环境间转移。 -/
theorem targetFalse_of_freeClosed_of_boundVal_eq {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {problem : DeepProblem σ} {env targetEnv : SetLevel.EnvAt.{x} M}
    (hClosed : FreeClosed problem)
    (hBound : ∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index)
    (hTargetFalse : ¬ Logic.FirstOrder.Formula.satisfies env problem.target) :
    ¬ Logic.FirstOrder.Formula.satisfies targetEnv problem.target := by
  intro hTarget
  exact hTargetFalse
    ((Formula.satisfies_iff_of_freeClosed_of_boundVal_eq hBound
      problem.target hClosed.1).mp hTarget)

end DeepProblem

/-- DAG 字句文字。`polarity = false` 表示对象层否定。 -/
structure Literal (σ : Signature) where
  polarity : Bool
  atom : Formula σ

namespace Literal

/-- 正文字。 -/
def pos {σ : Signature} (φ : Formula σ) : Literal σ :=
  { polarity := true, atom := φ }

/-- 负文字。 -/
def neg {σ : Signature} (φ : Formula σ) : Literal σ :=
  { polarity := false, atom := φ }

/-- 文字对应的对象语言公式。 -/
def toFormula {σ : Signature} (literal : Literal σ) : Formula σ :=
  if literal.polarity then literal.atom else .neg literal.atom

/-- 文字的自由变量支持。极性不改变支持。 -/
def freeSupport {σ : Signature} (literal : Literal σ) :
    Logic.FirstOrder.FreeVariable.Support σ :=
  Logic.FirstOrder.Formula.freeSupport literal.atom

/-- 文字公式视图与文字本身具有相同的自由变量支持。 -/
theorem freeSupport_toFormula {σ : Signature} (literal : Literal σ) :
    Logic.FirstOrder.Formula.freeSupport literal.toFormula = literal.freeSupport := by
  cases literal with
  | mk polarity atom =>
      cases polarity <;> rfl

/-- 将有限替换作用到文字。 -/
def applySubstitution {σ : Signature} [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) (literal : Literal σ) : Literal σ :=
  { literal with atom := Formula.applySubstitution subst literal.atom }

/-- 将文字中的 free variable 编号整体平移。 -/
def renameFreeVars {σ : Signature} (offset : Nat) (literal : Literal σ) :
    Literal σ :=
  { literal with atom := Formula.renameFreeVars offset literal.atom }

/-- 文字结构比较。 -/
def eq {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (left right : Literal σ) : Bool :=
  left.polarity == right.polarity && StructuralEq.formula left.atom right.atom

/-- 文字结构比较为真时，两侧文字实际相等。 -/
theorem eq_sound {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (left right : Literal σ) :
    left.eq right = true → left = right := by
  cases left
  cases right
  intro h
  simp [eq] at h
  rcases h with ⟨hPolarity, hAtom⟩
  cases hPolarity
  have hAtomEq := StructuralEq.formula_sound _ _ hAtom
  cases hAtomEq
  rfl

/-- 对象层文字在某个环境下为真。 -/
def Satisfies {σ : Signature} [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    (env : SetLevel.EnvAt.{x} M) (literal : Literal σ) : Prop :=
  Logic.FirstOrder.Formula.satisfies env literal.toFormula

/-- 文字满足性只依赖其自由变量支持和完整 bound stack。 -/
theorem satisfies_iff_of_agreesOn {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {left right : SetLevel.EnvAt.{x} M}
    (literal : Literal σ)
    (hEnv : Logic.FirstOrder.Env.AgreesOn literal.freeSupport left right) :
    Satisfies left literal ↔ Satisfies right literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · change
          (¬ Logic.FirstOrder.Formula.satisfies left atom) ↔
            ¬ Logic.FirstOrder.Formula.satisfies right atom
        exact not_congr
          (Logic.FirstOrder.Formula.satisfies_iff_of_agreesOn atom hEnv)
      · exact Logic.FirstOrder.Formula.satisfies_iff_of_agreesOn atom hEnv

/-- 文字替换的语义：语法替换等价于更新自由变量环境。 -/
theorem satisfies_applySubstitution_iff_of_envMatches {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {subst : TermSubstitution σ} {env targetEnv : SetLevel.EnvAt.{x} M}
    (hClosed : TermSubstitution.BoundClosed subst)
    (hEnv : TermSubstitution.EnvMatches subst env targetEnv)
    (literal : Literal σ) :
    Satisfies env (applySubstitution subst literal) ↔
      Satisfies targetEnv literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · change
          (¬ Logic.FirstOrder.Formula.satisfies env
              (Formula.applySubstitution subst atom)) ↔
            ¬ Logic.FirstOrder.Formula.satisfies targetEnv atom
        exact not_congr
          (Formula.satisfies_applySubstitution_iff_of_envMatches
            (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv atom)
      · exact
          Formula.satisfies_applySubstitution_iff_of_envMatches
            (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv atom

/-- 文字中的自由变量平移等价于投影自由变量环境。 -/
theorem satisfies_renameFreeVars_iff_of_envMatches {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {offset : Nat} {sourceEnv targetEnv : SetLevel.EnvAt.{x} M}
    (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv)
    (literal : Literal σ) :
    Satisfies sourceEnv (renameFreeVars offset literal) ↔
      Satisfies targetEnv literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · change
          (¬ Logic.FirstOrder.Formula.satisfies sourceEnv
              (Formula.renameFreeVars offset atom)) ↔
            ¬ Logic.FirstOrder.Formula.satisfies targetEnv atom
        exact not_congr
          (Formula.satisfies_renameFreeVars_iff_of_envMatches
            (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv atom)
      · exact
          Formula.satisfies_renameFreeVars_iff_of_envMatches
            (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv atom

/-- 文字是否匹配给定极性和原子。 -/
def matchesAtom {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (polarity : Bool) (atom : Formula σ)
    (literal : Literal σ) : Bool :=
  literal.polarity == polarity && StructuralEq.formula literal.atom atom

/-- 文字匹配检查通过时，极性和原子都实际相等。 -/
theorem matchesAtom_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {polarity : Bool} {atom : Formula σ} {literal : Literal σ}
    (hMatches : literal.matchesAtom polarity atom = true) :
    literal.polarity = polarity ∧ literal.atom = atom := by
  unfold matchesAtom at hMatches
  rcases Bool.and_eq_true_iff.mp hMatches with ⟨hPolarity, hAtom⟩
  exact ⟨beq_iff_eq.mp hPolarity,
    StructuralEq.formula_sound literal.atom atom hAtom⟩

/-- 互补 pivot 文字不可能同时为真。 -/
theorem not_satisfies_matchesAtom_complement {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {pivotPolarity : Bool} {atom : Formula σ} {left right : Literal σ}
    (hLeftMatch : left.matchesAtom pivotPolarity atom = true)
    (hRightMatch : right.matchesAtom (!pivotPolarity) atom = true)
    (hLeft : Satisfies env left) (hRight : Satisfies env right) : False := by
  cases left with
  | mk leftPolarity leftAtom =>
  cases right with
  | mk rightPolarity rightAtom =>
  rcases matchesAtom_sound hLeftMatch with ⟨hLeftPolarity, hLeftAtom⟩
  rcases matchesAtom_sound hRightMatch with ⟨hRightPolarity, hRightAtom⟩
  cases hLeftPolarity
  cases hLeftAtom
  cases hRightPolarity
  cases hRightAtom
  cases leftPolarity
  · simp [Satisfies, toFormula, Logic.FirstOrder.Formula.satisfies] at hLeft hRight
    exact hLeft hRight
  · simp [Satisfies, toFormula, Logic.FirstOrder.Formula.satisfies] at hLeft hRight
    exact hRight hLeft

/-- 结构相等的负等词文字不可能为真。 -/
theorem not_satisfies_reflexive_negative_equality {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {left right : Term σ} {literal : Literal σ}
    (hTerm : StructuralEq.term left right = true)
    (hMatch : literal.matchesAtom false (.equal left right) = true)
    (hLiteral : Satisfies env literal) : False := by
  rcases matchesAtom_sound hMatch with ⟨hPolarity, hAtom⟩
  have hTermEq : left = right := StructuralEq.term_sound left right hTerm
  cases literal
  cases hPolarity
  cases hAtom
  cases hTermEq
  simp [Satisfies, toFormula, Logic.FirstOrder.Formula.satisfies] at hLiteral

end Literal

/-- DAG 字句；空数组表示空字句。 -/
structure Clause (σ : Signature) where
  literals : Array (Literal σ) := #[]

namespace Clause

/-- 空字句。 -/
def empty {σ : Signature} : Clause σ :=
  { literals := #[] }

/-- 单文字字句。 -/
def singleton {σ : Signature} (literal : Literal σ) : Clause σ :=
  { literals := #[literal] }

/-- 将有限替换作用到字句。 -/
def applySubstitution {σ : Signature} [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) (clause : Clause σ) : Clause σ :=
  { literals := clause.literals.map (Literal.applySubstitution subst) }

/-- 将字句中的 free variable 编号整体平移。 -/
def renameFreeVars {σ : Signature} (offset : Nat) (clause : Clause σ) : Clause σ :=
  { literals := clause.literals.map (Literal.renameFreeVars offset) }

/-- 从一个公式构造正单文字字句。 -/
def ofFormula {σ : Signature} (φ : Formula σ) : Clause σ :=
  singleton (Literal.pos φ)

/-- 从一个公式构造负单文字字句。 -/
def ofNegatedFormula {σ : Signature} (φ : Formula σ) : Clause σ :=
  singleton (Literal.neg φ)

/-- 按索引抽取字句中的文字。越界索引会被丢弃，payload checker 另行拒绝。 -/
def atIndices {σ : Signature} (clause : Clause σ) (indices : Array Nat) : Clause σ :=
  { literals := indices.filterMap fun index => clause.literals[index]? }

/-- 字句是否为空。 -/
def isEmpty {σ : Signature} (clause : Clause σ) : Bool :=
  clause.literals.size == 0

/-- 字句是否至少含一个文字。 -/
def nonempty {σ : Signature} (clause : Clause σ) : Bool :=
  !clause.isEmpty

/-- 文字列表的自由变量支持。 -/
def freeSupportList {σ : Signature} : List (Literal σ) →
    Logic.FirstOrder.FreeVariable.Support σ
  | [] => []
  | literal :: rest => literal.freeSupport ++ freeSupportList rest

/-- 字句的自由变量支持。 -/
def freeSupport {σ : Signature} (clause : Clause σ) :
    Logic.FirstOrder.FreeVariable.Support σ :=
  freeSupportList clause.literals.toList

private def toFormulaList {σ : Signature} : List (Literal σ) → Formula σ
  | [] => .falsum
  | literal :: rest => .disj literal.toFormula (toFormulaList rest)

/-- 字句对应的析取公式；空字句解释为 `⊥`。 -/
def toFormula {σ : Signature} (clause : Clause σ) : Formula σ :=
  toFormulaList clause.literals.toList

/-- 字句公式视图与字句本身具有相同的自由变量支持。 -/
theorem freeSupport_toFormula {σ : Signature} (clause : Clause σ) :
    Logic.FirstOrder.Formula.freeSupport clause.toFormula = clause.freeSupport := by
  cases clause with
  | mk literals =>
      simp only [toFormula, freeSupport]
      induction literals.toList with
      | nil =>
          rfl
      | cons literal rest ih =>
          simp only [toFormulaList, Logic.FirstOrder.Formula.freeSupport, freeSupportList]
          rw [Literal.freeSupport_toFormula, ih]

private theorem literal_freeSupport_subset_of_mem_list {σ : Signature}
    {literal : Literal σ} :
    ∀ {literals : List (Literal σ)}, literal ∈ literals →
      ∀ fv, fv ∈ literal.freeSupport → fv ∈ freeSupportList literals
  | [], hMem, _fv, _hSupport => by
      cases hMem
  | head :: tail, hMem, fv, hSupport => by
      rcases List.mem_cons.mp hMem with hEq | hTail
      · cases hEq
        simp [freeSupportList, hSupport]
      · simp [freeSupportList,
          literal_freeSupport_subset_of_mem_list hTail fv hSupport]

/-- 字句成员文字的支持包含在整个字句支持中。 -/
theorem literal_freeSupport_subset_of_mem {σ : Signature}
    {literal : Literal σ} {clause : Clause σ}
    (hMem : literal ∈ clause.literals.toList) :
    ∀ fv, fv ∈ literal.freeSupport → fv ∈ clause.freeSupport := by
  intro fv hSupport
  exact literal_freeSupport_subset_of_mem_list hMem fv hSupport

private def literalListEq {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] :
    List (Literal σ) → List (Literal σ) → Bool
  | [], [] => true
  | literal :: rest, literal' :: rest' => literal.eq literal' && literalListEq rest rest'
  | _, _ => false

private theorem literalListEq_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (left : List (Literal σ)) :
    ∀ right : List (Literal σ), literalListEq left right = true → left = right := by
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | cons _ _ => simp [literalListEq] at h
  | cons literal rest ih =>
      intro right h
      cases right <;> simp [literalListEq] at h
      case cons literal' rest' =>
        rcases h with ⟨hLiteral, hRest⟩
        have hLiteralEq := Literal.eq_sound literal literal' hLiteral
        have hRestEq := ih _ hRest
        cases hLiteralEq
        cases hRestEq
        rfl

/-- 字句结构比较。 -/
def eq {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (left right : Clause σ) : Bool :=
  literalListEq left.literals.toList right.literals.toList

/-- 字句结构比较为真时，两侧字句实际相等。 -/
theorem eq_sound {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (left right : Clause σ) :
    left.eq right = true → left = right := by
  cases left
  case mk leftLiterals =>
  cases right
  case mk rightLiterals =>
  intro h
  simp [eq] at h
  have hList := literalListEq_sound _ _ h
  cases leftLiterals
  cases rightLiterals
  simp at hList
  simp [hList]

/-- 字句列表中过滤掉匹配给定极性和原子的文字。 -/
def filterOutList {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (polarity : Bool) (atom : Formula σ) :
    List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if literal.matchesAtom polarity atom then
        filterOutList polarity atom rest
      else
        literal :: filterOutList polarity atom rest

/-- 从字句中过滤掉匹配给定极性和原子的文字。 -/
def filterOut {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (polarity : Bool) (atom : Formula σ)
    (clause : Clause σ) : Clause σ :=
  { literals := (filterOutList polarity atom clause.literals.toList).toArray }

/-- 列表中存在结构相等的文字。 -/
def containsLiteralList {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (needle : Literal σ) : List (Literal σ) → Bool
  | [] => false
  | literal :: rest => needle.eq literal || containsLiteralList needle rest

/-- 字句中是否存在结构相等的文字。 -/
def containsLiteral {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (clause : Clause σ) (needle : Literal σ) : Bool :=
  containsLiteralList needle clause.literals.toList

/-- 一个字句的所有文字是否都被另一个字句覆盖。 -/
def allLiteralsCovered {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (source target : Clause σ) : Bool :=
  source.literals.toList.all fun literal => target.containsLiteral literal

/-- 字句是否含有匹配给定极性和原子的文字。 -/
def containsMatching {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (clause : Clause σ) (polarity : Bool) (atom : Formula σ) : Bool :=
  clause.literals.toList.any fun literal => literal.matchesAtom polarity atom

/-- resolution 结构结果：删去互补 pivot 后连接两个父字句。 -/
def resolutionResult {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (leftPolarity : Bool) (pivot : Formula σ) (left right : Clause σ) : Clause σ :=
  {
    literals :=
      (filterOutList leftPolarity pivot left.literals.toList ++
        filterOutList (!leftPolarity) pivot right.literals.toList).toArray
  }

/-- equality-resolution 结构结果：删去结构自等的负等词文字。 -/
def equalityResolutionResult {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left right : Term σ) (parent : Clause σ) : Clause σ :=
  parent.filterOut false (.equal left right)

/-- 未被过滤的列表成员仍在过滤后列表中。 -/
theorem mem_filterOutList_of_mem_of_not_matches {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {polarity : Bool} {atom : Formula σ} {literal : Literal σ} :
    ∀ {literals : List (Literal σ)}, literal ∈ literals →
      literal.matchesAtom polarity atom = false →
        literal ∈ filterOutList polarity atom literals
  | [], hMem, _ => by cases hMem
  | head :: rest, hMem, hNoMatch => by
      by_cases hHead : head.matchesAtom polarity atom = true
      · rw [filterOutList]
        simp [hHead]
        rcases List.mem_cons.mp hMem with hEq | hTail
        · subst hEq
          simp [hHead] at hNoMatch
        · exact mem_filterOutList_of_mem_of_not_matches hTail hNoMatch
      · have hHeadFalse : head.matchesAtom polarity atom = false := by
          cases hValue : head.matchesAtom polarity atom <;> simp [hValue] at hHead ⊢
        rw [filterOutList]
        simp [hHeadFalse]
        rcases List.mem_cons.mp hMem with hEq | hTail
        · exact Or.inl hEq
        · exact Or.inr (mem_filterOutList_of_mem_of_not_matches hTail hNoMatch)

/-- 左父字句中未被删去的文字会出现在 resolution 结果中。 -/
theorem mem_resolutionResult_left {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Formula σ}
    {literal : Literal σ}
    (hMem : literal ∈ left.literals.toList)
    (hNoMatch : literal.matchesAtom leftPolarity pivot = false) :
    literal ∈ (resolutionResult leftPolarity pivot left right).literals.toList := by
  simp [resolutionResult]
  exact Or.inl (mem_filterOutList_of_mem_of_not_matches hMem hNoMatch)

/-- 右父字句中未被删去的文字会出现在 resolution 结果中。 -/
theorem mem_resolutionResult_right {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Formula σ}
    {literal : Literal σ}
    (hMem : literal ∈ right.literals.toList)
    (hNoMatch : literal.matchesAtom (!leftPolarity) pivot = false) :
    literal ∈ (resolutionResult leftPolarity pivot left right).literals.toList := by
  simp [resolutionResult]
  exact Or.inr (mem_filterOutList_of_mem_of_not_matches hMem hNoMatch)

/-- equality-resolution 中未被删去的文字会出现在结果中。 -/
theorem mem_equalityResolutionResult {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {left right : Term σ} {parent : Clause σ} {literal : Literal σ}
    (hMem : literal ∈ parent.literals.toList)
    (hNoMatch : literal.matchesAtom false (.equal left right) = false) :
    literal ∈ (equalityResolutionResult left right parent).literals.toList := by
  simpa [equalityResolutionResult, filterOut] using
    mem_filterOutList_of_mem_of_not_matches hMem hNoMatch

/-- `containsLiteralList` 通过时，可取出结构相等的成员。 -/
theorem containsLiteralList_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {needle : Literal σ} :
    ∀ {literals : List (Literal σ)}, containsLiteralList needle literals = true →
      ∃ literal, literal ∈ literals ∧ literal = needle
  | [], h => by simp [containsLiteralList] at h
  | head :: rest, h => by
      simp [containsLiteralList] at h
      rcases h with hHead | hRest
      · exact ⟨head, List.mem_cons_self,
          (Literal.eq_sound needle head hHead).symm⟩
      · rcases containsLiteralList_sound hRest with ⟨literal, hMem, hEq⟩
        exact ⟨literal, List.mem_cons_of_mem head hMem, hEq⟩

/-- 覆盖检查通过时，source 中任一文字都能在 target 中找到结构相等文字。 -/
theorem allLiteralsCovered_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {source target : Clause σ} (hCovered : allLiteralsCovered source target = true) :
    ∀ {literal : Literal σ}, literal ∈ source.literals.toList →
      ∃ literal', literal' ∈ target.literals.toList ∧ literal' = literal := by
  intro literal hMem
  unfold allLiteralsCovered at hCovered
  have hAll := List.all_eq_true.mp hCovered
  have hContains : target.containsLiteral literal = true :=
    hAll literal hMem
  exact containsLiteralList_sound hContains

end Clause

/-! ## Refutation semantics -/

namespace Clause

/-- 字句在某个环境下的反证语义。 -/
def Satisfies {σ : Signature} [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    (env : SetLevel.EnvAt.{x} M) (clause : Clause σ) : Prop :=
  Logic.FirstOrder.Formula.satisfies env clause.toFormula

private theorem satisfies_toFormulaList_iff_exists_literal {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} :
    ∀ literals : List (Literal σ),
      Logic.FirstOrder.Formula.satisfies env (toFormulaList literals) ↔
        ∃ literal, literal ∈ literals ∧ Literal.Satisfies env literal
  | [] => by
      simp [toFormulaList, Logic.FirstOrder.Formula.satisfies]
  | literal :: rest => by
      simp [toFormulaList, Logic.FirstOrder.Formula.satisfies, Literal.Satisfies,
        satisfies_toFormulaList_iff_exists_literal (env := env) rest]

/-- 字句满足性等价于存在一个满足的文字。 -/
theorem satisfies_iff_exists_literal {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {clause : Clause σ} :
    Satisfies env clause ↔
      ∃ literal, literal ∈ clause.literals.toList ∧ Literal.Satisfies env literal := by
  cases clause
  simp [Satisfies, toFormula, satisfies_toFormulaList_iff_exists_literal]

/-- 字句满足性只依赖其自由变量支持和完整 bound stack。 -/
theorem satisfies_iff_of_agreesOn {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {left right : SetLevel.EnvAt.{x} M}
    (clause : Clause σ)
    (hEnv : Logic.FirstOrder.Env.AgreesOn clause.freeSupport left right) :
    Satisfies left clause ↔ Satisfies right clause := by
  constructor
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    have hLiteralEnv :
        Logic.FirstOrder.Env.AgreesOn literal.freeSupport left right :=
      hEnv.mono (literal_freeSupport_subset_of_mem hMem)
    exact satisfies_iff_exists_literal.mpr
      ⟨literal, hMem,
        (Literal.satisfies_iff_of_agreesOn literal hLiteralEnv).mp hLiteral⟩
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    have hLiteralEnv :
        Logic.FirstOrder.Env.AgreesOn literal.freeSupport left right :=
      hEnv.mono (literal_freeSupport_subset_of_mem hMem)
    exact satisfies_iff_exists_literal.mpr
      ⟨literal, hMem,
        (Literal.satisfies_iff_of_agreesOn literal hLiteralEnv).mpr hLiteral⟩

/-- 字句替换的语义：语法替换等价于更新自由变量环境。 -/
theorem satisfies_applySubstitution_iff_of_envMatches {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {subst : TermSubstitution σ} {env targetEnv : SetLevel.EnvAt.{x} M}
    (hClosed : TermSubstitution.BoundClosed subst)
    (hEnv : TermSubstitution.EnvMatches subst env targetEnv)
    (clause : Clause σ) :
    Satisfies env (applySubstitution subst clause) ↔
      Satisfies targetEnv clause := by
  constructor
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    have hMemList :
        literal ∈ clause.literals.toList.map (Literal.applySubstitution subst) := by
      simpa [applySubstitution, Array.toList_map] using hMem
    rcases List.mem_map.mp hMemList with ⟨sourceLiteral, hSourceMem, hEq⟩
    cases hEq
    exact satisfies_iff_exists_literal.mpr
      ⟨sourceLiteral, hSourceMem,
        (Literal.satisfies_applySubstitution_iff_of_envMatches
          hClosed hEnv sourceLiteral).mp hLiteral⟩
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    exact satisfies_iff_exists_literal.mpr
      ⟨Literal.applySubstitution subst literal,
        by
          have hMappedList :
              Literal.applySubstitution subst literal ∈
                clause.literals.toList.map (Literal.applySubstitution subst) :=
            List.mem_map.mpr ⟨literal, hMem, rfl⟩
          simpa [applySubstitution, Array.toList_map] using hMappedList,
        (Literal.satisfies_applySubstitution_iff_of_envMatches
          hClosed hEnv literal).mpr hLiteral⟩

/-- 字句中的自由变量平移等价于投影自由变量环境。 -/
theorem satisfies_renameFreeVars_iff_of_envMatches {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {offset : Nat} {sourceEnv targetEnv : SetLevel.EnvAt.{x} M}
    (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv)
    (clause : Clause σ) :
    Satisfies sourceEnv (renameFreeVars offset clause) ↔
      Satisfies targetEnv clause := by
  constructor
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    have hMemList :
        literal ∈ clause.literals.toList.map (Literal.renameFreeVars offset) := by
      simpa [renameFreeVars, Array.toList_map] using hMem
    rcases List.mem_map.mp hMemList with ⟨sourceLiteral, hSourceMem, hEq⟩
    cases hEq
    exact satisfies_iff_exists_literal.mpr
      ⟨sourceLiteral, hSourceMem,
        (Literal.satisfies_renameFreeVars_iff_of_envMatches
          hEnv sourceLiteral).mp hLiteral⟩
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    exact satisfies_iff_exists_literal.mpr
      ⟨Literal.renameFreeVars offset literal,
        by
          have hMappedList :
              Literal.renameFreeVars offset literal ∈
                clause.literals.toList.map (Literal.renameFreeVars offset) :=
            List.mem_map.mpr ⟨literal, hMem, rfl⟩
          simpa [renameFreeVars, Array.toList_map] using hMappedList,
        (Literal.satisfies_renameFreeVars_iff_of_envMatches
          hEnv literal).mpr hLiteral⟩

/-- `isEmpty` 检查通过时，字句底层文字列表为空。 -/
theorem literals_toList_eq_nil_of_isEmpty {σ : Signature} {clause : Clause σ}
    (hEmpty : clause.isEmpty = true) :
    clause.literals.toList = [] := by
  cases clause with
  | mk literals =>
      have hSize : literals.size = 0 := by
        have hBool : (literals.size == 0) = true := by
          simpa [isEmpty] using hEmpty
        cases h : literals.size with
        | zero => rfl
        | succ n =>
            have hFalse : (literals.size == 0) = false := by
              simp [h]
            rw [hFalse] at hBool
            cases hBool
      have hArray : literals = #[] :=
        Array.eq_empty_of_size_eq_zero hSize
      simp [hArray]

/-- 空字句在任意环境下都不可能满足。 -/
theorem not_satisfies_of_isEmpty {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {clause : Clause σ}
    (hEmpty : clause.isEmpty = true) (hSat : Satisfies env clause) : False := by
  have hList := literals_toList_eq_nil_of_isEmpty hEmpty
  rcases satisfies_iff_exists_literal.mp hSat with ⟨literal, hMem, _hLiteral⟩
  rw [hList] at hMem
  cases hMem

/-- 字句中的真文字给出字句满足性。 -/
theorem satisfies_of_literal_mem {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {clause : Clause σ}
    {literal : Literal σ} (hMem : literal ∈ clause.literals.toList)
    (hLiteral : Literal.Satisfies env literal) :
    Satisfies env clause :=
  satisfies_iff_exists_literal.mpr ⟨literal, hMem, hLiteral⟩

/-- resolution 结构结果的语义 soundness。 -/
theorem satisfies_resolutionResult {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Formula σ}
    (hLeft : Satisfies env left) (hRight : Satisfies env right) :
    Satisfies env (resolutionResult leftPolarity pivot left right) := by
  rcases satisfies_iff_exists_literal.mp hLeft with
    ⟨leftLiteral, hLeftMem, hLeftLiteral⟩
  cases hLeftMatch : leftLiteral.matchesAtom leftPolarity pivot with
  | false =>
      exact satisfies_of_literal_mem
        (mem_resolutionResult_left hLeftMem hLeftMatch) hLeftLiteral
  | true =>
      rcases satisfies_iff_exists_literal.mp hRight with
        ⟨rightLiteral, hRightMem, hRightLiteral⟩
      cases hRightMatch : rightLiteral.matchesAtom (!leftPolarity) pivot with
      | false =>
          exact satisfies_of_literal_mem
            (mem_resolutionResult_right hRightMem hRightMatch) hRightLiteral
      | true =>
          exact False.elim
            (Literal.not_satisfies_matchesAtom_complement
              hLeftMatch hRightMatch hLeftLiteral hRightLiteral)

/-- 父字句所有文字被结论覆盖时，父字句满足性可传递到结论。 -/
theorem satisfies_of_allLiteralsCovered {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {source target : Clause σ}
    (hCovered : source.allLiteralsCovered target = true)
    (hSource : Satisfies env source) :
    Satisfies env target := by
  rcases satisfies_iff_exists_literal.mp hSource with
    ⟨literal, hMem, hLiteral⟩
  rcases allLiteralsCovered_sound hCovered hMem with
    ⟨literal', hTargetMem, hEq⟩
  cases hEq
  exact satisfies_of_literal_mem hTargetMem hLiteral

/-- equality-resolution 结构结果的语义 soundness。 -/
theorem satisfies_equalityResolutionResult {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {left right : Term σ} {parent : Clause σ}
    (hTerm : StructuralEq.term left right = true)
    (hParent : Satisfies env parent) :
    Satisfies env (equalityResolutionResult left right parent) := by
  rcases satisfies_iff_exists_literal.mp hParent with
    ⟨literal, hMem, hLiteral⟩
  cases hMatch : literal.matchesAtom false (.equal left right) with
  | false =>
      exact satisfies_of_literal_mem
        (mem_equalityResolutionResult hMem hMatch) hLiteral
  | true =>
      exact False.elim
        (Literal.not_satisfies_reflexive_negative_equality hTerm hMatch hLiteral)

/-- 正单文字字句的语义回放。 -/
theorem satisfies_ofFormula {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {φ : Formula σ}
    (hφ : Logic.FirstOrder.Formula.satisfies env φ) :
    Satisfies env (ofFormula φ) := by
  simp [Satisfies, toFormula, toFormulaList, ofFormula, singleton, Literal.toFormula,
    Literal.pos, Logic.FirstOrder.Formula.satisfies, hφ]

/-- 负单文字字句的语义回放。 -/
theorem satisfies_ofNegatedFormula {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {φ : Formula σ}
    (hφ : ¬ Logic.FirstOrder.Formula.satisfies env φ) :
    Satisfies env (ofNegatedFormula φ) := by
  simp [Satisfies, toFormula, toFormulaList, ofNegatedFormula, singleton, Literal.toFormula,
    Literal.neg, Logic.FirstOrder.Formula.satisfies, hφ]

end Clause

/-! ## 原生一阶初始字句问题 -/

/--
一阶 DAG 直接消费的初始字句问题。

搜索与证书层只依赖这个结构，不再把公式级前提、目标和局部推理规则混在同一个接口里。
-/
structure ClauseProblem (σ : Signature) where
  initialClauses : Array (Clause σ)

namespace ClauseProblem

/-- 一个环境满足问题，指它满足全部初始字句。 -/
def Satisfies {σ : Signature} [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    (problem : ClauseProblem σ) (env : SetLevel.EnvAt.{x} M) : Prop :=
  ∀ (index : Nat) (clause : Clause σ),
    problem.initialClauses[index]? = some clause → Clause.Satisfies env clause

/-- 两个环境共享同一 locally-nameless bound stack。 -/
def SameBoundStack {σ : Signature} {M : SetLevel.StructureAt.{x} σ}
    (targetEnv sourceEnv : SetLevel.EnvAt.{x} M) : Prop :=
  ∀ sort index, targetEnv.boundVal sort index = sourceEnv.boundVal sort index

/--
初始字句问题在一个 bound stack 上有效。

自由变量环境可以任意变化；bound stack 保持不变，正好对应 substitution 与
standardize-apart 语义环境的稳定边界。
-/
def Valid {σ : Signature} [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    (problem : ClauseProblem σ) (sourceEnv : SetLevel.EnvAt.{x} M) : Prop :=
  ∀ targetEnv, SameBoundStack targetEnv sourceEnv → problem.Satisfies targetEnv

/-- 在相同 bound stack 的环境之间移动问题有效性。 -/
theorem Valid.of_sameBoundStack {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {problem : ClauseProblem σ}
    {sourceEnv targetEnv : SetLevel.EnvAt.{x} M}
    (hValid : problem.Valid sourceEnv)
    (hBound : SameBoundStack targetEnv sourceEnv) :
    problem.Valid targetEnv := by
  intro nextEnv hNext
  exact hValid nextEnv fun sort index =>
    (hNext sort index).trans (hBound sort index)

/--
把公式级问题直接编译成最小原生字句问题。

前提按原顺序占据前缀索引，最后一个索引固定保存目标的否定。
-/
def ofDeepProblem {σ : Signature} (problem : DeepProblem σ) : ClauseProblem σ where
  initialClauses :=
    (problem.premises.map Clause.ofFormula).toArray.push
      (Clause.ofNegatedFormula problem.target)

/-- 公式级问题的目标否定在直接编译后的固定索引。 -/
def negatedTargetIndex {σ : Signature} (problem : DeepProblem σ) : Nat :=
  problem.premises.length

/-- 直接编译后的目标否定索引确实读取到对应字句。 -/
@[simp]
theorem getElem?_ofDeepProblem_negatedTarget {σ : Signature}
  (problem : DeepProblem σ) :
    (ofDeepProblem problem).initialClauses[negatedTargetIndex problem]? =
      some (Clause.ofNegatedFormula problem.target) := by
  simp [ofDeepProblem, negatedTargetIndex]

/-- 一个公式级反例环境满足直接编译出的全部初始字句。 -/
theorem satisfies_ofDeepProblem {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (problem : DeepProblem σ) (env : SetLevel.EnvAt.{x} M)
    (hModels : Logic.FirstOrder.Theory.Models problem.theory env)
    (hTargetFalse : ¬ Logic.FirstOrder.Formula.satisfies env problem.target) :
    (ofDeepProblem problem).Satisfies env := by
  intro index clause hLookup
  unfold ofDeepProblem at hLookup
  rw [Array.getElem?_push] at hLookup
  by_cases hTargetIndex :
      index = (problem.premises.map Clause.ofFormula).toArray.size
  · rw [if_pos hTargetIndex] at hLookup
    cases Option.some.inj hLookup
    exact Clause.satisfies_ofNegatedFormula hTargetFalse
  · rw [if_neg hTargetIndex] at hLookup
    rw [List.getElem?_toArray, List.getElem?_map] at hLookup
    cases hPremise : problem.premises[index]? with
    | none => simp [hPremise] at hLookup
    | some premise =>
        simp [hPremise] at hLookup
        cases hLookup
        apply Clause.satisfies_ofFormula
        apply hModels
        rcases List.getElem?_eq_some_iff.mp hPremise with ⟨hIndex, hGet⟩
        rw [← hGet]
        exact List.getElem_mem hIndex

/--
free-closed 公式级反例可提升为直接编译字句问题的全环境有效性。

闭合合同只留在公式问题到字句问题的边界；DAG 内部规则不再依赖它。
-/
theorem valid_ofDeepProblem_of_freeClosed {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    (problem : DeepProblem σ) (env : SetLevel.EnvAt.{x} M)
    (hClosed : DeepProblem.FreeClosed problem)
    (hModels : Logic.FirstOrder.Theory.Models problem.theory env)
    (hTargetFalse : ¬ Logic.FirstOrder.Formula.satisfies env problem.target) :
    (ofDeepProblem problem).Valid env := by
  intro targetEnv hBound
  apply satisfies_ofDeepProblem
  · exact DeepProblem.models_of_freeClosed_of_boundVal_eq hClosed
      hBound hModels
  · exact DeepProblem.targetFalse_of_freeClosed_of_boundVal_eq hClosed
      hBound hTargetFalse

end ClauseProblem

/-! ## Guarded clause view -/

/-- AVATAR/CDCL 侧的 guard literal。 -/
abbrev GuardLit := PropResolution.Lit

/-- guard 集。语义上作为合取使用，表示对象字句激活所需的 CDCL 假设。 -/
abbrev GuardSet := PropResolution.Clause

/-- guard 集规范化：稳定排序并去重。 -/
def canonicalGuards (guards : GuardSet) : GuardSet :=
  PropResolution.canonicalClause guards

/-- 合并两个 guard 集。 -/
def mergeGuards (left right : GuardSet) : GuardSet :=
  canonicalGuards (left ++ right)

/-- guard 集结构相等。 -/
def guardSetEq (left right : GuardSet) : Bool :=
  PropResolution.clauseEq (canonicalGuards left) (canonicalGuards right)

/-- theory conflict `Γ ⟹ ⊥` 在 CDCL 侧产生的 learned clause `¬Γ`。 -/
def learnedClauseOfGuards (guards : GuardSet) : PropResolution.Clause :=
  canonicalGuards (guards.map PropResolution.Lit.neg)

/-- 规范插入不会凭空产生新文字。 -/
private theorem mem_of_mem_propInsertCanonicalLitList {old lit : PropResolution.Lit} :
    ∀ {lits : List PropResolution.Lit},
      old ∈ PropResolution.insertCanonicalLitList lits lit → old = lit ∨ old ∈ lits
  | [], hMem => by
      simp [PropResolution.insertCanonicalLitList] at hMem
      exact Or.inl hMem
  | current :: rest, hMem => by
      by_cases hEq : current = lit
      · rw [PropResolution.insertCanonicalLitList] at hMem
        simp [hEq] at hMem
        rcases hMem with hOld | hRest
        · exact Or.inl hOld
        · exact Or.inr (List.mem_cons.mpr (Or.inr hRest))
      · by_cases hLe : PropResolution.Lit.le lit current
        · rw [PropResolution.insertCanonicalLitList] at hMem
          simp [hEq, hLe] at hMem ⊢
          exact hMem
        · rw [PropResolution.insertCanonicalLitList] at hMem
          simp [hEq, hLe] at hMem ⊢
          rcases hMem with hHead | hTail
          · exact Or.inr (Or.inl hHead)
          · rcases mem_of_mem_propInsertCanonicalLitList hTail with hOld | hRest
            · exact Or.inl hOld
            · exact Or.inr (Or.inr hRest)

/-- 规范化不会凭空产生新文字。 -/
private theorem mem_of_mem_propCanonicalClauseList {lit : PropResolution.Lit} :
    ∀ {lits : List PropResolution.Lit},
      lit ∈ PropResolution.canonicalClauseList lits → lit ∈ lits
  | [], hMem => by
      simp [PropResolution.canonicalClauseList] at hMem
  | current :: rest, hMem => by
      rw [PropResolution.canonicalClauseList] at hMem
      rcases mem_of_mem_propInsertCanonicalLitList hMem with hCurrent | hRestCanonical
      · exact List.mem_cons.mpr (Or.inl hCurrent)
      · exact List.mem_cons.mpr
          (Or.inr (mem_of_mem_propCanonicalClauseList (lits := rest) hRestCanonical))

/-- 规范化字句中的文字一定来自原字句。 -/
private theorem mem_of_mem_propCanonicalClause {clause : PropResolution.Clause}
    {lit : PropResolution.Lit}
    (hMem : lit ∈ (PropResolution.canonicalClause clause).toList) :
    lit ∈ clause.toList := by
  simpa [PropResolution.canonicalClause] using mem_of_mem_propCanonicalClauseList hMem

/-- 大型 DAG 中的 guarded clause。空 guard 退化为普通一阶字句。 -/
structure GuardedClause (σ : Signature) where
  guards : GuardSet := #[]
  clause : Clause σ

namespace GuardedClause

/-- 裸 clause 视为无 guard 的 guarded clause。 -/
def plain {σ : Signature} (clause : Clause σ) : GuardedClause σ :=
  { guards := #[], clause := clause }

/-- guard 集是否为空。 -/
def unguarded {σ : Signature} (gclause : GuardedClause σ) : Bool :=
  gclause.guards.isEmpty

/-- 是否是无 guard 的全局空字句。 -/
def globallyEmpty {σ : Signature} (gclause : GuardedClause σ) : Bool :=
  gclause.unguarded && gclause.clause.isEmpty

/-- 是否是 AVATAR theory conflict：在某组 guard 下推出对象空字句。 -/
def theoryConflict {σ : Signature} (gclause : GuardedClause σ) : Bool :=
  !gclause.unguarded && gclause.clause.isEmpty

/-- guarded clause 结构比较。 -/
def eq {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (left right : GuardedClause σ) : Bool :=
  guardSetEq left.guards right.guards && left.clause.eq right.clause

end GuardedClause

/-! ## Node payloads -/

/-! ## Parent snapshots and local evidence -/

/-- payload 中引用父节点时携带的父字句快照。 -/
structure ParentClause (σ : Signature) where
  id : NodeId
  clause : Clause σ

namespace ParentClause

/-- 父字句快照的 id 必须出现在当前节点父边里。 -/
def idIn (parents : Array NodeId) (parent : ParentClause σ) : Bool :=
  parents.contains parent.id

/-- `idIn` 为真时，父 id 出现在父边列表中。 -/
theorem mem_toList_of_idIn {σ : Signature} {parents : Array NodeId}
    {parent : ParentClause σ} (hIn : parent.idIn parents = true) :
    parent.id ∈ parents.toList := by
  have hArray : parent.id ∈ parents := by
    simpa [idIn] using hIn
  exact Array.mem_def.mp hArray

/-- 父字句快照是否和给定字句结构一致。 -/
def clauseEq {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parent : ParentClause σ) (clause : Clause σ) : Bool :=
  parent.clause.eq clause

end ParentClause

/-- 单个父字句的 standardize-apart 证据。 -/
structure StandardizeApartSideEvidence (σ : Signature) where
  parent : ParentClause σ
  offset : Nat := 0
  renamed : Clause σ

namespace StandardizeApartSideEvidence

/-- 复算父字句 free-variable 平移后的快照。 -/
def expected {σ : Signature} (evidence : StandardizeApartSideEvidence σ) :
    Clause σ :=
  Clause.renameFreeVars evidence.offset evidence.parent.clause

/-- 单侧 standardize-apart 证据检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (evidence : StandardizeApartSideEvidence σ) :
    Bool :=
  evidence.renamed.eq evidence.expected

/-- 单侧 standardize-apart 检查通过时，改名快照等于复算结果。 -/
theorem check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {evidence : StandardizeApartSideEvidence σ}
    (hCheck : evidence.check = true) :
    evidence.renamed = evidence.expected :=
  Clause.eq_sound evidence.renamed evidence.expected hCheck

end StandardizeApartSideEvidence

/--
二元规则的 standardize-apart 证据。

`left/right` 对应 resolution 的左右父字句；在 rewrite/superposition 中对应
`equality/target`。证据显式保存“原始父快照 -> 改名后父快照”这一步。
-/
structure StandardizeApartEvidence (σ : Signature) where
  left : StandardizeApartSideEvidence σ
  right : StandardizeApartSideEvidence σ

namespace StandardizeApartEvidence

/-- 二元 standardize-apart 证据检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (evidence : StandardizeApartEvidence σ) :
    Bool :=
  evidence.left.check && evidence.right.check

/-- 二元 standardize-apart 检查通过时，两侧改名快照都等于复算结果。 -/
theorem check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {evidence : StandardizeApartEvidence σ}
    (hCheck : evidence.check = true) :
    evidence.left.renamed = evidence.left.expected ∧
      evidence.right.renamed = evidence.right.expected := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
  exact ⟨StandardizeApartSideEvidence.check_sound hLeft,
    StandardizeApartSideEvidence.check_sound hRight⟩

/-- 证据中记录的原始左父字句。 -/
def leftParent {σ : Signature} (evidence : StandardizeApartEvidence σ) :
    ParentClause σ :=
  evidence.left.parent

/-- 证据中记录的原始右父字句。 -/
def rightParent {σ : Signature} (evidence : StandardizeApartEvidence σ) :
    ParentClause σ :=
  evidence.right.parent

end StandardizeApartEvidence

/-- 本地规则族。所有通过 checker 的本地规则都必须落到一等 evidence。 -/
inductive LocalRuleFamily where
  | parentCdcl
  | equality
  | congruence
  | quantifier
  | theory
  | composite
  deriving Repr, Inhabited, DecidableEq

namespace LocalRuleFamily

/-- 本地规则族标签。 -/
def label : LocalRuleFamily → String
  | parentCdcl => "parent-CDCL"
  | equality => "equality"
  | congruence => "congruence"
  | quantifier => "quantifier"
  | theory => "theory"
  | composite => "composite"

/-- 本地规则族对应的公共规则标签。 -/
def ruleTags : LocalRuleFamily → Array Certificate.RuleTag
  | parentCdcl => #[.localRuleWitness, .parentCdclSkeleton, .firstOrderResolution]
  | equality => #[.localRuleWitness, .termEquality, .demodulation, .firstOrderSuperposition]
  | congruence => #[.localRuleWitness, .formulaCongruence, .argumentCongruence]
  | quantifier => #[.localRuleWitness, .quantifierCongruence]
  | theory => #[.localRuleWitness, .theoryFact]
  | composite => #[.localRuleWitness, .composite]

end LocalRuleFamily

/--
本地规则的可检查 evidence。

无替换规则已经接入当前对象层 soundness-supported 片段；带 substitution 的规则先作为
checked evidence 进入 DAG，等待替换语义引理补齐后再提升到 soundness-supported。
-/
structure ResolutionEvidence (σ : Signature) where
  left : ParentClause σ
  right : ParentClause σ
  pivot : Formula σ
  leftPolarity : Bool := true

/-- factoring 证据：当前覆盖无替换的重复/重排/去重字句规范化。 -/
structure FactoringEvidence (σ : Signature) where
  parent : ParentClause σ

/-- equality-resolution 证据：删除结构自等的负等词文字。 -/
structure EqualityResolutionEvidence (σ : Signature) where
  parent : ParentClause σ
  left : Term σ
  right : Term σ

/-- 重写/叠加规则的目标极性与类别。 -/
inductive RewriteKind where
  | demodulation
  | positiveSuperposition
  | negativeSuperposition
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr

namespace RewriteKind

/-- 规则类别标签。 -/
def label : RewriteKind → String
  | demodulation => "demodulation"
  | positiveSuperposition => "positive superposition"
  | negativeSuperposition => "negative superposition"

end RewriteKind

/-- 项上下文：只有一个洞位，填入项后恢复完整项。 -/
inductive TermContext (σ : Signature) where
  | hole
  | app (f : σ.FuncSymbol) (before : List (Term σ)) (ctx : TermContext σ)
      (suffix : List (Term σ))

namespace TermContext

/-- 用一个项填充上下文。 -/
def fill {σ : Signature} : TermContext σ → Term σ → Term σ
  | hole, term => term
  | app f before ctx suffix, term =>
      .app f (before ++ [fill ctx term] ++ suffix)

/-- 填充前后在解释下给出相同的项值。 -/
theorem eval_fill_eq_of_eq {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {ctx : TermContext σ} {lhs rhs : Term σ}
    (hEq : Logic.FirstOrder.Term.eval env lhs = Logic.FirstOrder.Term.eval env rhs) :
    Logic.FirstOrder.Term.eval env (ctx.fill lhs) =
      Logic.FirstOrder.Term.eval env (ctx.fill rhs) := by
  induction ctx generalizing lhs rhs with
  | hole =>
      simpa [fill] using hEq
  | app f before ctx suffix ih =>
      have hArgs :
          (before ++ [fill ctx lhs] ++ suffix).map (Logic.FirstOrder.Term.eval env) =
            (before ++ [fill ctx rhs] ++ suffix).map
              (Logic.FirstOrder.Term.eval env) := by
        simp [List.map_append, ih hEq]
      simpa [fill, Logic.FirstOrder.Term.eval, List.map_append] using
        congrArg (M.funcInterp f) hArgs

end TermContext

/-- 原子公式上下文：只在关系参数或等词两侧留一个洞。 -/
inductive AtomContext (σ : Signature) where
  | rel (r : σ.RelSymbol) (before : List (Term σ)) (ctx : TermContext σ)
      (suffix : List (Term σ))
  | equalLeft (ctx : TermContext σ) (right : Term σ)
  | equalRight (left : Term σ) (ctx : TermContext σ)

namespace AtomContext

/-- 原子上下文是否对应等词两侧。 -/
def isEquality {σ : Signature} : AtomContext σ → Bool
  | rel _ _ _ _ => false
  | equalLeft _ _ => true
  | equalRight _ _ => true

/-- 用一个项填充原子上下文。 -/
def fill {σ : Signature} : AtomContext σ → Term σ → Formula σ
  | rel r before ctx suffix, term =>
      .rel r (before ++ [ctx.fill term] ++ suffix)
  | equalLeft ctx right, term =>
      .equal (ctx.fill term) right
  | equalRight left ctx, term =>
      .equal left (ctx.fill term)

/-- 填充前后原子公式的满足性等价。 -/
theorem satisfies_iff_of_eval_eq {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {ctx : AtomContext σ} {lhs rhs : Term σ}
    (hEq : Logic.FirstOrder.Term.eval env lhs = Logic.FirstOrder.Term.eval env rhs) :
    Logic.FirstOrder.Formula.satisfies env (ctx.fill lhs) ↔
      Logic.FirstOrder.Formula.satisfies env (ctx.fill rhs) := by
  cases ctx with
  | rel r before ctx suffix =>
      have hArgs :
          (before ++ [ctx.fill lhs] ++ suffix).map (Logic.FirstOrder.Term.eval env) =
            (before ++ [ctx.fill rhs] ++ suffix).map
              (Logic.FirstOrder.Term.eval env) := by
        simp [List.map_append, TermContext.eval_fill_eq_of_eq hEq]
      change M.relInterp r
          ((before ++ [ctx.fill lhs] ++ suffix).map (Logic.FirstOrder.Term.eval env)) ↔
        M.relInterp r
          ((before ++ [ctx.fill rhs] ++ suffix).map (Logic.FirstOrder.Term.eval env))
      rw [hArgs]
  | equalLeft ctx right =>
      have hTerm := TermContext.eval_fill_eq_of_eq (ctx := ctx) hEq
      simp [fill, Logic.FirstOrder.Formula.satisfies, hTerm]
  | equalRight left ctx =>
      have hTerm := TermContext.eval_fill_eq_of_eq (ctx := ctx) hEq
      simp [fill, Logic.FirstOrder.Formula.satisfies, hTerm]

end AtomContext

/-- 从上下文和项构造一个文字。 -/
def literalOfContext {σ : Signature} (polarity : Bool) (ctx : AtomContext σ) (term : Term σ) :
    Literal σ :=
  { polarity := polarity, atom := ctx.fill term }

/-- 用结构相等的目标文字替换字句中所有相同文字。 -/
def rewriteLiteralList {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (needle replacement : Literal σ) :
    List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if literal.eq needle then
        replacement :: rewriteLiteralList needle replacement rest
      else
        literal :: rewriteLiteralList needle replacement rest

/-- 用文字替换规则改写字句。 -/
def rewriteLiteralResult {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (needle replacement : Literal σ) (clause : Clause σ) : Clause σ :=
  { literals := (rewriteLiteralList needle replacement clause.literals.toList).toArray }

/-- 叠加/重写证据。`kind` 只影响 checker 的附加边界，不影响核心替换公式。 -/
structure RewriteEvidence (σ : Signature) where
  equality : ParentClause σ
  target : ParentClause σ
  context : AtomContext σ
  lhs : Term σ
  rhs : Term σ
  /-- true 表示父字句按 `rhs = lhs` 书写，但重写方向仍为 `lhs ↦ rhs`。 -/
  equalityReversed : Bool := false
  targetPolarity : Bool := true

namespace RewriteEvidence

/-- 父字句中实际保存的等词方向。 -/
def equalityAtom {σ : Signature} (evidence : RewriteEvidence σ) : Formula σ :=
  if evidence.equalityReversed then
    .equal evidence.rhs evidence.lhs
  else
    .equal evidence.lhs evidence.rhs

/-- 文字针尖。 -/
def needle {σ : Signature} (evidence : RewriteEvidence σ) : Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.lhs

/-- 文字替换结果。 -/
def replacement {σ : Signature} (evidence : RewriteEvidence σ) : Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.rhs

/-- 叠加/重写结果字句。 -/
def result {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (evidence : RewriteEvidence σ) : Clause σ :=
  { literals :=
      (Clause.filterOutList true evidence.equalityAtom
          evidence.equality.clause.literals.toList ++
        rewriteLiteralList evidence.needle evidence.replacement
          evidence.target.clause.literals.toList).toArray }

/-- 规则类别的附加约束。 -/
def kindCheck {σ : Signature} (kind : RewriteKind) (evidence : RewriteEvidence σ) : Bool :=
  match kind with
  | .demodulation => decide (evidence.equality.clause.literals.size = 1)
  | .positiveSuperposition => evidence.targetPolarity
  | .negativeSuperposition =>
      !evidence.targetPolarity && evidence.context.isEquality

/-- 重写证据的可计算检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (kind : RewriteKind) (parents : Array NodeId)
    (conclusion : Clause σ) (evidence : RewriteEvidence σ) : Bool :=
  evidence.equality.idIn parents &&
    evidence.target.idIn parents &&
      evidence.equality.clause.containsMatching true evidence.equalityAtom &&
        evidence.target.clause.containsLiteral evidence.needle &&
          kindCheck kind evidence &&
            conclusion.eq (result evidence)

/-- 证据检查通过时，两个父字句快照都在父边中。 -/
theorem check_parents {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {kind : RewriteKind} {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : RewriteEvidence σ}
    (hCheck : check kind parents conclusion evidence = true) :
    evidence.equality.idIn parents = true ∧ evidence.target.idIn parents = true := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, _hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hKind⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hNeedle⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hEqualityContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hEqIn, hTargetIn⟩
  exact ⟨hEqIn, hTargetIn⟩

/-- 证据检查通过时，结论等于按证据构造出的重写结果。 -/
theorem check_conclusion {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {kind : RewriteKind} {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : RewriteEvidence σ}
    (hCheck : check kind parents conclusion evidence = true) :
    conclusion = result evidence := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, hConclusion⟩
  exact Clause.eq_sound conclusion (result evidence) hConclusion

/-- 若等词父字句在模型下成立，则可得到等词项值相等。 -/
theorem eval_eq_of_parent {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {evidence : RewriteEvidence σ}
    {literal : Literal σ}
    (hMatch : literal.matchesAtom true evidence.equalityAtom = true)
    (hLiteral : Literal.Satisfies env literal) :
    Logic.FirstOrder.Term.eval env evidence.lhs =
      Logic.FirstOrder.Term.eval env evidence.rhs := by
  cases literal with
  | mk polarity atom =>
      rcases Literal.matchesAtom_sound hMatch with ⟨hPolarity, hAtom⟩
      cases polarity
      · simp at hPolarity
      · cases hReversed : evidence.equalityReversed with
        | false =>
            have hAtom' :
                atom = (.equal evidence.lhs evidence.rhs : Formula σ) := by
              simpa [equalityAtom, hReversed] using hAtom
            cases hAtom'
            simpa [Literal.Satisfies, Literal.toFormula,
              Logic.FirstOrder.Formula.satisfies] using hLiteral
        | true =>
            have hAtom' :
                atom = (.equal evidence.rhs evidence.lhs : Formula σ) := by
              simpa [equalityAtom, hReversed] using hAtom
            cases hAtom'
            have hReverse :
                Logic.FirstOrder.Term.eval env evidence.rhs =
                  Logic.FirstOrder.Term.eval env evidence.lhs := by
              simpa [Literal.Satisfies, Literal.toFormula,
                Logic.FirstOrder.Formula.satisfies] using hLiteral
            exact hReverse.symm

/-- 文字满足性在重写前后等价。 -/
theorem satisfies_iff_replacement {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {evidence : RewriteEvidence σ}
    (hEq : Logic.FirstOrder.Term.eval env evidence.lhs =
      Logic.FirstOrder.Term.eval env evidence.rhs) :
    Literal.Satisfies env evidence.needle ↔ Literal.Satisfies env evidence.replacement := by
  cases evidence with
  | mk equality target context lhs rhs equalityReversed targetPolarity =>
      have hAtom := AtomContext.satisfies_iff_of_eval_eq (ctx := context) hEq
      cases targetPolarity <;>
        simp [needle, replacement, literalOfContext, Literal.Satisfies,
          Literal.toFormula, Logic.FirstOrder.Formula.satisfies, hAtom]

/-- 文字列表中某个满足文字若被替换，仍能在结果字句中找到满足文字。 -/
private theorem satisfies_rewriteLiteralList {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {needle replacement : Literal σ}
    (hRewrite : Literal.Satisfies env needle → Literal.Satisfies env replacement) :
    ∀ {literals : List (Literal σ)},
      (∃ literal, literal ∈ literals ∧ Literal.Satisfies env literal) →
        ∃ literal, literal ∈ rewriteLiteralList needle replacement literals ∧
          Literal.Satisfies env literal
  | [], h => by
      rcases h with ⟨literal, hMem, _hSat⟩
      cases hMem
  | literal :: rest, h => by
      rcases h with ⟨witness, hMem, hSat⟩
      by_cases hMatch : literal.eq needle = true
      · have hLiteralEq : literal = needle := Literal.eq_sound literal needle hMatch
        rw [rewriteLiteralList, hMatch]
        rcases List.mem_cons.mp hMem with hHead | hTail
        · have hSatLiteral : Literal.Satisfies env literal := by
            simpa [hHead] using hSat
          exact ⟨replacement, by simp, hRewrite (by simpa [hLiteralEq] using hSatLiteral)⟩
        · rcases satisfies_rewriteLiteralList (literals := rest) hRewrite
              ⟨witness, hTail, hSat⟩ with
            ⟨witness', hMem', hSat'⟩
          exact ⟨witness', by simp [hMem'], hSat'⟩
      · have hNoMatch : literal.eq needle = false := by
          cases hValue : literal.eq needle <;> simp [hValue] at hMatch ⊢
        rw [rewriteLiteralList, hNoMatch]
        rcases List.mem_cons.mp hMem with hHead | hTail
        · have hSatLiteral : Literal.Satisfies env literal := by
            simpa [hHead] using hSat
          exact ⟨literal, by simp, hSatLiteral⟩
        · rcases satisfies_rewriteLiteralList (literals := rest) hRewrite
              ⟨witness, hTail, hSat⟩ with
            ⟨witness', hMem', hSat'⟩
          exact ⟨witness', by simp [hMem'], hSat'⟩

/-- 重写后的字句仍保持满足性。 -/
theorem satisfies_result {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {evidence : RewriteEvidence σ}
    (hEquality : Clause.Satisfies env evidence.equality.clause)
    (hTarget : Clause.Satisfies env evidence.target.clause) :
    Clause.Satisfies env (result evidence) := by
  rcases Clause.satisfies_iff_exists_literal.mp hEquality with
    ⟨equalityLiteral, hEqualityMem, hEqualitySat⟩
  cases hMatch : equalityLiteral.matchesAtom true evidence.equalityAtom with
  | false =>
      exact Clause.satisfies_of_literal_mem
        (by
          simp [result]
          exact Or.inl (Clause.mem_filterOutList_of_mem_of_not_matches
            (polarity := true) (atom := evidence.equalityAtom)
            (literal := equalityLiteral) hEqualityMem hMatch))
        hEqualitySat
  | true =>
      have hEq :
          Logic.FirstOrder.Term.eval env evidence.lhs =
            Logic.FirstOrder.Term.eval env evidence.rhs :=
        eval_eq_of_parent (evidence := evidence) hMatch hEqualitySat
      have hRewrite :
          Literal.Satisfies env evidence.needle →
            Literal.Satisfies env evidence.replacement :=
        (satisfies_iff_replacement (evidence := evidence) hEq).mp
      have hTarget' :=
        satisfies_rewriteLiteralList (needle := evidence.needle)
          (replacement := evidence.replacement) hRewrite
          (by
            rcases Clause.satisfies_iff_exists_literal.mp hTarget with
              ⟨targetLiteral, hTargetMem, hTargetSat⟩
            exact ⟨targetLiteral, hTargetMem, hTargetSat⟩)
      rcases hTarget' with ⟨literal, hMem, hSat⟩
      exact Clause.satisfies_of_literal_mem
        (by
          simp [result]
          exact Or.inr hMem)
        hSat

end RewriteEvidence

namespace ResolutionEvidence

/-- resolution 结构 checker。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (conclusion : Clause σ)
    (evidence : ResolutionEvidence σ) : Bool :=
  evidence.left.idIn parents &&
    evidence.right.idIn parents &&
      evidence.left.clause.containsMatching evidence.leftPolarity evidence.pivot &&
        evidence.right.clause.containsMatching (!evidence.leftPolarity) evidence.pivot &&
          conclusion.eq
            (Clause.resolutionResult evidence.leftPolarity evidence.pivot
              evidence.left.clause evidence.right.clause)

end ResolutionEvidence

namespace FactoringEvidence

/-- factoring 结构 checker：结论与父字句文字集合等价，且不增大字句。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (conclusion : Clause σ)
    (evidence : FactoringEvidence σ) : Bool :=
  evidence.parent.idIn parents &&
    evidence.parent.clause.allLiteralsCovered conclusion &&
      conclusion.allLiteralsCovered evidence.parent.clause &&
        decide (conclusion.literals.size <= evidence.parent.clause.literals.size)

end FactoringEvidence

namespace EqualityResolutionEvidence

/-- equality-resolution 结构 checker。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (conclusion : Clause σ)
    (evidence : EqualityResolutionEvidence σ) : Bool :=
  evidence.parent.idIn parents &&
    StructuralEq.term evidence.left evidence.right &&
      evidence.parent.clause.containsMatching false (.equal evidence.left evidence.right) &&
        conclusion.eq
          (Clause.equalityResolutionResult evidence.left evidence.right evidence.parent.clause)

end EqualityResolutionEvidence

/-- 带 substitution 的 resolution 证据。 -/
structure SubstitutedResolutionEvidence (σ : Signature) where
  left : ParentClause σ
  right : ParentClause σ
  substitution : TermSubstitution σ := []
  pivot : Formula σ
  leftPolarity : Bool := true

namespace SubstitutedResolutionEvidence

/-- substitution 后的左父字句。 -/
def leftClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : SubstitutedResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.left.clause

/-- substitution 后的右父字句。 -/
def rightClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : SubstitutedResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.right.clause

/-- 带 substitution 的 resolution 结构 checker。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (conclusion : Clause σ)
    (evidence : SubstitutedResolutionEvidence σ) : Bool :=
  TermSubstitution.checkAdmissible evidence.substitution &&
    (evidence.left.idIn parents &&
      evidence.right.idIn parents &&
        (evidence.leftClause.containsMatching evidence.leftPolarity evidence.pivot) &&
          (evidence.rightClause.containsMatching (!evidence.leftPolarity) evidence.pivot) &&
            conclusion.eq
              (Clause.resolutionResult evidence.leftPolarity evidence.pivot
                evidence.leftClause evidence.rightClause))

/-- resolution 检查通过时，substitution 可采纳。 -/
theorem check_admissible {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : SubstitutedResolutionEvidence σ}
    (hCheck : check parents conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hAdmissible, _hRest⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

/-- resolution 检查通过时，结论等于结构 resolvent。 -/
theorem check_conclusion {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : SubstitutedResolutionEvidence σ}
    (hCheck : check parents conclusion evidence = true) :
    conclusion =
      Clause.resolutionResult evidence.leftPolarity evidence.pivot
        evidence.leftClause evidence.rightClause := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_hAdmissible, hRest⟩
  rcases Bool.and_eq_true_iff.mp hRest with ⟨hPrefix, hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hRightContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨_hLeft, _hParentsRight⟩
  exact Clause.eq_sound conclusion
    (Clause.resolutionResult evidence.leftPolarity evidence.pivot
      evidence.leftClause evidence.rightClause) hConclusion

/-- resolution 检查通过时，两个父字句快照都在父边中。 -/
theorem check_parents {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : SubstitutedResolutionEvidence σ}
    (hCheck : check parents conclusion evidence = true) :
    evidence.left.idIn parents = true ∧ evidence.right.idIn parents = true := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_hAdmissible, hRest⟩
  rcases Bool.and_eq_true_iff.mp hRest with ⟨hPrefix, _hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hRightContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hParents, _hLeftContains⟩
  exact Bool.and_eq_true_iff.mp hParents

end SubstitutedResolutionEvidence

/-- 带 substitution 的 factoring 证据。 -/
structure SubstitutedFactoringEvidence (σ : Signature) where
  parent : ParentClause σ
  substitution : TermSubstitution σ := []

namespace SubstitutedFactoringEvidence

/-- substitution 后的父字句。 -/
def parentClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : SubstitutedFactoringEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.parent.clause

/-- 带 substitution 的 factoring 结构 checker。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (conclusion : Clause σ)
    (evidence : SubstitutedFactoringEvidence σ) : Bool :=
  TermSubstitution.checkAdmissible evidence.substitution &&
    (evidence.parent.idIn parents &&
      evidence.parentClause.allLiteralsCovered conclusion &&
        conclusion.allLiteralsCovered evidence.parentClause &&
          decide (conclusion.literals.size <= evidence.parentClause.literals.size))

/-- factoring 检查通过时，substitution 可采纳。 -/
theorem check_admissible {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : SubstitutedFactoringEvidence σ}
    (hCheck : check parents conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hAdmissible, _hRest⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

/-- factoring 检查通过时，父字句和结论覆盖关系成立。 -/
theorem check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : SubstitutedFactoringEvidence σ}
    (hCheck : check parents conclusion evidence = true) :
    evidence.parent.idIn parents = true ∧
      evidence.parentClause.allLiteralsCovered conclusion = true ∧
        conclusion.allLiteralsCovered evidence.parentClause = true ∧
          conclusion.literals.size <= evidence.parentClause.literals.size := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_hAdmissible, hRest⟩
  rcases Bool.and_eq_true_iff.mp hRest with ⟨hPrefix, hSize⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, hReverse⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hParent, hForward⟩
  exact ⟨hParent, hForward, hReverse, by simpa using hSize⟩

end SubstitutedFactoringEvidence

/-- 带 substitution 的 equality-resolution 证据。 -/
structure SubstitutedEqualityResolutionEvidence (σ : Signature) where
  parent : ParentClause σ
  substitution : TermSubstitution σ := []
  left : Term σ
  right : Term σ

namespace SubstitutedEqualityResolutionEvidence

/-- substitution 后的父字句。 -/
def parentClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : SubstitutedEqualityResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.parent.clause

/-- 带 substitution 的 equality-resolution 结构 checker。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (conclusion : Clause σ)
    (evidence : SubstitutedEqualityResolutionEvidence σ) : Bool :=
  TermSubstitution.checkAdmissible evidence.substitution &&
    (evidence.parent.idIn parents &&
      StructuralEq.term evidence.left evidence.right &&
        evidence.parentClause.containsMatching false (.equal evidence.left evidence.right) &&
          conclusion.eq
            (Clause.equalityResolutionResult evidence.left evidence.right
              evidence.parentClause))

/-- equality-resolution 检查通过时，substitution 可采纳。 -/
theorem check_admissible {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : SubstitutedEqualityResolutionEvidence σ}
    (hCheck : check parents conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hAdmissible, _hRest⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

/-- equality-resolution 检查通过时，父字句和结果匹配。 -/
theorem check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : SubstitutedEqualityResolutionEvidence σ}
    (hCheck : check parents conclusion evidence = true) :
    evidence.parent.idIn parents = true ∧
      StructuralEq.term evidence.left evidence.right = true ∧
        evidence.parentClause.containsMatching false (.equal evidence.left evidence.right) = true ∧
          conclusion =
            Clause.equalityResolutionResult evidence.left evidence.right evidence.parentClause := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_hAdmissible, hRest⟩
  rcases Bool.and_eq_true_iff.mp hRest with ⟨hPrefix, hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, hContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hParent, hTerm⟩
  exact ⟨hParent, hTerm, hContains,
    Clause.eq_sound conclusion
      (Clause.equalityResolutionResult evidence.left evidence.right evidence.parentClause)
      hConclusion⟩

end SubstitutedEqualityResolutionEvidence

/-- 带 substitution 的重写/叠加证据。 -/
structure SubstitutedRewriteEvidence (σ : Signature) where
  equality : ParentClause σ
  target : ParentClause σ
  substitution : TermSubstitution σ := []
  context : AtomContext σ
  lhs : Term σ
  rhs : Term σ
  equalityReversed : Bool := false
  targetPolarity : Bool := true

namespace SubstitutedRewriteEvidence

/-- substitution 后的等词父字句。 -/
def equalityClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : SubstitutedRewriteEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.equality.clause

/-- substitution 后的目标父字句。 -/
def targetClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : SubstitutedRewriteEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.target.clause

/-- substitution 后父字句中实际保存的等词方向。 -/
def equalityAtom {σ : Signature} (evidence : SubstitutedRewriteEvidence σ) :
    Formula σ :=
  if evidence.equalityReversed then
    .equal evidence.rhs evidence.lhs
  else
    .equal evidence.lhs evidence.rhs

/-- substitution 后的证据视为普通重写证据。 -/
def asRewriteEvidence {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : SubstitutedRewriteEvidence σ) : RewriteEvidence σ :=
  {
    equality := { id := evidence.equality.id, clause := evidence.equalityClause }
    target := { id := evidence.target.id, clause := evidence.targetClause }
    context := evidence.context
    lhs := evidence.lhs
    rhs := evidence.rhs
    equalityReversed := evidence.equalityReversed
    targetPolarity := evidence.targetPolarity
  }

/-- 文字针尖。 -/
def needle {σ : Signature} (evidence : SubstitutedRewriteEvidence σ) : Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.lhs

/-- 文字替换结果。 -/
def replacement {σ : Signature} (evidence : SubstitutedRewriteEvidence σ) : Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.rhs

/-- 带 substitution 的重写/叠加结果字句。 -/
def result {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (evidence : SubstitutedRewriteEvidence σ) : Clause σ :=
  { literals :=
      (Clause.filterOutList true evidence.equalityAtom
          evidence.equalityClause.literals.toList ++
        rewriteLiteralList evidence.needle evidence.replacement
          evidence.targetClause.literals.toList).toArray }

/-- 规则类别的附加约束。 -/
def kindCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    (kind : RewriteKind) (evidence : SubstitutedRewriteEvidence σ) : Bool :=
  match kind with
  | .demodulation => decide (evidence.equalityClause.literals.size = 1)
  | .positiveSuperposition => evidence.targetPolarity
  | .negativeSuperposition =>
      !evidence.targetPolarity && evidence.context.isEquality

/-- 带 substitution 的重写证据可计算检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (kind : RewriteKind) (parents : Array NodeId)
    (conclusion : Clause σ) (evidence : SubstitutedRewriteEvidence σ) : Bool :=
  TermSubstitution.checkAdmissible evidence.substitution &&
    (evidence.equality.idIn parents &&
      evidence.target.idIn parents &&
        evidence.equalityClause.containsMatching true evidence.equalityAtom &&
          evidence.targetClause.containsLiteral evidence.needle &&
            kindCheck kind evidence &&
              conclusion.eq (result evidence))

/-- 重写检查通过时，substitution 可采纳。 -/
theorem check_admissible {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {kind : RewriteKind} {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : SubstitutedRewriteEvidence σ}
    (hCheck : check kind parents conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hAdmissible, _hRest⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

/-- 重写检查通过时，父边和结果匹配。 -/
theorem check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {kind : RewriteKind} {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : SubstitutedRewriteEvidence σ}
    (hCheck : check kind parents conclusion evidence = true) :
    evidence.equality.idIn parents = true ∧
      evidence.target.idIn parents = true ∧
        evidence.equalityClause.containsMatching true evidence.equalityAtom = true ∧
          evidence.targetClause.containsLiteral evidence.needle = true ∧
            kindCheck kind evidence = true ∧
              conclusion = result evidence := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_hAdmissible, hRest⟩
  rcases Bool.and_eq_true_iff.mp hRest with ⟨hPrefix, hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, hKind⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, hNeedle⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, hContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hEqual, hTarget⟩
  exact ⟨hEqual, hTarget, hContains, hNeedle, hKind,
    Clause.eq_sound conclusion (result evidence) hConclusion⟩

/-- substitution 后的重写/叠加结果保持满足性。 -/
theorem satisfies_result {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {evidence : SubstitutedRewriteEvidence σ}
    (hEquality : Clause.Satisfies env evidence.equalityClause)
    (hTarget : Clause.Satisfies env evidence.targetClause) :
    Clause.Satisfies env (result evidence) := by
  let ordinary := evidence.asRewriteEvidence
  have hOrdinary :
      Clause.Satisfies env (RewriteEvidence.result ordinary) :=
    RewriteEvidence.satisfies_result
      (evidence := ordinary)
      (by simpa [ordinary, asRewriteEvidence] using hEquality)
      (by simpa [ordinary, asRewriteEvidence] using hTarget)
  simpa [ordinary, asRewriteEvidence, result, RewriteEvidence.result,
    RewriteEvidence.needle, RewriteEvidence.replacement, needle, replacement]
    using hOrdinary

end SubstitutedRewriteEvidence

/-- 带 standardize-apart 与 substitution 的 resolution 证据。 -/
structure StandardizedSubstitutedResolutionEvidence (σ : Signature) where
  standardizeApart : StandardizeApartEvidence σ
  substitution : TermSubstitution σ := []
  pivot : Formula σ
  leftPolarity : Bool := true

namespace StandardizedSubstitutedResolutionEvidence

/-- 原始左父字句快照。 -/
def left {σ : Signature} (evidence : StandardizedSubstitutedResolutionEvidence σ) :
    ParentClause σ :=
  evidence.standardizeApart.leftParent

/-- 原始右父字句快照。 -/
def right {σ : Signature} (evidence : StandardizedSubstitutedResolutionEvidence σ) :
    ParentClause σ :=
  evidence.standardizeApart.rightParent

/-- 改名后的左父字句。 -/
def leftRenamedClause {σ : Signature}
    (evidence : StandardizedSubstitutedResolutionEvidence σ) : Clause σ :=
  evidence.standardizeApart.left.renamed

/-- 改名后的右父字句。 -/
def rightRenamedClause {σ : Signature}
    (evidence : StandardizedSubstitutedResolutionEvidence σ) : Clause σ :=
  evidence.standardizeApart.right.renamed

/-- 改名并 substitution 后的左父字句。 -/
def leftClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : StandardizedSubstitutedResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.leftRenamedClause

/-- 改名并 substitution 后的右父字句。 -/
def rightClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : StandardizedSubstitutedResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.rightRenamedClause

/-- 带 standardize-apart 的 resolution 结构 checker。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (conclusion : Clause σ)
    (evidence : StandardizedSubstitutedResolutionEvidence σ) : Bool :=
  evidence.standardizeApart.check &&
    TermSubstitution.checkAdmissible evidence.substitution &&
      (evidence.left.idIn parents &&
        evidence.right.idIn parents &&
          evidence.leftClause.containsMatching evidence.leftPolarity evidence.pivot &&
            evidence.rightClause.containsMatching (!evidence.leftPolarity) evidence.pivot &&
              conclusion.eq
                (Clause.resolutionResult evidence.leftPolarity evidence.pivot
                  evidence.leftClause evidence.rightClause))

/-- standardized resolution 检查通过时，substitution 可采纳。 -/
theorem check_admissible {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : StandardizedSubstitutedResolutionEvidence σ}
    (hCheck : check parents conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, _hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨_hStandardize, hAdmissible⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

/-- standardized resolution 检查通过时，父边和 resolution 结果匹配。 -/
theorem check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : StandardizedSubstitutedResolutionEvidence σ}
    (hCheck : check parents conclusion evidence = true) :
    evidence.left.idIn parents = true ∧
      evidence.right.idIn parents = true ∧
        conclusion =
          Clause.resolutionResult evidence.leftPolarity evidence.pivot
            evidence.leftClause evidence.rightClause := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨_hStandardize, _hAdmissible⟩
  rcases Bool.and_eq_true_iff.mp hRest with ⟨hPrefix, hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hRightContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hLeftContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hLeft, hRight⟩
  exact ⟨hLeft, hRight,
    Clause.eq_sound conclusion
      (Clause.resolutionResult evidence.leftPolarity evidence.pivot
        evidence.leftClause evidence.rightClause) hConclusion⟩

end StandardizedSubstitutedResolutionEvidence

/-- 带 standardize-apart 与 substitution 的 rewrite/superposition 证据。 -/
structure StandardizedSubstitutedRewriteEvidence (σ : Signature) where
  standardizeApart : StandardizeApartEvidence σ
  substitution : TermSubstitution σ := []
  context : AtomContext σ
  lhs : Term σ
  rhs : Term σ
  equalityReversed : Bool := false
  targetPolarity : Bool := true

namespace StandardizedSubstitutedRewriteEvidence

/-- 原始等词父字句快照。 -/
def equality {σ : Signature} (evidence : StandardizedSubstitutedRewriteEvidence σ) :
    ParentClause σ :=
  evidence.standardizeApart.leftParent

/-- 原始目标父字句快照。 -/
def target {σ : Signature} (evidence : StandardizedSubstitutedRewriteEvidence σ) :
    ParentClause σ :=
  evidence.standardizeApart.rightParent

/-- 改名后的等词父字句。 -/
def equalityRenamedClause {σ : Signature}
    (evidence : StandardizedSubstitutedRewriteEvidence σ) : Clause σ :=
  evidence.standardizeApart.left.renamed

/-- 改名后的目标父字句。 -/
def targetRenamedClause {σ : Signature}
    (evidence : StandardizedSubstitutedRewriteEvidence σ) : Clause σ :=
  evidence.standardizeApart.right.renamed

/-- 改名并 substitution 后的等词父字句。 -/
def equalityClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : StandardizedSubstitutedRewriteEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.equalityRenamedClause

/-- 改名并 substitution 后的目标父字句。 -/
def targetClause {σ : Signature} [DecidableEq σ.SortSymbol]
    (evidence : StandardizedSubstitutedRewriteEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.targetRenamedClause

/-- standardize-apart 与 substitution 后父字句中的实际等词方向。 -/
def equalityAtom {σ : Signature}
    (evidence : StandardizedSubstitutedRewriteEvidence σ) : Formula σ :=
  if evidence.equalityReversed then
    .equal evidence.rhs evidence.lhs
  else
    .equal evidence.lhs evidence.rhs

/-- 文字针尖。 -/
def needle {σ : Signature} (evidence : StandardizedSubstitutedRewriteEvidence σ) :
    Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.lhs

/-- 文字替换结果。 -/
def replacement {σ : Signature} (evidence : StandardizedSubstitutedRewriteEvidence σ) :
    Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.rhs

/-- 带 standardize-apart 的重写/叠加结果字句。 -/
def result {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (evidence : StandardizedSubstitutedRewriteEvidence σ) :
    Clause σ :=
  { literals :=
      (Clause.filterOutList true evidence.equalityAtom
          evidence.equalityClause.literals.toList ++
        rewriteLiteralList evidence.needle evidence.replacement
          evidence.targetClause.literals.toList).toArray }

/-- 规则类别的附加约束。 -/
def kindCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    (kind : RewriteKind) (evidence : StandardizedSubstitutedRewriteEvidence σ) :
    Bool :=
  match kind with
  | .demodulation => decide (evidence.equalityClause.literals.size = 1)
  | .positiveSuperposition => evidence.targetPolarity
  | .negativeSuperposition =>
      !evidence.targetPolarity && evidence.context.isEquality

/-- 带 standardize-apart 的重写/叠加证据可计算检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (kind : RewriteKind) (parents : Array NodeId)
    (conclusion : Clause σ) (evidence : StandardizedSubstitutedRewriteEvidence σ) :
    Bool :=
  evidence.standardizeApart.check &&
    TermSubstitution.checkAdmissible evidence.substitution &&
      (evidence.equality.idIn parents &&
        evidence.target.idIn parents &&
          evidence.equalityClause.containsMatching true evidence.equalityAtom &&
            evidence.targetClause.containsLiteral evidence.needle &&
              kindCheck kind evidence &&
                conclusion.eq (result evidence))

/-- standardized rewrite 检查通过时，substitution 可采纳。 -/
theorem check_admissible {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {kind : RewriteKind} {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : StandardizedSubstitutedRewriteEvidence σ}
    (hCheck : check kind parents conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, _hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨_hStandardize, hAdmissible⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

/-- standardized rewrite 检查通过时，父边、规则类别和结果匹配。 -/
theorem check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {kind : RewriteKind} {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : StandardizedSubstitutedRewriteEvidence σ}
    (hCheck : check kind parents conclusion evidence = true) :
    evidence.equality.idIn parents = true ∧
      evidence.target.idIn parents = true ∧
        kindCheck kind evidence = true ∧
        conclusion = evidence.result := by
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨_hStandardize, _hAdmissible⟩
  rcases Bool.and_eq_true_iff.mp hRest with ⟨hPrefix, hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, hKind⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hNeedle⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hEquality, hTarget⟩
  exact ⟨hEquality, hTarget, hKind, Clause.eq_sound conclusion evidence.result hConclusion⟩

end StandardizedSubstitutedRewriteEvidence

inductive LocalRuleEvidence (σ : Signature) where
  | parentCopy (parent : ParentClause σ)
  | resolution (evidence : ResolutionEvidence σ)
  | factoring (evidence : FactoringEvidence σ)
  | equalityResolution (evidence : EqualityResolutionEvidence σ)
  | demodulation (evidence : RewriteEvidence σ)
  | positiveSuperposition (evidence : RewriteEvidence σ)
  | negativeSuperposition (evidence : RewriteEvidence σ)
  | substitutedResolution (evidence : SubstitutedResolutionEvidence σ)
  | substitutedFactoring (evidence : SubstitutedFactoringEvidence σ)
  | substitutedEqualityResolution (evidence : SubstitutedEqualityResolutionEvidence σ)
  | substitutedDemodulation (evidence : SubstitutedRewriteEvidence σ)
  | substitutedPositiveSuperposition (evidence : SubstitutedRewriteEvidence σ)
  | substitutedNegativeSuperposition (evidence : SubstitutedRewriteEvidence σ)
  | standardizedSubstitutedResolution
      (evidence : StandardizedSubstitutedResolutionEvidence σ)
  | standardizedSubstitutedDemodulation
      (evidence : StandardizedSubstitutedRewriteEvidence σ)
  | standardizedSubstitutedPositiveSuperposition
      (evidence : StandardizedSubstitutedRewriteEvidence σ)
  | standardizedSubstitutedNegativeSuperposition
      (evidence : StandardizedSubstitutedRewriteEvidence σ)

namespace LocalRuleEvidence

/-- evidence 对应的规则族。 -/
def family {σ : Signature} : LocalRuleEvidence σ → LocalRuleFamily
  | parentCopy _ => .parentCdcl
  | resolution _ => .parentCdcl
  | factoring _ => .parentCdcl
  | equalityResolution _ => .equality
  | demodulation _ => .equality
  | positiveSuperposition _ => .equality
  | negativeSuperposition _ => .equality
  | substitutedResolution _ => .parentCdcl
  | substitutedFactoring _ => .parentCdcl
  | substitutedEqualityResolution _ => .equality
  | substitutedDemodulation _ => .equality
  | substitutedPositiveSuperposition _ => .equality
  | substitutedNegativeSuperposition _ => .equality
  | standardizedSubstitutedResolution _ => .parentCdcl
  | standardizedSubstitutedDemodulation _ => .equality
  | standardizedSubstitutedPositiveSuperposition _ => .equality
  | standardizedSubstitutedNegativeSuperposition _ => .equality

/-- evidence 直接引用的父字句快照。 -/
def parentClauses {σ : Signature} : LocalRuleEvidence σ → Array (ParentClause σ)
  | parentCopy parent => #[parent]
  | resolution evidence => #[evidence.left, evidence.right]
  | factoring evidence => #[evidence.parent]
  | equalityResolution evidence => #[evidence.parent]
  | demodulation evidence => #[evidence.equality, evidence.target]
  | positiveSuperposition evidence => #[evidence.equality, evidence.target]
  | negativeSuperposition evidence => #[evidence.equality, evidence.target]
  | substitutedResolution evidence => #[evidence.left, evidence.right]
  | substitutedFactoring evidence => #[evidence.parent]
  | substitutedEqualityResolution evidence => #[evidence.parent]
  | substitutedDemodulation evidence => #[evidence.equality, evidence.target]
  | substitutedPositiveSuperposition evidence => #[evidence.equality, evidence.target]
  | substitutedNegativeSuperposition evidence => #[evidence.equality, evidence.target]
  | standardizedSubstitutedResolution evidence => #[evidence.left, evidence.right]
  | standardizedSubstitutedDemodulation evidence => #[evidence.equality, evidence.target]
  | standardizedSubstitutedPositiveSuperposition evidence =>
      #[evidence.equality, evidence.target]
  | standardizedSubstitutedNegativeSuperposition evidence =>
      #[evidence.equality, evidence.target]

/-- 当前已经完成对象层 soundness 的 local evidence 片段。 -/
def soundnessSupported {σ : Signature} : LocalRuleEvidence σ → Bool
  | _ => true

/-- 本地 evidence 的可计算检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (conclusion : Clause σ) :
    LocalRuleEvidence σ → Bool
  | parentCopy parent =>
      parent.idIn parents && parent.clauseEq conclusion
  | resolution evidence =>
      evidence.check parents conclusion
  | factoring evidence =>
      evidence.check parents conclusion
  | equalityResolution evidence =>
      evidence.check parents conclusion
  | demodulation evidence =>
      evidence.check .demodulation parents conclusion
  | positiveSuperposition evidence =>
      evidence.check .positiveSuperposition parents conclusion
  | negativeSuperposition evidence =>
      evidence.check .negativeSuperposition parents conclusion
  | substitutedResolution evidence =>
      evidence.check parents conclusion
  | substitutedFactoring evidence =>
      evidence.check parents conclusion
  | substitutedEqualityResolution evidence =>
      evidence.check parents conclusion
  | substitutedDemodulation evidence =>
      evidence.check .demodulation parents conclusion
  | substitutedPositiveSuperposition evidence =>
      evidence.check .positiveSuperposition parents conclusion
  | substitutedNegativeSuperposition evidence =>
      evidence.check .negativeSuperposition parents conclusion
  | standardizedSubstitutedResolution evidence =>
      evidence.check parents conclusion
  | standardizedSubstitutedDemodulation evidence =>
      evidence.check .demodulation parents conclusion
  | standardizedSubstitutedPositiveSuperposition evidence =>
      evidence.check .positiveSuperposition parents conclusion
  | standardizedSubstitutedNegativeSuperposition evidence =>
      evidence.check .negativeSuperposition parents conclusion

/-- parent-copy evidence 检查通过时，结论等于记录的父字句。 -/
theorem parentCopy_check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {parent : ParentClause σ}
    (hCheck : check parents conclusion (.parentCopy parent) = true) :
    parent.idIn parents = true ∧ conclusion = parent.clause := by
  simp only [check, Bool.and_eq_true] at hCheck
  rcases hCheck with ⟨hParent, hClause⟩
  have hClause' : parent.clause.eq conclusion = true := by
    simpa [ParentClause.clauseEq] using hClause
  exact ⟨hParent, (Clause.eq_sound parent.clause conclusion hClause').symm⟩

/-- resolution evidence 检查通过时，结论等于结构 resolvent。 -/
theorem resolution_check_conclusion {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : ResolutionEvidence σ}
    (hCheck : check parents conclusion (.resolution evidence) = true) :
    conclusion =
      Clause.resolutionResult evidence.leftPolarity evidence.pivot
        evidence.left.clause evidence.right.clause := by
  unfold check ResolutionEvidence.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, hConclusion⟩
  exact Clause.eq_sound conclusion
    (Clause.resolutionResult evidence.leftPolarity evidence.pivot
      evidence.left.clause evidence.right.clause) hConclusion

/-- resolution evidence 检查通过时，两个父字句快照都在父边中。 -/
theorem resolution_check_parents {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : ResolutionEvidence σ}
    (hCheck : check parents conclusion (.resolution evidence) = true) :
    evidence.left.idIn parents = true ∧ evidence.right.idIn parents = true := by
  unfold check ResolutionEvidence.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, _hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hRightContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hLeftContains⟩
  exact Bool.and_eq_true_iff.mp hPrefix

/-- factoring evidence 检查通过时，父字句的每个文字都被结论覆盖。 -/
theorem factoring_check_parentCovered {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : FactoringEvidence σ}
    (hCheck : check parents conclusion (.factoring evidence) = true) :
    evidence.parent.clause.allLiteralsCovered conclusion = true := by
  unfold check FactoringEvidence.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, _hSize⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hReverse⟩
  exact (Bool.and_eq_true_iff.mp hPrefix).2

/-- factoring evidence 检查通过时，父字句快照在父边中。 -/
theorem factoring_check_parent {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : FactoringEvidence σ}
    (hCheck : check parents conclusion (.factoring evidence) = true) :
    evidence.parent.idIn parents = true := by
  unfold check FactoringEvidence.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, _hSize⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hReverse⟩
  exact (Bool.and_eq_true_iff.mp hPrefix).1

/-- equality-resolution evidence 检查通过时，可取出结构自等事实和结论结果。 -/
theorem equalityResolution_check_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : EqualityResolutionEvidence σ}
    (hCheck : check parents conclusion (.equalityResolution evidence) = true) :
    StructuralEq.term evidence.left evidence.right = true ∧
      conclusion =
        Clause.equalityResolutionResult evidence.left evidence.right evidence.parent.clause := by
  unfold check EqualityResolutionEvidence.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hContains⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨_hParent, hTerm⟩
  exact ⟨hTerm, Clause.eq_sound conclusion
    (Clause.equalityResolutionResult evidence.left evidence.right evidence.parent.clause)
    hConclusion⟩

/-- equality-resolution evidence 检查通过时，父字句快照在父边中。 -/
theorem equalityResolution_check_parent {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : EqualityResolutionEvidence σ}
    (hCheck : check parents conclusion (.equalityResolution evidence) = true) :
    evidence.parent.idIn parents = true := by
  unfold check EqualityResolutionEvidence.check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPrefix, _hConclusion⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hPrefix, _hContains⟩
  exact (Bool.and_eq_true_iff.mp hPrefix).1

/-- demodulation evidence 检查通过时，结论等于重写结果。 -/
theorem demodulation_check_conclusion {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : RewriteEvidence σ}
    (hCheck : check parents conclusion (.demodulation evidence) = true) :
    conclusion = evidence.result :=
  RewriteEvidence.check_conclusion (kind := .demodulation) hCheck

/-- positive-superposition evidence 检查通过时，结论等于重写结果。 -/
theorem positiveSuperposition_check_conclusion {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : RewriteEvidence σ}
    (hCheck : check parents conclusion (.positiveSuperposition evidence) = true) :
    conclusion = evidence.result :=
  RewriteEvidence.check_conclusion (kind := .positiveSuperposition) hCheck

/-- negative-superposition evidence 检查通过时，结论等于重写结果。 -/
theorem negativeSuperposition_check_conclusion {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : RewriteEvidence σ}
    (hCheck : check parents conclusion (.negativeSuperposition evidence) = true) :
    conclusion = evidence.result :=
  RewriteEvidence.check_conclusion (kind := .negativeSuperposition) hCheck

/-- demodulation evidence 检查通过时，两个父字句快照都在父边中。 -/
theorem demodulation_check_parents {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : RewriteEvidence σ}
    (hCheck : check parents conclusion (.demodulation evidence) = true) :
    evidence.equality.idIn parents = true ∧ evidence.target.idIn parents = true :=
  RewriteEvidence.check_parents (kind := .demodulation) hCheck

/-- positive-superposition evidence 检查通过时，两个父字句快照都在父边中。 -/
theorem positiveSuperposition_check_parents {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : RewriteEvidence σ}
    (hCheck : check parents conclusion (.positiveSuperposition evidence) = true) :
    evidence.equality.idIn parents = true ∧ evidence.target.idIn parents = true :=
  RewriteEvidence.check_parents (kind := .positiveSuperposition) hCheck

/-- negative-superposition evidence 检查通过时，两个父字句快照都在父边中。 -/
theorem negativeSuperposition_check_parents {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {conclusion : Clause σ} {evidence : RewriteEvidence σ}
    (hCheck : check parents conclusion (.negativeSuperposition evidence) = true) :
    evidence.equality.idIn parents = true ∧ evidence.target.idIn parents = true :=
  RewriteEvidence.check_parents (kind := .negativeSuperposition) hCheck

end LocalRuleEvidence

/-- 本地推理节点 payload。 -/
structure LocalRulePayload (σ : Signature) where
  family : LocalRuleFamily
  evidence : LocalRuleEvidence σ
  note : String := ""

namespace LocalRulePayload

/-- 本地规则 payload 的公共规则标签。 -/
def ruleTags {σ : Signature} (payload : LocalRulePayload σ) : Array Certificate.RuleTag :=
  payload.family.ruleTags

/-- 本地规则引用的父字句快照。 -/
def parentClauses {σ : Signature} (payload : LocalRulePayload σ) : Array (ParentClause σ) :=
  payload.evidence.parentClauses

/-- 当前已经完成对象层 soundness 的本地规则 payload 片段。 -/
def soundnessSupported {σ : Signature} (payload : LocalRulePayload σ) : Bool :=
  payload.evidence.soundnessSupported

/--
当前已经完成 guarded soundness 的本地规则 payload 片段。

所有 substitution 规则都通过环境搬运消费父节点的 guarded 不变量。
-/
def guardedSoundnessSupported {σ : Signature} (payload : LocalRulePayload σ) : Bool :=
  payload.soundnessSupported

/-- 本地规则结构检查：必须有完整 evidence，且 evidence 族和审计族一致。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (payload : LocalRulePayload σ)
    (conclusion : Clause σ) : Bool :=
  !parents.isEmpty &&
    payload.evidence.check parents conclusion &&
      decide (payload.evidence.family = payload.family)

/-- 本地规则摘要。 -/
def summary {σ : Signature} (payload : LocalRulePayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"local({payload.family.label}){note}"

end LocalRulePayload

/-! ## Propositional closure evidence -/

/-- 命题文字到对象层文字的链接。 -/
structure PropLiteralLink (σ : Signature) where
  prop : PropResolution.Lit
  object : Literal σ

namespace PropLiteralLink

/-- atom map 在对象层环境下诱导出的命题 valuation。 -/
def valuation {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (base : PropResolution.Valuation)
    (atomMap : Array (Formula σ)) (env : SetLevel.EnvAt.{x} M) :
    PropResolution.Valuation :=
  fun var =>
    match atomMap[var]? with
    | some atom => Logic.FirstOrder.Formula.satisfies env atom
    | none => base var

/-- guard/CDCL 专用变量不能落入对象 atomMap 的解释域。 -/
def outsideAtomMap {σ : Signature} (atomMap : Array (Formula σ))
    (lit : PropResolution.Lit) : Bool :=
  match atomMap[lit.var]? with
  | some _ => false
  | none => true

/-- 命题文字链接是否和全局 atom map 一致。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (atomMap : Array (Formula σ))
    (link : PropLiteralLink σ) : Bool :=
  link.prop.positive == link.object.polarity &&
    match atomMap[link.prop.var]? with
    | some atom => StructuralEq.formula atom link.object.atom
    | none => false

/-- 命题文字链接检查通过时，对象层文字满足性会传递到命题 valuation。 -/
theorem sound {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {M : SetLevel.StructureAt.{x} σ}
    {base : PropResolution.Valuation} {atomMap : Array (Formula σ)}
    {env : SetLevel.EnvAt.{x} M}
    {link : PropLiteralLink σ}
    (hCheck : link.check atomMap = true)
    (hObject : Literal.Satisfies env link.object) :
    link.prop.Holds (valuation base atomMap env) := by
  cases link with
  | mk prop object =>
  cases prop with
  | mk var positive =>
  cases object with
  | mk objectPolarity objectAtom =>
  unfold check at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPolarity, hAtomCheck⟩
  have hPolarityEq : positive = objectPolarity :=
    beq_iff_eq.mp hPolarity
  cases hLookup : atomMap[var]? with
  | none =>
      simp [hLookup] at hAtomCheck
  | some atom =>
      have hAtomCheck' : StructuralEq.formula atom objectAtom = true := by
        simpa [hLookup] using hAtomCheck
      have hAtomEq : atom = objectAtom :=
        StructuralEq.formula_sound atom objectAtom hAtomCheck'
      cases hPolarityEq
      cases positive <;>
        simpa [PropResolution.Lit.Holds, valuation, Literal.Satisfies,
          Literal.toFormula, hLookup, hAtomEq,
          Logic.FirstOrder.Formula.satisfies] using hObject

/-- `outsideAtomMap` 变量在混合 valuation 中仍按外部 guard/CDCL valuation 解释。 -/
theorem holds_valuation_iff_of_outsideAtomMap {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    {base : PropResolution.Valuation} {atomMap : Array (Formula σ)}
    {env : SetLevel.EnvAt.{x} M} {lit : PropResolution.Lit}
    (hOutside : outsideAtomMap atomMap lit = true) :
    lit.Holds (valuation base atomMap env) ↔ lit.Holds base := by
  cases lit with
  | mk var positive =>
      unfold outsideAtomMap at hOutside
      cases hLookup : atomMap[var]? with
      | some atom =>
          simp [hLookup] at hOutside
      | none =>
          cases positive <;>
            simp [PropResolution.Lit.Holds, valuation, hLookup]

/-- `outsideAtomMap` 对取反文字保持不变。 -/
theorem outsideAtomMap_neg {σ : Signature} {atomMap : Array (Formula σ)}
    {lit : PropResolution.Lit}
    (hOutside : outsideAtomMap atomMap lit = true) :
    outsideAtomMap atomMap lit.neg = true := by
  cases lit
  simpa [outsideAtomMap, PropResolution.Lit.neg] using hOutside

end PropLiteralLink

/-- 一个父对象字句命题化为一条 initial prop clause 的证据。 -/
structure PropParentClauseLink (σ : Signature) where
  parent : ParentClause σ
  literalLinks : Array (PropLiteralLink σ)

namespace PropParentClauseLink

/-- 由 literal links 计算命题字句。 -/
def encodedClause {σ : Signature} (link : PropParentClauseLink σ) : PropResolution.Clause :=
  PropResolution.canonicalClause (link.literalLinks.map fun literal => literal.prop)

/-- 由 literal links 恢复对象字句。 -/
def objectClause {σ : Signature} (link : PropParentClauseLink σ) : Clause σ :=
  { literals := link.literalLinks.map fun literal => literal.object }

/-- 父字句命题化链接的可计算检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (atomMap : Array (Formula σ))
    (initial : PropResolution.InitialClause) (link : PropParentClauseLink σ) : Bool :=
  link.parent.idIn parents &&
    link.parent.clause.eq link.objectClause &&
      PropResolution.clauseEq initial.clause link.encodedClause &&
        link.literalLinks.all fun literal => literal.check atomMap

/-- 父对象字句的满足性会传递到命题化后的 encoded clause。 -/
theorem encodedClause_satisfies_of_object {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {base : PropResolution.Valuation}
    {atomMap : Array (Formula σ)} {env : SetLevel.EnvAt.{x} M}
    {link : PropParentClauseLink σ}
    (hLiteralChecks :
      (link.literalLinks.all fun literal => literal.check atomMap) = true)
    (hObject : Clause.Satisfies env link.objectClause) :
    PropResolution.Clause.Satisfies
      (PropLiteralLink.valuation base atomMap env) link.encodedClause := by
  rcases Clause.satisfies_iff_exists_literal.mp hObject with
    ⟨objectLiteral, hObjectMem, hObjectSat⟩
  have hMapped :
      objectLiteral ∈ (link.literalLinks.map fun literal => literal.object).toList := by
    simpa [objectClause] using hObjectMem
  have hMappedList :
      objectLiteral ∈
        List.map (fun literal => literal.object) link.literalLinks.toList := by
    simpa [Array.toList_map] using hMapped
  rcases List.mem_map.mp hMappedList with
    ⟨literalLink, hLinkMem, hObjectEq⟩
  have hCheck : literalLink.check atomMap = true := by
    have hArrayMem : literalLink ∈ link.literalLinks := Array.mem_def.mpr hLinkMem
    rcases Array.mem_iff_getElem.mp hArrayMem with ⟨i, hLt, hGet⟩
    have hAll := Array.all_eq_true.mp hLiteralChecks
    have hAt := hAll i hLt
    simpa [hGet] using hAt
  have hPropMem :
      literalLink.prop ∈
        (PropResolution.canonicalClause
          (link.literalLinks.map fun literal => literal.prop)).toList := by
    apply PropResolution.mem_canonicalClause_of_mem
    have hPropMemRaw :
        literalLink.prop ∈
          List.map (fun literal => literal.prop) link.literalLinks.toList :=
      List.mem_map_of_mem hLinkMem
    simpa [Array.toList_map] using hPropMemRaw
  have hPropHolds :
      literalLink.prop.Holds (PropLiteralLink.valuation base atomMap env) :=
    PropLiteralLink.sound hCheck (by simpa [hObjectEq] using hObjectSat)
  exact PropResolution.Clause.satisfies_of_mem hPropMem hPropHolds

end PropParentClauseLink

/-- guarded object clause 作为 CDCL activation clause 的证据。 -/
structure PropGuardActivationLink (σ : Signature) where
  parent : ParentClause σ
  guards : GuardSet
  literalLinks : Array (PropLiteralLink σ)

namespace PropGuardActivationLink

/-- 由 guard 和 object literal links 计算 CDCL activation clause：`¬Γ ∨ prop(C)`。 -/
def encodedClause {σ : Signature} (link : PropGuardActivationLink σ) :
    PropResolution.Clause :=
  PropResolution.canonicalClause
    (link.guards.map PropResolution.Lit.neg ++
      link.literalLinks.map fun literal => literal.prop)

/-- 由 literal links 恢复对象字句。 -/
def objectClause {σ : Signature} (link : PropGuardActivationLink σ) : Clause σ :=
  { literals := link.literalLinks.map fun literal => literal.object }

/-- guarded activation 链接的局部可计算检查。父节点真实 guards 由 DAG 级 checker 检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (atomMap : Array (Formula σ))
    (initial : PropResolution.InitialClause) (link : PropGuardActivationLink σ) : Bool :=
  link.parent.idIn parents &&
    link.parent.clause.eq link.objectClause &&
      PropResolution.clauseEq initial.clause link.encodedClause &&
        link.guards.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
          link.literalLinks.all fun literal => literal.check atomMap

/-- guarded activation clause `¬Γ ∨ prop(C)` 的命题满足性。 -/
theorem encodedClause_satisfies {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : SetLevel.StructureAt.{x} σ} {base : PropResolution.Valuation}
    {atomMap : Array (Formula σ)} {env : SetLevel.EnvAt.{x} M}
    {link : PropGuardActivationLink σ}
    (hGuardChecks :
      (link.guards.all fun literal =>
        PropLiteralLink.outsideAtomMap atomMap literal) = true)
    (hLiteralChecks :
      (link.literalLinks.all fun literal => literal.check atomMap) = true)
    (hObjectOfGuards :
      (∀ lit, lit ∈ (canonicalGuards link.guards).toList → lit.Holds base) →
        Clause.Satisfies env link.objectClause) :
    PropResolution.Clause.Satisfies
      (PropLiteralLink.valuation base atomMap env) link.encodedClause := by
  classical
  by_cases hGuards :
      ∀ lit, lit ∈ (canonicalGuards link.guards).toList → lit.Holds base
  · rcases Clause.satisfies_iff_exists_literal.mp (hObjectOfGuards hGuards) with
      ⟨objectLiteral, hObjectMem, hObjectSat⟩
    have hMapped :
        objectLiteral ∈ (link.literalLinks.map fun literal => literal.object).toList := by
      simpa [objectClause] using hObjectMem
    have hMappedList :
        objectLiteral ∈
          List.map (fun literal => literal.object) link.literalLinks.toList := by
      simpa [Array.toList_map] using hMapped
    rcases List.mem_map.mp hMappedList with
      ⟨literalLink, hLinkMem, hObjectEq⟩
    have hCheck : literalLink.check atomMap = true := by
      have hArrayMem : literalLink ∈ link.literalLinks := Array.mem_def.mpr hLinkMem
      rcases Array.mem_iff_getElem.mp hArrayMem with ⟨i, hLt, hGet⟩
      have hAll := Array.all_eq_true.mp hLiteralChecks
      have hAt := hAll i hLt
      simpa [hGet] using hAt
    have hPropMemRaw :
        literalLink.prop ∈ (link.literalLinks.map fun literal => literal.prop).toList := by
      have hPropMemList :
          literalLink.prop ∈
            List.map (fun literal => literal.prop) link.literalLinks.toList :=
        List.mem_map_of_mem hLinkMem
      simpa [Array.toList_map] using hPropMemList
    have hPropMem :
        literalLink.prop ∈ link.encodedClause.toList := by
      apply PropResolution.mem_canonicalClause_of_mem
      simp
      exact Or.inr ⟨literalLink, Array.mem_def.mpr hLinkMem, rfl⟩
    have hPropHolds :
        literalLink.prop.Holds (PropLiteralLink.valuation base atomMap env) :=
      PropLiteralLink.sound hCheck (by simpa [hObjectEq] using hObjectSat)
    exact PropResolution.Clause.satisfies_of_mem hPropMem hPropHolds
  · rcases Classical.not_forall.mp hGuards with ⟨guardLit, hNotGuard⟩
    have hGuardMem : guardLit ∈ (canonicalGuards link.guards).toList := by
      by_cases hMem : guardLit ∈ (canonicalGuards link.guards).toList
      · exact hMem
      · exact False.elim (hNotGuard (by intro h; exact False.elim (hMem h)))
    have hGuardFalse : ¬ guardLit.Holds base := by
      intro hHold
      exact hNotGuard (by intro _hMem; exact hHold)
    have hRawGuardMem : guardLit ∈ link.guards.toList :=
      mem_of_mem_propCanonicalClause hGuardMem
    have hOutside : PropLiteralLink.outsideAtomMap atomMap guardLit = true := by
      have hArrayMem : guardLit ∈ link.guards := Array.mem_def.mpr hRawGuardMem
      rcases Array.mem_iff_getElem.mp hArrayMem with ⟨i, hLt, hGet⟩
      have hAll := Array.all_eq_true.mp hGuardChecks
      have hAt := hAll i hLt
      simpa [hGet] using hAt
    have hNegOutside :
        PropLiteralLink.outsideAtomMap atomMap guardLit.neg = true :=
      PropLiteralLink.outsideAtomMap_neg hOutside
    have hNegBase : guardLit.neg.Holds base := by
      cases guardLit with
      | mk var positive =>
          cases positive <;>
            simpa [PropResolution.Lit.Holds, PropResolution.Lit.neg] using hGuardFalse
    have hNegMixed :
        guardLit.neg.Holds (PropLiteralLink.valuation base atomMap env) :=
      (PropLiteralLink.holds_valuation_iff_of_outsideAtomMap
        (base := base) (env := env) hNegOutside).2 hNegBase
    have hNegMem :
        guardLit.neg ∈ link.encodedClause.toList := by
      apply PropResolution.mem_canonicalClause_of_mem
      simp
      exact Or.inl ⟨guardLit, Array.mem_def.mpr hRawGuardMem, rfl⟩
    exact PropResolution.Clause.satisfies_of_mem hNegMem hNegMixed

end PropGuardActivationLink

/-- CDCL initial clause 对应一个已经物化的命题 learned-clause 节点。 -/
structure PropLearnedClauseLink where
  parent : NodeId
  clause : PropResolution.Clause

namespace PropLearnedClauseLink

/-- learned-clause 链接的可计算检查。 -/
def check {σ : Signature} (parents : Array NodeId) (atomMap : Array (Formula σ))
    (initial : PropResolution.InitialClause)
    (link : PropLearnedClauseLink) : Bool :=
  parents.contains link.parent &&
    link.clause.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
      PropResolution.clauseEq initial.clause link.clause

/-- theory-conflict guards 产生的 learned clause `¬Γ` 在 `Γ` 不全真时成立。 -/
theorem satisfies_of_not_guards {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} {base : PropResolution.Valuation}
    {atomMap : Array (Formula σ)} {env : SetLevel.EnvAt.{x} M}
    {link : PropLearnedClauseLink} {guards : GuardSet}
    (hClause : link.clause = learnedClauseOfGuards guards)
    (hOutside :
      (link.clause.all fun literal =>
        PropLiteralLink.outsideAtomMap atomMap literal) = true)
    (hNotGuards :
      ¬ ∀ lit, lit ∈ (canonicalGuards guards).toList → lit.Holds base) :
    PropResolution.Clause.Satisfies
      (PropLiteralLink.valuation base atomMap env) link.clause := by
  classical
  rcases Classical.not_forall.mp hNotGuards with ⟨guardLit, hNotGuard⟩
  have hGuardMem : guardLit ∈ (canonicalGuards guards).toList := by
    by_cases hMem : guardLit ∈ (canonicalGuards guards).toList
    · exact hMem
    · exact False.elim (hNotGuard (by intro h; exact False.elim (hMem h)))
  have hGuardFalse : ¬ guardLit.Holds base := by
    intro hHold
    exact hNotGuard (by intro _hMem; exact hHold)
  have hRawGuardMem : guardLit ∈ guards.toList :=
    mem_of_mem_propCanonicalClause hGuardMem
  have hNegMemLearned :
      guardLit.neg ∈ (learnedClauseOfGuards guards).toList := by
    have hMapMem :
        guardLit.neg ∈ (guards.map PropResolution.Lit.neg).toList :=
      by
        have hMapMemList :
            guardLit.neg ∈ List.map PropResolution.Lit.neg guards.toList :=
          List.mem_map_of_mem (f := PropResolution.Lit.neg) hRawGuardMem
        simpa [Array.toList_map] using hMapMemList
    simpa [learnedClauseOfGuards] using
      PropResolution.mem_canonicalClause_of_mem hMapMem
  have hNegMemClause : guardLit.neg ∈ link.clause.toList := by
    simpa [hClause] using hNegMemLearned
  have hNegOutside :
      PropLiteralLink.outsideAtomMap atomMap guardLit.neg = true := by
    have hArrayMem : guardLit.neg ∈ link.clause := Array.mem_def.mpr hNegMemClause
    rcases Array.mem_iff_getElem.mp hArrayMem with ⟨i, hLt, hGet⟩
    have hAll := Array.all_eq_true.mp hOutside
    have hAt := hAll i hLt
    simpa [hGet] using hAt
  have hNegBase : guardLit.neg.Holds base := by
    cases guardLit with
    | mk var positive =>
        cases positive <;>
          simpa [PropResolution.Lit.Holds, PropResolution.Lit.neg] using hGuardFalse
  have hNegMixed :
      guardLit.neg.Holds (PropLiteralLink.valuation base atomMap env) :=
    (PropLiteralLink.holds_valuation_iff_of_outsideAtomMap
      (base := base) (env := env) hNegOutside).2 hNegBase
  exact PropResolution.Clause.satisfies_of_mem hNegMemClause hNegMixed

end PropLearnedClauseLink

/-- CDCL initial clause 对应一个 AVATAR split descriptor 的 selector skeleton。 -/
structure PropAvatarSkeletonLink where
  parent : NodeId
  skeleton : PropResolution.Clause

namespace PropAvatarSkeletonLink

/--
AVATAR skeleton 链接的局部可计算检查。

split payload 与 skeleton 的对应关系由 DAG 级 checker 复核；这里检查父边、initial 槽位
以及 selector 变量不与对象 atom map 碰撞。
-/
def check {σ : Signature} (parents : Array NodeId) (atomMap : Array (Formula σ))
    (initial : PropResolution.InitialClause)
    (link : PropAvatarSkeletonLink) : Bool :=
  parents.contains link.parent &&
    link.skeleton.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
      PropResolution.clauseEq initial.clause link.skeleton

end PropAvatarSkeletonLink

/-- initial prop clause 的对象层来源。 -/
inductive PropInitialJustification (σ : Signature) where
  | parentClause (link : PropParentClauseLink σ)
  | guardActivationClause (link : PropGuardActivationLink σ)
  | propLearnedClause (link : PropLearnedClauseLink)
  | avatarSkeleton (link : PropAvatarSkeletonLink)

/-- 两类纯命题 initial justification 的最小 replay 键。 -/
structure PropositionalJustificationKeys where
  parents : List NodeId := []
  clauses : List PropResolution.Clause := []
  deriving Repr, Inhabited, Lean.ToExpr

namespace PropInitialJustification

/-- initial justification 中引用的父字句快照。 -/
def parentClause? {σ : Signature} : PropInitialJustification σ → Option (ParentClause σ)
  | parentClause link => some link.parent
  | guardActivationClause link => some link.parent
  | propLearnedClause _ => none
  | avatarSkeleton _ => none

/-- initial justification 的可计算检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (atomMap : Array (Formula σ))
    (initial : PropResolution.InitialClause) :
    PropInitialJustification σ → Bool
  | parentClause link =>
      link.check parents atomMap initial
  | guardActivationClause link =>
      link.check parents atomMap initial
  | propLearnedClause link =>
      link.check parents atomMap initial
  | avatarSkeleton link =>
      link.check parents atomMap initial

/-- residual CDCL guarded soundness 当前支持的 initial 来源。 -/
def guardedSoundnessSupported {σ : Signature} : PropInitialJustification σ → Bool
  | parentClause _ => true
  | guardActivationClause _ => true
  | propLearnedClause _ => true
  | avatarSkeleton _ => false

end PropInitialJustification

namespace PropositionalJustificationKeys

/-- 仅当所有 justification 都是纯命题 learned/skeleton 分支时抽取 replay 键。 -/
def ofJustifications? {σ : Signature} :
    List (PropInitialJustification σ) → Option PropositionalJustificationKeys
  | [] => some {}
  | justification :: rest => do
      let keys ← ofJustifications? rest
      match justification with
      | .propLearnedClause link =>
          some {
            parents := link.parent :: keys.parents
            clauses := link.clause :: keys.clauses
          }
      | .avatarSkeleton link =>
          some {
            parents := link.parent :: keys.parents
            clauses := link.skeleton :: keys.clauses
          }
      | _ =>
          none

/-- replay 键中的每个父节点都出现在 residual 节点父边数组中。 -/
def parentsCheck (parents : Array NodeId)
    (keys : PropositionalJustificationKeys) : Bool :=
  keys.parents.all parents.contains

/-- replay 键中的 selector/guard 变量都位于对象 atom map 之外。 -/
def outsideAtomMapCheck {σ : Signature} (atomMap : Array (Formula σ))
    (keys : PropositionalJustificationKeys) : Bool :=
  keys.clauses.all fun clause =>
    clause.all fun literal => PropLiteralLink.outsideAtomMap atomMap literal

/-- 纯命题键对父边、initial 字句与 atom-map 边界的向量化检查。 -/
def check {σ : Signature} (parents : Array NodeId) (atomMap : Array (Formula σ))
    (initialClauses : Array PropResolution.InitialClause)
    (keys : PropositionalJustificationKeys) : Bool :=
  keys.parentsCheck parents &&
    keys.outsideAtomMapCheck atomMap &&
      decide
        ((PropResolution.initialClauseDatabase initialClauses).toList = keys.clauses)

/-- 父键列表等于节点父边列表时，逐项 membership 检查成立。 -/
theorem parentsCheck_eq_true_of_eq (parents : Array NodeId)
    (keys : PropositionalJustificationKeys)
    (hParents : keys.parents = parents.toList) :
    keys.parentsCheck parents = true := by
  apply List.all_eq_true.mpr
  intro parent hParent
  rw [hParents] at hParent
  exact Array.contains_eq_true_of_mem (Array.mem_def.mpr hParent)

end PropositionalJustificationKeys

/-- residual CDCL 使用的命题闭合 payload。 -/
structure PropositionalClosurePayload (σ : Signature) where
  atomMap : Array (Formula σ) := #[]
  initialClauses : Array PropResolution.InitialClause
  initialJustifications : Array (PropInitialJustification σ) := #[]
  proof : PropResolution.CdclProof
  stats : Certificate.Stats := {}
  note : String := ""

namespace PropositionalClosurePayload

/-- 根据 CDCL payload 计算默认统计。 -/
def computedStats {σ : Signature} (payload : PropositionalClosurePayload σ) : Certificate.Stats :=
  {
    steps := payload.proof.journal.steps.size
    clauses := payload.initialClauses.size + payload.proof.journal.learns.size
    generated := payload.proof.journal.learns.size
    retained := payload.initialClauses.size + payload.proof.journal.learns.size
    verified := payload.proof.journal.learns.size
    residuals := 0
    fuel := payload.stats.fuel
  }

/-- 命题闭合 payload 引用的父字句快照。 -/
def parentClauses {σ : Signature} (payload : PropositionalClosurePayload σ) :
    Array (ParentClause σ) :=
  payload.initialJustifications.filterMap PropInitialJustification.parentClause?

/-- 列表版 initial justification 检查，避免数组索引证明进入大型 replay。 -/
def justificationsListCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array NodeId) (atomMap : Array (Formula σ)) :
    List PropResolution.InitialClause → List (PropInitialJustification σ) → Bool
  | [], [] => true
  | initial :: initials, justification :: justifications =>
      justification.check parents atomMap initial &&
        justificationsListCheck parents atomMap initials justifications
  | _, _ => false

/-- 列表 checker 为真时，任意同槽位 initial/justification 的局部检查为真。 -/
theorem justificationsListCheck_at {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array NodeId) (atomMap : Array (Formula σ)) :
    ∀ {initials : List PropResolution.InitialClause}
      {justifications : List (PropInitialJustification σ)},
      justificationsListCheck parents atomMap initials justifications = true →
      ∀ slot (hInitial : slot < initials.length)
        (hJustification : slot < justifications.length),
        justifications[slot].check parents atomMap initials[slot] = true
  | [], _, hCheck, slot, hInitial, _ => by
      cases hInitial
  | _ :: _, [], hCheck, slot, _hInitial, _hJustification => by
      simp [justificationsListCheck] at hCheck
  | initial :: initials, justification :: justifications, hCheck,
      0, _hInitial, _hJustification => by
      exact (Bool.and_eq_true_iff.mp hCheck).1
  | initial :: initials, justification :: justifications, hCheck,
      slot + 1, hInitial, hJustification => by
      exact justificationsListCheck_at parents atomMap
        (Bool.and_eq_true_iff.mp hCheck).2 slot
        (Nat.lt_of_succ_lt_succ hInitial)
        (Nat.lt_of_succ_lt_succ hJustification)

/-- 纯命题 replay 键的四个分量推出逐槽位 justification checker。 -/
theorem justificationsListCheck_eq_true_of_propositionalKeys {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array NodeId) (atomMap : Array (Formula σ)) :
    ∀ {initials : List PropResolution.InitialClause}
      {justifications : List (PropInitialJustification σ)}
      {keys : PropositionalJustificationKeys},
      PropositionalJustificationKeys.ofJustifications? justifications = some keys →
      initials.map (fun initial => initial.clause) = keys.clauses →
      keys.parentsCheck parents = true →
      keys.outsideAtomMapCheck atomMap = true →
      justificationsListCheck parents atomMap initials justifications = true
  | [], [], keys, hKeys, _hClauses, _hParents, _hOutside => by
      simp [PropositionalJustificationKeys.ofJustifications?] at hKeys
      subst keys
      rfl
  | _ :: _, [], keys, hKeys, hClauses, _hParents, _hOutside => by
      simp [PropositionalJustificationKeys.ofJustifications?] at hKeys
      subst keys
      simp at hClauses
  | [], justification :: justifications, keys, hKeys, hClauses, _hParents, _hOutside => by
      cases hRest :
          PropositionalJustificationKeys.ofJustifications? justifications with
      | none =>
          simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
      | some tailKeys =>
          cases justification with
          | parentClause link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
          | guardActivationClause link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
          | propLearnedClause link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
              subst keys
              simp at hClauses
          | avatarSkeleton link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
              subst keys
              simp at hClauses
  | initial :: initials, justification :: justifications, keys,
      hKeys, hClauses, hParents, hOutside => by
      cases hRest :
          PropositionalJustificationKeys.ofJustifications? justifications with
      | none =>
          simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
      | some tailKeys =>
          cases justification with
          | parentClause link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
          | guardActivationClause link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
          | propLearnedClause link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
              subst keys
              have hClauseParts :
                  initial.clause = link.clause ∧
                    initials.map (fun item => item.clause) = tailKeys.clauses := by
                simpa using hClauses
              have hParentParts :
                  parents.contains link.parent = true ∧
                    tailKeys.parentsCheck parents = true := by
                simpa [PropositionalJustificationKeys.parentsCheck] using hParents
              have hOutsideParts :
                  (link.clause.all fun literal =>
                    PropLiteralLink.outsideAtomMap atomMap literal) = true ∧
                    tailKeys.outsideAtomMapCheck atomMap = true := by
                simpa [PropositionalJustificationKeys.outsideAtomMapCheck] using hOutside
              have hTail :=
                justificationsListCheck_eq_true_of_propositionalKeys
                  parents atomMap hRest hClauseParts.2
                    hParentParts.2 hOutsideParts.2
              apply Bool.and_eq_true_iff.mpr
              refine ⟨?_, hTail⟩
              apply Bool.and_eq_true_iff.mpr
              exact ⟨Bool.and_eq_true_iff.mpr
                  ⟨hParentParts.1, hOutsideParts.1⟩,
                PropResolution.clauseEq_eq.mpr hClauseParts.1⟩
          | avatarSkeleton link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
              subst keys
              have hClauseParts :
                  initial.clause = link.skeleton ∧
                    initials.map (fun item => item.clause) = tailKeys.clauses := by
                simpa using hClauses
              have hParentParts :
                  parents.contains link.parent = true ∧
                    tailKeys.parentsCheck parents = true := by
                simpa [PropositionalJustificationKeys.parentsCheck] using hParents
              have hOutsideParts :
                  (link.skeleton.all fun literal =>
                    PropLiteralLink.outsideAtomMap atomMap literal) = true ∧
                    tailKeys.outsideAtomMapCheck atomMap = true := by
                simpa [PropositionalJustificationKeys.outsideAtomMapCheck] using hOutside
              have hTail :=
                justificationsListCheck_eq_true_of_propositionalKeys
                  parents atomMap hRest hClauseParts.2
                    hParentParts.2 hOutsideParts.2
              apply Bool.and_eq_true_iff.mpr
              refine ⟨?_, hTail⟩
              apply Bool.and_eq_true_iff.mpr
              exact ⟨Bool.and_eq_true_iff.mpr
                  ⟨hParentParts.1, hOutsideParts.1⟩,
                PropResolution.clauseEq_eq.mpr hClauseParts.1⟩

/-- 每条 initial clause 是否都有同槽位 justification。 -/
def justificationsCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array NodeId) (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialClauses.size == payload.initialJustifications.size &&
    match
      PropositionalJustificationKeys.ofJustifications?
        payload.initialJustifications.toList
    with
    | some keys =>
        keys.check parents payload.atomMap payload.initialClauses
    | none =>
        justificationsListCheck parents payload.atomMap
          payload.initialClauses.toList payload.initialJustifications.toList

/-- 整体 justification checker 为真时，可恢复通用逐槽位列表 checker。 -/
theorem justificationsListCheck_eq_true_of_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {payload : PropositionalClosurePayload σ}
    (hCheck : payload.justificationsCheck parents = true) :
    justificationsListCheck parents payload.atomMap
      payload.initialClauses.toList payload.initialJustifications.toList = true := by
  unfold justificationsCheck at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_hSize, hBody⟩
  cases hKeys :
      PropositionalJustificationKeys.ofJustifications?
        payload.initialJustifications.toList with
  | none =>
      simpa [hKeys] using hBody
  | some keys =>
      have hFields :
          (keys.parentsCheck parents = true ∧
            keys.outsideAtomMapCheck payload.atomMap = true) ∧
              (PropResolution.initialClauseDatabase payload.initialClauses).toList =
                keys.clauses := by
        simpa [hKeys, PropositionalJustificationKeys.check] using hBody
      have hClauses :
          payload.initialClauses.toList.map (fun initial => initial.clause) =
            keys.clauses := by
        simpa [PropResolution.initialClauseDatabase, Array.toList_map] using hFields.2
      exact justificationsListCheck_eq_true_of_propositionalKeys
        parents payload.atomMap hKeys hClauses hFields.1.1 hFields.1.2

/-- 纯命题键抽取与四个小型检查合成原 justification checker。 -/
theorem justificationsCheck_eq_true_of_propositionalKeys {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array NodeId) (payload : PropositionalClosurePayload σ)
    (keys : PropositionalJustificationKeys)
    (hSize :
      (payload.initialClauses.size == payload.initialJustifications.size) = true)
    (hKeys :
      PropositionalJustificationKeys.ofJustifications?
        payload.initialJustifications.toList = some keys)
    (hClauses :
      (PropResolution.initialClauseDatabase payload.initialClauses).toList =
        keys.clauses)
    (hParents : keys.parentsCheck parents = true)
    (hOutside : keys.outsideAtomMapCheck payload.atomMap = true) :
    payload.justificationsCheck parents = true := by
  simp [justificationsCheck, hSize, hKeys,
    PropositionalJustificationKeys.check, hClauses, hParents, hOutside]

/-- 命题闭合 payload 的可计算检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId)
    (payload : PropositionalClosurePayload σ) : Bool :=
  PropResolution.checkedUnsat payload.initialClauses payload.proof &&
    payload.justificationsCheck parents &&
    payload.stats.steps == payload.computedStats.steps &&
    payload.stats.clauses == payload.computedStats.clauses &&
    payload.stats.generated == payload.computedStats.generated &&
    payload.stats.retained == payload.computedStats.retained &&
    payload.stats.verified == payload.computedStats.verified

/-- CDCL、initial 来源与统计字段证明合成命题闭合 payload checker。 -/
theorem check_eq_true_of_components {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (parents : Array NodeId) (payload : PropositionalClosurePayload σ)
    (hUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof = true)
    (hJustifications : payload.justificationsCheck parents = true)
    (hSteps : (payload.stats.steps == payload.computedStats.steps) = true)
    (hClauses : (payload.stats.clauses == payload.computedStats.clauses) = true)
    (hGenerated : (payload.stats.generated == payload.computedStats.generated) = true)
    (hRetained : (payload.stats.retained == payload.computedStats.retained) = true)
    (hVerified : (payload.stats.verified == payload.computedStats.verified) = true) :
    payload.check parents = true := by
  simp [check, hUnsat, hJustifications, hSteps, hClauses, hGenerated,
    hRetained, hVerified]

/-- residual CDCL 进入 guarded soundness 时允许的 initial 来源集合。 -/
def guardedSoundnessSupported {σ : Signature}
    (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialJustifications.all PropInitialJustification.guardedSoundnessSupported

/-- 从纯数据 CDCL 结果构造命题闭合 payload；最终合法性仍由 DAG checker 复算。 -/
def ofRaw {σ : Signature} (initialClauses : Array PropResolution.InitialClause)
    (proof : PropResolution.CdclProof)
    (atomMap : Array (Formula σ) := #[])
    (initialJustifications : Array (PropInitialJustification σ) := #[])
    (fuel : Nat := 0) (note : String := "") : PropositionalClosurePayload σ :=
  let payload : PropositionalClosurePayload σ := {
    atomMap := atomMap
    initialClauses := initialClauses
    initialJustifications := initialJustifications
    proof := proof
    stats := { fuel := fuel }
    note := note
  }
  { payload with stats := payload.computedStats }

/-- 从 checked UNSAT 证书构造命题闭合 payload。 -/
def ofCheckedUnsat {σ : Signature} (cert : PropResolution.CheckedUnsatCertificate)
    (atomMap : Array (Formula σ) := #[])
    (initialJustifications : Array (PropInitialJustification σ) := #[])
    (fuel : Nat := 0) (note : String := "") : PropositionalClosurePayload σ :=
  ofRaw cert.initialClauses cert.proof atomMap initialJustifications fuel note

/-- 命题闭合摘要。 -/
def summary {σ : Signature} (payload : PropositionalClosurePayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"prop-closure(initial={payload.initialClauses.size}; " ++
    s!"learns={payload.proof.journal.learns.size}; " ++
      s!"steps={payload.proof.journal.steps.size}){note}"

end PropositionalClosurePayload

/--
AVATAR source split descriptor。

该节点仍然复述原 source 字句，只把完整 literal partition 与 selector 表登记为后续
component 节点和命题 skeleton 的唯一可信来源。
-/
structure AvatarSplitPayload (σ : Signature) where
  source : ParentClause σ
  partitions : Array (Array Nat)
  selectors : PropResolution.Clause
  note : String := ""

namespace AvatarSplitPayload

/-- split descriptor 引用的原 source 快照。 -/
def parentClauses {σ : Signature} (payload : AvatarSplitPayload σ) :
    Array (ParentClause σ) :=
  #[payload.source]

/-- split descriptor 的局部可计算检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (parents : Array NodeId) (payload : AvatarSplitPayload σ)
    (conclusion : Clause σ) : Bool :=
  parents.size == 1 &&
    payload.source.idIn parents &&
      payload.source.clause.eq conclusion &&
        AvatarSplit.indexPartitionOk payload.source.clause.literals.size payload.partitions &&
          AvatarSplit.selectorsOk payload.partitions payload.selectors

/-- split descriptor 摘要。 -/
def summary {σ : Signature} (payload : AvatarSplitPayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"avatarSplit(source={payload.source.id}; components={payload.partitions.size}){note}"

end AvatarSplitPayload

/--
AVATAR component 节点。

具体 component 字句与 singleton selector 都从父 split descriptor 复算，不在 payload
中重复保存，避免大型证明项随 component 数量重复整份 partition。
-/
structure AvatarComponentPayload (σ : Signature) where
  split : ParentClause σ
  componentIndex : Nat
  note : String := ""

namespace AvatarComponentPayload

/-- component 节点引用的 split descriptor 快照。 -/
def parentClauses {σ : Signature} (payload : AvatarComponentPayload σ) :
    Array (ParentClause σ) :=
  #[payload.split]

/-- component 的局部检查；结论与 selector 由 DAG 级 checker 读取父 payload 后复算。 -/
def check {σ : Signature} (parents : Array NodeId)
    (payload : AvatarComponentPayload σ) : Bool :=
  parents.size == 1 && payload.split.idIn parents

/-- component 摘要。 -/
def summary {σ : Signature} (payload : AvatarComponentPayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"avatarComponent(split={payload.split.id}; index={payload.componentIndex}){note}"

end AvatarComponentPayload

/-- theory conflict 节点：显式表示某组 guard `Γ` 推出对象空字句。 -/
structure TheoryConflictPayload (σ : Signature) where
  conflict : ParentClause σ
  note : String := ""

namespace TheoryConflictPayload

/-- theory conflict 引用的父字句快照。 -/
def parentClauses {σ : Signature} (payload : TheoryConflictPayload σ) :
    Array (ParentClause σ) :=
  #[payload.conflict]

/-- theory conflict 结构检查。guard 是否等于父 conflict guard 由 DAG 级 checker 检查。 -/
def check {σ : Signature} (parents : Array NodeId) (payload : TheoryConflictPayload σ)
    (conclusion : Clause σ) : Bool :=
  payload.conflict.idIn parents &&
    payload.conflict.clause.isEmpty &&
      conclusion.isEmpty

/-- theory conflict 摘要。 -/
def summary {σ : Signature} (payload : TheoryConflictPayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"theoryConflict(parent={payload.conflict.id}){note}"

end TheoryConflictPayload

/-- 由 theory conflict `Γ ⟹ ⊥` 物化出的命题 learned clause `¬Γ`。 -/
structure PropositionalLearnedClausePayload where
  conflict : NodeId
  learned : PropResolution.Clause
  note : String := ""

namespace PropositionalLearnedClausePayload

/-- learned clause 结构检查。`learned = ¬Γ` 由 DAG 级 checker 根据父节点 guard 检查。 -/
def check {σ : Signature} (parents : Array NodeId)
    (payload : PropositionalLearnedClausePayload) (conclusion : Clause σ) : Bool :=
  parents.contains payload.conflict &&
    conclusion.isEmpty

/-- learned clause 摘要。 -/
def summary (payload : PropositionalLearnedClausePayload) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"propLearned(conflict={payload.conflict}; lits={payload.learned.size}){note}"

end PropositionalLearnedClausePayload

/-- DAG 节点 payload。 -/
inductive Payload (σ : Signature) where
  | source (initialIndex : Nat)
  | avatarSplit (payload : AvatarSplitPayload σ)
  | avatarComponent (payload : AvatarComponentPayload σ)
  | localRule (payload : LocalRulePayload σ)
  | theoryConflict (payload : TheoryConflictPayload σ)
  | propositionalLearnedClause (payload : PropositionalLearnedClausePayload)
  | residualCdcl (payload : PropositionalClosurePayload σ)

namespace Payload

/-- payload 对应的公共规则标签。 -/
def ruleTags {σ : Signature} : Payload σ → Array Certificate.RuleTag
  | source _ => #[.sourceOrigin, .sourceFact]
  | avatarSplit _ => #[.sourceOrigin, .dagTopology]
  | avatarComponent _ => #[.sourceFact, .dagTopology]
  | localRule payload => payload.ruleTags
  | theoryConflict _ => #[.theoryConflict, .dagTopology]
  | propositionalLearnedClause _ => #[.propositionalLearnedClause, .parentCdclSkeleton]
  | residualCdcl _ => #[.residualCdcl, .parentCdclSkeleton]

/-- payload 对应的公共后端。 -/
def backend {σ : Signature} : Payload σ → Certificate.Backend
  | source _ => .sourceReplay
  | avatarSplit _ => .dagReflection
  | avatarComponent _ => .dagReflection
  | localRule _ => .superposition
  | theoryConflict _ => .dagReflection
  | propositionalLearnedClause _ => .propositionalCdcl
  | residualCdcl _ => .residualCdcl

/-- payload 对应的公共阶段。 -/
def phase {σ : Signature} : Payload σ → Certificate.Phase
  | source _ => .sourceMaterialization
  | avatarSplit _ => .sourceMaterialization
  | avatarComponent _ => .sourceMaterialization
  | localRule _ => .saturation
  | theoryConflict _ => .dagCheck
  | propositionalLearnedClause _ => .residualSplit
  | residualCdcl _ => .residualSplit

/-- payload 对应的闭合来源。 -/
def closureKind? {σ : Signature} : Payload σ → Option Certificate.ClosureKind
  | residualCdcl _ => some .residualCdcl
  | _ => none

/-- payload 是否允许作为对象层全局空根。 -/
def rootClosureEligible {σ : Signature} : Payload σ → Bool
  | propositionalLearnedClause _ => false
  | _ => true

/-- payload 中记录的父字句快照。 -/
def parentClauses {σ : Signature} : Payload σ → Array (ParentClause σ)
  | source _ => #[]
  | avatarSplit payload => payload.parentClauses
  | avatarComponent payload => payload.parentClauses
  | localRule payload => payload.parentClauses
  | theoryConflict payload => payload.parentClauses
  | propositionalLearnedClause _ => #[]
  | residualCdcl payload => payload.parentClauses

/-- payload 的结构检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (problem : ClauseProblem σ) (parents : Array NodeId)
    (conclusion : Clause σ) : Payload σ → Bool
  | source initialIndex =>
      parents.isEmpty &&
        match problem.initialClauses[initialIndex]? with
        | some initial => conclusion.eq initial
        | none => false
  | avatarSplit payload =>
      payload.check parents conclusion
  | avatarComponent payload =>
      payload.check parents
  | localRule payload =>
      payload.check parents conclusion
  | theoryConflict payload =>
      payload.check parents conclusion
  | propositionalLearnedClause payload =>
      payload.check parents conclusion
  | residualCdcl payload =>
      !parents.isEmpty && conclusion.isEmpty && payload.check parents

/-- residual CDCL 的三个包装字段与 closure payload 证明合成 payload checker。 -/
theorem residualCdcl_check_eq_true_of_components {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (problem : ClauseProblem σ) (parents : Array NodeId) (conclusion : Clause σ)
    (payload : PropositionalClosurePayload σ)
    (hParents : (!parents.isEmpty) = true)
    (hConclusion : conclusion.isEmpty = true)
    (hPayload : payload.check parents = true) :
    check problem parents conclusion (.residualCdcl payload) = true := by
  simp [check, hParents, hConclusion, hPayload]

/--
当前已经完成对象语义 soundness 的 payload 片段。

`residualCdcl` 的对象层无 guard 闭合仍不属于这个片段。source 只能引用
`ClauseProblem.initialClauses`，因此不再存在外部 fact 注入分支。
-/
def soundnessSupported {σ : Signature} : Payload σ → Bool
  | source _ => true
  | avatarSplit _ => false
  | avatarComponent _ => false
  | localRule payload => payload.soundnessSupported
  | theoryConflict _ => true
  | propositionalLearnedClause _ => false
  | residualCdcl _ => false

/--
当前已经完成 guarded soundness 的 payload 片段。

命题 learned-clause 节点只作为 guarded proof artifact 使用：它继承 theory-conflict
的 guard，并不允许作为无条件对象层空字句。residual CDCL 也只先进入 guarded 总定理。
-/
def guardedSoundnessSupported {σ : Signature} : Payload σ → Bool
  | source _ => true
  | avatarSplit _ => false
  | avatarComponent _ => false
  | localRule payload => payload.guardedSoundnessSupported
  | theoryConflict _ => true
  | propositionalLearnedClause _ => true
  | residualCdcl payload => payload.guardedSoundnessSupported

/-- payload 摘要。 -/
def summary {σ : Signature} : Payload σ → String
  | source initialIndex => s!"source(initial[{initialIndex}])"
  | avatarSplit payload => payload.summary
  | avatarComponent payload => payload.summary
  | localRule payload => payload.summary
  | theoryConflict payload => payload.summary
  | propositionalLearnedClause payload => payload.summary
  | residualCdcl payload => s!"residualCdcl; {payload.summary}"

end Payload

/-! ## DAG nodes -/

/-- 大型 DAG 的一个节点。结论统一表示为字句。 -/
structure Node (σ : Signature) where
  id : NodeId
  parents : Array NodeId := #[]
  ruleTags : Array Certificate.RuleTag := #[]
  guards : GuardSet := #[]
  conclusion : Clause σ
  payload : Payload σ

namespace Node

/-- 当前节点作为 guarded clause 的结论。 -/
def guardedConclusion {σ : Signature} (node : Node σ) : GuardedClause σ :=
  { guards := node.guards, clause := node.conclusion }

/-- 当前节点是否没有 AVATAR guard。 -/
def unguarded {σ : Signature} (node : Node σ) : Bool :=
  node.guards.isEmpty

/-- 当前节点是否是无 guard 的全局空字句。 -/
def globallyClosed {σ : Signature} (node : Node σ) : Bool :=
  node.guardedConclusion.globallyEmpty

/-- 当前节点是否是带 guard 的 AVATAR theory conflict。 -/
def theoryConflict {σ : Signature} (node : Node σ) : Bool :=
  node.guardedConclusion.theoryConflict

/-- 节点规则标签是否与 payload 默认标签完全一致。 -/
def ruleTagsOk {σ : Signature} (node : Node σ) : Bool :=
  node.ruleTags == node.payload.ruleTags

/-- 当前已经完成对象层 soundness 的节点片段。guarded 节点必须等待后续 guarded soundness。 -/
def soundnessSupported {σ : Signature} (node : Node σ) : Bool :=
  node.unguarded && node.payload.soundnessSupported

/-- 当前已经完成 guarded 对象层 soundness 的节点片段。 -/
def guardedSoundnessSupported {σ : Signature} (node : Node σ) : Bool :=
  node.payload.guardedSoundnessSupported

/-- 节点局部结构检查。拓扑由 `DAG.check` 统一检查。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (problem : ClauseProblem σ) (node : Node σ) : Bool :=
  node.ruleTagsOk && node.payload.check problem node.parents node.conclusion

/-- 规则标签与 payload 证明合成节点局部 checker。 -/
theorem check_eq_true_of_components {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (problem : ClauseProblem σ) (node : Node σ)
    (hRuleTags : node.ruleTagsOk = true)
    (hPayload : node.payload.check problem node.parents node.conclusion = true) :
    node.check problem = true :=
  Bool.and_eq_true_iff.mpr ⟨hRuleTags, hPayload⟩

/-- 节点检查通过时，规则标签检查通过。 -/
theorem ruleTagsOk_of_check_eq_true {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node : Node σ} (hCheck : node.check problem = true) :
    node.ruleTagsOk = true := by
  have hFields :
      node.ruleTagsOk = true ∧
        node.payload.check problem node.parents node.conclusion = true := by
    simpa [check] using hCheck
  exact hFields.1

/-- 节点检查通过时，payload 检查通过。 -/
theorem payload_check_of_check_eq_true {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node : Node σ} (hCheck : node.check problem = true) :
    node.payload.check problem node.parents node.conclusion = true := by
  have hFields :
      node.ruleTagsOk = true ∧
        node.payload.check problem node.parents node.conclusion = true := by
    simpa [check] using hCheck
  exact hFields.2

/-- 节点摘要。 -/
def summary {σ : Signature} (node : Node σ) : String :=
  s!"#{node.id}; parents={node.parents.size}; guards={node.guards.size}; " ++
    s!"lits={node.conclusion.literals.size}; " ++ node.payload.summary

/-- 转成公共审计节点。 -/
def toPublicNode {σ : Signature} (node : Node σ) : Certificate.Node :=
  {
    id := node.id
    backend := node.payload.backend
    phase := node.payload.phase
    label := node.summary
    ruleTags := node.ruleTags
    closureKind? :=
      match node.payload.closureKind? with
      | some kind => some kind
      | none => if node.globallyClosed then some .dagReflection else none
    stats := {
      steps := 1
      clauses := 1
      literals := node.conclusion.literals.size
      verified := 0
      residuals :=
        match node.payload with
        | .residualCdcl _ => 1
        | _ => 0
    }
    dependencies := node.parents
  }

end Node

namespace Node

/--
单个 DAG 节点的反证语义不变量。

只要初始字句问题在当前 bound stack 上有效，节点结论就在当前环境成立。
-/
def RefutationInvariant {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : ClauseProblem σ) (node : Node σ) : Prop :=
  ∀ {M : SetLevel.StructureAt.{x} σ}, ∀ env : SetLevel.EnvAt.{x} M,
    problem.Valid env → Clause.Satisfies env node.conclusion

/-- guard 集在某个命题 valuation 下全部为真；语义按规范化后的集合读取。 -/
def GuardsHold (valuation : PropResolution.Valuation) (guards : GuardSet) : Prop :=
  ∀ lit, lit ∈ (canonicalGuards guards).toList → lit.Holds valuation

/-- guard 集结构相等会保持 guard 满足性。 -/
theorem GuardsHold.of_guardSetEq {valuation : PropResolution.Valuation}
    {left right : GuardSet} (hEq : guardSetEq left right = true)
    (hGuards : GuardsHold valuation left) :
    GuardsHold valuation right := by
  intro lit hLit
  have hCanonical : canonicalGuards left = canonicalGuards right :=
    PropResolution.clauseEq_eq.mp (by simpa [guardSetEq] using hEq)
  exact hGuards lit (by simpa [hCanonical] using hLit)

/-- guard array 为空时，其底层列表为空。 -/
theorem guard_toList_eq_nil_of_isEmpty {guards : GuardSet}
    (hEmpty : guards.isEmpty = true) :
    guards.toList = [] := by
  have hSize : guards.size = 0 := by
    have hBool : (guards.size == 0) = true := by
      simpa [Array.isEmpty] using hEmpty
    cases h : guards.size with
    | zero => rfl
    | succ n =>
        have hFalse : (guards.size == 0) = false := by
          simp [h]
        rw [hFalse] at hBool
        cases hBool
  have hArray : guards = #[] :=
    Array.eq_empty_of_size_eq_zero hSize
  simp [hArray]

/-- 空 guard 集在任意 valuation 下都成立。 -/
theorem GuardsHold.of_isEmpty {valuation : PropResolution.Valuation}
    {guards : GuardSet} (hEmpty : guards.isEmpty = true) :
    GuardsHold valuation guards := by
  intro lit hLit
  have hRaw : lit ∈ guards.toList :=
    mem_of_mem_propCanonicalClause hLit
  have hList := guard_toList_eq_nil_of_isEmpty hEmpty
  simp [hList] at hRaw

/--
guarded 节点的反证语义不变量。

它把 AVATAR/CDCL 的 guard 作为外层条件保存下来：只要当前 guard 集在命题 valuation
下全真，对象层结论字句就必须在一阶语义下为真。
-/
def GuardedRefutationInvariant {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : ClauseProblem σ) (valuation : PropResolution.Valuation) (node : Node σ) : Prop :=
  ∀ {M : SetLevel.StructureAt.{x} σ}, ∀ env : SetLevel.EnvAt.{x} M,
    problem.Valid env → GuardsHold valuation node.guards →
      Clause.Satisfies env node.conclusion

/-- 无条件反证不变量可退化为 guarded 反证不变量。 -/
theorem guardedRefutationInvariant_of_refutationInvariant {σ : Signature}
    [DecidableEq σ.SortSymbol] {problem : ClauseProblem σ}
    {valuation : PropResolution.Valuation} {node : Node σ}
    (hInvariant : RefutationInvariant.{x} problem node) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  intro M env hProblem _hGuards
  exact hInvariant env hProblem

/-- admissible substitution 会把父字句满足性搬到替换后字句。 -/
theorem satisfies_applySubstitution_of_refutationInvariant {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {subst : TermSubstitution σ} {node : Node σ}
    (hAdmissible : TermSubstitution.BoundClosed subst ∧
      TermSubstitution.WellSorted subst)
    (hInvariant : RefutationInvariant.{x} problem node)
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    (hProblem : problem.Valid env) :
    Clause.Satisfies env (Clause.applySubstitution subst node.conclusion) := by
  let targetEnv := TermSubstitution.semanticEnv subst env hAdmissible.2
  have hEnvMatches :=
    TermSubstitution.semanticEnv_matches (subst := subst) (env := env)
      (hAdmissible := hAdmissible.2)
  have hProblem' : problem.Valid targetEnv :=
    hProblem.of_sameBoundStack hEnvMatches.1
  have hSatTarget : Clause.Satisfies targetEnv node.conclusion :=
    hInvariant targetEnv hProblem'
  exact (Clause.satisfies_applySubstitution_iff_of_envMatches
      (subst := subst) (env := env) (targetEnv := targetEnv)
      hAdmissible.1 hEnvMatches node.conclusion).mpr hSatTarget

/-- guarded 父不变量也可搬到替换后字句。 -/
theorem satisfies_applySubstitution_of_guardedRefutationInvariant {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {subst : TermSubstitution σ} {node : Node σ}
    (hAdmissible : TermSubstitution.BoundClosed subst ∧
      TermSubstitution.WellSorted subst)
    (hInvariant : GuardedRefutationInvariant.{x} problem valuation node)
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    (hProblem : problem.Valid env)
    (hGuards : GuardsHold valuation node.guards) :
    Clause.Satisfies env (Clause.applySubstitution subst node.conclusion) := by
  let targetEnv := TermSubstitution.semanticEnv subst env hAdmissible.2
  have hEnvMatches :=
    TermSubstitution.semanticEnv_matches (subst := subst) (env := env)
      (hAdmissible := hAdmissible.2)
  have hProblem' : problem.Valid targetEnv :=
    hProblem.of_sameBoundStack hEnvMatches.1
  have hSatTarget : Clause.Satisfies targetEnv node.conclusion :=
    hInvariant targetEnv hProblem' hGuards
  exact (Clause.satisfies_applySubstitution_iff_of_envMatches
      (subst := subst) (env := env) (targetEnv := targetEnv)
      hAdmissible.1 hEnvMatches node.conclusion).mpr hSatTarget

/-- 标准化分离后再 substitution 的父字句满足性可被搬运。 -/
theorem satisfies_standardizedSubstitution_of_refutationInvariant {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {offset : Nat} {subst : TermSubstitution σ}
    {node : Node σ}
    (hAdmissible : TermSubstitution.BoundClosed subst ∧
      TermSubstitution.WellSorted subst)
    (hInvariant : RefutationInvariant.{x} problem node)
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    (hProblem : problem.Valid env) :
    Clause.Satisfies env
      (Clause.applySubstitution subst (Clause.renameFreeVars offset node.conclusion)) := by
  let substitutionEnv := TermSubstitution.semanticEnv subst env hAdmissible.2
  have hSubstitutionEnv :=
    TermSubstitution.semanticEnv_matches (subst := subst) (env := env)
      (hAdmissible := hAdmissible.2)
  let renamedEnv := FreeVarRenaming.semanticEnv offset substitutionEnv
  have hRenamedEnv :=
    FreeVarRenaming.semanticEnv_matches (offset := offset)
      (sourceEnv := substitutionEnv)
  have hProblem' : problem.Valid substitutionEnv :=
    hProblem.of_sameBoundStack hSubstitutionEnv.1
  have hProblem'' : problem.Valid renamedEnv :=
    hProblem'.of_sameBoundStack hRenamedEnv.1
  have hSatOriginal : Clause.Satisfies renamedEnv node.conclusion :=
    hInvariant renamedEnv hProblem''
  have hSatRenamed : Clause.Satisfies substitutionEnv
      (Clause.renameFreeVars offset node.conclusion) :=
    (Clause.satisfies_renameFreeVars_iff_of_envMatches
      (offset := offset) (sourceEnv := substitutionEnv) (targetEnv := renamedEnv)
      hRenamedEnv node.conclusion).mpr hSatOriginal
  exact (Clause.satisfies_applySubstitution_iff_of_envMatches
      (subst := subst) (env := env) (targetEnv := substitutionEnv)
      hAdmissible.1 hSubstitutionEnv (Clause.renameFreeVars offset node.conclusion)).mpr
    hSatRenamed

/-- guarded 父不变量也可搬运到标准化分离后再 substitution 的字句。 -/
theorem satisfies_standardizedSubstitution_of_guardedRefutationInvariant
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {problem : ClauseProblem σ}
    {valuation : PropResolution.Valuation} {offset : Nat} {subst : TermSubstitution σ}
    {node : Node σ}
    (hAdmissible : TermSubstitution.BoundClosed subst ∧
      TermSubstitution.WellSorted subst)
    (hInvariant : GuardedRefutationInvariant.{x} problem valuation node)
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    (hProblem : problem.Valid env)
    (hGuards : GuardsHold valuation node.guards) :
    Clause.Satisfies env
      (Clause.applySubstitution subst (Clause.renameFreeVars offset node.conclusion)) := by
  let substitutionEnv := TermSubstitution.semanticEnv subst env hAdmissible.2
  have hSubstitutionEnv :=
    TermSubstitution.semanticEnv_matches (subst := subst) (env := env)
      (hAdmissible := hAdmissible.2)
  let renamedEnv := FreeVarRenaming.semanticEnv offset substitutionEnv
  have hRenamedEnv :=
    FreeVarRenaming.semanticEnv_matches (offset := offset)
      (sourceEnv := substitutionEnv)
  have hProblem' : problem.Valid substitutionEnv :=
    hProblem.of_sameBoundStack hSubstitutionEnv.1
  have hProblem'' : problem.Valid renamedEnv :=
    hProblem'.of_sameBoundStack hRenamedEnv.1
  have hSatOriginal : Clause.Satisfies renamedEnv node.conclusion :=
    hInvariant renamedEnv hProblem'' hGuards
  have hSatRenamed : Clause.Satisfies substitutionEnv
      (Clause.renameFreeVars offset node.conclusion) :=
    (Clause.satisfies_renameFreeVars_iff_of_envMatches
      (offset := offset) (sourceEnv := substitutionEnv) (targetEnv := renamedEnv)
      hRenamedEnv node.conclusion).mpr hSatOriginal
  exact (Clause.satisfies_applySubstitution_iff_of_envMatches
      (subst := subst) (env := env) (targetEnv := substitutionEnv)
      hAdmissible.1 hSubstitutionEnv (Clause.renameFreeVars offset node.conclusion)).mpr
    hSatRenamed

/-- source 索引经过 checker 对齐后满足反证语义不变量。 -/
theorem sourceRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node : Node σ} {initialIndex : Nat}
    (hSource : node.payload = .source initialIndex)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hSource] at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_hParentsEmpty, hSourceCheck⟩
  cases hLookup : problem.initialClauses[initialIndex]? with
  | none => simp [hLookup] at hSourceCheck
  | some initial =>
      have hConclusion : node.conclusion = initial :=
        Clause.eq_sound node.conclusion initial (by
          simpa [Payload.check, hLookup] using hSourceCheck)
      intro M env hProblem
      rw [hConclusion]
      exact hProblem env (fun _ _ => rfl) initialIndex initial hLookup

/-- parent-copy 本地规则保持反证语义不变量。 -/
theorem localRuleParentCopyRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node parentNode : Node σ} {payload : LocalRulePayload σ}
    {parent : ParentClause σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .parentCopy parent)
    (hParentClause : parent.clause = parentNode.conclusion)
    (hParentInvariant : RefutationInvariant.{x} problem parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  rcases LocalRuleEvidence.parentCopy_check_sound hEvidenceCheck with
    ⟨_hParentIn, hConclusion⟩
  intro M env hProblem
  rw [hConclusion, hParentClause]
  exact hParentInvariant env hProblem

/-- parent-copy 本地规则保持 guarded 反证语义不变量。 -/
theorem localRuleParentCopyGuardedRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {node parentNode : Node σ} {payload : LocalRulePayload σ}
    {parent : ParentClause σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .parentCopy parent)
    (hParentClause : parent.clause = parentNode.conclusion)
    (hParentGuards : GuardsHold valuation node.guards → GuardsHold valuation parentNode.guards)
    (hParentInvariant : GuardedRefutationInvariant.{x} problem valuation parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  rcases LocalRuleEvidence.parentCopy_check_sound hEvidenceCheck with
    ⟨_hParentIn, hConclusion⟩
  intro M env hProblem hGuards
  rw [hConclusion, hParentClause]
  exact hParentInvariant env hProblem (hParentGuards hGuards)

/-- resolution 本地规则保持反证语义不变量。 -/
theorem resolutionRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node leftNode rightNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : ResolutionEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .resolution evidence)
    (hLeftClause : evidence.left.clause = leftNode.conclusion)
    (hRightClause : evidence.right.clause = rightNode.conclusion)
    (hLeftInvariant : RefutationInvariant.{x} problem leftNode)
    (hRightInvariant : RefutationInvariant.{x} problem rightNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion (.resolution evidence) = true := by
    simpa [LocalRuleEvidence.check, ResolutionEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.resolution_check_conclusion hEvidenceCheck'
  intro M env hProblem
  rw [hConclusion]
  exact Clause.satisfies_resolutionResult
    (by simpa [hLeftClause] using hLeftInvariant env hProblem)
    (by simpa [hRightClause] using hRightInvariant env hProblem)

/-- factoring 本地规则保持反证语义不变量。 -/
theorem factoringRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node parentNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : FactoringEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .factoring evidence)
    (hParentClause : evidence.parent.clause = parentNode.conclusion)
    (hParentInvariant : RefutationInvariant.{x} problem parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion (.factoring evidence) = true := by
    simpa [LocalRuleEvidence.check, FactoringEvidence.check] using hEvidenceCheck
  have hCovered := LocalRuleEvidence.factoring_check_parentCovered hEvidenceCheck'
  intro M env hProblem
  apply Clause.satisfies_of_allLiteralsCovered hCovered
  simpa [hParentClause] using hParentInvariant env hProblem

/-- equality-resolution 本地规则保持反证语义不变量。 -/
theorem equalityResolutionRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node parentNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : EqualityResolutionEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .equalityResolution evidence)
    (hParentClause : evidence.parent.clause = parentNode.conclusion)
    (hParentInvariant : RefutationInvariant.{x} problem parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.equalityResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, EqualityResolutionEvidence.check] using
      hEvidenceCheck
  rcases LocalRuleEvidence.equalityResolution_check_sound hEvidenceCheck' with
    ⟨hTerm, hConclusion⟩
  intro M env hProblem
  rw [hConclusion]
  exact Clause.satisfies_equalityResolutionResult hTerm
    (by simpa [hParentClause] using hParentInvariant env hProblem)

/-- substituted resolution 本地规则保持反证语义不变量。 -/
theorem substitutedResolutionRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node leftNode rightNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : SubstitutedResolutionEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedResolution evidence)
    (hLeftClause : evidence.left.clause = leftNode.conclusion)
    (hRightClause : evidence.right.clause = rightNode.conclusion)
    (hLeftInvariant : RefutationInvariant.{x} problem leftNode)
    (hRightInvariant : RefutationInvariant.{x} problem rightNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.substitutedResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedResolutionEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedResolutionEvidence.check_admissible hEvidenceCheck'
  have hConclusion := SubstitutedResolutionEvidence.check_conclusion hEvidenceCheck'
  intro M env hProblem
  rw [hConclusion]
  exact Clause.satisfies_resolutionResult
    (by
      simpa [← hLeftClause] using
        satisfies_applySubstitution_of_refutationInvariant
          (problem := problem) (subst := evidence.substitution) (node := leftNode)
          hAdmissible hLeftInvariant hProblem)
    (by
      simpa [← hRightClause] using
        satisfies_applySubstitution_of_refutationInvariant
          (problem := problem) (subst := evidence.substitution) (node := rightNode)
          hAdmissible hRightInvariant hProblem)

/-- substituted factoring 本地规则保持反证语义不变量。 -/
theorem substitutedFactoringRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node parentNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : SubstitutedFactoringEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedFactoring evidence)
    (hParentClause : evidence.parent.clause = parentNode.conclusion)
    (hParentInvariant : RefutationInvariant.{x} problem parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.substitutedFactoring evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedFactoringEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedFactoringEvidence.check_admissible hEvidenceCheck'
  have hCovered := SubstitutedFactoringEvidence.check_sound hEvidenceCheck'
  intro M env hProblem
  apply Clause.satisfies_of_allLiteralsCovered hCovered.2.1
  simpa [← hParentClause] using
    satisfies_applySubstitution_of_refutationInvariant
      (problem := problem) (subst := evidence.substitution) (node := parentNode)
      hAdmissible hParentInvariant hProblem

/-- substituted equality-resolution 本地规则保持反证语义不变量。 -/
theorem substitutedEqualityResolutionRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node parentNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : SubstitutedEqualityResolutionEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedEqualityResolution evidence)
    (hParentClause : evidence.parent.clause = parentNode.conclusion)
    (hParentInvariant : RefutationInvariant.{x} problem parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.substitutedEqualityResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedEqualityResolutionEvidence.check] using
      hEvidenceCheck
  have hAdmissible := SubstitutedEqualityResolutionEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedEqualityResolutionEvidence.check_sound hEvidenceCheck' with
    ⟨_hParent, hTerm, _hContains, hConclusion⟩
  intro M env hProblem
  rw [hConclusion]
  exact Clause.satisfies_equalityResolutionResult hTerm
    (by
      simpa [← hParentClause] using
        satisfies_applySubstitution_of_refutationInvariant
          (problem := problem) (subst := evidence.substitution) (node := parentNode)
          hAdmissible hParentInvariant hProblem)

/-- substituted resolution 保持 guarded 反证语义不变量。 -/
theorem substitutedResolutionGuardedRefutationInvariant_of_payload_check
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {problem : ClauseProblem σ}
    {valuation : PropResolution.Valuation} {node leftNode rightNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : SubstitutedResolutionEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedResolution evidence)
    (hLeftClause : evidence.left.clause = leftNode.conclusion)
    (hRightClause : evidence.right.clause = rightNode.conclusion)
    (hLeftGuards : GuardsHold valuation node.guards →
      GuardsHold valuation leftNode.guards)
    (hRightGuards : GuardsHold valuation node.guards →
      GuardsHold valuation rightNode.guards)
    (hLeftInvariant : GuardedRefutationInvariant.{x} problem valuation leftNode)
    (hRightInvariant : GuardedRefutationInvariant.{x} problem valuation rightNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.substitutedResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedResolutionEvidence.check] using
      hEvidenceCheck
  have hAdmissible := SubstitutedResolutionEvidence.check_admissible hEvidenceCheck'
  have hConclusion := SubstitutedResolutionEvidence.check_conclusion hEvidenceCheck'
  intro M env hProblem hGuards
  rw [hConclusion]
  exact Clause.satisfies_resolutionResult
    (by
      simpa [← hLeftClause] using
        satisfies_applySubstitution_of_guardedRefutationInvariant
          (problem := problem) (subst := evidence.substitution) (node := leftNode)
          hAdmissible hLeftInvariant hProblem (hLeftGuards hGuards))
    (by
      simpa [← hRightClause] using
        satisfies_applySubstitution_of_guardedRefutationInvariant
          (problem := problem) (subst := evidence.substitution) (node := rightNode)
          hAdmissible hRightInvariant hProblem (hRightGuards hGuards))

/-- substituted factoring 保持 guarded 反证语义不变量。 -/
theorem substitutedFactoringGuardedRefutationInvariant_of_payload_check
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {problem : ClauseProblem σ}
    {valuation : PropResolution.Valuation} {node parentNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : SubstitutedFactoringEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedFactoring evidence)
    (hParentClause : evidence.parent.clause = parentNode.conclusion)
    (hParentGuards : GuardsHold valuation node.guards →
      GuardsHold valuation parentNode.guards)
    (hParentInvariant : GuardedRefutationInvariant.{x} problem valuation parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.substitutedFactoring evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedFactoringEvidence.check] using
      hEvidenceCheck
  have hAdmissible := SubstitutedFactoringEvidence.check_admissible hEvidenceCheck'
  have hCovered := SubstitutedFactoringEvidence.check_sound hEvidenceCheck'
  intro M env hProblem hGuards
  apply Clause.satisfies_of_allLiteralsCovered hCovered.2.1
  simpa [← hParentClause] using
    satisfies_applySubstitution_of_guardedRefutationInvariant
      (problem := problem) (subst := evidence.substitution) (node := parentNode)
      hAdmissible hParentInvariant hProblem (hParentGuards hGuards)

/-- substituted equality-resolution 保持 guarded 反证语义不变量。 -/
theorem substitutedEqualityResolutionGuardedRefutationInvariant_of_payload_check
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {problem : ClauseProblem σ}
    {valuation : PropResolution.Valuation} {node parentNode : Node σ}
    {payload : LocalRulePayload σ}
    {evidence : SubstitutedEqualityResolutionEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedEqualityResolution evidence)
    (hParentClause : evidence.parent.clause = parentNode.conclusion)
    (hParentGuards : GuardsHold valuation node.guards →
      GuardsHold valuation parentNode.guards)
    (hParentInvariant : GuardedRefutationInvariant.{x} problem valuation parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.substitutedEqualityResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedEqualityResolutionEvidence.check] using
      hEvidenceCheck
  have hAdmissible :=
    SubstitutedEqualityResolutionEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedEqualityResolutionEvidence.check_sound hEvidenceCheck' with
    ⟨_hParent, hTerm, _hContains, hConclusion⟩
  intro M env hProblem hGuards
  rw [hConclusion]
  exact Clause.satisfies_equalityResolutionResult hTerm
    (by
      simpa [← hParentClause] using
        satisfies_applySubstitution_of_guardedRefutationInvariant
          (problem := problem) (subst := evidence.substitution) (node := parentNode)
          hAdmissible hParentInvariant hProblem (hParentGuards hGuards))

/-- 通用 substituted rewrite/superposition 结论保持反证语义不变量。 -/
private theorem substitutedRewriteRefutationInvariant_of_conclusion {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node equalityNode targetNode : Node σ}
    {evidence : SubstitutedRewriteEvidence σ}
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hConclusion : node.conclusion = evidence.result)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : RefutationInvariant.{x} problem equalityNode)
    (hTargetInvariant : RefutationInvariant.{x} problem targetNode) :
    RefutationInvariant.{x} problem node := by
  intro M env hProblem
  rw [hConclusion]
  exact SubstitutedRewriteEvidence.satisfies_result
    (by
      simpa [← hEqualityClause] using
        satisfies_applySubstitution_of_refutationInvariant
          (problem := problem) (subst := evidence.substitution) (node := equalityNode)
          hAdmissible hEqualityInvariant hProblem)
    (by
      simpa [← hTargetClause] using
        satisfies_applySubstitution_of_refutationInvariant
          (problem := problem) (subst := evidence.substitution) (node := targetNode)
          hAdmissible hTargetInvariant hProblem)

/-- substituted demodulation 本地规则保持反证语义不变量。 -/
theorem substitutedDemodulationRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node equalityNode targetNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : SubstitutedRewriteEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedDemodulation evidence)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : RefutationInvariant.{x} problem equalityNode)
    (hTargetInvariant : RefutationInvariant.{x} problem targetNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.substitutedDemodulation evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedRewriteEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedRewriteEvidence.check_sound hEvidenceCheck' with
    ⟨_hEqualityIn, _hTargetIn, _hContains, _hNeedle, _hKind, hConclusion⟩
  intro M env hProblem
  exact (substitutedRewriteRefutationInvariant_of_conclusion hAdmissible
    hConclusion hEqualityClause hTargetClause hEqualityInvariant hTargetInvariant)
    (env := env) hProblem

/-- substituted positive-superposition 本地规则保持反证语义不变量。 -/
theorem substitutedPositiveSuperpositionRefutationInvariant_of_payload_check
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node equalityNode targetNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : SubstitutedRewriteEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedPositiveSuperposition evidence)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : RefutationInvariant.{x} problem equalityNode)
    (hTargetInvariant : RefutationInvariant.{x} problem targetNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.substitutedPositiveSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedRewriteEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedRewriteEvidence.check_sound hEvidenceCheck' with
    ⟨_hEqualityIn, _hTargetIn, _hContains, _hNeedle, _hKind, hConclusion⟩
  intro M env hProblem
  exact (substitutedRewriteRefutationInvariant_of_conclusion hAdmissible
    hConclusion hEqualityClause hTargetClause hEqualityInvariant hTargetInvariant)
    (env := env) hProblem

/-- substituted negative-superposition 本地规则保持反证语义不变量。 -/
theorem substitutedNegativeSuperpositionRefutationInvariant_of_payload_check
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node equalityNode targetNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : SubstitutedRewriteEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedNegativeSuperposition evidence)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : RefutationInvariant.{x} problem equalityNode)
    (hTargetInvariant : RefutationInvariant.{x} problem targetNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.substitutedNegativeSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedRewriteEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedRewriteEvidence.check_sound hEvidenceCheck' with
    ⟨_hEqualityIn, _hTargetIn, _hContains, _hNeedle, _hKind, hConclusion⟩
  intro M env hProblem
  exact (substitutedRewriteRefutationInvariant_of_conclusion hAdmissible
    hConclusion hEqualityClause hTargetClause hEqualityInvariant hTargetInvariant)
    (env := env) hProblem

/-- standardized resolution 的语义核心；调用方负责从 payload checker 提取这些事实。 -/
private theorem standardizedResolutionRefutationInvariant_of_check
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {problem : ClauseProblem σ}
    {node leftNode rightNode : Node σ}
    {evidence : StandardizedSubstitutedResolutionEvidence σ}
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hStandardize :
      evidence.standardizeApart.left.renamed =
        evidence.standardizeApart.left.expected ∧
      evidence.standardizeApart.right.renamed =
        evidence.standardizeApart.right.expected)
    (hConclusion : node.conclusion =
      Clause.resolutionResult evidence.leftPolarity evidence.pivot
        evidence.leftClause evidence.rightClause)
    (hLeftClause : evidence.left.clause = leftNode.conclusion)
    (hRightClause : evidence.right.clause = rightNode.conclusion)
    (hLeftInvariant : RefutationInvariant.{x} problem leftNode)
    (hRightInvariant : RefutationInvariant.{x} problem rightNode) :
    RefutationInvariant.{x} problem node := by
  intro M env hProblem
  rw [hConclusion]
  exact Clause.satisfies_resolutionResult
    (by
      have hSat :=
        satisfies_standardizedSubstitution_of_refutationInvariant
          (problem := problem) (offset := evidence.standardizeApart.left.offset)
          (subst := evidence.substitution) (node := leftNode)
          hAdmissible hLeftInvariant hProblem
      simpa [StandardizedSubstitutedResolutionEvidence.leftClause,
        StandardizedSubstitutedResolutionEvidence.leftRenamedClause,
        StandardizedSubstitutedResolutionEvidence.left,
        StandardizeApartEvidence.leftParent,
        StandardizeApartSideEvidence.expected, hStandardize.1, ← hLeftClause] using hSat)
    (by
      have hSat :=
        satisfies_standardizedSubstitution_of_refutationInvariant
          (problem := problem) (offset := evidence.standardizeApart.right.offset)
          (subst := evidence.substitution) (node := rightNode)
          hAdmissible hRightInvariant hProblem
      simpa [StandardizedSubstitutedResolutionEvidence.rightClause,
        StandardizedSubstitutedResolutionEvidence.rightRenamedClause,
        StandardizedSubstitutedResolutionEvidence.right,
        StandardizeApartEvidence.rightParent,
        StandardizeApartSideEvidence.expected, hStandardize.2, ← hRightClause] using hSat)

/-- standardized rewrite/superposition 的语义核心。 -/
private theorem standardizedRewriteRefutationInvariant_of_check
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {problem : ClauseProblem σ}
    {node equalityNode targetNode : Node σ}
    {evidence : StandardizedSubstitutedRewriteEvidence σ}
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hStandardize :
      evidence.standardizeApart.left.renamed =
        evidence.standardizeApart.left.expected ∧
      evidence.standardizeApart.right.renamed =
        evidence.standardizeApart.right.expected)
    (hConclusion : node.conclusion = evidence.result)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : RefutationInvariant.{x} problem equalityNode)
    (hTargetInvariant : RefutationInvariant.{x} problem targetNode) :
    RefutationInvariant.{x} problem node := by
  intro M env hProblem
  rw [hConclusion]
  let ordinary : SubstitutedRewriteEvidence σ := {
    equality := { id := evidence.equality.id, clause := evidence.equalityRenamedClause }
    target := { id := evidence.target.id, clause := evidence.targetRenamedClause }
    substitution := evidence.substitution
    context := evidence.context
    lhs := evidence.lhs
    rhs := evidence.rhs
    equalityReversed := evidence.equalityReversed
    targetPolarity := evidence.targetPolarity
  }
  have hResult := SubstitutedRewriteEvidence.satisfies_result (evidence := ordinary)
    (by
      have hSat :=
        satisfies_standardizedSubstitution_of_refutationInvariant
          (problem := problem) (offset := evidence.standardizeApart.left.offset)
          (subst := evidence.substitution) (node := equalityNode)
          hAdmissible hEqualityInvariant hProblem
      simpa [StandardizedSubstitutedRewriteEvidence.equalityClause,
        StandardizedSubstitutedRewriteEvidence.equalityRenamedClause,
        StandardizedSubstitutedRewriteEvidence.equality,
        StandardizeApartEvidence.leftParent,
        StandardizeApartSideEvidence.expected, hStandardize.1, ← hEqualityClause,
        ordinary, SubstitutedRewriteEvidence.equalityClause] using hSat)
    (by
      have hSat :=
        satisfies_standardizedSubstitution_of_refutationInvariant
          (problem := problem) (offset := evidence.standardizeApart.right.offset)
          (subst := evidence.substitution) (node := targetNode)
          hAdmissible hTargetInvariant hProblem
      simpa [StandardizedSubstitutedRewriteEvidence.targetClause,
        StandardizedSubstitutedRewriteEvidence.targetRenamedClause,
        StandardizedSubstitutedRewriteEvidence.target,
        StandardizeApartEvidence.rightParent,
        StandardizeApartSideEvidence.expected, hStandardize.2, ← hTargetClause,
        ordinary, SubstitutedRewriteEvidence.targetClause] using hSat)
  simpa [ordinary, StandardizedSubstitutedRewriteEvidence.result,
    SubstitutedRewriteEvidence.result, StandardizedSubstitutedRewriteEvidence.needle,
    StandardizedSubstitutedRewriteEvidence.replacement, SubstitutedRewriteEvidence.needle,
    SubstitutedRewriteEvidence.replacement] using hResult

/-- guarded standardized resolution 的语义核心。 -/
private theorem standardizedResolutionGuardedRefutationInvariant_of_check
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {problem : ClauseProblem σ}
    {valuation : PropResolution.Valuation}
    {node leftNode rightNode : Node σ}
    {evidence : StandardizedSubstitutedResolutionEvidence σ}
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hStandardize :
      evidence.standardizeApart.left.renamed =
        evidence.standardizeApart.left.expected ∧
      evidence.standardizeApart.right.renamed =
        evidence.standardizeApart.right.expected)
    (hConclusion : node.conclusion =
      Clause.resolutionResult evidence.leftPolarity evidence.pivot
        evidence.leftClause evidence.rightClause)
    (hLeftClause : evidence.left.clause = leftNode.conclusion)
    (hRightClause : evidence.right.clause = rightNode.conclusion)
    (hLeftInvariant : GuardedRefutationInvariant.{x} problem valuation leftNode)
    (hRightInvariant : GuardedRefutationInvariant.{x} problem valuation rightNode)
    (hLeftGuards : GuardsHold valuation node.guards →
      GuardsHold valuation leftNode.guards)
    (hRightGuards : GuardsHold valuation node.guards →
      GuardsHold valuation rightNode.guards) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  intro M env hProblem hGuards
  rw [hConclusion]
  exact Clause.satisfies_resolutionResult
    (by
      have hSat :=
        satisfies_standardizedSubstitution_of_guardedRefutationInvariant
          (problem := problem) (valuation := valuation)
          (offset := evidence.standardizeApart.left.offset)
          (subst := evidence.substitution) (node := leftNode)
          hAdmissible hLeftInvariant hProblem (hLeftGuards hGuards)
      simpa [StandardizedSubstitutedResolutionEvidence.leftClause,
        StandardizedSubstitutedResolutionEvidence.leftRenamedClause,
        StandardizedSubstitutedResolutionEvidence.left,
        StandardizeApartEvidence.leftParent,
        StandardizeApartSideEvidence.expected, hStandardize.1, ← hLeftClause] using hSat)
    (by
      have hSat :=
        satisfies_standardizedSubstitution_of_guardedRefutationInvariant
          (problem := problem) (valuation := valuation)
          (offset := evidence.standardizeApart.right.offset)
          (subst := evidence.substitution) (node := rightNode)
          hAdmissible hRightInvariant hProblem (hRightGuards hGuards)
      simpa [StandardizedSubstitutedResolutionEvidence.rightClause,
        StandardizedSubstitutedResolutionEvidence.rightRenamedClause,
        StandardizedSubstitutedResolutionEvidence.right,
        StandardizeApartEvidence.rightParent,
        StandardizeApartSideEvidence.expected, hStandardize.2, ← hRightClause] using hSat)

/-- guarded standardized rewrite/superposition 的语义核心。 -/
private theorem standardizedRewriteGuardedRefutationInvariant_of_check
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {problem : ClauseProblem σ}
    {valuation : PropResolution.Valuation}
    {node equalityNode targetNode : Node σ}
    {evidence : StandardizedSubstitutedRewriteEvidence σ}
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hStandardize :
      evidence.standardizeApart.left.renamed =
        evidence.standardizeApart.left.expected ∧
      evidence.standardizeApart.right.renamed =
        evidence.standardizeApart.right.expected)
    (hConclusion : node.conclusion = evidence.result)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : GuardedRefutationInvariant.{x} problem valuation equalityNode)
    (hTargetInvariant : GuardedRefutationInvariant.{x} problem valuation targetNode)
    (hEqualityGuards : GuardsHold valuation node.guards →
      GuardsHold valuation equalityNode.guards)
    (hTargetGuards : GuardsHold valuation node.guards →
      GuardsHold valuation targetNode.guards) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  intro M env hProblem hGuards
  rw [hConclusion]
  let ordinary : SubstitutedRewriteEvidence σ := {
    equality := { id := evidence.equality.id, clause := evidence.equalityRenamedClause }
    target := { id := evidence.target.id, clause := evidence.targetRenamedClause }
    substitution := evidence.substitution
    context := evidence.context
    lhs := evidence.lhs
    rhs := evidence.rhs
    equalityReversed := evidence.equalityReversed
    targetPolarity := evidence.targetPolarity
  }
  have hResult := SubstitutedRewriteEvidence.satisfies_result (evidence := ordinary)
    (by
      have hSat :=
        satisfies_standardizedSubstitution_of_guardedRefutationInvariant
          (problem := problem) (valuation := valuation)
          (offset := evidence.standardizeApart.left.offset)
          (subst := evidence.substitution) (node := equalityNode)
          hAdmissible hEqualityInvariant hProblem
          (hEqualityGuards hGuards)
      simpa [StandardizedSubstitutedRewriteEvidence.equalityClause,
        StandardizedSubstitutedRewriteEvidence.equalityRenamedClause,
        StandardizedSubstitutedRewriteEvidence.equality,
        StandardizeApartEvidence.leftParent,
        StandardizeApartSideEvidence.expected, hStandardize.1, ← hEqualityClause,
        ordinary, SubstitutedRewriteEvidence.equalityClause] using hSat)
    (by
      have hSat :=
        satisfies_standardizedSubstitution_of_guardedRefutationInvariant
          (problem := problem) (valuation := valuation)
          (offset := evidence.standardizeApart.right.offset)
          (subst := evidence.substitution) (node := targetNode)
          hAdmissible hTargetInvariant hProblem
          (hTargetGuards hGuards)
      simpa [StandardizedSubstitutedRewriteEvidence.targetClause,
        StandardizedSubstitutedRewriteEvidence.targetRenamedClause,
        StandardizedSubstitutedRewriteEvidence.target,
        StandardizeApartEvidence.rightParent,
        StandardizeApartSideEvidence.expected, hStandardize.2, ← hTargetClause,
        ordinary, SubstitutedRewriteEvidence.targetClause] using hSat)
  simpa [ordinary, StandardizedSubstitutedRewriteEvidence.result,
    SubstitutedRewriteEvidence.result, StandardizedSubstitutedRewriteEvidence.needle,
    StandardizedSubstitutedRewriteEvidence.replacement, SubstitutedRewriteEvidence.needle,
    SubstitutedRewriteEvidence.replacement] using hResult

/-- 通用重写/叠加结论保持反证语义不变量。 -/
private theorem rewriteRefutationInvariant_of_conclusion {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node equalityNode targetNode : Node σ}
    {evidence : RewriteEvidence σ}
    (hConclusion : node.conclusion = evidence.result)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : RefutationInvariant.{x} problem equalityNode)
    (hTargetInvariant : RefutationInvariant.{x} problem targetNode) :
    RefutationInvariant.{x} problem node := by
  intro M env hProblem
  rw [hConclusion]
  exact RewriteEvidence.satisfies_result
    (by simpa [hEqualityClause] using hEqualityInvariant env hProblem)
    (by simpa [hTargetClause] using hTargetInvariant env hProblem)

/-- demodulation 本地规则保持反证语义不变量。 -/
theorem demodulationRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node equalityNode targetNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : RewriteEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .demodulation evidence)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : RefutationInvariant.{x} problem equalityNode)
    (hTargetInvariant : RefutationInvariant.{x} problem targetNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion (.demodulation evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.demodulation_check_conclusion hEvidenceCheck'
  intro M env hProblem
  exact (rewriteRefutationInvariant_of_conclusion hConclusion
    hEqualityClause hTargetClause hEqualityInvariant hTargetInvariant)
    (env := env) hProblem

/-- positive-superposition 本地规则保持反证语义不变量。 -/
theorem positiveSuperpositionRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node equalityNode targetNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : RewriteEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .positiveSuperposition evidence)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : RefutationInvariant.{x} problem equalityNode)
    (hTargetInvariant : RefutationInvariant.{x} problem targetNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.positiveSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.positiveSuperposition_check_conclusion hEvidenceCheck'
  intro M env hProblem
  exact (rewriteRefutationInvariant_of_conclusion hConclusion
    hEqualityClause hTargetClause hEqualityInvariant hTargetInvariant)
    (env := env) hProblem

/-- negative-superposition 本地规则保持反证语义不变量。 -/
theorem negativeSuperpositionRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {node equalityNode targetNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : RewriteEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .negativeSuperposition evidence)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityInvariant : RefutationInvariant.{x} problem equalityNode)
    (hTargetInvariant : RefutationInvariant.{x} problem targetNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    RefutationInvariant.{x} problem node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.negativeSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.negativeSuperposition_check_conclusion hEvidenceCheck'
  intro M env hProblem
  exact (rewriteRefutationInvariant_of_conclusion hConclusion
    hEqualityClause hTargetClause hEqualityInvariant hTargetInvariant)
    (env := env) hProblem

/-- resolution 本地规则保持 guarded 反证语义不变量。 -/
theorem resolutionGuardedRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {node leftNode rightNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : ResolutionEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .resolution evidence)
    (hLeftClause : evidence.left.clause = leftNode.conclusion)
    (hRightClause : evidence.right.clause = rightNode.conclusion)
    (hLeftGuards : GuardsHold valuation node.guards → GuardsHold valuation leftNode.guards)
    (hRightGuards : GuardsHold valuation node.guards → GuardsHold valuation rightNode.guards)
    (hLeftInvariant : GuardedRefutationInvariant.{x} problem valuation leftNode)
    (hRightInvariant : GuardedRefutationInvariant.{x} problem valuation rightNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion (.resolution evidence) = true := by
    simpa [LocalRuleEvidence.check, ResolutionEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.resolution_check_conclusion hEvidenceCheck'
  intro M env hProblem hGuards
  rw [hConclusion]
  exact Clause.satisfies_resolutionResult
    (by simpa [hLeftClause] using
      hLeftInvariant env hProblem (hLeftGuards hGuards))
    (by simpa [hRightClause] using
      hRightInvariant env hProblem (hRightGuards hGuards))

/-- factoring 本地规则保持 guarded 反证语义不变量。 -/
theorem factoringGuardedRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {node parentNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : FactoringEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .factoring evidence)
    (hParentClause : evidence.parent.clause = parentNode.conclusion)
    (hParentGuards : GuardsHold valuation node.guards → GuardsHold valuation parentNode.guards)
    (hParentInvariant : GuardedRefutationInvariant.{x} problem valuation parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion (.factoring evidence) = true := by
    simpa [LocalRuleEvidence.check, FactoringEvidence.check] using hEvidenceCheck
  have hCovered := LocalRuleEvidence.factoring_check_parentCovered hEvidenceCheck'
  intro M env hProblem hGuards
  apply Clause.satisfies_of_allLiteralsCovered hCovered
  simpa [hParentClause] using
    hParentInvariant env hProblem (hParentGuards hGuards)

/-- equality-resolution 本地规则保持 guarded 反证语义不变量。 -/
theorem equalityResolutionGuardedRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {node parentNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : EqualityResolutionEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .equalityResolution evidence)
    (hParentClause : evidence.parent.clause = parentNode.conclusion)
    (hParentGuards : GuardsHold valuation node.guards → GuardsHold valuation parentNode.guards)
    (hParentInvariant : GuardedRefutationInvariant.{x} problem valuation parentNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.equalityResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, EqualityResolutionEvidence.check] using
      hEvidenceCheck
  rcases LocalRuleEvidence.equalityResolution_check_sound hEvidenceCheck' with
    ⟨hTerm, hConclusion⟩
  intro M env hProblem hGuards
  rw [hConclusion]
  exact Clause.satisfies_equalityResolutionResult hTerm
    (by simpa [hParentClause] using
      hParentInvariant env hProblem (hParentGuards hGuards))

/-- 通用 guarded 重写/叠加结论保持反证语义不变量。 -/
private theorem rewriteGuardedRefutationInvariant_of_conclusion {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {node equalityNode targetNode : Node σ}
    {evidence : RewriteEvidence σ}
    (hConclusion : node.conclusion = evidence.result)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityGuards : GuardsHold valuation node.guards → GuardsHold valuation equalityNode.guards)
    (hTargetGuards : GuardsHold valuation node.guards → GuardsHold valuation targetNode.guards)
    (hEqualityInvariant : GuardedRefutationInvariant.{x} problem valuation equalityNode)
    (hTargetInvariant : GuardedRefutationInvariant.{x} problem valuation targetNode) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  intro M env hProblem hGuards
  rw [hConclusion]
  exact RewriteEvidence.satisfies_result
    (by simpa [hEqualityClause] using
      hEqualityInvariant env hProblem (hEqualityGuards hGuards))
    (by simpa [hTargetClause] using
      hTargetInvariant env hProblem (hTargetGuards hGuards))

/-- demodulation 本地规则保持 guarded 反证语义不变量。 -/
theorem demodulationGuardedRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {node equalityNode targetNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : RewriteEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .demodulation evidence)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityGuards : GuardsHold valuation node.guards → GuardsHold valuation equalityNode.guards)
    (hTargetGuards : GuardsHold valuation node.guards → GuardsHold valuation targetNode.guards)
    (hEqualityInvariant : GuardedRefutationInvariant.{x} problem valuation equalityNode)
    (hTargetInvariant : GuardedRefutationInvariant.{x} problem valuation targetNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion (.demodulation evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.demodulation_check_conclusion hEvidenceCheck'
  intro M env hProblem hGuards
  exact (rewriteGuardedRefutationInvariant_of_conclusion hConclusion
    hEqualityClause hTargetClause hEqualityGuards hTargetGuards
    hEqualityInvariant hTargetInvariant) (env := env) hProblem hGuards

/-- positive-superposition 本地规则保持 guarded 反证语义不变量。 -/
theorem positiveSuperpositionGuardedRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {node equalityNode targetNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : RewriteEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .positiveSuperposition evidence)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityGuards : GuardsHold valuation node.guards → GuardsHold valuation equalityNode.guards)
    (hTargetGuards : GuardsHold valuation node.guards → GuardsHold valuation targetNode.guards)
    (hEqualityInvariant : GuardedRefutationInvariant.{x} problem valuation equalityNode)
    (hTargetInvariant : GuardedRefutationInvariant.{x} problem valuation targetNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.positiveSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.positiveSuperposition_check_conclusion hEvidenceCheck'
  intro M env hProblem hGuards
  exact (rewriteGuardedRefutationInvariant_of_conclusion hConclusion
    hEqualityClause hTargetClause hEqualityGuards hTargetGuards
    hEqualityInvariant hTargetInvariant) (env := env) hProblem hGuards

/-- negative-superposition 本地规则保持 guarded 反证语义不变量。 -/
theorem negativeSuperpositionGuardedRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {node equalityNode targetNode : Node σ}
    {payload : LocalRulePayload σ} {evidence : RewriteEvidence σ}
    (hLocal : node.payload = .localRule payload)
    (hEvidence : payload.evidence = .negativeSuperposition evidence)
    (hEqualityClause : evidence.equality.clause = equalityNode.conclusion)
    (hTargetClause : evidence.target.clause = targetNode.conclusion)
    (hEqualityGuards : GuardsHold valuation node.guards → GuardsHold valuation equalityNode.guards)
    (hTargetGuards : GuardsHold valuation node.guards → GuardsHold valuation targetNode.guards)
    (hEqualityInvariant : GuardedRefutationInvariant.{x} problem valuation equalityNode)
    (hTargetInvariant : GuardedRefutationInvariant.{x} problem valuation targetNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hLocal] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold LocalRulePayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check node.parents node.conclusion
        (.negativeSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.negativeSuperposition_check_conclusion hEvidenceCheck'
  intro M env hProblem hGuards
  exact (rewriteGuardedRefutationInvariant_of_conclusion hConclusion
    hEqualityClause hTargetClause hEqualityGuards hTargetGuards
    hEqualityInvariant hTargetInvariant) (env := env) hProblem hGuards

/-- theory-conflict 节点保持 guarded 反证语义不变量。 -/
theorem theoryConflictGuardedRefutationInvariant_of_payload_check {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {problem : ClauseProblem σ} {valuation : PropResolution.Valuation}
    {node conflictNode : Node σ} {payload : TheoryConflictPayload σ}
    (hPayload : node.payload = .theoryConflict payload)
    (hConflictClause : payload.conflict.clause = conflictNode.conclusion)
    (hConflictGuards :
      GuardsHold valuation node.guards → GuardsHold valuation conflictNode.guards)
    (hConflictInvariant : GuardedRefutationInvariant.{x} problem valuation conflictNode)
    (hCheck : node.payload.check problem node.parents node.conclusion = true) :
    GuardedRefutationInvariant.{x} problem valuation node := by
  rw [hPayload] at hCheck
  have hPayloadCheck : payload.check node.parents node.conclusion = true := by
    simpa [Payload.check] using hCheck
  unfold TheoryConflictPayload.check at hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hPayloadCheck with ⟨hPrefix, hConclusionEmpty⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨_hParentIn, hConflictEmpty⟩
  intro M env hProblem hGuards
  have hConflictNodeEmpty : conflictNode.conclusion.isEmpty = true := by
    rw [← hConflictClause]
    exact hConflictEmpty
  have hConflictSat :=
    hConflictInvariant env hProblem (hConflictGuards hGuards)
  exact False.elim (Clause.not_satisfies_of_isEmpty hConflictNodeEmpty hConflictSat)

end Node

/-! ## Whole certificate -/

/-- 零层级大型 DAG 证书。 -/
structure DAG (σ : Signature) where
  problem : ClauseProblem σ
  root : NodeId
  nodes : Array (Node σ)

namespace DAG

/-- 通过 dense id 读取节点。 -/
def node? {σ : Signature} (dag : DAG σ) (id : NodeId) : Option (Node σ) :=
  dag.nodes[id]?

/-- 带边界证明读取节点。 -/
def nodeAt {σ : Signature} (dag : DAG σ) (index : Nat)
    (hIndex : index < dag.nodes.size) : Node σ :=
  dag.nodes[index]'hIndex

@[simp]
theorem node?_eq_some_nodeAt {σ : Signature} (dag : DAG σ) {index : Nat}
    (hIndex : index < dag.nodes.size) :
    dag.node? index = some (dag.nodeAt index hIndex) := by
  simp [node?, nodeAt]

/-- 单个父字句快照是否和 DAG 中的真实父节点结论一致。 -/
def parentSnapshotChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (parent : ParentClause σ) : Bool :=
  match dag.node? parent.id with
  | some node => node.conclusion.eq parent.clause
  | none => false

/-- 父字句快照检查通过时，可取出真实 DAG 父节点及其结论等式。 -/
theorem parentSnapshotChecked_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} {parent : ParentClause σ}
    (hChecked : dag.parentSnapshotChecked parent = true) :
    ∃ node, dag.node? parent.id = some node ∧ node.conclusion = parent.clause := by
  unfold parentSnapshotChecked at hChecked
  cases hNode : dag.node? parent.id with
  | none =>
      simp [hNode] at hChecked
  | some node =>
      have hClause : node.conclusion.eq parent.clause = true := by
        simpa [hNode] using hChecked
      exact ⟨node, rfl, Clause.eq_sound node.conclusion parent.clause hClause⟩

/-- 单个节点携带的所有父字句快照都必须和 DAG 中真实父节点一致。 -/
def nodeParentSnapshotsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (node : Node σ) : Bool :=
  node.payload.parentClauses.all fun parent => dag.parentSnapshotChecked parent

/-- 所有 payload 记录的父字句快照都必须和 DAG 中真实父节点一致。 -/
def parentSnapshotsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.all dag.nodeParentSnapshotsChecked

/-- 父字句快照检查的列表视图，供 replay 使用稳定的 checker 常量头。 -/
def parentSnapshotsListChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.toList.all dag.nodeParentSnapshotsChecked

/-- 读取父节点 guard 集。 -/
def parentGuards? {σ : Signature} (dag : DAG σ) (id : NodeId) : Option GuardSet := do
  let node ← dag.node? id
  some node.guards

/-- list 版父节点 guard 规范并集，供 checker 与 soundness 证明共同消费。 -/
def parentGuardUnionList? {σ : Signature} (dag : DAG σ) :
    List NodeId → Option GuardSet
  | [] => some #[]
  | parent :: rest => do
      let parentGuards ← dag.parentGuards? parent
      let restGuards ← parentGuardUnionList? dag rest
      some (mergeGuards parentGuards restGuards)

/--
计算一组父节点 guard 的规范并集。

这是 guarded local step 的可信边界：搜索器可以随意调度 guard，但证书 checker 必须
重新计算结论 guard 是否恰好等于所有父节点 guard 的并集。
-/
def parentGuardUnion? {σ : Signature} (dag : DAG σ) (parents : Array NodeId) :
    Option GuardSet :=
  dag.parentGuardUnionList? parents.toList

/-- 左侧 guard 在合并后仍然成立。 -/
theorem mem_canonical_mergeGuards_left {left right : GuardSet} {lit : GuardLit}
    (hMem : lit ∈ (canonicalGuards left).toList) :
    lit ∈ (canonicalGuards (mergeGuards left right)).toList := by
  have hRaw : lit ∈ left.toList :=
    mem_of_mem_propCanonicalClause hMem
  have hAppend : lit ∈ (left ++ right).toList := by
    simp [hRaw]
  have hMerged : lit ∈ (mergeGuards left right).toList := by
    simpa [mergeGuards, canonicalGuards] using
      PropResolution.mem_canonicalClause_of_mem hAppend
  exact PropResolution.mem_canonicalClause_of_mem hMerged

/-- 右侧 guard 在合并后仍然成立。 -/
theorem mem_canonical_mergeGuards_right {left right : GuardSet} {lit : GuardLit}
    (hMem : lit ∈ (canonicalGuards right).toList) :
    lit ∈ (canonicalGuards (mergeGuards left right)).toList := by
  have hRaw : lit ∈ right.toList :=
    mem_of_mem_propCanonicalClause hMem
  have hAppend : lit ∈ (left ++ right).toList := by
    simp [hRaw]
  have hMerged : lit ∈ (mergeGuards left right).toList := by
    simpa [mergeGuards, canonicalGuards] using
      PropResolution.mem_canonicalClause_of_mem hAppend
  exact PropResolution.mem_canonicalClause_of_mem hMerged

/-- 父节点出现在父边列表中时，它的 guard 会出现在计算出的父 guard 并集中。 -/
theorem mem_parentGuardUnionList_of_parent_mem {σ : Signature} {dag : DAG σ}
    {parents : List NodeId} {parent : NodeId} {parentNode : Node σ}
    {guards : GuardSet} {lit : GuardLit}
    (hUnion : dag.parentGuardUnionList? parents = some guards)
    (hParentMem : parent ∈ parents)
    (hParentNode : dag.node? parent = some parentNode)
    (hLit : lit ∈ (canonicalGuards parentNode.guards).toList) :
    lit ∈ (canonicalGuards guards).toList := by
  induction parents generalizing guards with
  | nil =>
      cases hParentMem
  | cons head rest ih =>
      simp [parentGuardUnionList?] at hUnion
      cases hHeadNode : dag.parentGuards? head with
      | none =>
          simp [hHeadNode] at hUnion
      | some headGuards =>
        cases hRestUnion : dag.parentGuardUnionList? rest with
        | none =>
            simp [hHeadNode, hRestUnion] at hUnion
        | some restGuards =>
          have hGuardsEq : guards = mergeGuards headGuards restGuards := by
            simpa [hHeadNode, hRestUnion] using hUnion.symm
          rcases List.mem_cons.mp hParentMem with hHead | hRest
          · subst hHead
            have hHeadGuards : headGuards = parentNode.guards := by
              unfold parentGuards? at hHeadNode
              rw [hParentNode] at hHeadNode
              cases hHeadNode
              rfl
            subst guards
            simpa [hHeadGuards] using
              mem_canonical_mergeGuards_left
                (left := parentNode.guards) (right := restGuards) hLit
          · subst guards
            exact mem_canonical_mergeGuards_right
              (left := headGuards) (right := restGuards)
              (ih hRestUnion hRest)

/-- 命题 learned-clause initial 必须指向已经物化的 learned 节点。 -/
def propLearnedInitialLinkOk {σ : Signature} (dag : DAG σ)
    (parents : Array NodeId) (link : PropLearnedClauseLink) : Bool :=
  parents.contains link.parent &&
    match dag.node? link.parent with
    | some parentNode =>
        match parentNode.payload with
        | .propositionalLearnedClause payload =>
            PropResolution.clauseEq link.clause payload.learned
        | _ => false
    | none => false

/-- 普通 parent initial 只能引用无 guard 的对象父字句。 -/
def propParentInitialLinkOk {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ)
    (parents : Array NodeId) (link : PropParentClauseLink σ) : Bool :=
  parents.contains link.parent.id &&
    dag.parentSnapshotChecked link.parent &&
    match dag.node? link.parent.id with
    | some parentNode => parentNode.unguarded
    | none => false

/-- guard activation initial 必须引用真实父节点的 guard 集。 -/
def propGuardActivationInitialLinkOk {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ)
    (parents : Array NodeId) (link : PropGuardActivationLink σ) : Bool :=
  parents.contains link.parent.id &&
    dag.parentSnapshotChecked link.parent &&
    match dag.node? link.parent.id with
    | some parentNode =>
        !parentNode.unguarded && guardSetEq link.guards parentNode.guards
    | none => false

/-- AVATAR skeleton initial 必须精确引用真实 split descriptor 的 selector skeleton。 -/
def propAvatarSkeletonInitialLinkOk {σ : Signature} (dag : DAG σ)
    (parents : Array NodeId) (link : PropAvatarSkeletonLink) : Bool :=
  parents.contains link.parent &&
    match dag.node? link.parent with
    | some parentNode =>
        parentNode.unguarded &&
          match parentNode.payload with
          | .avatarSplit payload =>
              PropResolution.clauseEq link.skeleton
                (PropResolution.canonicalClause payload.selectors)
          | _ => false
    | none => false

/-- initial justification 中需要整图信息的部分。 -/
def propInitialJustificationDagOk {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ)
    (parents : Array NodeId) : PropInitialJustification σ → Bool
  | .parentClause link => dag.propParentInitialLinkOk parents link
  | .propLearnedClause link => dag.propLearnedInitialLinkOk parents link
  | .guardActivationClause link => dag.propGuardActivationInitialLinkOk parents link
  | .avatarSkeleton link => dag.propAvatarSkeletonInitialLinkOk parents link

/-- CDCL 闭合节点中所有命题 learned initial 都必须和 DAG learned 节点对齐。 -/
def propInitialLinksOk {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (node : Node σ) : Bool :=
  match node.payload with
  | .residualCdcl payload =>
      payload.initialJustifications.all fun justification =>
        dag.propInitialJustificationDagOk node.parents justification
  | _ => true

/-- split descriptor 必须直接引用真实、无 guard 的 canonical source 节点。 -/
def avatarSplitNodeOk {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (node : Node σ) (payload : AvatarSplitPayload σ) : Bool :=
  node.unguarded &&
    dag.parentSnapshotChecked payload.source &&
      match dag.node? payload.source.id with
      | some sourceNode =>
          sourceNode.unguarded &&
            match sourceNode.payload with
            | .source _ => true
            | _ => false
      | none => false

/-- component 必须从父 split descriptor 的 partition 与 selector 表机械复算。 -/
def avatarComponentNodeOk {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (node : Node σ) (payload : AvatarComponentPayload σ) : Bool :=
  dag.parentSnapshotChecked payload.split &&
    match dag.node? payload.split.id with
    | some splitNode =>
        splitNode.unguarded &&
          match splitNode.payload with
          | .avatarSplit splitPayload =>
              match splitPayload.partitions[payload.componentIndex]?,
                  AvatarSplit.selectorAt? splitPayload.selectors payload.componentIndex with
              | some indices, some selector =>
                  node.conclusion.eq (Clause.atIndices splitNode.conclusion indices) &&
                    guardSetEq node.guards #[selector]
              | _, _ => false
          | _ => false
    | none => false

/-- 单个节点的 DAG 级额外结构检查。 -/
def localNodeGuardsOk {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (node : Node σ) : Bool :=
  match node.payload with
  | .avatarSplit payload =>
      dag.avatarSplitNodeOk node payload
  | .avatarComponent payload =>
      dag.avatarComponentNodeOk node payload
  | .localRule _ =>
      match dag.parentGuardUnion? node.parents with
      | some guards => guardSetEq node.guards guards
      | none => false
  | .theoryConflict _ =>
      match dag.parentGuardUnion? node.parents with
      | some guards => guardSetEq node.guards guards
      | none => false
  | .propositionalLearnedClause payload =>
      node.conclusion.isEmpty &&
        match dag.node? payload.conflict with
        | some conflictNode =>
          conflictNode.theoryConflict &&
            guardSetEq node.guards conflictNode.guards &&
              (match conflictNode.payload with
              | .theoryConflict _ =>
                  PropResolution.clauseEq payload.learned
                    (learnedClauseOfGuards conflictNode.guards)
              | _ => false)
        | none => false
  | _ => true

/-- 单个节点需要整图信息的额外结构约束。 -/
def nodeGuardsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (node : Node σ) : Bool :=
  dag.localNodeGuardsOk node && dag.propInitialLinksOk node

/-- 所有需要整图信息的额外结构约束。 -/
def guardsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.all dag.nodeGuardsChecked

/-- guard 检查的列表视图，供 replay 使用稳定的 checker 常量头。 -/
def guardsListChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.toList.all dag.nodeGuardsChecked

/-- 整图结构 checker 为真时，每个节点的 guard 局部检查都为真。 -/
theorem guardsChecked_of_eq_true {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hGuards : dag.guardsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hGuards
  have hNode :
      dag.localNodeGuardsOk (dag.nodeAt index hIndex) &&
        dag.propInitialLinksOk (dag.nodeAt index hIndex) = true := by
    simpa [guardsChecked, nodeGuardsChecked, nodeAt] using hAll index hIndex
  have hFields :
      dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true ∧
        dag.propInitialLinksOk (dag.nodeAt index hIndex) = true := by
    simpa using hNode
  exact hFields.1

/-- 整图结构 checker 为真时，CDCL learned initial 链接都已对齐。 -/
theorem propInitialLinksChecked_of_eq_true {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hGuards : dag.guardsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      dag.propInitialLinksOk (dag.nodeAt index hIndex) = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hGuards
  have hNode :
      dag.localNodeGuardsOk (dag.nodeAt index hIndex) &&
        dag.propInitialLinksOk (dag.nodeAt index hIndex) = true := by
    simpa [guardsChecked, nodeGuardsChecked, nodeAt] using hAll index hIndex
  have hFields :
      dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true ∧
        dag.propInitialLinksOk (dag.nodeAt index hIndex) = true := by
    simpa using hNode
  exact hFields.2

/-- 根节点是否存在。 -/
def rootExists {σ : Signature} (dag : DAG σ) : Bool :=
  dag.root < dag.nodes.size

/-- 根节点是否为空字句。 -/
def rootClosed {σ : Signature} (dag : DAG σ) : Bool :=
  match dag.node? dag.root with
  | some node => node.globallyClosed && node.payload.rootClosureEligible
  | none => false

/-- 单个节点编号是否与宿主数组位置一致。 -/
def denseIdChecked {σ : Signature} (index : Nat) (node : Node σ) : Bool :=
  node.id == index

/-- 节点编号是否与数组位置一致。 -/
def denseIds {σ : Signature} (dag : DAG σ) : Bool :=
  (dag.nodes.mapIdx denseIdChecked).all fun ok => ok

private theorem nat_eq_of_beq_eq_true {left right : Nat} (h : (left == right) = true) :
    left = right := by
  by_cases hEq : left = right
  · exact hEq
  · have hFalse : (left == right) = false := by
      simp [hEq]
    simp [hFalse] at h

/-- dense-id checker 为真时，每个节点的 id 等于数组位置。 -/
theorem denseIds_of_eq_true {σ : Signature} {dag : DAG σ}
    (hDense : dag.denseIds = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      (dag.nodeAt index hIndex).id = index := by
  intro index hIndex
  let checks := dag.nodes.mapIdx fun index node => node.id == index
  have hAll : ∀ index (hIndex : index < checks.size), checks[index] = true := by
    simpa [denseIds, denseIdChecked, checks] using (Array.all_eq_true.mp hDense)
  have hMapIndex : index < checks.size := by
    simpa [checks, Array.size_mapIdx] using hIndex
  have hCheck := hAll index hMapIndex
  have hGet :
      checks[index] = ((dag.nodeAt index hIndex).id == index) := by
    simp [checks, nodeAt, Array.getElem_mapIdx]
  rw [hGet] at hCheck
  exact nat_eq_of_beq_eq_true hCheck

/-- 单个节点的每条父边是否指向更早的 dense 节点。 -/
def nodeParentsBefore {σ : Signature} (index : Nat) (node : Node σ) : Bool :=
  node.parents.toList.all fun parent => decide (parent < index)

/-- 每条父边是否指向更早的 dense 节点。 -/
def parentsBefore {σ : Signature} (dag : DAG σ) : Bool :=
  (dag.nodes.mapIdx nodeParentsBefore).all fun ok => ok

/-- Prop 版父边拓扑条件。soundness 证明消费这个版本。 -/
def ParentsBefore {σ : Signature} (dag : DAG σ) : Prop :=
  ∀ index (hIndex : index < dag.nodes.size),
    ∀ parent, parent ∈ (dag.nodeAt index hIndex).parents.toList → parent < index

/-- 可计算父边 checker 推出 Prop 版拓扑条件。 -/
theorem parentsBefore_of_eq_true {σ : Signature} {dag : DAG σ}
    (hParents : dag.parentsBefore = true) : dag.ParentsBefore := by
  intro index hIndex parent hParent
  have hAll := Array.all_eq_true.mp hParents
  have hMapIndex : index < (dag.nodes.mapIdx nodeParentsBefore).size := by
    simpa using hIndex
  have hNodeCheck :
      nodeParentsBefore index (dag.nodeAt index hIndex) = true := by
    simpa [parentsBefore, nodeAt, Array.getElem_mapIdx] using
      hAll index hMapIndex
  have hParentCheck :=
    List.all_eq_true.mp hNodeCheck parent hParent
  simpa [nodeParentsBefore] using hParentCheck

/-- 所有节点 payload 是否通过结构检查。 -/
def payloadsChecked {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.nodes.all fun node => node.check dag.problem

/-- 列表逐项携带布尔 checker 证明，供大型 replay 线性组合。 -/
inductive CheckedList {α : Type} (check : α → Bool) : List α → Prop where
  | nil : CheckedList check []
  | cons {head tail} :
      check head = true →
        CheckedList check tail →
          CheckedList check (head :: tail)

namespace CheckedList

/-- 逐项证明合成列表 `all` checker。 -/
theorem all_eq_true {α : Type} {check : α → Bool} {values : List α}
    (checked : CheckedList check values) :
    values.all check = true := by
  induction checked with
  | nil => rfl
  | cons hHead _ ih =>
      exact Bool.and_eq_true_iff.mpr ⟨hHead, ih⟩

end CheckedList

/--
分块携带列表 checker 证明。

块内沿用 `CheckedList`，块间只按块数递归，供 replay 缓存有界深度的局部证明。
-/
inductive CheckedListChunks {α : Type} (check : α → Bool) : List α → Prop where
  | nil : CheckedListChunks check []
  | cons {chunk tail} :
      CheckedList check chunk →
        CheckedListChunks check tail →
          CheckedListChunks check (chunk ++ tail)
  | block {chunk tail} :
      chunk.all check = true →
        CheckedListChunks check tail →
          CheckedListChunks check (chunk ++ tail)

namespace CheckedListChunks

/-- 分块逐项证明合成列表 `all` checker。 -/
theorem all_eq_true {α : Type} {check : α → Bool} {values : List α}
    (checked : CheckedListChunks check values) :
    values.all check = true := by
  induction checked with
  | nil => rfl
  | cons hChunk _ ih =>
      simp [List.all_append, hChunk.all_eq_true, ih]
  | block hChunk _ ih =>
      simp [List.all_append, hChunk, ih]

end CheckedListChunks

/-- 带宿主索引的列表逐项携带布尔 checker 证明。 -/
inductive CheckedIndexedList {α : Type} (check : Nat → α → Bool) :
    Nat → List α → Prop where
  | nil {start} : CheckedIndexedList check start []
  | cons {start head tail} :
      check start head = true →
        CheckedIndexedList check (start + 1) tail →
          CheckedIndexedList check start (head :: tail)

namespace CheckedIndexedList

/-- 逐项索引证明合成 `mapIdx` 后的列表 `all` checker。 -/
theorem mapIdx_all_eq_true {α : Type} {check : Nat → α → Bool}
    {start : Nat} {values : List α}
    (checked : CheckedIndexedList check start values) :
    (values.mapIdx fun offset value => check (start + offset) value).all id = true := by
  induction checked with
  | nil => rfl
  | cons hHead _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Bool.and_eq_true_iff.mpr ⟨hHead, ih⟩

end CheckedIndexedList

/-- 逐节点局部 checker 证明合成 DAG 的 payload 数组检查。 -/
theorem payloadsChecked_eq_true_of_nodes {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ)
    (checked : CheckedList (fun node => node.check dag.problem) dag.nodes.toList) :
    dag.payloadsChecked = true := by
  change dag.nodes.all (fun node => node.check dag.problem) = true
  rw [← Array.all_toList]
  exact checked.all_eq_true

/-- 分块逐节点证明合成 DAG 的 payload 数组检查。 -/
theorem payloadsChecked_eq_true_of_chunks {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ)
    (checked :
      CheckedListChunks (fun node => node.check dag.problem) dag.nodes.toList) :
    dag.payloadsChecked = true := by
  change dag.nodes.all (fun node => node.check dag.problem) = true
  rw [← Array.all_toList]
  exact checked.all_eq_true

/-- 逐节点索引证明合成 DAG 的 dense-id 数组检查。 -/
theorem denseIds_eq_true_of_nodes {σ : Signature} (dag : DAG σ)
    (checked : CheckedIndexedList denseIdChecked 0 dag.nodes.toList) :
    dag.denseIds = true := by
  unfold denseIds
  rw [← Array.all_toList, Array.toList_mapIdx]
  simpa using checked.mapIdx_all_eq_true

/-- 逐节点索引证明合成 DAG 的父边拓扑数组检查。 -/
theorem parentsBefore_eq_true_of_nodes {σ : Signature} (dag : DAG σ)
    (checked : CheckedIndexedList nodeParentsBefore 0 dag.nodes.toList) :
    dag.parentsBefore = true := by
  unfold parentsBefore
  rw [← Array.all_toList, Array.toList_mapIdx]
  simpa using checked.mapIdx_all_eq_true

/-- 逐节点证明合成 DAG 的父字句快照数组检查。 -/
theorem parentSnapshotsChecked_eq_true_of_nodes {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ)
    (checked : CheckedList dag.nodeParentSnapshotsChecked dag.nodes.toList) :
    dag.parentSnapshotsChecked = true := by
  change dag.nodes.all dag.nodeParentSnapshotsChecked = true
  rw [← Array.all_toList]
  exact checked.all_eq_true

/-- 命名列表 checker 直接合成父字句快照数组检查。 -/
theorem parentSnapshotsChecked_eq_true_of_listCheck {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (checked : dag.parentSnapshotsListChecked = true) :
    dag.parentSnapshotsChecked = true := by
  unfold parentSnapshotsListChecked at checked
  unfold parentSnapshotsChecked
  rw [← Array.all_toList]
  exact checked

/-- 逐节点证明合成 DAG 的 guard 与命题 initial-link 数组检查。 -/
theorem guardsChecked_eq_true_of_nodes {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ)
    (checked : CheckedList dag.nodeGuardsChecked dag.nodes.toList) :
    dag.guardsChecked = true := by
  change dag.nodes.all dag.nodeGuardsChecked = true
  rw [← Array.all_toList]
  exact checked.all_eq_true

/-- 命名列表 checker 直接合成 guard 与命题 initial-link 数组检查。 -/
theorem guardsChecked_eq_true_of_listCheck {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) (checked : dag.guardsListChecked = true) :
    dag.guardsChecked = true := by
  unfold guardsListChecked at checked
  unfold guardsChecked
  rw [← Array.all_toList]
  exact checked

/-- DAG 中所有 source 节点引用的初始字句 slot。 -/
def sourceInitialIndices {σ : Signature} (dag : DAG σ) : Array Nat :=
  dag.nodes.filterMap fun node =>
    match node.payload with
    | .source initialIndex => some initialIndex
    | _ => none

/-- source、split 与 component 唯一性检查所需的最小 key 载荷。 -/
structure SourceUniquenessKeys where
  sourceInitialIndices : Array Nat := #[]
  splitSourceIds : Array NodeId := #[]
  componentSlots : Array (NodeId × Nat) := #[]
  deriving Repr, Inhabited, Lean.ToExpr

namespace SourceUniquenessKeys

/-- 从一个 DAG 节点收集唯一性检查所需的 key。 -/
def pushNode {σ : Signature}
    (keys : SourceUniquenessKeys) (node : Node σ) : SourceUniquenessKeys :=
  match node.payload with
  | .source initialIndex =>
      { keys with sourceInitialIndices := keys.sourceInitialIndices.push initialIndex }
  | .avatarSplit payload =>
      { keys with splitSourceIds := keys.splitSourceIds.push payload.source.id }
  | .avatarComponent payload =>
      { keys with
        componentSlots := keys.componentSlots.push (payload.split.id, payload.componentIndex) }
  | _ =>
      keys

/-- 一个有限列表是否没有重复元素。 -/
def noDuplicates {α : Type} [BEq α] : List α → Bool
  | [] => true
  | head :: tail => !tail.contains head && noDuplicates tail

/-- 抽取后的 key 是否满足 source 有界及三类 key 各自唯一。 -/
def check (keys : SourceUniquenessKeys) (sourceLimit : Nat) : Bool :=
  (keys.sourceInitialIndices.all fun index => index < sourceLimit) &&
    noDuplicates keys.sourceInitialIndices.toList &&
      noDuplicates keys.splitSourceIds.toList &&
        noDuplicates keys.componentSlots.toList

end SourceUniquenessKeys

/-- 从整张 DAG 抽取 source、split 与 component 唯一性 key。 -/
def sourceUniquenessKeys {σ : Signature} (dag : DAG σ) : SourceUniquenessKeys :=
  dag.nodes.foldl SourceUniquenessKeys.pushNode {}

/--
canonical source 与 AVATAR split/component 来源必须唯一。

每个初始字句 slot 最多一个 source；每个 source 最多一个 split descriptor；每个 split
descriptor 的 component slot 最多一个节点。
-/
def sourceIndicesUnique {σ : Signature} (dag : DAG σ) : Bool :=
  dag.sourceUniquenessKeys.check dag.problem.initialClauses.size

/-- 抽取 key 的等式与小型 key checker 合成 DAG source 唯一性检查。 -/
theorem sourceIndicesUnique_eq_true_of_keys {σ : Signature}
    (dag : DAG σ) (keys : SourceUniquenessKeys)
    (hKeys : dag.sourceUniquenessKeys = keys)
    (hCheck : keys.check dag.problem.initialClauses.size = true) :
    dag.sourceIndicesUnique = true := by
  simpa [sourceIndicesUnique, hKeys] using hCheck

/-- DAG 中每个节点是否都落在当前已证明 soundness 的 payload 片段中。 -/
def soundnessSupported {σ : Signature} (dag : DAG σ) : Bool :=
  dag.nodes.all fun node => node.soundnessSupported

/-- DAG 中每个节点是否都落在当前已证明 guarded soundness 的 payload 片段中。 -/
def guardedSoundnessSupported {σ : Signature} (dag : DAG σ) : Bool :=
  dag.nodes.all fun node => node.guardedSoundnessSupported

/-- payload checker 为真时，每个节点的局部检查都为真。 -/
theorem payloadsChecked_of_eq_true {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hPayloads : dag.payloadsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      (dag.nodeAt index hIndex).check dag.problem = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hPayloads
  simpa [payloadsChecked, nodeAt] using hAll index hIndex

/-- soundness 支持片段 checker 为真时，每个节点都落在该片段中。 -/
theorem soundnessSupported_of_eq_true {σ : Signature} {dag : DAG σ}
    (hSupported : dag.soundnessSupported = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      (dag.nodeAt index hIndex).payload.soundnessSupported = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hSupported
  have hNode : (dag.nodeAt index hIndex).soundnessSupported = true := by
    simpa [soundnessSupported, nodeAt] using hAll index hIndex
  have hFields :
      (dag.nodeAt index hIndex).unguarded = true ∧
        (dag.nodeAt index hIndex).payload.soundnessSupported = true := by
    simpa [Node.soundnessSupported] using hNode
  exact hFields.2

/-- guarded soundness 支持片段 checker 为真时，每个节点都落在该片段中。 -/
theorem guardedSoundnessSupported_of_eq_true {σ : Signature} {dag : DAG σ}
    (hSupported : dag.guardedSoundnessSupported = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      (dag.nodeAt index hIndex).payload.guardedSoundnessSupported = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hSupported
  have hNode : (dag.nodeAt index hIndex).guardedSoundnessSupported = true := by
    simpa [guardedSoundnessSupported, nodeAt] using hAll index hIndex
  simpa [Node.guardedSoundnessSupported] using hNode

/-- soundness 支持片段 checker 为真时，每个节点都没有 AVATAR guard。 -/
theorem nodeUnguarded_of_soundnessSupported_eq_true {σ : Signature} {dag : DAG σ}
    (hSupported : dag.soundnessSupported = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      (dag.nodeAt index hIndex).unguarded = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hSupported
  have hNode : (dag.nodeAt index hIndex).soundnessSupported = true := by
    simpa [soundnessSupported, nodeAt] using hAll index hIndex
  have hFields :
      (dag.nodeAt index hIndex).unguarded = true ∧
        (dag.nodeAt index hIndex).payload.soundnessSupported = true := by
    simpa [Node.soundnessSupported] using hNode
  exact hFields.1

/-- DAG 中所有带 guard 的节点。 -/
def guardedNodes {σ : Signature} (dag : DAG σ) : Array (Node σ) :=
  dag.nodes.filter fun node => !node.unguarded

/-- DAG 中已经材料化的 AVATAR theory conflicts。 -/
def theoryConflicts {σ : Signature} (dag : DAG σ) : Array (Node σ) :=
  dag.nodes.filter Node.theoryConflict

/-- DAG 中已经材料化的命题 learned clause 节点。 -/
def propositionalLearnedClauses {σ : Signature} (dag : DAG σ) : Array (Node σ) :=
  dag.nodes.filter fun node =>
    match node.payload with
    | .propositionalLearnedClause _ => true
    | _ => false

/-- DAG 结构 checker。 -/
def check {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Bool :=
  dag.rootExists && dag.rootClosed && dag.denseIds && dag.parentsBefore &&
    dag.payloadsChecked && dag.parentSnapshotsChecked && dag.guardsChecked &&
      dag.sourceIndicesUnique

/-- 八个命名结构检查的证明合成整张 DAG checker。 -/
theorem check_eq_true_of_components {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ)
    (hRootExists : dag.rootExists = true)
    (hRootClosed : dag.rootClosed = true)
    (hDenseIds : dag.denseIds = true)
    (hParentsBefore : dag.parentsBefore = true)
    (hPayloadsChecked : dag.payloadsChecked = true)
    (hParentSnapshotsChecked : dag.parentSnapshotsChecked = true)
    (hGuardsChecked : dag.guardsChecked = true)
    (hSourceIndicesUnique : dag.sourceIndicesUnique = true) :
    dag.check = true :=
  Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr
        ⟨Bool.and_eq_true_iff.mpr
          ⟨Bool.and_eq_true_iff.mpr
            ⟨Bool.and_eq_true_iff.mpr
              ⟨Bool.and_eq_true_iff.mpr ⟨hRootExists, hRootClosed⟩, hDenseIds⟩,
              hParentsBefore⟩,
            hPayloadsChecked⟩,
          hParentSnapshotsChecked⟩,
        hGuardsChecked⟩,
      hSourceIndicesUnique⟩

/-- 当前 DAG 的公共组合证书摘要。 -/
def toComposite {σ : Signature} (dag : DAG σ) : Certificate.Composite :=
  {
    root := dag.root
    nodes := dag.nodes.map Node.toPublicNode
    residuals := dag.nodes.filterMap fun node =>
      match node.payload with
      | .residualCdcl _ => some node.id
      | _ => none
  }

/-- DAG 摘要。 -/
def summary {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : String :=
  s!"root={dag.root}; nodes={dag.nodes.size}; check={dag.check}; " ++
    s!"rootClosed={dag.rootClosed}; dense={dag.denseIds}; parentsBefore={dag.parentsBefore}; " ++
      s!"parentSnapshots={dag.parentSnapshotsChecked}; guards={dag.guardsChecked}; " ++
        s!"sourceUnique={dag.sourceIndicesUnique}"

/--
拓扑归纳骨架。

若每个节点的性质只需要假设其父节点性质，并且 `ParentsBefore` 保证父节点都位于
当前节点之前，则性质可按数组顺序推广到整张 DAG。
-/
theorem topologicalInduction {σ : Signature} (dag : DAG σ) (hParents : dag.ParentsBefore)
    {P : ∀ index, index < dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < dag.nodes.size),
        (∀ parent (hParent : parent ∈ (dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex)
              (dag.nodeAt parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (dag.nodeAt index hIndex)) :
    ∀ index (hIndex : index < dag.nodes.size),
      P index hIndex (dag.nodeAt index hIndex) := by
  have hAll :
      ∀ index (hIndex : index < dag.nodes.size),
        P index hIndex (dag.nodeAt index hIndex) := by
    intro index
    refine Nat.strongRecOn index ?_
    intro index ih hIndex
    exact hStep index hIndex (fun parent hParent =>
      let hParentLt := hParents index hIndex parent hParent
      let hParentSize := Nat.lt_trans hParentLt hIndex
      ih parent hParentLt hParentSize)
  exact hAll

/-- 根节点版本的拓扑归纳骨架。 -/
theorem rootByTopologicalInduction {σ : Signature} (dag : DAG σ)
    (hRoot : dag.root < dag.nodes.size) (hParents : dag.ParentsBefore)
    {P : ∀ index, index < dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < dag.nodes.size),
        (∀ parent (hParent : parent ∈ (dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex)
              (dag.nodeAt parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (dag.nodeAt index hIndex)) :
    P dag.root hRoot (dag.nodeAt dag.root hRoot) :=
  dag.topologicalInduction hParents hStep dag.root hRoot

end DAG

namespace DAG

/--
整张 DAG 的反证语义不变量。

它要求每个节点都满足 `Node.RefutationInvariant`；后续拓扑归纳将把 source / local /
ground / residual 的局部 soundness 统一接到这里。
-/
def RefutationInvariant {σ : Signature} [DecidableEq σ.SortSymbol] (dag : DAG σ) : Prop :=
  ∀ index (hIndex : index < dag.nodes.size),
    Node.RefutationInvariant.{x} (σ := σ) dag.problem (dag.nodeAt index hIndex)

/-- 整张 DAG 的 guarded 反证语义不变量。 -/
def GuardedRefutationInvariant {σ : Signature} [DecidableEq σ.SortSymbol]
    (dag : DAG σ) (valuation : PropResolution.Valuation) : Prop :=
  ∀ index (hIndex : index < dag.nodes.size),
    Node.GuardedRefutationInvariant.{x} (σ := σ) dag.problem valuation
      (dag.nodeAt index hIndex)

end DAG

/-- 已通过结构 checker 的大型 DAG。 -/
structure CheckedDAG {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] where
  dag : DAG σ
  checked : dag.check = true

namespace CheckedDAG

/-- 从未检查 DAG 计算式构造 checked DAG。 -/
def mk? {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ) : Option (CheckedDAG (σ := σ)) :=
  if h : dag.check = true then
    some { dag := dag, checked := h }
  else
    none

/-- checked DAG 对应的原生初始字句问题。 -/
def problem {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) : ClauseProblem σ :=
  cert.dag.problem

/-- checked DAG 的公共组合证书摘要。 -/
def toComposite {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) : Certificate.Composite :=
  cert.dag.toComposite

private theorem check_implies_rootExists_bool {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hCheck : dag.check = true) : dag.rootExists = true := by
  have hFields :
      ((((((dag.rootExists = true ∧ dag.rootClosed = true) ∧ dag.denseIds = true) ∧
        dag.parentsBefore = true) ∧ dag.payloadsChecked = true) ∧
          dag.parentSnapshotsChecked = true) ∧ dag.guardsChecked = true) ∧
            dag.sourceIndicesUnique = true := by
    simpa [DAG.check] using hCheck
  exact hFields.1.1.1.1.1.1.1

private theorem check_implies_rootClosed_bool {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hCheck : dag.check = true) : dag.rootClosed = true := by
  have hFields :
      ((((((dag.rootExists = true ∧ dag.rootClosed = true) ∧ dag.denseIds = true) ∧
        dag.parentsBefore = true) ∧ dag.payloadsChecked = true) ∧
          dag.parentSnapshotsChecked = true) ∧ dag.guardsChecked = true) ∧
            dag.sourceIndicesUnique = true := by
    simpa [DAG.check] using hCheck
  exact hFields.1.1.1.1.1.1.2

private theorem check_implies_denseIds_bool {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hCheck : dag.check = true) : dag.denseIds = true := by
  have hFields :
      ((((((dag.rootExists = true ∧ dag.rootClosed = true) ∧ dag.denseIds = true) ∧
        dag.parentsBefore = true) ∧ dag.payloadsChecked = true) ∧
          dag.parentSnapshotsChecked = true) ∧ dag.guardsChecked = true) ∧
            dag.sourceIndicesUnique = true := by
    simpa [DAG.check] using hCheck
  exact hFields.1.1.1.1.1.2

private theorem check_implies_parentsBefore_bool {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hCheck : dag.check = true) : dag.parentsBefore = true := by
  have hFields :
      ((((((dag.rootExists = true ∧ dag.rootClosed = true) ∧ dag.denseIds = true) ∧
        dag.parentsBefore = true) ∧ dag.payloadsChecked = true) ∧
          dag.parentSnapshotsChecked = true) ∧ dag.guardsChecked = true) ∧
            dag.sourceIndicesUnique = true := by
    simpa [DAG.check] using hCheck
  exact hFields.1.1.1.1.2

private theorem check_implies_payloadsChecked_bool {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hCheck : dag.check = true) : dag.payloadsChecked = true := by
  have hFields :
      ((((((dag.rootExists = true ∧ dag.rootClosed = true) ∧ dag.denseIds = true) ∧
        dag.parentsBefore = true) ∧ dag.payloadsChecked = true) ∧
          dag.parentSnapshotsChecked = true) ∧ dag.guardsChecked = true) ∧
            dag.sourceIndicesUnique = true := by
    simpa [DAG.check] using hCheck
  exact hFields.1.1.1.2

private theorem check_implies_parentSnapshotsChecked_bool {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hCheck : dag.check = true) : dag.parentSnapshotsChecked = true := by
  have hFields :
      ((((((dag.rootExists = true ∧ dag.rootClosed = true) ∧ dag.denseIds = true) ∧
        dag.parentsBefore = true) ∧ dag.payloadsChecked = true) ∧
          dag.parentSnapshotsChecked = true) ∧ dag.guardsChecked = true) ∧
            dag.sourceIndicesUnique = true := by
    simpa [DAG.check] using hCheck
  exact hFields.1.1.2

private theorem check_implies_guardsChecked_bool {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hCheck : dag.check = true) : dag.guardsChecked = true := by
  have hFields :
      ((((((dag.rootExists = true ∧ dag.rootClosed = true) ∧ dag.denseIds = true) ∧
        dag.parentsBefore = true) ∧ dag.payloadsChecked = true) ∧
          dag.parentSnapshotsChecked = true) ∧ dag.guardsChecked = true) ∧
            dag.sourceIndicesUnique = true := by
    simpa [DAG.check] using hCheck
  exact hFields.1.2

private theorem check_implies_sourceIndicesUnique_bool {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} (hCheck : dag.check = true) : dag.sourceIndicesUnique = true := by
  have hFields :
      ((((((dag.rootExists = true ∧ dag.rootClosed = true) ∧ dag.denseIds = true) ∧
        dag.parentsBefore = true) ∧ dag.payloadsChecked = true) ∧
          dag.parentSnapshotsChecked = true) ∧ dag.guardsChecked = true) ∧
            dag.sourceIndicesUnique = true := by
    simpa [DAG.check] using hCheck
  exact hFields.2

/-- checked DAG 的根节点存在性。 -/
theorem rootExists {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    cert.dag.root < cert.dag.nodes.size := by
  have hRootBool := check_implies_rootExists_bool cert.checked
  simpa [DAG.rootExists] using hRootBool

/-- checked DAG 的根节点闭合检查。 -/
theorem rootClosed {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    cert.dag.rootClosed = true :=
  check_implies_rootClosed_bool cert.checked

/-- checked DAG 的根节点结论是空字句。 -/
theorem rootNodeClosed {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    (cert.dag.nodeAt cert.dag.root cert.rootExists).conclusion.isEmpty = true := by
  have hClosed :
      (cert.dag.nodeAt cert.dag.root cert.rootExists).globallyClosed = true := by
    have hFields :
        (cert.dag.nodeAt cert.dag.root cert.rootExists).globallyClosed = true ∧
          (cert.dag.nodeAt cert.dag.root cert.rootExists).payload.rootClosureEligible = true := by
      simpa [DAG.rootClosed, cert.dag.node?_eq_some_nodeAt cert.rootExists] using
        cert.rootClosed
    exact hFields.1
  have hFields :
      (cert.dag.nodeAt cert.dag.root cert.rootExists).unguarded = true ∧
        (cert.dag.nodeAt cert.dag.root cert.rootExists).conclusion.isEmpty = true := by
    simpa [Node.globallyClosed, Node.guardedConclusion, GuardedClause.globallyEmpty,
      GuardedClause.unguarded, Node.unguarded] using hClosed
  exact hFields.2

/-- checked DAG 的根节点没有 AVATAR guard。 -/
theorem rootNodeUnguarded {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    (cert.dag.nodeAt cert.dag.root cert.rootExists).unguarded = true := by
  have hClosed :
      (cert.dag.nodeAt cert.dag.root cert.rootExists).globallyClosed = true := by
    have hFields :
        (cert.dag.nodeAt cert.dag.root cert.rootExists).globallyClosed = true ∧
          (cert.dag.nodeAt cert.dag.root cert.rootExists).payload.rootClosureEligible = true := by
      simpa [DAG.rootClosed, cert.dag.node?_eq_some_nodeAt cert.rootExists] using
        cert.rootClosed
    exact hFields.1
  have hFields :
      (cert.dag.nodeAt cert.dag.root cert.rootExists).unguarded = true ∧
        (cert.dag.nodeAt cert.dag.root cert.rootExists).conclusion.isEmpty = true := by
    simpa [Node.globallyClosed, Node.guardedConclusion, GuardedClause.globallyEmpty,
      GuardedClause.unguarded, Node.unguarded] using hClosed
  exact hFields.1

/-- checked DAG 的 dense-id 检查。 -/
theorem denseIds {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    cert.dag.denseIds = true :=
  check_implies_denseIds_bool cert.checked

/-- checked DAG 中每个节点的 id 等于数组位置。 -/
theorem nodeId {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).id = index :=
  DAG.denseIds_of_eq_true cert.denseIds index hIndex

/-- checked DAG 的 Prop 版父边拓扑条件。 -/
theorem parentsBefore {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    cert.dag.ParentsBefore :=
  DAG.parentsBefore_of_eq_true (check_implies_parentsBefore_bool cert.checked)

/-- checked DAG 的 payload 全检布尔条件。 -/
theorem payloadsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    cert.dag.payloadsChecked = true :=
  check_implies_payloadsChecked_bool cert.checked

/-- checked DAG 的父字句快照全检布尔条件。 -/
theorem parentSnapshotsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    cert.dag.parentSnapshotsChecked = true :=
  check_implies_parentSnapshotsChecked_bool cert.checked

/-- checked DAG 的 guard 合并全检布尔条件。 -/
theorem guardsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    cert.dag.guardsChecked = true :=
  check_implies_guardsChecked_bool cert.checked

/-- checked DAG 中每个 initial slot 至多有一个 source 节点。 -/
theorem sourceIndicesUnique {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    cert.dag.sourceIndicesUnique = true :=
  check_implies_sourceIndicesUnique_bool cert.checked

/-- checked DAG 中每个节点的局部检查都通过。 -/
theorem nodeChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).check cert.dag.problem = true :=
  DAG.payloadsChecked_of_eq_true cert.payloadsChecked index hIndex

/-- checked DAG 中每个节点的规则标签检查都通过。 -/
theorem nodeRuleTagsOk {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).ruleTagsOk = true :=
  Node.ruleTagsOk_of_check_eq_true (cert.nodeChecked index hIndex)

/-- checked DAG 中每个节点的 payload 检查都通过。 -/
theorem nodePayloadChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).payload.check cert.dag.problem
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true :=
  Node.payload_check_of_check_eq_true (cert.nodeChecked index hIndex)

/-- checked DAG 中每个节点的 guard 局部检查都通过。 -/
theorem nodeGuardsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    cert.dag.localNodeGuardsOk (cert.dag.nodeAt index hIndex) = true :=
  DAG.guardsChecked_of_eq_true cert.guardsChecked index hIndex

/-- checked DAG 中每个 CDCL learned initial 链接都已经和 learned 节点对齐。 -/
theorem nodePropInitialLinksChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    cert.dag.propInitialLinksOk (cert.dag.nodeAt index hIndex) = true :=
  DAG.propInitialLinksChecked_of_eq_true cert.guardsChecked index hIndex

/-- checked DAG 中指定节点落在当前已证明 soundness 的 payload 片段。 -/
theorem nodeSoundnessSupported {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (hSupported : cert.dag.soundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).payload.soundnessSupported = true :=
  DAG.soundnessSupported_of_eq_true hSupported index hIndex

/-- checked DAG 中指定节点落在当前已证明 guarded soundness 的 payload 片段。 -/
theorem nodeGuardedSoundnessSupported {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size) :
    (cert.dag.nodeAt index hIndex).payload.guardedSoundnessSupported = true :=
  DAG.guardedSoundnessSupported_of_eq_true hSupported index hIndex

/-- 本地规则节点的 guard checker 给出当前 guard 到父 guard 的传递。 -/
theorem parentGuardsHold_of_localNodeGuardsOk {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (parent : NodeId)
    (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentSize : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation} :
    Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
      Node.GuardsHold valuation (cert.dag.nodeAt parent hParentSize).guards := by
  have hGuardCheck := cert.nodeGuardsChecked index hIndex
  unfold DAG.localNodeGuardsOk at hGuardCheck
  rw [hLocal] at hGuardCheck
  cases hUnion :
      cert.dag.parentGuardUnion? (cert.dag.nodeAt index hIndex).parents with
  | none =>
      simp [hUnion] at hGuardCheck
  | some unionGuards =>
      have hEq :
          guardSetEq (cert.dag.nodeAt index hIndex).guards unionGuards = true := by
        simpa [hUnion] using hGuardCheck
      intro hCurrentGuards
      have hUnionGuards : Node.GuardsHold valuation unionGuards :=
        Node.GuardsHold.of_guardSetEq hEq hCurrentGuards
      intro lit hLit
      exact hUnionGuards lit
        (DAG.mem_parentGuardUnionList_of_parent_mem
          (dag := cert.dag)
          (parents := (cert.dag.nodeAt index hIndex).parents.toList)
          (parent := parent)
          (parentNode := cert.dag.nodeAt parent hParentSize)
          (guards := unionGuards)
          (lit := lit)
          (by simpa [DAG.parentGuardUnion?] using hUnion)
          hParentMem
          (cert.dag.node?_eq_some_nodeAt hParentSize)
          hLit)

/-- theory-conflict 节点的 guard checker 给出当前 guard 到父 conflict guard 的传递。 -/
theorem parentGuardsHold_of_theoryConflictNodeGuardsOk {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : TheoryConflictPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload)
    (parent : NodeId)
    (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentSize : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation} :
    Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
      Node.GuardsHold valuation (cert.dag.nodeAt parent hParentSize).guards := by
  have hGuardCheck := cert.nodeGuardsChecked index hIndex
  unfold DAG.localNodeGuardsOk at hGuardCheck
  rw [hPayload] at hGuardCheck
  cases hUnion :
      cert.dag.parentGuardUnion? (cert.dag.nodeAt index hIndex).parents with
  | none =>
      simp [hUnion] at hGuardCheck
  | some unionGuards =>
      have hEq :
          guardSetEq (cert.dag.nodeAt index hIndex).guards unionGuards = true := by
        simpa [hUnion] using hGuardCheck
      intro hCurrentGuards
      have hUnionGuards : Node.GuardsHold valuation unionGuards :=
        Node.GuardsHold.of_guardSetEq hEq hCurrentGuards
      intro lit hLit
      exact hUnionGuards lit
        (DAG.mem_parentGuardUnionList_of_parent_mem
          (dag := cert.dag)
          (parents := (cert.dag.nodeAt index hIndex).parents.toList)
          (parent := parent)
          (parentNode := cert.dag.nodeAt parent hParentSize)
          (guards := unionGuards)
          (lit := lit)
          (by simpa [DAG.parentGuardUnion?] using hUnion)
          hParentMem
          (cert.dag.node?_eq_some_nodeAt hParentSize)
          hLit)

/--
checked DAG 拓扑 step 的 source 分支。

父节点不变量在 source 分支中不会被使用；保留该参数是为了让本定理能直接嵌入后续
统一 `topologicalInduction` 的 step 形状。
-/
theorem sourceTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (_hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (initialIndex : Nat)
    (hSource : (cert.dag.nodeAt index hIndex).payload = .source initialIndex) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) :=
  Node.sourceRefutationInvariant_of_payload_check hSource
    (cert.nodePayloadChecked index hIndex)

/-- checked DAG 中 parent-copy evidence 的父字句快照已经和真实父节点对齐。 -/
theorem parentCopySnapshotChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (parent : ParentClause σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .parentCopy parent) :
    cert.dag.parentSnapshotChecked parent = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  simpa [Payload.parentClauses, LocalRulePayload.parentClauses,
    LocalRuleEvidence.parentClauses, hEvidence] using hNode

/-- checked DAG 中 theory-conflict payload 的父字句快照已经和真实父节点对齐。 -/
theorem theoryConflictSnapshotChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : TheoryConflictPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload) :
    cert.dag.parentSnapshotChecked payload.conflict = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hPayload] at hNode
  simpa [Payload.parentClauses, TheoryConflictPayload.parentClauses] using hNode

/-- checked DAG 中 resolution evidence 的父字句快照已经和真实父节点对齐。 -/
theorem resolutionSnapshotsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : ResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .resolution evidence) :
    cert.dag.parentSnapshotChecked evidence.left = true ∧
      cert.dag.parentSnapshotChecked evidence.right = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  have hBoth :
      (cert.dag.parentSnapshotChecked evidence.left &&
        cert.dag.parentSnapshotChecked evidence.right) = true := by
    simpa [Payload.parentClauses, LocalRulePayload.parentClauses,
      LocalRuleEvidence.parentClauses, hEvidence] using hNode
  exact Bool.and_eq_true_iff.mp hBoth

/-- checked DAG 中 substituted resolution evidence 的父字句快照已经和真实父节点对齐。 -/
theorem substitutedResolutionSnapshotsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : SubstitutedResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedResolution evidence) :
    cert.dag.parentSnapshotChecked evidence.left = true ∧
      cert.dag.parentSnapshotChecked evidence.right = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  have hBoth :
      (cert.dag.parentSnapshotChecked evidence.left &&
        cert.dag.parentSnapshotChecked evidence.right) = true := by
    simpa [Payload.parentClauses, LocalRulePayload.parentClauses,
      LocalRuleEvidence.parentClauses, hEvidence] using hNode
  exact Bool.and_eq_true_iff.mp hBoth

/-- checked DAG 中 standardized resolution evidence 的父字句快照已经对齐。 -/
theorem standardizedResolutionSnapshotsChecked {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .standardizedSubstitutedResolution evidence) :
    cert.dag.parentSnapshotChecked evidence.left = true ∧
      cert.dag.parentSnapshotChecked evidence.right = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  have hBoth :
      (cert.dag.parentSnapshotChecked evidence.left &&
        cert.dag.parentSnapshotChecked evidence.right) = true := by
    simpa [Payload.parentClauses, LocalRulePayload.parentClauses,
      LocalRuleEvidence.parentClauses, hEvidence] using hNode
  exact Bool.and_eq_true_iff.mp hBoth

/-- checked DAG 中 factoring evidence 的父字句快照已经和真实父节点对齐。 -/
theorem factoringSnapshotChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : FactoringEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .factoring evidence) :
    cert.dag.parentSnapshotChecked evidence.parent = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  simpa [Payload.parentClauses, LocalRulePayload.parentClauses,
    LocalRuleEvidence.parentClauses, hEvidence] using hNode

/-- checked DAG 中 substituted factoring evidence 的父字句快照已经和真实父节点对齐。 -/
theorem substitutedFactoringSnapshotChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : SubstitutedFactoringEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedFactoring evidence) :
    cert.dag.parentSnapshotChecked evidence.parent = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  simpa [Payload.parentClauses, LocalRulePayload.parentClauses,
    LocalRuleEvidence.parentClauses, hEvidence] using hNode

/-- checked DAG 中 equality-resolution evidence 的父字句快照已经和真实父节点对齐。 -/
theorem equalityResolutionSnapshotChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : EqualityResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .equalityResolution evidence) :
    cert.dag.parentSnapshotChecked evidence.parent = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  simpa [Payload.parentClauses, LocalRulePayload.parentClauses,
    LocalRuleEvidence.parentClauses, hEvidence] using hNode

/-- checked DAG 中 substituted equality-resolution evidence 的父字句快照已经和真实父节点对齐。 -/
theorem substitutedEqualityResolutionSnapshotChecked {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : SubstitutedEqualityResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedEqualityResolution evidence) :
    cert.dag.parentSnapshotChecked evidence.parent = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  simpa [Payload.parentClauses, LocalRulePayload.parentClauses,
    LocalRuleEvidence.parentClauses, hEvidence] using hNode

/-- checked DAG 中 substituted rewrite/superposition evidence 的父字句快照已经和真实父节点对齐。 -/
theorem substitutedRewriteSnapshotsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : SubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    cert.dag.parentSnapshotChecked evidence.equality = true ∧
      cert.dag.parentSnapshotChecked evidence.target = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  have hBoth :
      (cert.dag.parentSnapshotChecked evidence.equality &&
        cert.dag.parentSnapshotChecked evidence.target) = true := by
    simpa [Payload.parentClauses, LocalRulePayload.parentClauses, hParentClauses] using hNode
  exact Bool.and_eq_true_iff.mp hBoth

/-- checked DAG 中 standardized rewrite evidence 的父字句快照已经对齐。 -/
theorem standardizedRewriteSnapshotsChecked {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    cert.dag.parentSnapshotChecked evidence.equality = true ∧
      cert.dag.parentSnapshotChecked evidence.target = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  have hBoth :
      (cert.dag.parentSnapshotChecked evidence.equality &&
        cert.dag.parentSnapshotChecked evidence.target) = true := by
    simpa [Payload.parentClauses, LocalRulePayload.parentClauses, hParentClauses] using hNode
  exact Bool.and_eq_true_iff.mp hBoth

/-- checked DAG 中重写/叠加 evidence 的两个父字句快照已经和真实父节点对齐。 -/
theorem rewriteSnapshotsChecked {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ) (evidence : RewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    cert.dag.parentSnapshotChecked evidence.equality = true ∧
      cert.dag.parentSnapshotChecked evidence.target = true := by
  have hAllNodes := Array.all_eq_true.mp cert.parentSnapshotsChecked
  have hNode :
      ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hNode
  have hBoth :
      (cert.dag.parentSnapshotChecked evidence.equality &&
        cert.dag.parentSnapshotChecked evidence.target) = true := by
    simpa [Payload.parentClauses, LocalRulePayload.parentClauses, hParentClauses] using hNode
  exact Bool.and_eq_true_iff.mp hBoth

/-- 父字句快照布尔检查给出快照字句和真实父节点结论的一致性。 -/
theorem parentClause_eq_nodeAt_of_snapshot {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (parent : ParentClause σ) (hParentSize : parent.id < cert.dag.nodes.size)
    (hSnapshot : cert.dag.parentSnapshotChecked parent = true) :
    parent.clause = (cert.dag.nodeAt parent.id hParentSize).conclusion := by
  rcases DAG.parentSnapshotChecked_sound hSnapshot with
    ⟨snapshotNode, hSnapshotNode, hSnapshotClause⟩
  have hSnapshotNodeEq : snapshotNode = cert.dag.nodeAt parent.id hParentSize := by
    rw [cert.dag.node?_eq_some_nodeAt hParentSize] at hSnapshotNode
    cases hSnapshotNode
    rfl
  have hSnapshotClause' :
      (cert.dag.nodeAt parent.id hParentSize).conclusion = parent.clause := by
    simpa [hSnapshotNodeEq] using hSnapshotClause
  exact hSnapshotClause'.symm

/-- checked DAG 拓扑 step 的 parent-copy 本地规则分支。 -/
theorem localRuleParentCopyTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (parent : ParentClause σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .parentCopy parent) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  rcases LocalRuleEvidence.parentCopy_check_sound hEvidenceCheck with
    ⟨hParentInBool, hConclusion⟩
  have hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentInBool
  let hParentLt := cert.parentsBefore index hIndex parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt parent.id hParentSize) :=
    hParents parent.id hParentMem
  have hSnapshotBool :=
    cert.parentCopySnapshotChecked index hIndex payload parent hLocal hEvidence
  rcases DAG.parentSnapshotChecked_sound hSnapshotBool with
    ⟨snapshotNode, hSnapshotNode, hSnapshotClause⟩
  have hSnapshotNodeEq : snapshotNode = cert.dag.nodeAt parent.id hParentSize := by
    rw [cert.dag.node?_eq_some_nodeAt hParentSize] at hSnapshotNode
    cases hSnapshotNode
    rfl
  have hParentClause : parent.clause =
      (cert.dag.nodeAt parent.id hParentSize).conclusion := by
    have hSnapshotClause' :
        (cert.dag.nodeAt parent.id hParentSize).conclusion = parent.clause := by
      simpa [hSnapshotNodeEq] using hSnapshotClause
    exact hSnapshotClause'.symm
  intro M env hProblem
  rw [hConclusion, hParentClause]
  exact hParentInvariant env hProblem

/-- checked DAG 拓扑 step 的 resolution 本地规则分支。 -/
theorem resolutionTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : ResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .resolution evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.resolution evidence) = true := by
    simpa [LocalRuleEvidence.check, ResolutionEvidence.check] using hEvidenceCheck
  have hIds := LocalRuleEvidence.resolution_check_parents hEvidenceCheck'
  have hSnapshots :=
    cert.resolutionSnapshotsChecked index hIndex payload evidence hLocal hEvidence
  have hLeftMem : evidence.left.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hRightMem : evidence.right.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hLeftLt := cert.parentsBefore index hIndex evidence.left.id hLeftMem
  let hRightLt := cert.parentsBefore index hIndex evidence.right.id hRightMem
  let hLeftSize := Nat.lt_trans hLeftLt hIndex
  let hRightSize := Nat.lt_trans hRightLt hIndex
  have hLeftClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.left hLeftSize hSnapshots.1
  have hRightClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.right hRightSize hSnapshots.2
  have hLeftInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.left.id hLeftSize) :=
    hParents evidence.left.id hLeftMem
  have hRightInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.right.id hRightSize) :=
    hParents evidence.right.id hRightMem
  intro M env hProblem
  exact (Node.resolutionRefutationInvariant_of_payload_check
    (problem := cert.dag.problem)
    (node := cert.dag.nodeAt index hIndex)
    (leftNode := cert.dag.nodeAt evidence.left.id hLeftSize)
    (rightNode := cert.dag.nodeAt evidence.right.id hRightSize)
    hLocal hEvidence hLeftClause hRightClause hLeftInvariant hRightInvariant
    (cert.nodePayloadChecked index hIndex)) (env := env) hProblem

/-- checked DAG 拓扑 step 的 factoring 本地规则分支。 -/
theorem factoringTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : FactoringEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .factoring evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.factoring evidence) = true := by
    simpa [LocalRuleEvidence.check, FactoringEvidence.check] using hEvidenceCheck
  have hParentIn := LocalRuleEvidence.factoring_check_parent hEvidenceCheck'
  have hSnapshot :=
    cert.factoringSnapshotChecked index hIndex payload evidence hLocal hEvidence
  have hParentMem : evidence.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.parentsBefore index hIndex evidence.parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.parent hParentSize hSnapshot
  have hParentInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.parent.id hParentSize) :=
    hParents evidence.parent.id hParentMem
  intro M env hProblem
  exact (Node.factoringRefutationInvariant_of_payload_check
    (problem := cert.dag.problem)
    (node := cert.dag.nodeAt index hIndex)
    (parentNode := cert.dag.nodeAt evidence.parent.id hParentSize)
    hLocal hEvidence hParentClause hParentInvariant
    (cert.nodePayloadChecked index hIndex)) (env := env) hProblem

/-- checked DAG 拓扑 step 的 equality-resolution 本地规则分支。 -/
theorem equalityResolutionTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : EqualityResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .equalityResolution evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.equalityResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, EqualityResolutionEvidence.check] using hEvidenceCheck
  rcases LocalRuleEvidence.equalityResolution_check_sound hEvidenceCheck' with
    ⟨hTerm, hConclusion⟩
  have hParentIn := LocalRuleEvidence.equalityResolution_check_parent hEvidenceCheck'
  have hSnapshot :=
    cert.equalityResolutionSnapshotChecked index hIndex payload evidence hLocal hEvidence
  have hParentMem : evidence.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.parentsBefore index hIndex evidence.parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.parent hParentSize hSnapshot
  have hParentInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.parent.id hParentSize) :=
    hParents evidence.parent.id hParentMem
  intro M env hProblem
  exact (Node.equalityResolutionRefutationInvariant_of_payload_check
    (problem := cert.dag.problem)
    (node := cert.dag.nodeAt index hIndex)
    (parentNode := cert.dag.nodeAt evidence.parent.id hParentSize)
    hLocal hEvidence hParentClause hParentInvariant
    (cert.nodePayloadChecked index hIndex)) (env := env) hProblem

/-- checked DAG 拓扑 step 的 substituted resolution 本地规则分支。 -/
theorem substitutedResolutionTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedResolution evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.substitutedResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedResolutionEvidence.check] using hEvidenceCheck
  have hIds := SubstitutedResolutionEvidence.check_parents hEvidenceCheck'
  have hSnapshots :=
    cert.substitutedResolutionSnapshotsChecked index hIndex payload evidence hLocal hEvidence
  have hLeftMem : evidence.left.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hRightMem : evidence.right.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hLeftLt := cert.parentsBefore index hIndex evidence.left.id hLeftMem
  let hRightLt := cert.parentsBefore index hIndex evidence.right.id hRightMem
  let hLeftSize := Nat.lt_trans hLeftLt hIndex
  let hRightSize := Nat.lt_trans hRightLt hIndex
  have hLeftClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.left hLeftSize hSnapshots.1
  have hRightClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.right hRightSize hSnapshots.2
  have hLeftInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.left.id hLeftSize) :=
    hParents evidence.left.id hLeftMem
  have hRightInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.right.id hRightSize) :=
    hParents evidence.right.id hRightMem
  intro M env hProblem
  exact (Node.substitutedResolutionRefutationInvariant_of_payload_check
    (problem := cert.dag.problem)
    (node := cert.dag.nodeAt index hIndex)
    (leftNode := cert.dag.nodeAt evidence.left.id hLeftSize)
    (rightNode := cert.dag.nodeAt evidence.right.id hRightSize)
    hLocal hEvidence hLeftClause hRightClause hLeftInvariant hRightInvariant
    (cert.nodePayloadChecked index hIndex)) (env := env) hProblem

/-- checked DAG 拓扑 step 的 substituted factoring 本地规则分支。 -/
theorem substitutedFactoringTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedFactoringEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedFactoring evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.substitutedFactoring evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedFactoringEvidence.check] using hEvidenceCheck
  have hSound := SubstitutedFactoringEvidence.check_sound hEvidenceCheck'
  have hAdmissible := SubstitutedFactoringEvidence.check_admissible hEvidenceCheck'
  have hParentIn := hSound.1
  have hSnapshot :=
    cert.substitutedFactoringSnapshotChecked index hIndex payload evidence hLocal hEvidence
  have hParentMem : evidence.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
    exact ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.parentsBefore index hIndex evidence.parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.parent hParentSize hSnapshot
  have hParentInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.parent.id hParentSize) :=
    hParents evidence.parent.id hParentMem
  intro M env hProblem
  apply Clause.satisfies_of_allLiteralsCovered hSound.2.1
  simpa [← hParentClause] using
    Node.satisfies_applySubstitution_of_refutationInvariant
      (problem := cert.dag.problem) (subst := evidence.substitution)
      (node := cert.dag.nodeAt evidence.parent.id hParentSize)
      hAdmissible hParentInvariant hProblem

/-- checked DAG 拓扑 step 的 substituted equality-resolution 本地规则分支。 -/
theorem substitutedEqualityResolutionTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedEqualityResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedEqualityResolution evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.substitutedEqualityResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedEqualityResolutionEvidence.check] using
      hEvidenceCheck
  have hSound := SubstitutedEqualityResolutionEvidence.check_sound hEvidenceCheck'
  have hAdmissible := SubstitutedEqualityResolutionEvidence.check_admissible hEvidenceCheck'
  rcases hSound with ⟨hParentIn, hTerm, _hContains, hConclusion⟩
  have hSnapshot :=
    cert.substitutedEqualityResolutionSnapshotChecked index hIndex payload evidence hLocal hEvidence
  have hParentMem : evidence.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
    exact ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.parentsBefore index hIndex evidence.parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.parent hParentSize hSnapshot
  have hParentInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.parent.id hParentSize) :=
    hParents evidence.parent.id hParentMem
  intro M env hProblem
  rw [hConclusion]
  exact Clause.satisfies_equalityResolutionResult hTerm
    (by
      simpa [← hParentClause] using
        Node.satisfies_applySubstitution_of_refutationInvariant
          (problem := cert.dag.problem) (subst := evidence.substitution)
          (node := cert.dag.nodeAt evidence.parent.id hParentSize)
          hAdmissible hParentInvariant hProblem)

/-- checked DAG 拓扑 step 的 substituted rewrite/superposition 核心。 -/
private theorem substitutedRewriteTopologicalStepCore {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hConclusion : (cert.dag.nodeAt index hIndex).conclusion = evidence.result)
    (hIds : evidence.equality.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
      evidence.target.idIn (cert.dag.nodeAt index hIndex).parents = true)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hSnapshots :=
    cert.substitutedRewriteSnapshotsChecked index hIndex payload evidence hLocal
      hParentClauses
  have hEqualityMem :
      evidence.equality.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hTargetMem :
      evidence.target.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hEqualityLt := cert.parentsBefore index hIndex evidence.equality.id hEqualityMem
  let hTargetLt := cert.parentsBefore index hIndex evidence.target.id hTargetMem
  let hEqualitySize := Nat.lt_trans hEqualityLt hIndex
  let hTargetSize := Nat.lt_trans hTargetLt hIndex
  have hEqualityClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.equality hEqualitySize
      hSnapshots.1
  have hTargetClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.target hTargetSize hSnapshots.2
  have hEqualityInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.equality.id hEqualitySize) :=
    hParents evidence.equality.id hEqualityMem
  have hTargetInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.target.id hTargetSize) :=
    hParents evidence.target.id hTargetMem
  intro M env hProblem
  rw [hConclusion]
  exact SubstitutedRewriteEvidence.satisfies_result
    (by
      simpa [SubstitutedRewriteEvidence.equalityClause, hEqualityClause] using
        Node.satisfies_applySubstitution_of_refutationInvariant
          (problem := cert.dag.problem) (subst := evidence.substitution)
          (node := cert.dag.nodeAt evidence.equality.id hEqualitySize)
          hAdmissible hEqualityInvariant hProblem)
    (by
      simpa [SubstitutedRewriteEvidence.targetClause, hTargetClause] using
        Node.satisfies_applySubstitution_of_refutationInvariant
          (problem := cert.dag.problem) (subst := evidence.substitution)
          (node := cert.dag.nodeAt evidence.target.id hTargetSize)
          hAdmissible hTargetInvariant hProblem)

/-- checked DAG 拓扑 step 的 substituted demodulation 本地规则分支。 -/
theorem substitutedDemodulationTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedDemodulation evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      SubstitutedRewriteEvidence.check .demodulation
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedRewriteEvidence.check_sound hEvidenceCheck' with
    ⟨hEqualityIn, hTargetIn, _hContains, _hNeedle, _hKind, hConclusion⟩
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem
  exact (cert.substitutedRewriteTopologicalStepCore index hIndex hParents
    payload evidence hLocal hAdmissible hConclusion ⟨hEqualityIn, hTargetIn⟩
    hParentClauses) (env := env) hProblem

/-- checked DAG 拓扑 step 的 substituted positive-superposition 本地规则分支。 -/
theorem substitutedPositiveSuperpositionTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedPositiveSuperposition evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      SubstitutedRewriteEvidence.check .positiveSuperposition
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedRewriteEvidence.check_sound hEvidenceCheck' with
    ⟨hEqualityIn, hTargetIn, _hContains, _hNeedle, _hKind, hConclusion⟩
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem
  exact (cert.substitutedRewriteTopologicalStepCore index hIndex hParents
    payload evidence hLocal hAdmissible hConclusion ⟨hEqualityIn, hTargetIn⟩
    hParentClauses) (env := env) hProblem

/-- checked DAG 拓扑 step 的 substituted negative-superposition 本地规则分支。 -/
theorem substitutedNegativeSuperpositionTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedNegativeSuperposition evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      SubstitutedRewriteEvidence.check .negativeSuperposition
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedRewriteEvidence.check_sound hEvidenceCheck' with
    ⟨hEqualityIn, hTargetIn, _hContains, _hNeedle, _hKind, hConclusion⟩
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem
  exact (cert.substitutedRewriteTopologicalStepCore index hIndex hParents
    payload evidence hLocal hAdmissible hConclusion ⟨hEqualityIn, hTargetIn⟩
    hParentClauses) (env := env) hProblem

/-- checked DAG 拓扑 step 的 standardized resolution 核心。 -/
private theorem standardizedResolutionTopologicalStepCore {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .standardizedSubstitutedResolution evidence)
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hStandardize :
      evidence.standardizeApart.left.renamed =
        evidence.standardizeApart.left.expected ∧
      evidence.standardizeApart.right.renamed =
        evidence.standardizeApart.right.expected)
    (hConclusion : (cert.dag.nodeAt index hIndex).conclusion =
      Clause.resolutionResult evidence.leftPolarity evidence.pivot
        evidence.leftClause evidence.rightClause)
    (hIds : evidence.left.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
      evidence.right.idIn (cert.dag.nodeAt index hIndex).parents = true) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hSnapshots :=
    cert.standardizedResolutionSnapshotsChecked index hIndex payload evidence hLocal
      hEvidence
  have hLeftMem : evidence.left.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hRightMem : evidence.right.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hLeftSize := Nat.lt_trans
    (cert.parentsBefore index hIndex evidence.left.id hLeftMem) hIndex
  let hRightSize := Nat.lt_trans
    (cert.parentsBefore index hIndex evidence.right.id hRightMem) hIndex
  have hLeftClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.left hLeftSize hSnapshots.1
  have hRightClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.right hRightSize hSnapshots.2
  have hLeftInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.left.id hLeftSize) :=
    hParents evidence.left.id hLeftMem
  have hRightInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.right.id hRightSize) :=
    hParents evidence.right.id hRightMem
  intro M env hProblem
  exact Node.standardizedResolutionRefutationInvariant_of_check
    hAdmissible hStandardize hConclusion hLeftClause hRightClause
    hLeftInvariant hRightInvariant (env := env) hProblem

/-- checked DAG 拓扑 step 的 standardized rewrite/superposition 核心。 -/
private theorem standardizedRewriteTopologicalStepCore {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hStandardize :
      evidence.standardizeApart.left.renamed =
        evidence.standardizeApart.left.expected ∧
      evidence.standardizeApart.right.renamed =
        evidence.standardizeApart.right.expected)
    (hConclusion : (cert.dag.nodeAt index hIndex).conclusion = evidence.result)
    (hIds : evidence.equality.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
      evidence.target.idIn (cert.dag.nodeAt index hIndex).parents = true)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hSnapshots :=
    cert.standardizedRewriteSnapshotsChecked index hIndex payload evidence hLocal
      hParentClauses
  have hEqualityMem :
      evidence.equality.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hTargetMem :
      evidence.target.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hEqualitySize := Nat.lt_trans
    (cert.parentsBefore index hIndex evidence.equality.id hEqualityMem) hIndex
  let hTargetSize := Nat.lt_trans
    (cert.parentsBefore index hIndex evidence.target.id hTargetMem) hIndex
  have hEqualityClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.equality hEqualitySize hSnapshots.1
  have hTargetClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.target hTargetSize hSnapshots.2
  have hEqualityInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.equality.id hEqualitySize) :=
    hParents evidence.equality.id hEqualityMem
  have hTargetInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.target.id hTargetSize) :=
    hParents evidence.target.id hTargetMem
  intro M env hProblem
  exact Node.standardizedRewriteRefutationInvariant_of_check
    hAdmissible hStandardize hConclusion hEqualityClause hTargetClause
    hEqualityInvariant hTargetInvariant (env := env) hProblem

/-- checked DAG 拓扑 step 的 standardized resolution 本地规则分支。 -/
theorem standardizedResolutionTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .standardizedSubstitutedResolution evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      StandardizedSubstitutedResolutionEvidence.check
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  unfold StandardizedSubstitutedResolutionEvidence.check at hEvidenceCheck'
  rcases Bool.and_eq_true_iff.mp hEvidenceCheck' with ⟨hPrefix, _hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hStandardizeCheck, _hAdmissibleCheck⟩
  have hStandardize := StandardizeApartEvidence.check_sound hStandardizeCheck
  have hAdmissible :=
    StandardizedSubstitutedResolutionEvidence.check_admissible hEvidenceCheck'
  have hSound :=
    StandardizedSubstitutedResolutionEvidence.check_sound hEvidenceCheck'
  intro M env hProblem
  exact (cert.standardizedResolutionTopologicalStepCore index hIndex hParents
    payload evidence hLocal hEvidence hAdmissible hStandardize hSound.2.2
    ⟨hSound.1, hSound.2.1⟩) (env := env) hProblem

/-- checked DAG 拓扑 step 的 standardized demodulation 本地规则分支。 -/
theorem standardizedDemodulationTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .standardizedSubstitutedDemodulation evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      StandardizedSubstitutedRewriteEvidence.check .demodulation
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  unfold StandardizedSubstitutedRewriteEvidence.check at hEvidenceCheck'
  rcases Bool.and_eq_true_iff.mp hEvidenceCheck' with ⟨hPrefix, _hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hStandardizeCheck, _hAdmissibleCheck⟩
  have hStandardize := StandardizeApartEvidence.check_sound hStandardizeCheck
  have hAdmissible :=
    StandardizedSubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  have hSound := StandardizedSubstitutedRewriteEvidence.check_sound hEvidenceCheck'
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem
  exact (cert.standardizedRewriteTopologicalStepCore index hIndex hParents
    payload evidence hLocal hAdmissible hStandardize hSound.2.2.2
    ⟨hSound.1, hSound.2.1⟩ hParentClauses)
    (env := env) hProblem

/-- checked DAG 拓扑 step 的 standardized positive-superposition 本地规则分支。 -/
theorem standardizedPositiveSuperpositionTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence =
      .standardizedSubstitutedPositiveSuperposition evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      StandardizedSubstitutedRewriteEvidence.check .positiveSuperposition
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  unfold StandardizedSubstitutedRewriteEvidence.check at hEvidenceCheck'
  rcases Bool.and_eq_true_iff.mp hEvidenceCheck' with ⟨hPrefix, _hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hStandardizeCheck, _hAdmissibleCheck⟩
  have hStandardize := StandardizeApartEvidence.check_sound hStandardizeCheck
  have hAdmissible :=
    StandardizedSubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  have hSound := StandardizedSubstitutedRewriteEvidence.check_sound hEvidenceCheck'
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem
  exact (cert.standardizedRewriteTopologicalStepCore index hIndex hParents
    payload evidence hLocal hAdmissible hStandardize hSound.2.2.2
    ⟨hSound.1, hSound.2.1⟩ hParentClauses)
    (env := env) hProblem

/-- checked DAG 拓扑 step 的 standardized negative-superposition 本地规则分支。 -/
theorem standardizedNegativeSuperpositionTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence =
      .standardizedSubstitutedNegativeSuperposition evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      StandardizedSubstitutedRewriteEvidence.check .negativeSuperposition
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  unfold StandardizedSubstitutedRewriteEvidence.check at hEvidenceCheck'
  rcases Bool.and_eq_true_iff.mp hEvidenceCheck' with ⟨hPrefix, _hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hStandardizeCheck, _hAdmissibleCheck⟩
  have hStandardize := StandardizeApartEvidence.check_sound hStandardizeCheck
  have hAdmissible :=
    StandardizedSubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  have hSound := StandardizedSubstitutedRewriteEvidence.check_sound hEvidenceCheck'
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem
  exact (cert.standardizedRewriteTopologicalStepCore index hIndex hParents
    payload evidence hLocal hAdmissible hStandardize hSound.2.2.2
    ⟨hSound.1, hSound.2.1⟩ hParentClauses)
    (env := env) hProblem

/-- checked DAG 上 guarded standardized resolution 的核心。 -/
private theorem standardizedResolutionGuardedTopologicalStepCore {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .standardizedSubstitutedResolution evidence)
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hStandardize :
      evidence.standardizeApart.left.renamed =
        evidence.standardizeApart.left.expected ∧
      evidence.standardizeApart.right.renamed =
        evidence.standardizeApart.right.expected)
    (hConclusion : (cert.dag.nodeAt index hIndex).conclusion =
      Clause.resolutionResult evidence.leftPolarity evidence.pivot
        evidence.leftClause evidence.rightClause)
    (hIds : evidence.left.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
      evidence.right.idIn (cert.dag.nodeAt index hIndex).parents = true) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hSnapshots :=
    cert.standardizedResolutionSnapshotsChecked index hIndex payload evidence hLocal
      hEvidence
  have hLeftMem : evidence.left.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hRightMem : evidence.right.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hLeftSize := Nat.lt_trans
    (cert.parentsBefore index hIndex evidence.left.id hLeftMem) hIndex
  let hRightSize := Nat.lt_trans
    (cert.parentsBefore index hIndex evidence.right.id hRightMem) hIndex
  have hLeftClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.left hLeftSize hSnapshots.1
  have hRightClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.right hRightSize hSnapshots.2
  have hLeftInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.left.id hLeftSize) :=
    hParents evidence.left.id hLeftMem
  have hRightInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.right.id hRightSize) :=
    hParents evidence.right.id hRightMem
  have hLeftGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.left.id hLeftSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.left.id hLeftMem hLeftSize
  have hRightGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.right.id hRightSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.right.id hRightMem hRightSize
  intro M env hProblem hGuards
  exact Node.standardizedResolutionGuardedRefutationInvariant_of_check
    hAdmissible hStandardize hConclusion hLeftClause hRightClause
    hLeftInvariant hRightInvariant hLeftGuards hRightGuards
    (env := env) hProblem hGuards

/-- checked DAG 上 guarded standardized rewrite/superposition 的核心。 -/
private theorem standardizedRewriteGuardedTopologicalStepCore {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hStandardize :
      evidence.standardizeApart.left.renamed =
        evidence.standardizeApart.left.expected ∧
      evidence.standardizeApart.right.renamed =
        evidence.standardizeApart.right.expected)
    (hConclusion : (cert.dag.nodeAt index hIndex).conclusion = evidence.result)
    (hIds : evidence.equality.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
      evidence.target.idIn (cert.dag.nodeAt index hIndex).parents = true)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hSnapshots :=
    cert.standardizedRewriteSnapshotsChecked index hIndex payload evidence hLocal
      hParentClauses
  have hEqualityMem :
      evidence.equality.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hTargetMem :
      evidence.target.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hEqualitySize := Nat.lt_trans
    (cert.parentsBefore index hIndex evidence.equality.id hEqualityMem) hIndex
  let hTargetSize := Nat.lt_trans
    (cert.parentsBefore index hIndex evidence.target.id hTargetMem) hIndex
  have hEqualityClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.equality hEqualitySize
      hSnapshots.1
  have hTargetClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.target hTargetSize hSnapshots.2
  have hEqualityInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.equality.id hEqualitySize) :=
    hParents evidence.equality.id hEqualityMem
  have hTargetInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.target.id hTargetSize) :=
    hParents evidence.target.id hTargetMem
  have hEqualityGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation
          (cert.dag.nodeAt evidence.equality.id hEqualitySize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.equality.id hEqualityMem hEqualitySize
  have hTargetGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation
          (cert.dag.nodeAt evidence.target.id hTargetSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.target.id hTargetMem hTargetSize
  intro M env hProblem hGuards
  exact Node.standardizedRewriteGuardedRefutationInvariant_of_check
    hAdmissible hStandardize hConclusion hEqualityClause hTargetClause
    hEqualityInvariant hTargetInvariant hEqualityGuards hTargetGuards
    (env := env) hProblem hGuards

/-- checked DAG 上 guarded standardized resolution 分支。 -/
theorem standardizedResolutionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .standardizedSubstitutedResolution evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      StandardizedSubstitutedResolutionEvidence.check
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  unfold StandardizedSubstitutedResolutionEvidence.check at hEvidenceCheck'
  rcases Bool.and_eq_true_iff.mp hEvidenceCheck' with ⟨hPrefix, _hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hStandardizeCheck, _hAdmissibleCheck⟩
  have hStandardize := StandardizeApartEvidence.check_sound hStandardizeCheck
  have hAdmissible :=
    StandardizedSubstitutedResolutionEvidence.check_admissible hEvidenceCheck'
  have hSound :=
    StandardizedSubstitutedResolutionEvidence.check_sound hEvidenceCheck'
  intro M env hProblem hGuards
  exact (cert.standardizedResolutionGuardedTopologicalStepCore valuation index hIndex
    hParents payload evidence hLocal hEvidence hAdmissible hStandardize hSound.2.2
    ⟨hSound.1, hSound.2.1⟩)
    (env := env) hProblem hGuards

/-- guarded standardized rewrite 分支的公共 checker 解包。 -/
private theorem standardizedRewriteGuardedTopologicalStepOfCheck
    {σ : Signature} [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {kind : RewriteKind}
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidenceCheck :
      StandardizedSubstitutedRewriteEvidence.check kind
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  unfold StandardizedSubstitutedRewriteEvidence.check at hEvidenceCheck
  rcases Bool.and_eq_true_iff.mp hEvidenceCheck with ⟨hPrefix, _hRest⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hStandardizeCheck, _hAdmissibleCheck⟩
  have hStandardize := StandardizeApartEvidence.check_sound hStandardizeCheck
  have hAdmissible :=
    StandardizedSubstitutedRewriteEvidence.check_admissible hEvidenceCheck
  have hSound := StandardizedSubstitutedRewriteEvidence.check_sound hEvidenceCheck
  intro M env hProblem hGuards
  exact (cert.standardizedRewriteGuardedTopologicalStepCore valuation index hIndex
    hParents payload evidence hLocal hAdmissible hStandardize hSound.2.2.2
    ⟨hSound.1, hSound.2.1⟩ hParentClauses)
    (env := env) hProblem hGuards

/-- checked DAG 上 guarded standardized demodulation 分支。 -/
theorem standardizedDemodulationGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .standardizedSubstitutedDemodulation evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      StandardizedSubstitutedRewriteEvidence.check .demodulation
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem hGuards
  exact cert.standardizedRewriteGuardedTopologicalStepOfCheck valuation
    index hIndex hParents payload evidence hLocal hEvidenceCheck' hParentClauses
    (env := env) hProblem hGuards

/-- checked DAG 上 guarded standardized positive-superposition 分支。 -/
theorem standardizedPositiveSuperpositionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence =
      .standardizedSubstitutedPositiveSuperposition evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      StandardizedSubstitutedRewriteEvidence.check .positiveSuperposition
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem hGuards
  exact cert.standardizedRewriteGuardedTopologicalStepOfCheck valuation
    index hIndex hParents payload evidence hLocal hEvidenceCheck' hParentClauses
    (env := env) hProblem hGuards

/-- checked DAG 上 guarded standardized negative-superposition 分支。 -/
theorem standardizedNegativeSuperpositionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : StandardizedSubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence =
      .standardizedSubstitutedNegativeSuperposition evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      StandardizedSubstitutedRewriteEvidence.check .negativeSuperposition
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem hGuards
  exact cert.standardizedRewriteGuardedTopologicalStepOfCheck valuation
    index hIndex hParents payload evidence hLocal hEvidenceCheck' hParentClauses
    (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的通用重写/叠加核心。 -/
private theorem rewriteTopologicalStepCore {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : RewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hConclusion : (cert.dag.nodeAt index hIndex).conclusion = evidence.result)
    (hIds : evidence.equality.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
      evidence.target.idIn (cert.dag.nodeAt index hIndex).parents = true)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hSnapshots :=
    cert.rewriteSnapshotsChecked index hIndex payload evidence hLocal hParentClauses
  have hEqualityMem :
      evidence.equality.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hTargetMem :
      evidence.target.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hEqualityLt := cert.parentsBefore index hIndex evidence.equality.id hEqualityMem
  let hTargetLt := cert.parentsBefore index hIndex evidence.target.id hTargetMem
  let hEqualitySize := Nat.lt_trans hEqualityLt hIndex
  let hTargetSize := Nat.lt_trans hTargetLt hIndex
  have hEqualityClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.equality hEqualitySize hSnapshots.1
  have hTargetClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.target hTargetSize hSnapshots.2
  have hEqualityInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.equality.id hEqualitySize) :=
    hParents evidence.equality.id hEqualityMem
  have hTargetInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt evidence.target.id hTargetSize) :=
    hParents evidence.target.id hTargetMem
  intro M env hProblem
  rw [hConclusion]
  exact RewriteEvidence.satisfies_result
    (by simpa [hEqualityClause] using hEqualityInvariant env hProblem)
    (by simpa [hTargetClause] using hTargetInvariant env hProblem)

/-- checked DAG 拓扑 step 的 demodulation 本地规则分支。 -/
theorem demodulationTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : RewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .demodulation evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.demodulation evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.demodulation_check_conclusion hEvidenceCheck'
  have hIds := LocalRuleEvidence.demodulation_check_parents hEvidenceCheck'
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem
  exact (cert.rewriteTopologicalStepCore index hIndex hParents payload evidence hLocal
    hConclusion hIds hParentClauses) (env := env) hProblem

/-- checked DAG 拓扑 step 的 positive-superposition 本地规则分支。 -/
theorem positiveSuperpositionTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : RewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .positiveSuperposition evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.positiveSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.positiveSuperposition_check_conclusion hEvidenceCheck'
  have hIds := LocalRuleEvidence.positiveSuperposition_check_parents hEvidenceCheck'
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem
  exact (cert.rewriteTopologicalStepCore index hIndex hParents payload evidence hLocal
    hConclusion hIds hParentClauses) (env := env) hProblem

/-- checked DAG 拓扑 step 的 negative-superposition 本地规则分支。 -/
theorem negativeSuperpositionTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : RewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .negativeSuperposition evidence) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.negativeSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.negativeSuperposition_check_conclusion hEvidenceCheck'
  have hIds := LocalRuleEvidence.negativeSuperposition_check_parents hEvidenceCheck'
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem
  exact (cert.rewriteTopologicalStepCore index hIndex hParents payload evidence hLocal
    hConclusion hIds hParentClauses) (env := env) hProblem

/-- checked DAG 拓扑 step 的 guarded source 分支。 -/
theorem sourceGuardedTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (_hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (initialIndex : Nat)
    (hSource : (cert.dag.nodeAt index hIndex).payload = .source initialIndex) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) :=
  Node.guardedRefutationInvariant_of_refutationInvariant
    (Node.sourceRefutationInvariant_of_payload_check hSource
      (cert.nodePayloadChecked index hIndex))

/-- checked DAG 拓扑 step 的 guarded theory-conflict 分支。 -/
theorem theoryConflictGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : TheoryConflictPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hPayload] at hPayloadCheck
  have hTheoryCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold TheoryConflictPayload.check at hTheoryCheck
  rcases Bool.and_eq_true_iff.mp hTheoryCheck with ⟨hPrefix, _hConclusionEmpty⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hParentIn, _hConflictEmpty⟩
  have hParentMem :
      payload.conflict.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.parentsBefore index hIndex payload.conflict.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hConflictInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt payload.conflict.id hParentSize) :=
    hParents payload.conflict.id hParentMem
  have hSnapshot :=
    cert.theoryConflictSnapshotChecked index hIndex payload hPayload
  have hConflictClause :=
    cert.parentClause_eq_nodeAt_of_snapshot payload.conflict hParentSize hSnapshot
  have hConflictGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation
          (cert.dag.nodeAt payload.conflict.id hParentSize).guards :=
    cert.parentGuardsHold_of_theoryConflictNodeGuardsOk index hIndex payload hPayload
      payload.conflict.id hParentMem hParentSize
  intro M env hProblem hGuards
  exact (Node.theoryConflictGuardedRefutationInvariant_of_payload_check
    (problem := cert.dag.problem)
    (node := cert.dag.nodeAt index hIndex)
    (conflictNode := cert.dag.nodeAt payload.conflict.id hParentSize)
    hPayload hConflictClause hConflictGuards hConflictInvariant
    (cert.nodePayloadChecked index hIndex)) (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded propositional-learned 分支。 -/
theorem propositionalLearnedClauseGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : PropositionalLearnedClausePayload)
    (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .propositionalLearnedClause payload) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hPayload] at hPayloadCheck
  have hLearnedCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold PropositionalLearnedClausePayload.check at hLearnedCheck
  rcases Bool.and_eq_true_iff.mp hLearnedCheck with
    ⟨hParentIn, _hConclusionEmpty⟩
  have hParentMem :
      payload.conflict ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
    have hArray : payload.conflict ∈ (cert.dag.nodeAt index hIndex).parents := by
      simpa using hParentIn
    exact Array.mem_def.mp hArray
  let hParentLt := cert.parentsBefore index hIndex payload.conflict hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hConflictInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt payload.conflict hParentSize) :=
    hParents payload.conflict hParentMem
  have hGuardCheck := cert.nodeGuardsChecked index hIndex
  have hConflictNodeSome :
      cert.dag.node? payload.conflict =
        some (cert.dag.nodeAt payload.conflict hParentSize) :=
    cert.dag.node?_eq_some_nodeAt hParentSize
  simp [DAG.localNodeGuardsOk, hPayload, hConflictNodeSome] at hGuardCheck
  rcases hGuardCheck with ⟨_hNodeEmpty, hConflictFields⟩
  rcases hConflictFields with ⟨hConflictPrefix, _hLearnedEq⟩
  rcases hConflictPrefix with ⟨hConflictTheory, hGuardEq⟩
  have hConflictEmpty :
      (cert.dag.nodeAt payload.conflict hParentSize).conclusion.isEmpty = true := by
    have hTheory :
        (cert.dag.nodeAt payload.conflict hParentSize).unguarded = false ∧
          (cert.dag.nodeAt payload.conflict hParentSize).conclusion.isEmpty = true := by
      simpa [Node.theoryConflict, GuardedClause.theoryConflict,
        Node.guardedConclusion, GuardedClause.unguarded, Node.unguarded]
        using hConflictTheory
    exact hTheory.2
  intro M env hProblem hGuards
  have hConflictGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt payload.conflict hParentSize).guards :=
    Node.GuardsHold.of_guardSetEq hGuardEq hGuards
  have hConflictSat :=
    hConflictInvariant env hProblem hConflictGuards
  exact False.elim (Clause.not_satisfies_of_isEmpty hConflictEmpty hConflictSat)

/-- residual CDCL 的 initial justification 槽位检查解包。 -/
private theorem propClosureJustificationCheckAt {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array NodeId} {payload : PropositionalClosurePayload σ}
    (hCheck : payload.justificationsCheck parents = true)
    {slot : Nat} (hSlot : slot < payload.initialClauses.size) :
    ∃ hJust : slot < payload.initialJustifications.size,
      (payload.initialJustifications[slot]).check parents payload.atomMap
        payload.initialClauses[slot] = true := by
  have hListCheck :=
    PropositionalClosurePayload.justificationsListCheck_eq_true_of_check hCheck
  unfold PropositionalClosurePayload.justificationsCheck at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hSizeBool, _hBody⟩
  have hSizeEq :
      payload.initialClauses.size = payload.initialJustifications.size := by
    by_cases hEq : payload.initialClauses.size = payload.initialJustifications.size
    · exact hEq
    · have hFalse :
          (payload.initialClauses.size == payload.initialJustifications.size) = false := by
        simp [hEq]
      rw [hFalse] at hSizeBool
      cases hSizeBool
  have hJust : slot < payload.initialJustifications.size := by
    simpa [hSizeEq] using hSlot
  refine ⟨hJust, ?_⟩
  have hAt :=
    PropositionalClosurePayload.justificationsListCheck_at
      parents payload.atomMap hListCheck slot
      (by simpa using hSlot) (by simpa using hJust)
  simpa using hAt

/-- residual CDCL 的 guarded-support 检查解包到单个 initial justification。 -/
private theorem propClosureJustificationSupportedAt {σ : Signature}
    {payload : PropositionalClosurePayload σ}
    (hSupported : payload.guardedSoundnessSupported = true)
    {slot : Nat} (hSlot : slot < payload.initialJustifications.size) :
    (payload.initialJustifications[slot]).guardedSoundnessSupported = true := by
  have hAll := Array.all_eq_true.mp hSupported
  simpa [PropositionalClosurePayload.guardedSoundnessSupported] using hAll slot hSlot

/-- checked DAG 拓扑 step 的 guarded residual-CDCL 分支。 -/
theorem residualCdclGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : PropositionalClosurePayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .residualCdcl payload)
    (hPayloadSupported : payload.guardedSoundnessSupported = true) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hPayload] at hPayloadCheck
  have hResidualCheck :
      (!((cert.dag.nodeAt index hIndex).parents.isEmpty) &&
          (cert.dag.nodeAt index hIndex).conclusion.isEmpty &&
            payload.check (cert.dag.nodeAt index hIndex).parents) = true := by
    simpa [Payload.check] using hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hResidualCheck with
    ⟨_hResidualPrefix, hClosureCheck⟩
  have hClosureParts := hClosureCheck
  unfold PropositionalClosurePayload.check at hClosureParts
  simp at hClosureParts
  rcases hClosureParts with ⟨hClosureParts, _hVerifiedStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hRetainedStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hGeneratedStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hClauseStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hStepsStats⟩
  rcases hClosureParts with ⟨hCheckedUnsatProof, hJustificationsCheckProof⟩
  have hCheckedUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof = true :=
    hCheckedUnsatProof
  have hJustificationsCheck :
      payload.justificationsCheck (cert.dag.nodeAt index hIndex).parents = true :=
    hJustificationsCheckProof
  have hInitialLinks :=
    cert.nodePropInitialLinksChecked index hIndex
  have hDagInitials :
      payload.initialJustifications.all
        (fun justification =>
          cert.dag.propInitialJustificationDagOk
            (cert.dag.nodeAt index hIndex).parents justification) = true := by
    simpa [DAG.propInitialLinksOk, hPayload] using hInitialLinks
  intro M env hProblem _hGuards
  have hInitialSatisfies :
      ∀ initial, initial ∈ payload.initialClauses.toList →
        PropResolution.Clause.Satisfies
          (PropLiteralLink.valuation valuation payload.atomMap env) initial.clause := by
    intro initial hInitialMem
    have hInitialArray : initial ∈ payload.initialClauses :=
      Array.mem_def.mpr hInitialMem
    rcases Array.mem_iff_getElem.mp hInitialArray with
      ⟨slot, hSlot, hInitialGet⟩
    rcases propClosureJustificationCheckAt hJustificationsCheck hSlot with
      ⟨hJustSlot, hJustificationCheck⟩
    have hJustificationSupported :=
      propClosureJustificationSupportedAt hPayloadSupported hJustSlot
    have hDagOk :=
      (Array.all_eq_true.mp hDagInitials) slot hJustSlot
    cases hJustification :
        payload.initialJustifications[slot] with
    | parentClause link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropParentClauseLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hCheckPrefix, hLiteralChecks⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentInBool, hObjectEqBool⟩
        have hInitialEq : initial.clause = link.encodedClause :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hObjectEq : link.parent.clause = link.objectClause :=
          Clause.eq_sound link.parent.clause link.objectClause hObjectEqBool
        have hDagParent :
            cert.dag.propParentInitialLinkOk
              (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
          ParentClause.mem_toList_of_idIn hParentInBool
        let hParentLt := cert.parentsBefore index hIndex link.parent.id hParentMem
        let hParentSize := Nat.lt_trans hParentLt hIndex
        have hParentNodeSome :
            cert.dag.node? link.parent.id =
              some (cert.dag.nodeAt link.parent.id hParentSize) :=
          cert.dag.node?_eq_some_nodeAt hParentSize
        unfold DAG.propParentInitialLinkOk at hDagParent
        rw [hParentNodeSome] at hDagParent
        rcases Bool.and_eq_true_iff.mp hDagParent with
          ⟨hDagParentPrefix, hParentUnguarded⟩
        rcases Bool.and_eq_true_iff.mp hDagParentPrefix with
          ⟨_hParentContains, hSnapshot⟩
        have hParentInvariant :
            Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
              (cert.dag.nodeAt link.parent.id hParentSize) :=
          hParents link.parent.id hParentMem
        have hParentGuards :
            Node.GuardsHold valuation
              (cert.dag.nodeAt link.parent.id hParentSize).guards :=
          Node.GuardsHold.of_isEmpty (by
            simpa [Node.unguarded] using hParentUnguarded)
        have hParentSat :=
          hParentInvariant env hProblem hParentGuards
        have hSnapshotClause :=
          cert.parentClause_eq_nodeAt_of_snapshot link.parent hParentSize hSnapshot
        have hObjectSat : Clause.Satisfies env link.objectClause := by
          have hObjectConclusion :
              link.objectClause =
                (cert.dag.nodeAt link.parent.id hParentSize).conclusion :=
            hObjectEq.symm.trans hSnapshotClause
          simpa [hObjectConclusion] using hParentSat
        have hEncodedSat :=
          PropParentClauseLink.encodedClause_satisfies_of_object
            (base := valuation) (atomMap := payload.atomMap)
            hLiteralChecks hObjectSat
        simpa [hInitialEq] using hEncodedSat
    | guardActivationClause link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropGuardActivationLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hCheckPrefix, hLiteralChecks⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hCheckPrefix, hGuardChecks⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentInBool, hObjectEqBool⟩
        have hInitialEq : initial.clause = link.encodedClause :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hObjectEq : link.parent.clause = link.objectClause :=
          Clause.eq_sound link.parent.clause link.objectClause hObjectEqBool
        have hDagActivation :
            cert.dag.propGuardActivationInitialLinkOk
              (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
          ParentClause.mem_toList_of_idIn hParentInBool
        let hParentLt := cert.parentsBefore index hIndex link.parent.id hParentMem
        let hParentSize := Nat.lt_trans hParentLt hIndex
        have hParentNodeSome :
            cert.dag.node? link.parent.id =
              some (cert.dag.nodeAt link.parent.id hParentSize) :=
          cert.dag.node?_eq_some_nodeAt hParentSize
        unfold DAG.propGuardActivationInitialLinkOk at hDagActivation
        rw [hParentNodeSome] at hDagActivation
        rcases Bool.and_eq_true_iff.mp hDagActivation with
          ⟨hDagPrefix, hGuardFields⟩
        rcases Bool.and_eq_true_iff.mp hDagPrefix with
          ⟨_hParentContains, hSnapshot⟩
        rcases Bool.and_eq_true_iff.mp hGuardFields with
          ⟨_hParentGuarded, hGuardEq⟩
        have hParentInvariant :
            Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
              (cert.dag.nodeAt link.parent.id hParentSize) :=
          hParents link.parent.id hParentMem
        have hSnapshotClause :=
          cert.parentClause_eq_nodeAt_of_snapshot link.parent hParentSize hSnapshot
        have hObjectOfGuards :
            (∀ lit, lit ∈ (canonicalGuards link.guards).toList →
              lit.Holds valuation) → Clause.Satisfies env link.objectClause := by
          intro hLinkGuards
          have hParentGuards :
              Node.GuardsHold valuation
                (cert.dag.nodeAt link.parent.id hParentSize).guards :=
            Node.GuardsHold.of_guardSetEq hGuardEq hLinkGuards
          have hParentSat :=
            hParentInvariant env hProblem hParentGuards
          have hObjectConclusion :
              link.objectClause =
                (cert.dag.nodeAt link.parent.id hParentSize).conclusion :=
            hObjectEq.symm.trans hSnapshotClause
          simpa [hObjectConclusion] using hParentSat
        have hEncodedSat :=
          PropGuardActivationLink.encodedClause_satisfies
            (base := valuation) (atomMap := payload.atomMap)
            hGuardChecks hLiteralChecks hObjectOfGuards
        simpa [hInitialEq] using hEncodedSat
    | propLearnedClause link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropLearnedClauseLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentContains, hOutside⟩
        have hInitialEq : initial.clause = link.clause :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hDagLearned :
            cert.dag.propLearnedInitialLinkOk
              (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
          have hArray :
              link.parent ∈ (cert.dag.nodeAt index hIndex).parents := by
            simpa using hParentContains
          exact Array.mem_def.mp hArray
        let hParentLt := cert.parentsBefore index hIndex link.parent hParentMem
        let hParentSize := Nat.lt_trans hParentLt hIndex
        have hParentNodeSome :
            cert.dag.node? link.parent =
              some (cert.dag.nodeAt link.parent hParentSize) :=
          cert.dag.node?_eq_some_nodeAt hParentSize
        unfold DAG.propLearnedInitialLinkOk at hDagLearned
        rw [hParentNodeSome] at hDagLearned
        rcases Bool.and_eq_true_iff.mp hDagLearned with
          ⟨_hParentContainsDag, hLearnedMatch⟩
        cases hParentPayload :
            (cert.dag.nodeAt link.parent hParentSize).payload with
        | propositionalLearnedClause learnedPayload =>
            simp [hParentPayload] at hLearnedMatch
            have hLinkLearnedEq : link.clause = learnedPayload.learned :=
              PropResolution.clauseEq_eq.mp (by simpa using hLearnedMatch)
            have hParentPayloadCheck := cert.nodePayloadChecked link.parent hParentSize
            simp [hParentPayload] at hParentPayloadCheck
            have hLearnedPayloadCheck :
                learnedPayload.check
                  (cert.dag.nodeAt link.parent hParentSize).parents
                  (cert.dag.nodeAt link.parent hParentSize).conclusion = true := by
              simpa [Payload.check] using hParentPayloadCheck
            unfold PropositionalLearnedClausePayload.check at hLearnedPayloadCheck
            rcases Bool.and_eq_true_iff.mp hLearnedPayloadCheck with
              ⟨_hConflictParent, hParentConclusionEmpty⟩
            have hParentGuardCheck := cert.nodeGuardsChecked link.parent hParentSize
            unfold DAG.localNodeGuardsOk at hParentGuardCheck
            simp [hParentPayload] at hParentGuardCheck
            rcases hParentGuardCheck with
              ⟨_hParentEmptyFromGuards, hConflictMatch⟩
            cases hConflictNode? : cert.dag.node? learnedPayload.conflict with
            | none =>
                have hFalse : False := by
                  simp [hConflictNode?] at hConflictMatch
                exact False.elim hFalse
            | some conflictNode =>
                have hConflictMatch' :
                    conflictNode.theoryConflict &&
                      guardSetEq (cert.dag.nodeAt link.parent hParentSize).guards
                        conflictNode.guards &&
                        (match conflictNode.payload with
                        | Payload.theoryConflict payload =>
                            PropResolution.clauseEq learnedPayload.learned
                              (learnedClauseOfGuards conflictNode.guards)
                        | _ => false) = true := by
                  simpa [hConflictNode?] using hConflictMatch
                rcases Bool.and_eq_true_iff.mp hConflictMatch' with
                  ⟨hConflictPrefix, hLearnedEqBool⟩
                rcases Bool.and_eq_true_iff.mp hConflictPrefix with
                  ⟨_hConflictTheory, hGuardEq⟩
                cases hConflictPayload : conflictNode.payload with
                | theoryConflict _ =>
                    rw [hConflictPayload] at hLearnedEqBool
                    have hLearnedEqConflict :
                        learnedPayload.learned =
                          learnedClauseOfGuards conflictNode.guards :=
                      PropResolution.clauseEq_eq.mp (by simpa using hLearnedEqBool)
                    by_cases hParentGuards :
                        Node.GuardsHold valuation
                          (cert.dag.nodeAt link.parent hParentSize).guards
                    · have hParentInvariant :
                          Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
                            (cert.dag.nodeAt link.parent hParentSize) :=
                        hParents link.parent hParentMem
                      have hParentSat :=
                        hParentInvariant env hProblem hParentGuards
                      exact False.elim
                        (Clause.not_satisfies_of_isEmpty
                          hParentConclusionEmpty hParentSat)
                    · have hNotConflictGuards :
                          ¬ Node.GuardsHold valuation conflictNode.guards := by
                        intro hConflictGuards
                        apply hParentGuards
                        intro lit hLit
                        have hCanonical :
                            canonicalGuards
                              (cert.dag.nodeAt link.parent hParentSize).guards =
                              canonicalGuards conflictNode.guards :=
                          PropResolution.clauseEq_eq.mp
                            (by simpa [guardSetEq] using hGuardEq)
                        exact hConflictGuards lit (by
                          simpa [hCanonical] using hLit)
                      have hClauseEq :
                          link.clause = learnedClauseOfGuards conflictNode.guards :=
                        hLinkLearnedEq.trans hLearnedEqConflict
                      have hLearnedSat :=
                        PropLearnedClauseLink.satisfies_of_not_guards
                          (base := valuation) (atomMap := payload.atomMap)
                          (env := env) (link := link)
                          (guards := conflictNode.guards)
                          hClauseEq hOutside hNotConflictGuards
                      simpa [hInitialEq] using hLearnedSat
                | source _ =>
                    have hFalse : False := by
                      simp [hConflictPayload] at hLearnedEqBool
                    exact False.elim hFalse
                | avatarSplit _ =>
                    have hFalse : False := by
                      simp [hConflictPayload] at hLearnedEqBool
                    exact False.elim hFalse
                | avatarComponent _ =>
                    have hFalse : False := by
                      simp [hConflictPayload] at hLearnedEqBool
                    exact False.elim hFalse
                | localRule _ =>
                    have hFalse : False := by
                      simp [hConflictPayload] at hLearnedEqBool
                    exact False.elim hFalse
                | propositionalLearnedClause _ =>
                    have hFalse : False := by
                      simp [hConflictPayload] at hLearnedEqBool
                    exact False.elim hFalse
                | residualCdcl _ =>
                    have hFalse : False := by
                      simp [hConflictPayload] at hLearnedEqBool
                    exact False.elim hFalse
        | source _ =>
            have hFalse : False := by
              simp [hParentPayload] at hLearnedMatch
            exact False.elim hFalse
        | avatarSplit _ =>
            have hFalse : False := by
              simp [hParentPayload] at hLearnedMatch
            exact False.elim hFalse
        | avatarComponent _ =>
            have hFalse : False := by
              simp [hParentPayload] at hLearnedMatch
            exact False.elim hFalse
        | localRule _ =>
            have hFalse : False := by
              simp [hParentPayload] at hLearnedMatch
            exact False.elim hFalse
        | theoryConflict _ =>
            have hFalse : False := by
              simp [hParentPayload] at hLearnedMatch
            exact False.elim hFalse
        | residualCdcl _ =>
            have hFalse : False := by
              simp [hParentPayload] at hLearnedMatch
            exact False.elim hFalse
    | avatarSkeleton link =>
        have hUnsupported :
            (PropInitialJustification.avatarSkeleton link :
              PropInitialJustification σ).guardedSoundnessSupported = true := by
          simpa [hJustification] using hJustificationSupported
        simp [PropInitialJustification.guardedSoundnessSupported] at hUnsupported
  exact False.elim
    (PropResolution.checkedUnsat_sound hInitialSatisfies hCheckedUnsat)

/-- checked DAG 拓扑 step 的 guarded parent-copy 本地规则分支。 -/
theorem localRuleParentCopyGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (parent : ParentClause σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .parentCopy parent) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  rcases LocalRuleEvidence.parentCopy_check_sound hEvidenceCheck with
    ⟨hParentInBool, _hConclusion⟩
  have hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentInBool
  let hParentLt := cert.parentsBefore index hIndex parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt parent.id hParentSize) :=
    hParents parent.id hParentMem
  have hSnapshotBool :=
    cert.parentCopySnapshotChecked index hIndex payload parent hLocal hEvidence
  have hParentClause :
      parent.clause = (cert.dag.nodeAt parent.id hParentSize).conclusion :=
    cert.parentClause_eq_nodeAt_of_snapshot parent hParentSize hSnapshotBool
  have hParentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt parent.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      parent.id hParentMem hParentSize
  intro M env hProblem hGuards
  exact (Node.localRuleParentCopyGuardedRefutationInvariant_of_payload_check
    (problem := cert.dag.problem)
    (node := cert.dag.nodeAt index hIndex)
    (parentNode := cert.dag.nodeAt parent.id hParentSize)
    hLocal hEvidence hParentClause hParentGuards hParentInvariant
    (cert.nodePayloadChecked index hIndex)) (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded resolution 本地规则分支。 -/
theorem resolutionGuardedTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : ResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .resolution evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.resolution evidence) = true := by
    simpa [LocalRuleEvidence.check, ResolutionEvidence.check] using hEvidenceCheck
  have hIds := LocalRuleEvidence.resolution_check_parents hEvidenceCheck'
  have hSnapshots :=
    cert.resolutionSnapshotsChecked index hIndex payload evidence hLocal hEvidence
  have hLeftMem : evidence.left.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hRightMem : evidence.right.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hLeftLt := cert.parentsBefore index hIndex evidence.left.id hLeftMem
  let hRightLt := cert.parentsBefore index hIndex evidence.right.id hRightMem
  let hLeftSize := Nat.lt_trans hLeftLt hIndex
  let hRightSize := Nat.lt_trans hRightLt hIndex
  have hLeftClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.left hLeftSize hSnapshots.1
  have hRightClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.right hRightSize hSnapshots.2
  have hLeftInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.left.id hLeftSize) :=
    hParents evidence.left.id hLeftMem
  have hRightInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.right.id hRightSize) :=
    hParents evidence.right.id hRightMem
  have hLeftGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.left.id hLeftSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.left.id hLeftMem hLeftSize
  have hRightGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.right.id hRightSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.right.id hRightMem hRightSize
  intro M env hProblem hGuards
  exact (Node.resolutionGuardedRefutationInvariant_of_payload_check
    (problem := cert.dag.problem)
    (node := cert.dag.nodeAt index hIndex)
    (leftNode := cert.dag.nodeAt evidence.left.id hLeftSize)
    (rightNode := cert.dag.nodeAt evidence.right.id hRightSize)
    hLocal hEvidence hLeftClause hRightClause hLeftGuards hRightGuards
    hLeftInvariant hRightInvariant
    (cert.nodePayloadChecked index hIndex)) (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded factoring 本地规则分支。 -/
theorem factoringGuardedTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : FactoringEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .factoring evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.factoring evidence) = true := by
    simpa [LocalRuleEvidence.check, FactoringEvidence.check] using hEvidenceCheck
  have hParentIn := LocalRuleEvidence.factoring_check_parent hEvidenceCheck'
  have hSnapshot :=
    cert.factoringSnapshotChecked index hIndex payload evidence hLocal hEvidence
  have hParentMem : evidence.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.parentsBefore index hIndex evidence.parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.parent hParentSize hSnapshot
  have hParentInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.parent.id hParentSize) :=
    hParents evidence.parent.id hParentMem
  have hParentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.parent.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.parent.id hParentMem hParentSize
  intro M env hProblem hGuards
  exact (Node.factoringGuardedRefutationInvariant_of_payload_check
    (problem := cert.dag.problem)
    (node := cert.dag.nodeAt index hIndex)
    (parentNode := cert.dag.nodeAt evidence.parent.id hParentSize)
    hLocal hEvidence hParentClause hParentGuards hParentInvariant
    (cert.nodePayloadChecked index hIndex)) (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded equality-resolution 本地规则分支。 -/
theorem equalityResolutionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : EqualityResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .equalityResolution evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.equalityResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, EqualityResolutionEvidence.check] using hEvidenceCheck
  have hParentIn := LocalRuleEvidence.equalityResolution_check_parent hEvidenceCheck'
  have hSnapshot :=
    cert.equalityResolutionSnapshotChecked index hIndex payload evidence hLocal hEvidence
  have hParentMem : evidence.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.parentsBefore index hIndex evidence.parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.parent hParentSize hSnapshot
  have hParentInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.parent.id hParentSize) :=
    hParents evidence.parent.id hParentMem
  have hParentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.parent.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.parent.id hParentMem hParentSize
  intro M env hProblem hGuards
  exact (Node.equalityResolutionGuardedRefutationInvariant_of_payload_check
    (problem := cert.dag.problem)
    (node := cert.dag.nodeAt index hIndex)
    (parentNode := cert.dag.nodeAt evidence.parent.id hParentSize)
    hLocal hEvidence hParentClause hParentGuards hParentInvariant
    (cert.nodePayloadChecked index hIndex)) (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded substituted resolution 分支。 -/
theorem substitutedResolutionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedResolution evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.substitutedResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedResolutionEvidence.check] using
      hEvidenceCheck
  have hIds := SubstitutedResolutionEvidence.check_parents hEvidenceCheck'
  have hSnapshots :=
    cert.substitutedResolutionSnapshotsChecked index hIndex payload evidence
      hLocal hEvidence
  have hLeftMem :
      evidence.left.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hRightMem :
      evidence.right.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hLeftLt := cert.parentsBefore index hIndex evidence.left.id hLeftMem
  let hRightLt := cert.parentsBefore index hIndex evidence.right.id hRightMem
  let hLeftSize := Nat.lt_trans hLeftLt hIndex
  let hRightSize := Nat.lt_trans hRightLt hIndex
  have hLeftClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.left hLeftSize hSnapshots.1
  have hRightClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.right hRightSize hSnapshots.2
  have hLeftInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.left.id hLeftSize) :=
    hParents evidence.left.id hLeftMem
  have hRightInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.right.id hRightSize) :=
    hParents evidence.right.id hRightMem
  have hLeftGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation
          (cert.dag.nodeAt evidence.left.id hLeftSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.left.id hLeftMem hLeftSize
  have hRightGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation
          (cert.dag.nodeAt evidence.right.id hRightSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.right.id hRightMem hRightSize
  intro M env hProblem hGuards
  exact
    (Node.substitutedResolutionGuardedRefutationInvariant_of_payload_check
      (problem := cert.dag.problem)
      (node := cert.dag.nodeAt index hIndex)
      (leftNode := cert.dag.nodeAt evidence.left.id hLeftSize)
      (rightNode := cert.dag.nodeAt evidence.right.id hRightSize)
      hLocal hEvidence hLeftClause hRightClause hLeftGuards hRightGuards
      hLeftInvariant hRightInvariant (cert.nodePayloadChecked index hIndex))
      (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded substituted factoring 分支。 -/
theorem substitutedFactoringGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedFactoringEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedFactoring evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.substitutedFactoring evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedFactoringEvidence.check] using
      hEvidenceCheck
  have hParentIn :=
    (SubstitutedFactoringEvidence.check_sound hEvidenceCheck').1
  have hSnapshot :=
    cert.substitutedFactoringSnapshotChecked index hIndex payload evidence
      hLocal hEvidence
  have hParentMem :
      evidence.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.parentsBefore index hIndex evidence.parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.parent hParentSize hSnapshot
  have hParentInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.parent.id hParentSize) :=
    hParents evidence.parent.id hParentMem
  have hParentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation
          (cert.dag.nodeAt evidence.parent.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.parent.id hParentMem hParentSize
  intro M env hProblem hGuards
  exact
    (Node.substitutedFactoringGuardedRefutationInvariant_of_payload_check
      (problem := cert.dag.problem)
      (node := cert.dag.nodeAt index hIndex)
      (parentNode := cert.dag.nodeAt evidence.parent.id hParentSize)
      hLocal hEvidence hParentClause hParentGuards hParentInvariant
      (cert.nodePayloadChecked index hIndex))
      (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded substituted equality-resolution 分支。 -/
theorem substitutedEqualityResolutionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ)
    (evidence : SubstitutedEqualityResolutionEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedEqualityResolution evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.substitutedEqualityResolution evidence) = true := by
    simpa [LocalRuleEvidence.check, SubstitutedEqualityResolutionEvidence.check] using
      hEvidenceCheck
  have hParentIn :=
    (SubstitutedEqualityResolutionEvidence.check_sound hEvidenceCheck').1
  have hSnapshot :=
    cert.substitutedEqualityResolutionSnapshotChecked index hIndex payload evidence
      hLocal hEvidence
  have hParentMem :
      evidence.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.parentsBefore index hIndex evidence.parent.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hParentClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.parent hParentSize hSnapshot
  have hParentInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.parent.id hParentSize) :=
    hParents evidence.parent.id hParentMem
  have hParentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation
          (cert.dag.nodeAt evidence.parent.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.parent.id hParentMem hParentSize
  intro M env hProblem hGuards
  exact
    (Node.substitutedEqualityResolutionGuardedRefutationInvariant_of_payload_check
      (problem := cert.dag.problem)
      (node := cert.dag.nodeAt index hIndex)
      (parentNode := cert.dag.nodeAt evidence.parent.id hParentSize)
      hLocal hEvidence hParentClause hParentGuards hParentInvariant
      (cert.nodePayloadChecked index hIndex))
      (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded 通用重写/叠加核心。 -/
private theorem rewriteGuardedTopologicalStepCore {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : RewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hConclusion : (cert.dag.nodeAt index hIndex).conclusion = evidence.result)
    (hIds : evidence.equality.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
      evidence.target.idIn (cert.dag.nodeAt index hIndex).parents = true)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hSnapshots :=
    cert.rewriteSnapshotsChecked index hIndex payload evidence hLocal hParentClauses
  have hEqualityMem :
      evidence.equality.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hTargetMem :
      evidence.target.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hEqualityLt := cert.parentsBefore index hIndex evidence.equality.id hEqualityMem
  let hTargetLt := cert.parentsBefore index hIndex evidence.target.id hTargetMem
  let hEqualitySize := Nat.lt_trans hEqualityLt hIndex
  let hTargetSize := Nat.lt_trans hTargetLt hIndex
  have hEqualityClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.equality hEqualitySize hSnapshots.1
  have hTargetClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.target hTargetSize hSnapshots.2
  have hEqualityInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.equality.id hEqualitySize) :=
    hParents evidence.equality.id hEqualityMem
  have hTargetInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.target.id hTargetSize) :=
    hParents evidence.target.id hTargetMem
  have hEqualityGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.equality.id hEqualitySize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.equality.id hEqualityMem hEqualitySize
  have hTargetGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.target.id hTargetSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.target.id hTargetMem hTargetSize
  intro M env hProblem hGuards
  rw [hConclusion]
  exact RewriteEvidence.satisfies_result
    (by simpa [hEqualityClause] using
      hEqualityInvariant env hProblem (hEqualityGuards hGuards))
    (by simpa [hTargetClause] using
      hTargetInvariant env hProblem (hTargetGuards hGuards))

/-- checked DAG 拓扑 step 的 guarded demodulation 本地规则分支。 -/
theorem demodulationGuardedTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : RewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .demodulation evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.demodulation evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.demodulation_check_conclusion hEvidenceCheck'
  have hIds := LocalRuleEvidence.demodulation_check_parents hEvidenceCheck'
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem hGuards
  exact (cert.rewriteGuardedTopologicalStepCore valuation index hIndex hParents
    payload evidence hLocal hConclusion hIds hParentClauses)
    (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded positive-superposition 本地规则分支。 -/
theorem positiveSuperpositionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : RewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .positiveSuperposition evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.positiveSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.positiveSuperposition_check_conclusion hEvidenceCheck'
  have hIds := LocalRuleEvidence.positiveSuperposition_check_parents hEvidenceCheck'
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem hGuards
  exact (cert.rewriteGuardedTopologicalStepCore valuation index hIndex hParents
    payload evidence hLocal hConclusion hIds hParentClauses)
    (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded negative-superposition 本地规则分支。 -/
theorem negativeSuperpositionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : RewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .negativeSuperposition evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      LocalRuleEvidence.check (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion
        (.negativeSuperposition evidence) = true := by
    simpa [LocalRuleEvidence.check, RewriteEvidence.check] using hEvidenceCheck
  have hConclusion := LocalRuleEvidence.negativeSuperposition_check_conclusion hEvidenceCheck'
  have hIds := LocalRuleEvidence.negativeSuperposition_check_parents hEvidenceCheck'
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem hGuards
  exact (cert.rewriteGuardedTopologicalStepCore valuation index hIndex hParents
    payload evidence hLocal hConclusion hIds hParentClauses)
    (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded substituted rewrite/superposition 核心。 -/
private theorem substitutedRewriteGuardedTopologicalStepCore {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hAdmissible : TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution)
    (hConclusion : (cert.dag.nodeAt index hIndex).conclusion = evidence.result)
    (hIds : evidence.equality.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
      evidence.target.idIn (cert.dag.nodeAt index hIndex).parents = true)
    (hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target]) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hSnapshots :=
    cert.substitutedRewriteSnapshotsChecked index hIndex payload evidence hLocal
      hParentClauses
  have hEqualityMem :
      evidence.equality.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.1
  have hTargetMem :
      evidence.target.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIds.2
  let hEqualityLt := cert.parentsBefore index hIndex evidence.equality.id hEqualityMem
  let hTargetLt := cert.parentsBefore index hIndex evidence.target.id hTargetMem
  let hEqualitySize := Nat.lt_trans hEqualityLt hIndex
  let hTargetSize := Nat.lt_trans hTargetLt hIndex
  have hEqualityClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.equality hEqualitySize
      hSnapshots.1
  have hTargetClause :=
    cert.parentClause_eq_nodeAt_of_snapshot evidence.target hTargetSize hSnapshots.2
  have hEqualityInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.equality.id hEqualitySize) :=
    hParents evidence.equality.id hEqualityMem
  have hTargetInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt evidence.target.id hTargetSize) :=
    hParents evidence.target.id hTargetMem
  have hEqualityGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.equality.id hEqualitySize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.equality.id hEqualityMem hEqualitySize
  have hTargetGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt evidence.target.id hTargetSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex payload hLocal
      evidence.target.id hTargetMem hTargetSize
  intro M env hProblem hGuards
  rw [hConclusion]
  exact SubstitutedRewriteEvidence.satisfies_result
    (by
      simpa [SubstitutedRewriteEvidence.equalityClause, hEqualityClause] using
        Node.satisfies_applySubstitution_of_guardedRefutationInvariant
          (problem := cert.dag.problem) (subst := evidence.substitution)
          (node := cert.dag.nodeAt evidence.equality.id hEqualitySize)
          hAdmissible hEqualityInvariant hProblem
          (hEqualityGuards hGuards))
    (by
      simpa [SubstitutedRewriteEvidence.targetClause, hTargetClause] using
        Node.satisfies_applySubstitution_of_guardedRefutationInvariant
          (problem := cert.dag.problem) (subst := evidence.substitution)
          (node := cert.dag.nodeAt evidence.target.id hTargetSize)
          hAdmissible hTargetInvariant hProblem
          (hTargetGuards hGuards))

/-- checked DAG 拓扑 step 的 guarded substituted demodulation 本地规则分支。 -/
theorem substitutedDemodulationGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedDemodulation evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      SubstitutedRewriteEvidence.check .demodulation
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedRewriteEvidence.check_sound hEvidenceCheck' with
    ⟨hEqualityIn, hTargetIn, _hContains, _hNeedle, _hKind, hConclusion⟩
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem hGuards
  exact (cert.substitutedRewriteGuardedTopologicalStepCore valuation
    index hIndex hParents payload evidence hLocal hAdmissible hConclusion
    ⟨hEqualityIn, hTargetIn⟩ hParentClauses)
    (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded substituted positive-superposition 本地规则分支。 -/
theorem substitutedPositiveSuperpositionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedPositiveSuperposition evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      SubstitutedRewriteEvidence.check .positiveSuperposition
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedRewriteEvidence.check_sound hEvidenceCheck' with
    ⟨hEqualityIn, hTargetIn, _hContains, _hNeedle, _hKind, hConclusion⟩
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem hGuards
  exact (cert.substitutedRewriteGuardedTopologicalStepCore valuation
    index hIndex hParents payload evidence hLocal hAdmissible hConclusion
    ⟨hEqualityIn, hTargetIn⟩ hParentClauses)
    (env := env) hProblem hGuards

/-- checked DAG 拓扑 step 的 guarded substituted negative-superposition 本地规则分支。 -/
theorem substitutedNegativeSuperpositionGuardedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (evidence : SubstitutedRewriteEvidence σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (hEvidence : payload.evidence = .substitutedNegativeSuperposition evidence) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := cert.nodePayloadChecked index hIndex
  rw [hLocal] at hPayloadCheck
  have hLocalCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with ⟨hLeft, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hParentsNonempty, hEvidenceCheck⟩
  rw [hEvidence] at hEvidenceCheck
  have hEvidenceCheck' :
      SubstitutedRewriteEvidence.check .negativeSuperposition
        (cert.dag.nodeAt index hIndex).parents
        (cert.dag.nodeAt index hIndex).conclusion evidence = true := by
    simpa [LocalRuleEvidence.check] using hEvidenceCheck
  have hAdmissible := SubstitutedRewriteEvidence.check_admissible hEvidenceCheck'
  rcases SubstitutedRewriteEvidence.check_sound hEvidenceCheck' with
    ⟨hEqualityIn, hTargetIn, _hContains, _hNeedle, _hKind, hConclusion⟩
  have hParentClauses :
      payload.evidence.parentClauses = #[evidence.equality, evidence.target] := by
    rw [hEvidence]
    simp [LocalRuleEvidence.parentClauses]
  intro M env hProblem hGuards
  exact (cert.substitutedRewriteGuardedTopologicalStepCore valuation
    index hIndex hParents payload evidence hLocal hAdmissible hConclusion
    ⟨hEqualityIn, hTargetIn⟩ hParentClauses)
    (env := env) hProblem hGuards

/-- checked DAG 上可直接使用的拓扑归纳骨架。 -/
theorem topologicalInduction {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {P : ∀ index, index < cert.dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < cert.dag.nodes.size),
        (∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
            P parent
              (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)
              (cert.dag.nodeAt parent
                (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex))) →
          P index hIndex (cert.dag.nodeAt index hIndex)) :
    ∀ index (hIndex : index < cert.dag.nodes.size),
      P index hIndex (cert.dag.nodeAt index hIndex) :=
  cert.dag.topologicalInduction cert.parentsBefore hStep

/-- checked DAG 根节点版本的拓扑归纳骨架。 -/
theorem rootByTopologicalInduction {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {P : ∀ index, index < cert.dag.nodes.size → Node σ → Prop}
    (hStep :
      ∀ index (hIndex : index < cert.dag.nodes.size),
        (∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
            P parent
              (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)
              (cert.dag.nodeAt parent
                (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex))) →
          P index hIndex (cert.dag.nodeAt index hIndex)) :
    P cert.dag.root cert.rootExists (cert.dag.nodeAt cert.dag.root cert.rootExists) :=
  cert.dag.rootByTopologicalInduction cert.rootExists cert.parentsBefore hStep

/-- 当前已证明 soundness 片段的一步拓扑回放。 -/
theorem soundnessSupportedTopologicalStep {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    (hSupported : cert.dag.soundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex))) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hNodeSupported := cert.nodeSoundnessSupported hSupported index hIndex
  cases hPayload : (cert.dag.nodeAt index hIndex).payload with
  | source initialIndex =>
      intro M env hProblem
      exact (cert.sourceTopologicalStep index hIndex hParents initialIndex hPayload)
        (env := env) hProblem
  | avatarSplit payload =>
      simp [hPayload, Payload.soundnessSupported] at hNodeSupported
  | avatarComponent payload =>
      simp [hPayload, Payload.soundnessSupported] at hNodeSupported
  | localRule payload =>
      cases hEvidence : payload.evidence with
      | parentCopy parent =>
          intro M env hProblem
          exact (cert.localRuleParentCopyTopologicalStep index hIndex hParents
            payload parent hPayload hEvidence) (env := env) hProblem
      | resolution evidence =>
          intro M env hProblem
          exact (cert.resolutionTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | factoring evidence =>
          intro M env hProblem
          exact (cert.factoringTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | equalityResolution evidence =>
          intro M env hProblem
          exact (cert.equalityResolutionTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | demodulation evidence =>
          intro M env hProblem
          exact (cert.demodulationTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | positiveSuperposition evidence =>
          intro M env hProblem
          exact (cert.positiveSuperpositionTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | negativeSuperposition evidence =>
          intro M env hProblem
          exact (cert.negativeSuperpositionTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | substitutedResolution evidence =>
          intro M env hProblem
          exact (cert.substitutedResolutionTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | substitutedFactoring evidence =>
          intro M env hProblem
          exact (cert.substitutedFactoringTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | substitutedEqualityResolution evidence =>
          intro M env hProblem
          exact (cert.substitutedEqualityResolutionTopologicalStep index hIndex
            hParents payload evidence hPayload hEvidence) (env := env) hProblem
      | substitutedDemodulation evidence =>
          intro M env hProblem
          exact (cert.substitutedDemodulationTopologicalStep index hIndex
            hParents payload evidence hPayload hEvidence) (env := env) hProblem
      | substitutedPositiveSuperposition evidence =>
          intro M env hProblem
          exact (cert.substitutedPositiveSuperpositionTopologicalStep index hIndex
            hParents payload evidence hPayload hEvidence) (env := env) hProblem
      | substitutedNegativeSuperposition evidence =>
          intro M env hProblem
          exact (cert.substitutedNegativeSuperpositionTopologicalStep index hIndex
            hParents payload evidence hPayload hEvidence) (env := env) hProblem
      | standardizedSubstitutedResolution evidence =>
          intro M env hProblem
          exact (cert.standardizedResolutionTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | standardizedSubstitutedDemodulation evidence =>
          intro M env hProblem
          exact (cert.standardizedDemodulationTopologicalStep index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem
      | standardizedSubstitutedPositiveSuperposition evidence =>
          intro M env hProblem
          exact (cert.standardizedPositiveSuperpositionTopologicalStep index hIndex
            hParents payload evidence hPayload hEvidence) (env := env) hProblem
      | standardizedSubstitutedNegativeSuperposition evidence =>
          intro M env hProblem
          exact (cert.standardizedNegativeSuperpositionTopologicalStep index hIndex
            hParents payload evidence hPayload hEvidence) (env := env) hProblem
  | theoryConflict payload =>
      let valuation : PropResolution.Valuation := fun _ => False
      have hGuardedParents :
          ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
            Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
              (cert.dag.nodeAt parent
                (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex)) :=
        fun parent hParent =>
          Node.guardedRefutationInvariant_of_refutationInvariant
            (hParents parent hParent)
      have hNodeUnguarded :=
        DAG.nodeUnguarded_of_soundnessSupported_eq_true hSupported index hIndex
      have hGuards :
          Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards :=
        Node.GuardsHold.of_isEmpty (by
          simpa [Node.unguarded] using hNodeUnguarded)
      intro M env hProblem
      exact (cert.theoryConflictGuardedTopologicalStep valuation index hIndex
        hGuardedParents payload hPayload) (env := env) hProblem hGuards
  | propositionalLearnedClause payload =>
      simp [hPayload, Payload.soundnessSupported] at hNodeSupported
  | residualCdcl payload =>
      simp [hPayload, Payload.soundnessSupported] at hNodeSupported

/-- 当前已证明 guarded soundness 片段的一步拓扑回放。 -/
theorem guardedSoundnessSupportedTopologicalStep {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
          (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.parentsBefore index hIndex parent hParent) hIndex))) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt index hIndex) := by
  have hNodeSupported := cert.nodeGuardedSoundnessSupported hSupported index hIndex
  cases hPayload : (cert.dag.nodeAt index hIndex).payload with
  | source initialIndex =>
      intro M env hProblem hGuards
      exact (cert.sourceGuardedTopologicalStep valuation index hIndex hParents
        initialIndex hPayload) (env := env) hProblem hGuards
  | avatarSplit payload =>
      simp [hPayload, Payload.guardedSoundnessSupported] at hNodeSupported
  | avatarComponent payload =>
      simp [hPayload, Payload.guardedSoundnessSupported] at hNodeSupported
  | localRule payload =>
      cases hEvidence : payload.evidence with
      | parentCopy parent =>
          intro M env hProblem hGuards
          exact (cert.localRuleParentCopyGuardedTopologicalStep valuation index hIndex
            hParents payload parent hPayload hEvidence)
            (env := env) hProblem hGuards
      | resolution evidence =>
          intro M env hProblem hGuards
          exact (cert.resolutionGuardedTopologicalStep valuation index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem hGuards
      | factoring evidence =>
          intro M env hProblem hGuards
          exact (cert.factoringGuardedTopologicalStep valuation index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem hGuards
      | equalityResolution evidence =>
          intro M env hProblem hGuards
          exact (cert.equalityResolutionGuardedTopologicalStep valuation index hIndex
            hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | demodulation evidence =>
          intro M env hProblem hGuards
          exact (cert.demodulationGuardedTopologicalStep valuation index hIndex hParents
            payload evidence hPayload hEvidence) (env := env) hProblem hGuards
      | positiveSuperposition evidence =>
          intro M env hProblem hGuards
          exact (cert.positiveSuperpositionGuardedTopologicalStep valuation index hIndex
            hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | negativeSuperposition evidence =>
          intro M env hProblem hGuards
          exact (cert.negativeSuperpositionGuardedTopologicalStep valuation index hIndex
            hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | substitutedResolution evidence =>
          intro M env hProblem hGuards
          exact (cert.substitutedResolutionGuardedTopologicalStep valuation
            index hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | substitutedFactoring evidence =>
          intro M env hProblem hGuards
          exact (cert.substitutedFactoringGuardedTopologicalStep valuation
            index hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | substitutedEqualityResolution evidence =>
          intro M env hProblem hGuards
          exact (cert.substitutedEqualityResolutionGuardedTopologicalStep valuation
            index hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | substitutedDemodulation evidence =>
          intro M env hProblem hGuards
          exact (cert.substitutedDemodulationGuardedTopologicalStep valuation
            index hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | substitutedPositiveSuperposition evidence =>
          intro M env hProblem hGuards
          exact (cert.substitutedPositiveSuperpositionGuardedTopologicalStep
            valuation index hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | substitutedNegativeSuperposition evidence =>
          intro M env hProblem hGuards
          exact (cert.substitutedNegativeSuperpositionGuardedTopologicalStep
            valuation index hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | standardizedSubstitutedResolution evidence =>
          intro M env hProblem hGuards
          exact (cert.standardizedResolutionGuardedTopologicalStep valuation index
            hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | standardizedSubstitutedDemodulation evidence =>
          intro M env hProblem hGuards
          exact (cert.standardizedDemodulationGuardedTopologicalStep valuation index
            hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | standardizedSubstitutedPositiveSuperposition evidence =>
          intro M env hProblem hGuards
          exact (cert.standardizedPositiveSuperpositionGuardedTopologicalStep valuation
            index hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
      | standardizedSubstitutedNegativeSuperposition evidence =>
          intro M env hProblem hGuards
          exact (cert.standardizedNegativeSuperpositionGuardedTopologicalStep valuation
            index hIndex hParents payload evidence hPayload hEvidence)
            (env := env) hProblem hGuards
  | theoryConflict payload =>
      intro M env hProblem hGuards
      exact (cert.theoryConflictGuardedTopologicalStep valuation index hIndex hParents
        payload hPayload) (env := env) hProblem hGuards
  | propositionalLearnedClause payload =>
      intro M env hProblem hGuards
      exact (cert.propositionalLearnedClauseGuardedTopologicalStep valuation
        index hIndex hParents payload hPayload) (env := env) hProblem hGuards
  | residualCdcl payload =>
      have hPayloadSupported : payload.guardedSoundnessSupported = true := by
        simpa [hPayload, Payload.guardedSoundnessSupported] using hNodeSupported
      intro M env hProblem hGuards
      exact (cert.residualCdclGuardedTopologicalStep valuation index hIndex
        hParents payload hPayload hPayloadSupported)
        (env := env) hProblem hGuards

/-- 整图 soundness：当前支持片段中的每个 checked 节点都满足反证语义不变量。 -/
theorem refutationInvariant_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (hSupported : cert.dag.soundnessSupported = true) :
    DAG.RefutationInvariant.{x} cert.dag :=
  cert.topologicalInduction
    (P := fun _ _ node => Node.RefutationInvariant.{x} cert.dag.problem node)
    (fun index hIndex hParents =>
      cert.soundnessSupportedTopologicalStep hSupported index hIndex hParents)

/-- 整图 guarded soundness：当前 guarded 支持片段中的每个 checked 节点都满足条件化不变量。 -/
theorem guardedRefutationInvariant_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    DAG.GuardedRefutationInvariant.{x} cert.dag valuation :=
  cert.topologicalInduction
    (P := fun _ _ node =>
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation node)
    (fun index hIndex hParents =>
      cert.guardedSoundnessSupportedTopologicalStep valuation hSupported
        index hIndex hParents)

/-- 根节点 soundness：整图拓扑归纳直接给出 root 的反证语义不变量。 -/
theorem rootRefutationInvariant_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (hSupported : cert.dag.soundnessSupported = true) :
    Node.RefutationInvariant.{x} cert.dag.problem
      (cert.dag.nodeAt cert.dag.root cert.rootExists) :=
  cert.rootByTopologicalInduction
    (P := fun _ _ node => Node.RefutationInvariant.{x} cert.dag.problem node)
    (fun index hIndex hParents =>
      cert.soundnessSupportedTopologicalStep hSupported index hIndex hParents)

/-- 根节点 guarded soundness：整图拓扑归纳直接给出 root 的条件化反证语义不变量。 -/
theorem rootGuardedRefutationInvariant_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
      (cert.dag.nodeAt cert.dag.root cert.rootExists) :=
  cert.rootByTopologicalInduction
    (P := fun _ _ node =>
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation node)
    (fun index hIndex hParents =>
      cert.guardedSoundnessSupportedTopologicalStep valuation hSupported
        index hIndex hParents)

/-- 若 root 的反证语义不变量成立，则 checked DAG 的空根给出语义矛盾。 -/
theorem rootEmptyContradiction_of_rootInvariant {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (hRootInvariant :
      Node.RefutationInvariant.{x} cert.dag.problem
        (cert.dag.nodeAt cert.dag.root cert.rootExists))
    {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M)
    (hProblem : cert.dag.problem.Valid env) : False :=
  Clause.not_satisfies_of_isEmpty cert.rootNodeClosed
    (hRootInvariant env hProblem)

/-- 若 root 的 guarded 反证语义不变量成立，则 checked DAG 的无 guard 空根给出语义矛盾。 -/
theorem rootEmptyContradiction_of_rootGuardedInvariant {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (hRootInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation
        (cert.dag.nodeAt cert.dag.root cert.rootExists))
    {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M)
    (hProblem : cert.dag.problem.Valid env) : False := by
  have hRootGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt cert.dag.root cert.rootExists).guards :=
    Node.GuardsHold.of_isEmpty (by
      simpa [Node.unguarded] using cert.rootNodeUnguarded)
  exact Clause.not_satisfies_of_isEmpty cert.rootNodeClosed
    (hRootInvariant env hProblem hRootGuards)

/-- 当前支持片段的 root empty contradiction。 -/
theorem rootEmptyContradiction_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ))
    (hSupported : cert.dag.soundnessSupported = true)
    {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M)
    (hProblem : cert.dag.problem.Valid env) : False :=
  cert.rootEmptyContradiction_of_rootInvariant
    (cert.rootRefutationInvariant_of_soundnessSupported hSupported)
    env hProblem

/-- 当前 guarded 支持片段的 root empty contradiction。 -/
theorem rootEmptyContradiction_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (valuation : PropResolution.Valuation)
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M)
    (hProblem : cert.dag.problem.Valid env) : False :=
  cert.rootEmptyContradiction_of_rootGuardedInvariant valuation
    (cert.rootGuardedRefutationInvariant_of_guardedSoundnessSupported valuation
      hSupported)
    env hProblem

/-- 当前支持片段的 checked DAG 证书推出其直接编译来源的深嵌入语义蕴涵。 -/
theorem semanticallyEntails_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.soundnessSupported = true) :
    SetLevel.SemanticallyEntailsAt.{x} problem.theory problem.target := by
  intro M env hModels
  classical
  by_cases hTarget : Logic.FirstOrder.Formula.satisfies env problem.target
  · exact hTarget
  · have hClauseProblem : cert.dag.problem.Valid env := by
      rw [hProblem]
      exact ClauseProblem.valid_ofDeepProblem_of_freeClosed
        problem env hClosed hModels hTarget
    exact False.elim
      (cert.rootEmptyContradiction_of_soundnessSupported
        hSupported env hClauseProblem)

/-- 当前 guarded 支持片段的 checked DAG 证书推出其直接编译来源的深嵌入语义蕴涵。 -/
theorem semanticallyEntails_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    SetLevel.SemanticallyEntailsAt.{x} problem.theory problem.target := by
  intro M env hModels
  classical
  let valuation : PropResolution.Valuation := fun _ => False
  by_cases hTarget : Logic.FirstOrder.Formula.satisfies env problem.target
  · exact hTarget
  · have hClauseProblem : cert.dag.problem.Valid env := by
      rw [hProblem]
      exact ClauseProblem.valid_ofDeepProblem_of_freeClosed
        problem env hClosed hModels hTarget
    exact False.elim
      (cert.rootEmptyContradiction_of_guardedSoundnessSupported
        valuation hSupported env hClauseProblem)

/--
当前 guarded 支持片段也可消费一个显式的 countermodel-to-clause-validity 桥。

这条接口不要求 DAG problem 由公式 problem 直接编译；预处理器可以先扩张模型，再把
canonical 初始字句有效性提供给整图 root contradiction。
-/
theorem semanticallyEntails_of_guardedSoundnessSupported_of_valid
    {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.dag.problem.Valid targetEnv) :
    SetLevel.SemanticallyEntailsAt.{x} problem.theory problem.target := by
  intro M env hModels
  classical
  let valuation : PropResolution.Valuation := fun _ => False
  by_cases hTarget : Logic.FirstOrder.Formula.satisfies env problem.target
  · exact hTarget
  · rcases hValid env hModels hTarget with ⟨target, targetEnv, hClauseProblem⟩
    exact False.elim
      (cert.rootEmptyContradiction_of_guardedSoundnessSupported
        valuation hSupported targetEnv hClauseProblem)

/-- 当前支持片段的 checked DAG 可物化为任意模型 universe 上的语义证书。 -/
def semanticCertificateAt_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.soundnessSupported = true) :
    SetLevel.SemanticCertificateAt.{x} problem.theory problem.target where
  entails := cert.semanticallyEntails_of_soundnessSupported
    problem hProblem hClosed hSupported

/-- 当前支持片段的 checked DAG 可物化为直接编译来源的零层语义证书。 -/
def semanticCertificate_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.soundnessSupported = true) :
    SetLevel.SemanticCertificate problem.theory problem.target :=
  cert.semanticCertificateAt_of_soundnessSupported
    problem hProblem hClosed hSupported

/-- 当前 guarded 支持片段可物化为任意模型 universe 上的语义证书。 -/
def semanticCertificateAt_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    SetLevel.SemanticCertificateAt.{x} problem.theory problem.target where
  entails := cert.semanticallyEntails_of_guardedSoundnessSupported
    problem hProblem hClosed hSupported

/-- 当前 guarded 支持片段的 checked DAG 可物化为直接编译来源的零层语义证书。 -/
def semanticCertificate_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    SetLevel.SemanticCertificate problem.theory problem.target :=
  cert.semanticCertificateAt_of_guardedSoundnessSupported
    problem hProblem hClosed hSupported

/-- 显式 validity bridge 驱动的 universe-polymorphic 语义证书。 -/
def semanticCertificateAt_of_guardedSoundnessSupported_of_valid
    {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.dag.problem.Valid targetEnv) :
    SetLevel.SemanticCertificateAt.{x} problem.theory problem.target where
  entails :=
    cert.semanticallyEntails_of_guardedSoundnessSupported_of_valid
      problem hSupported hValid

/-- 显式 validity bridge 驱动的零层语义证书。 -/
def semanticCertificate_of_guardedSoundnessSupported_of_valid
    {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    (hValid :
      ∀ {M : SetLevel.Structure σ} (env : SetLevel.Env M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.Structure σ),
              ∃ (targetEnv : SetLevel.Env target),
                cert.dag.problem.Valid targetEnv) :
    SetLevel.SemanticCertificate problem.theory problem.target :=
  cert.semanticCertificateAt_of_guardedSoundnessSupported_of_valid
    problem hSupported hValid

/-- 当前支持片段可直接降为任意模型 universe 上的 checked certificate。 -/
def checkedCertificateAt_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.soundnessSupported = true) :
    SetLevel.CheckedCertificateAt.{x} (σ := σ) where
  problem := problem
  cert := cert.semanticCertificateAt_of_soundnessSupported
    problem hProblem hClosed hSupported

/-- 当前支持片段的 checked DAG 可直接降为自动化主线的零层 checked certificate。 -/
def checkedCertificate_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.soundnessSupported = true) :
    SetLevel.CheckedCertificate (σ := σ) :=
  cert.checkedCertificateAt_of_soundnessSupported
    problem hProblem hClosed hSupported

/-- 当前 guarded 支持片段可直接降为任意模型 universe 上的 checked certificate。 -/
def checkedCertificateAt_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    SetLevel.CheckedCertificateAt.{x} (σ := σ) where
  problem := problem
  cert := cert.semanticCertificateAt_of_guardedSoundnessSupported
    problem hProblem hClosed hSupported

/-- 当前 guarded 支持片段可直接降为自动化主线的零层 checked certificate。 -/
def checkedCertificate_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    SetLevel.CheckedCertificate (σ := σ) :=
  cert.checkedCertificateAt_of_guardedSoundnessSupported
    problem hProblem hClosed hSupported

/-- 当前支持片段的 checked DAG 接入任意模型 universe 的后端成功协议。 -/
def backendSuccessAt_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.soundnessSupported = true) :
    SetLevel.BackendSuccessAt.{x} problem where
  backend := .dagReflection
  phase := .dagCheck
  cert := cert.semanticCertificateAt_of_soundnessSupported
    problem hProblem hClosed hSupported
  audit? := some cert.toComposite
  note := "DAG soundness-supported fragment"

/-- 当前支持片段的 checked DAG 接入零 universe 后端成功协议。 -/
def backendSuccess_of_soundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.soundnessSupported = true) :
    SetLevel.BackendSuccess problem :=
  cert.backendSuccessAt_of_soundnessSupported
    problem hProblem hClosed hSupported

/-- 当前 guarded 支持片段的 checked DAG 接入任意模型 universe 的后端成功协议。 -/
def backendSuccessAt_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    SetLevel.BackendSuccessAt.{x} problem where
  backend := .dagReflection
  phase := .dagCheck
  cert := cert.semanticCertificateAt_of_guardedSoundnessSupported
    problem hProblem hClosed hSupported
  audit? := some cert.toComposite
  note := "DAG guarded soundness-supported fragment"

/-- 当前 guarded 支持片段的 checked DAG 接入零 universe 后端成功协议。 -/
def backendSuccess_of_guardedSoundnessSupported {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    SetLevel.BackendSuccess problem :=
  cert.backendSuccessAt_of_guardedSoundnessSupported
    problem hProblem hClosed hSupported

/-- 显式 validity bridge 驱动的 universe-polymorphic 后端成功结果。 -/
def backendSuccessAt_of_guardedSoundnessSupported_of_valid
    {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.dag.problem.Valid targetEnv) :
    SetLevel.BackendSuccessAt.{x} problem where
  backend := .dagReflection
  phase := .dagCheck
  cert := cert.semanticCertificateAt_of_guardedSoundnessSupported_of_valid
    problem hSupported hValid
  audit? := some cert.toComposite
  note := "DAG guarded soundness-supported fragment via checked preprocessing"

/-- 显式 validity bridge 驱动的零 universe 后端成功结果。 -/
def backendSuccess_of_guardedSoundnessSupported_of_valid
    {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    (cert : CheckedDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.dag.guardedSoundnessSupported = true)
    (hValid :
      ∀ {M : SetLevel.Structure σ} (env : SetLevel.Env M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.Structure σ),
              ∃ (targetEnv : SetLevel.Env target),
                cert.dag.problem.Valid targetEnv) :
    SetLevel.BackendSuccess problem :=
  cert.backendSuccessAt_of_guardedSoundnessSupported_of_valid
    problem hSupported hValid

end CheckedDAG

end DAGCertificate
end Automation
end YesMetaZFC
