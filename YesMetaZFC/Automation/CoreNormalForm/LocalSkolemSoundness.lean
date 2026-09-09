import YesMetaZFC.Automation.CoreNormalForm.LocalSkolem
import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness
/-!
# Local Skolem soundness
本模块证明局部 Skolem 化的模型扩张保守性。核心结论不是同模型语义等价：
全称量词会被打开成新自由变量，存在量词会引入新函数符号。正确接口是源公式可满足时，
checker 固定的局部 Skolem 结果也可满足，从而结果不可满足可以反推源公式不可满足。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm
universe x
namespace Semantics
namespace Model
/-- 模型扩张保留载体；隐式类型比较可展开此定义。 -/
@[implicit_reducible]
def overrideFunction (M : Model) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) : Model where
  Carrier := M.Carrier
  default := M.default
  sortInterp := M.sortInterp
  sortNonempty := M.sortNonempty
  functionInterp := fun target args =>
    if target = symbol then interpretation args else M.functionInterp target args
  predicateInterp := M.predicateInterp
  applyInterp := M.applyInterp
  boolValue := M.boolValue
  notValue := M.notValue
  andValue := M.andValue
  orValue := M.orValue
  impValue := M.impValue
  iffValue := M.iffValue
  quoteValue := M.quoteValue
  lambdaValue := M.lambdaValue
  iteValue := M.iteValue
  boolHolds := M.boolHolds
theorem overrideFunction_functionSort {M : Model} (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) (hBase : ∀ target arguments, M.sortInterp target.outputSort (M.functionInterp target arguments)) (hInterpretation : ∀ arguments, M.sortInterp symbol.outputSort (interpretation arguments)) : ∀ target arguments, (M.overrideFunction symbol interpretation).sortInterp target.outputSort ((M.overrideFunction symbol interpretation).functionInterp target arguments) := by
  intro target arguments
  by_cases hTarget : target = symbol
  · subst target
    simpa [overrideFunction] using hInterpretation arguments
  · simpa [overrideFunction, hTarget] using hBase target arguments
@[implicit_reducible]
def overrideFunctionValue (M : Model) (symbol : FunctionSymbol) (value : M.Carrier) : Model :=
  M.overrideFunction symbol fun _ => value
end Model
namespace FoolContract
theorem overrideFunction {M : Model} (contract : FoolContract M) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) (hInterpretation : ∀ arguments, M.sortInterp symbol.outputSort (interpretation arguments)) : FoolContract (M.overrideFunction symbol interpretation) :=
  {
    contract with
    function_sort :=
      Model.overrideFunction_functionSort symbol interpretation
        contract.function_sort hInterpretation
  }
end FoolContract
namespace FoolLambdaContract
theorem overrideFunction {M : Model} (contract : FoolLambdaContract M) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) (hInterpretation : ∀ arguments, M.sortInterp symbol.outputSort (interpretation arguments)) : FoolLambdaContract (M.overrideFunction symbol interpretation) :=
  {
    contract with
    function_sort :=
      Model.overrideFunction_functionSort symbol interpretation
        contract.function_sort hInterpretation
  }
end FoolLambdaContract
namespace Env
def rebaseOverrideFunction {M : Model} (env : Env M) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) : Env (M.overrideFunction symbol interpretation) where
  boundVal := env.boundVal
  freeVal := env.freeVal
def unbaseOverrideFunction {M : Model} {symbol : FunctionSymbol} {interpretation : List M.Carrier → M.Carrier} (env : Env (M.overrideFunction symbol interpretation)) : Env M where
  boundVal := env.boundVal
  freeVal := env.freeVal
@[simp]
theorem rebaseOverrideFunction_unbaseOverrideFunction {M : Model} {symbol : FunctionSymbol} {interpretation : List M.Carrier → M.Carrier} (env : Env (M.overrideFunction symbol interpretation)) : rebaseOverrideFunction (unbaseOverrideFunction env) symbol interpretation = env := by
  cases env
  rfl
@[simp]
theorem unbaseOverrideFunction_rebaseOverrideFunction {M : Model} (env : Env M) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) : unbaseOverrideFunction (rebaseOverrideFunction env symbol interpretation) = env := by
  cases env
  rfl
theorem respectsFree_unbaseOverrideFunction {M : Model} {symbol : FunctionSymbol} {interpretation : List M.Carrier → M.Carrier} {env : Env (M.overrideFunction symbol interpretation)} (hFree : RespectsFree env) : RespectsFree (unbaseOverrideFunction env) := by
  intro sort id
  exact hFree sort id
def rebaseOverride {M : Model} (env : Env M) (symbol : FunctionSymbol) (value : M.Carrier) : Env (M.overrideFunctionValue symbol value) :=
  rebaseOverrideFunction env symbol fun _ => value
theorem setFree_self {M : Model} (env : Env M) (sort : CoreSort) (id : VarId) : env.setFree sort id (env.freeVal sort id) = env := by
  cases env with
  | mk boundVal freeVal =>
      simp only [setFree]
      congr 1
      funext targetSort targetId
      by_cases hSort : targetSort = sort
      · by_cases hId : targetId = id
        · subst targetSort
          subst targetId
          simp
        · simp [hSort, hId]
      · simp [hSort]
def FreeAgreement {M : Model} (parameters : List DefinitionalCnf.FreeVarParam) (left right : Env M) : Prop :=
  ∀ parameter, parameter ∈ parameters →
    left.freeVal parameter.sort parameter.varId =
      right.freeVal parameter.sort parameter.varId
namespace FreeAgreement
theorem mono {M : Model} {larger smaller : List DefinitionalCnf.FreeVarParam} {left right : Env M} (hAgreement : FreeAgreement larger left right) (hSubset : ∀ parameter, parameter ∈ smaller → parameter ∈ larger) : FreeAgreement smaller left right := by
  intro parameter hParameter
  exact hAgreement parameter (hSubset parameter hParameter)
theorem push {M : Model} {parameters : List DefinitionalCnf.FreeVarParam} {left right : Env M} (hAgreement : FreeAgreement parameters left right) (value : M.Carrier) : FreeAgreement parameters (left.push value) (right.push value) := by
  intro parameter hParameter
  exact hAgreement parameter hParameter
end FreeAgreement
end Env
namespace FreeSupport
theorem mem_insert_self (parameter : DefinitionalCnf.FreeVarParam) (parameters : List DefinitionalCnf.FreeVarParam) : parameter ∈ DefinitionalCnf.FreeVarParam.insert parameter parameters := by
  by_cases hMem : parameter ∈ parameters
  · simp [DefinitionalCnf.FreeVarParam.insert, hMem]
  · simp [DefinitionalCnf.FreeVarParam.insert, hMem]
theorem mem_insert_of_mem {parameter existing : DefinitionalCnf.FreeVarParam} {parameters : List DefinitionalCnf.FreeVarParam} (hMem : existing ∈ parameters) : existing ∈ DefinitionalCnf.FreeVarParam.insert parameter parameters := by
  by_cases hParameter : parameter ∈ parameters
  · simp [DefinitionalCnf.FreeVarParam.insert, hParameter, hMem]
  · simp [DefinitionalCnf.FreeVarParam.insert, hParameter, hMem]
theorem mem_insert_cases {parameter existing : DefinitionalCnf.FreeVarParam} {parameters : List DefinitionalCnf.FreeVarParam} (hMem : existing ∈ DefinitionalCnf.FreeVarParam.insert parameter parameters) : existing = parameter ∨ existing ∈ parameters := by
  unfold DefinitionalCnf.FreeVarParam.insert at hMem
  split at hMem
  · exact Or.inr hMem
  · rcases List.mem_append.mp hMem with hExisting | hNew
    · exact Or.inr hExisting
    · exact Or.inl (List.mem_singleton.mp hNew)
theorem mem_merge_left {parameter : DefinitionalCnf.FreeVarParam} {left right : List DefinitionalCnf.FreeVarParam} (hMem : parameter ∈ left) : parameter ∈ DefinitionalCnf.FreeVarParam.merge left right := by
  induction right generalizing left with
  | nil => simpa [DefinitionalCnf.FreeVarParam.merge] using hMem
  | cons head tail ih =>
      change
        parameter ∈
          tail.foldl (fun parameters parameter => DefinitionalCnf.FreeVarParam.insert parameter parameters) (DefinitionalCnf.FreeVarParam.insert head left)
      exact ih (mem_insert_of_mem hMem)
theorem mem_merge_right {parameter : DefinitionalCnf.FreeVarParam} {left right : List DefinitionalCnf.FreeVarParam} (hMem : parameter ∈ right) : parameter ∈ DefinitionalCnf.FreeVarParam.merge left right := by
  induction right generalizing left with
  | nil => simp at hMem
  | cons head tail ih =>
      change
        parameter ∈
          tail.foldl (fun parameters parameter => DefinitionalCnf.FreeVarParam.insert parameter parameters) (DefinitionalCnf.FreeVarParam.insert head left)
      rcases List.mem_cons.mp hMem with hHead | hTail
      · subst parameter
        exact mem_merge_left (mem_insert_self head left)
      · exact ih hTail
theorem mem_merge_cases {parameter : DefinitionalCnf.FreeVarParam} {left right : List DefinitionalCnf.FreeVarParam} (hMem : parameter ∈ DefinitionalCnf.FreeVarParam.merge left right) : parameter ∈ left ∨ parameter ∈ right := by
  induction right generalizing left with
  | nil => exact Or.inl hMem
  | cons head tail ih =>
      change
        parameter ∈
          tail.foldl (fun parameters parameter => DefinitionalCnf.FreeVarParam.insert parameter parameters)
            (DefinitionalCnf.FreeVarParam.insert head left) at hMem
      rcases ih hMem with hInserted | hTail
      · rcases mem_insert_cases hInserted with hHead | hLeft
        · exact Or.inr (by simp [hHead])
        · exact Or.inl hLeft
      · exact Or.inr (by simp [hTail])
mutual
  def TermSupportedBy (parameters : List DefinitionalCnf.FreeVarParam) : Term → Prop
    | Term.bvar .. => True
    | Term.fvar sort id => ({ sort := sort, varId := id } : DefinitionalCnf.FreeVarParam) ∈ parameters
    | Term.app _ args => TermListSupportedBy parameters args
    | Term.apply fn arg => TermSupportedBy parameters fn ∧ TermSupportedBy parameters arg
    | Term.bool _ => True
    | Term.notE body => TermSupportedBy parameters body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => TermSupportedBy parameters left ∧ TermSupportedBy parameters right
    | Term.quote formula => FormulaSupportedBy parameters formula
    | Term.lam _ _ body => TermSupportedBy parameters body
    | Term.ite _ condition thenTerm elseTerm =>
        FormulaSupportedBy parameters condition ∧
          TermSupportedBy parameters thenTerm ∧
            TermSupportedBy parameters elseTerm
  def FormulaSupportedBy (parameters : List DefinitionalCnf.FreeVarParam) : Formula → Prop
    | Formula.trueE
    | Formula.falseE => True
    | Formula.atom _ args => TermListSupportedBy parameters args
    | Formula.equal _ left right => TermSupportedBy parameters left ∧ TermSupportedBy parameters right
    | Formula.boolTerm term => TermSupportedBy parameters term
    | Formula.neg body => FormulaSupportedBy parameters body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => FormulaSupportedBy parameters left ∧ FormulaSupportedBy parameters right
    | Formula.forallE _ body
    | Formula.existsE _ body => FormulaSupportedBy parameters body
  def TermListSupportedBy (parameters : List DefinitionalCnf.FreeVarParam) : List Term → Prop
    | [] => True
    | term :: terms => TermSupportedBy parameters term ∧ TermListSupportedBy parameters terms
end
def AtomSupportedBy (parameters : List DefinitionalCnf.FreeVarParam) : Atom → Prop
  | Atom.predicate _ args => TermListSupportedBy parameters args
  | Atom.equal _ left right => TermSupportedBy parameters left ∧ TermSupportedBy parameters right
  | Atom.boolTerm term => TermSupportedBy parameters term
def LiteralSupportedBy (parameters : List DefinitionalCnf.FreeVarParam) (literal : Literal) : Prop :=
  AtomSupportedBy parameters literal.atom
def NnfSupportedBy (parameters : List DefinitionalCnf.FreeVarParam) : Nnf → Prop
  | Nnf.trueE
  | Nnf.falseE => True
  | Nnf.lit literal => LiteralSupportedBy parameters literal
  | Nnf.conj left right
  | Nnf.disj left right => NnfSupportedBy parameters left ∧ NnfSupportedBy parameters right
  | Nnf.forallE _ body
  | Nnf.existsE _ body => NnfSupportedBy parameters body
mutual
  def termFreeClosed : Term → Bool
    | Term.bvar .. => true
    | Term.fvar .. => false
    | Term.app _ args => termListFreeClosed args
    | Term.apply fn arg => termFreeClosed fn && termFreeClosed arg
    | Term.bool .. => true
    | Term.notE body => termFreeClosed body
    | Term.andE left right
    | Term.orE left right
    | Term.impE left right
    | Term.iffE left right => termFreeClosed left && termFreeClosed right
    | Term.quote formula => formulaFreeClosed formula
    | Term.lam _ _ body => termFreeClosed body
    | Term.ite _ condition thenTerm elseTerm =>
        formulaFreeClosed condition &&
          termFreeClosed thenTerm && termFreeClosed elseTerm
  def formulaFreeClosed : Formula → Bool
    | Formula.trueE
    | Formula.falseE => true
    | Formula.atom _ args => termListFreeClosed args
    | Formula.equal _ left right => termFreeClosed left && termFreeClosed right
    | Formula.boolTerm term => termFreeClosed term
    | Formula.neg body => formulaFreeClosed body
    | Formula.imp left right
    | Formula.conj left right
    | Formula.disj left right
    | Formula.iffE left right => formulaFreeClosed left && formulaFreeClosed right
    | Formula.forallE _ body
    | Formula.existsE _ body => formulaFreeClosed body
  def termListFreeClosed : List Term → Bool
    | [] => true
    | term :: terms => termFreeClosed term && termListFreeClosed terms
end
def atomFreeClosed : Atom → Bool
  | Atom.predicate _ args => termListFreeClosed args
  | Atom.equal _ left right => termFreeClosed left && termFreeClosed right
  | Atom.boolTerm term => termFreeClosed term
def nnfFreeClosed : Nnf → Bool
  | Nnf.trueE
  | Nnf.falseE => true
  | Nnf.lit literal => atomFreeClosed literal.atom
  | Nnf.conj left right
  | Nnf.disj left right => nnfFreeClosed left && nnfFreeClosed right
  | Nnf.forallE _ body
  | Nnf.existsE _ body => nnfFreeClosed body
private theorem termFreeClosed_iff_supported (term : Term) : termFreeClosed term = true ↔ TermSupportedBy [] term := by
  apply Term.rec (motive_1 := fun term => termFreeClosed term = true ↔ TermSupportedBy [] term)
    (motive_2 := fun formula => formulaFreeClosed formula = true ↔ FormulaSupportedBy [] formula)
    (motive_3 := fun terms => termListFreeClosed terms = true ↔ TermListSupportedBy [] terms)
  all_goals
    simp_all [termFreeClosed, formulaFreeClosed, termListFreeClosed, TermSupportedBy, FormulaSupportedBy, TermListSupportedBy, and_assoc]
private theorem formulaFreeClosed_iff_supported (formula : Formula) : formulaFreeClosed formula = true ↔ FormulaSupportedBy [] formula := by
  apply Formula.rec (motive_1 := fun term => termFreeClosed term = true ↔ TermSupportedBy [] term)
    (motive_2 := fun formula => formulaFreeClosed formula = true ↔ FormulaSupportedBy [] formula)
    (motive_3 := fun terms => termListFreeClosed terms = true ↔ TermListSupportedBy [] terms)
  all_goals
    simp_all [termFreeClosed, formulaFreeClosed, termListFreeClosed, TermSupportedBy, FormulaSupportedBy, TermListSupportedBy, and_assoc]
private theorem termListFreeClosed_iff_supported (terms : List Term) : termListFreeClosed terms = true ↔ TermListSupportedBy [] terms := by
  apply Term.rec_1 (motive_1 := fun term => termFreeClosed term = true ↔ TermSupportedBy [] term)
    (motive_2 := fun formula => formulaFreeClosed formula = true ↔ FormulaSupportedBy [] formula)
    (motive_3 := fun terms => termListFreeClosed terms = true ↔ TermListSupportedBy [] terms)
  all_goals
    simp_all [termFreeClosed, formulaFreeClosed, termListFreeClosed, TermSupportedBy, FormulaSupportedBy, TermListSupportedBy, and_assoc]
theorem termFreeClosed_sound {term : Term} (h : termFreeClosed term = true) : TermSupportedBy [] term := (termFreeClosed_iff_supported term).mp h
theorem formulaFreeClosed_sound {formula : Formula} (h : formulaFreeClosed formula = true) : FormulaSupportedBy [] formula :=
  (formulaFreeClosed_iff_supported formula).mp h
theorem termListFreeClosed_sound {terms : List Term} (h : termListFreeClosed terms = true) : TermListSupportedBy [] terms :=
  (termListFreeClosed_iff_supported terms).mp h
theorem nnfFreeClosed_sound {nnf : Nnf} (h : nnfFreeClosed nnf = true) : NnfSupportedBy [] nnf := by
  induction nnf with
  | trueE
  | falseE => trivial
  | lit literal =>
      rcases literal with ⟨positive, atom⟩
      simp only [nnfFreeClosed] at h
      change AtomSupportedBy [] atom
      cases atom with
      | predicate predicate args =>
          simp only [atomFreeClosed] at h
          exact termListFreeClosed_sound h
      | equal sort left right =>
          simp only [atomFreeClosed] at h
          rcases Bool.and_eq_true_iff.mp h with ⟨hLeft, hRight⟩
          exact ⟨termFreeClosed_sound hLeft, termFreeClosed_sound hRight⟩
      | boolTerm term =>
          simp only [atomFreeClosed] at h
          exact termFreeClosed_sound h
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight =>
      change NnfSupportedBy [] left ∧ NnfSupportedBy [] right
      rcases Bool.and_eq_true_iff.mp h with ⟨hLeft, hRight⟩
      exact ⟨ihLeft hLeft, ihRight hRight⟩
  | forallE sort body ih
  | existsE sort body ih => exact ih h
/-- 支持集拼接只保留成员关系；构造算法的去重顺序不进入上层证明。 -/
theorem mem_merge_iff {parameter : DefinitionalCnf.FreeVarParam}
    {left right : List DefinitionalCnf.FreeVarParam} :
    parameter ∈ DefinitionalCnf.FreeVarParam.merge left right ↔
      parameter ∈ left ∨ parameter ∈ right :=
  ⟨mem_merge_cases, fun h => h.elim mem_merge_left mem_merge_right⟩

mutual
  /-- 结构支持与实际收集的自由参数精确对应。 -/
  theorem termSupportedBy_iff (parameters : List DefinitionalCnf.FreeVarParam) (term : Term) :
      TermSupportedBy parameters term ↔
        ∀ parameter ∈ DefinitionalCnf.Term.freeVarParams term, parameter ∈ parameters := by
    cases term <;> simp only [TermSupportedBy, DefinitionalCnf.Term.freeVarParams,
      termSupportedBy_iff, formulaSupportedBy_iff, termListSupportedBy_iff,
      mem_merge_iff, or_imp, forall_and, List.mem_singleton, List.not_mem_nil,
      implies_true, false_implies, forall_eq]
  theorem formulaSupportedBy_iff (parameters : List DefinitionalCnf.FreeVarParam) (formula : Formula) :
      FormulaSupportedBy parameters formula ↔
        ∀ parameter ∈ DefinitionalCnf.Formula.freeVarParams formula, parameter ∈ parameters := by
    cases formula <;> simp only [FormulaSupportedBy, DefinitionalCnf.Formula.freeVarParams,
      termSupportedBy_iff, formulaSupportedBy_iff, termListSupportedBy_iff,
      mem_merge_iff, or_imp, forall_and, List.not_mem_nil, implies_true, false_implies]
  theorem termListSupportedBy_iff (parameters : List DefinitionalCnf.FreeVarParam) (terms : List Term) :
      TermListSupportedBy parameters terms ↔
        ∀ parameter ∈ DefinitionalCnf.Term.freeVarParamsList terms, parameter ∈ parameters := by
    cases terms <;> simp only [TermListSupportedBy, DefinitionalCnf.Term.freeVarParamsList,
      termSupportedBy_iff, termListSupportedBy_iff, mem_merge_iff, or_imp, forall_and,
      List.not_mem_nil, implies_true, false_implies]
end

theorem term_freeVarParams_mem (parameters : List DefinitionalCnf.FreeVarParam) : ∀ term, TermSupportedBy parameters
    term → ∀ parameter, parameter ∈ DefinitionalCnf.Term.freeVarParams term → parameter ∈ parameters := by
  intro syntaxValue hSupported
  exact (termSupportedBy_iff parameters syntaxValue).mp hSupported

theorem formula_freeVarParams_mem (parameters : List DefinitionalCnf.FreeVarParam) : ∀ formula, FormulaSupportedBy
    parameters formula → ∀ parameter, parameter ∈ DefinitionalCnf.Formula.freeVarParams formula → parameter ∈ parameters
    := by
  intro syntaxValue hSupported
  exact (formulaSupportedBy_iff parameters syntaxValue).mp hSupported

theorem termList_freeVarParams_mem (parameters : List DefinitionalCnf.FreeVarParam) : ∀ terms, TermListSupportedBy
    parameters terms → ∀ parameter, parameter ∈ DefinitionalCnf.Term.freeVarParamsList terms → parameter ∈ parameters :=
    by
  intro syntaxValue hSupported
  exact (termListSupportedBy_iff parameters syntaxValue).mp hSupported
theorem atom_freeVarParams_mem (parameters : List DefinitionalCnf.FreeVarParam) (atom : Atom) (hSupported : AtomSupportedBy parameters atom) (parameter : DefinitionalCnf.FreeVarParam) (hParameter : parameter ∈ DefinitionalCnf.atomFreeVarParams atom) : parameter ∈ parameters := by
  cases atom with
  | predicate predicate args =>
      exact termList_freeVarParams_mem parameters args hSupported
        parameter hParameter
  | equal sort left right =>
      rcases mem_merge_cases hParameter with hLeft | hRight
      · exact term_freeVarParams_mem parameters left hSupported.1 parameter hLeft
      · exact term_freeVarParams_mem parameters right hSupported.2 parameter hRight
  | boolTerm term => exact term_freeVarParams_mem parameters term hSupported parameter hParameter
theorem nnf_freeVarParams_mem (parameters : List DefinitionalCnf.FreeVarParam) : ∀ nnf, NnfSupportedBy parameters nnf → ∀ parameter, parameter ∈ DefinitionalCnf.nnfFreeVarParams nnf → parameter ∈ parameters := by
  intro nnf hSupported parameter hParameter
  induction nnf with
  | trueE
  | falseE => simp [DefinitionalCnf.nnfFreeVarParams] at hParameter
  | lit literal =>
      exact atom_freeVarParams_mem parameters literal.atom hSupported
        parameter hParameter
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight =>
      rcases mem_merge_cases hParameter with hLeft | hRight
      · exact ihLeft hSupported.1 hLeft
      · exact ihRight hSupported.2 hRight
  | forallE sort body ih
  | existsE sort body ih => exact ih hSupported hParameter
theorem termSupportedBy_mono {smaller larger : List DefinitionalCnf.FreeVarParam} (hSubset : ∀ parameter, parameter ∈
    smaller → parameter ∈ larger) : ∀ term, TermSupportedBy smaller term → TermSupportedBy larger term := by
  intro syntaxValue hSupported
  exact (termSupportedBy_iff larger syntaxValue).mpr (fun parameter hParameter =>
    hSubset parameter ((termSupportedBy_iff smaller syntaxValue).mp hSupported parameter hParameter))

theorem formulaSupportedBy_mono {smaller larger : List DefinitionalCnf.FreeVarParam} (hSubset : ∀ parameter, parameter ∈
    smaller → parameter ∈ larger) : ∀ formula, FormulaSupportedBy smaller formula → FormulaSupportedBy larger formula :=
    by
  intro syntaxValue hSupported
  exact (formulaSupportedBy_iff larger syntaxValue).mpr (fun parameter hParameter =>
    hSubset parameter ((formulaSupportedBy_iff smaller syntaxValue).mp hSupported parameter hParameter))

theorem termListSupportedBy_mono {smaller larger : List DefinitionalCnf.FreeVarParam} (hSubset : ∀ parameter, parameter
    ∈ smaller → parameter ∈ larger) : ∀ terms, TermListSupportedBy smaller terms → TermListSupportedBy larger terms :=
    by
  intro syntaxValue hSupported
  exact (termListSupportedBy_iff larger syntaxValue).mpr (fun parameter hParameter =>
    hSubset parameter ((termListSupportedBy_iff smaller syntaxValue).mp hSupported parameter hParameter))
theorem atomSupportedBy_mono {smaller larger : List DefinitionalCnf.FreeVarParam} (hSubset : ∀ parameter, parameter ∈ smaller → parameter ∈ larger) (atom : Atom) (hSupported : AtomSupportedBy smaller atom) : AtomSupportedBy larger atom := by
  cases atom with
  | predicate predicate args => exact termListSupportedBy_mono hSubset args hSupported
  | equal sort left right =>
      exact ⟨termSupportedBy_mono hSubset left hSupported.1, termSupportedBy_mono hSubset right hSupported.2⟩
  | boolTerm term => exact termSupportedBy_mono hSubset term hSupported
theorem nnfSupportedBy_mono {smaller larger : List DefinitionalCnf.FreeVarParam} (hSubset : ∀ parameter, parameter ∈ smaller → parameter ∈ larger) : ∀ nnf, NnfSupportedBy smaller nnf → NnfSupportedBy larger nnf := by
  intro nnf hSupported
  induction nnf with
  | trueE
  | falseE => trivial
  | lit literal => exact atomSupportedBy_mono hSubset literal.atom hSupported
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight => exact ⟨ihLeft hSupported.1, ihRight hSupported.2⟩
  | forallE sort body ih
  | existsE sort body ih => exact ih hSupported
mutual
  theorem termSupportedBy_shiftAbove (parameters : List DefinitionalCnf.FreeVarParam) (amount : Nat) : ∀ term cutoff, TermSupportedBy parameters term → TermSupportedBy parameters (Term.shiftAbove amount cutoff term) := by

    intro term cutoff hSupported
    cases term <;> simp_all only [Term.shiftAbove, TermSupportedBy,
      termSupportedBy_shiftAbove,
      formulaSupportedBy_shiftAbove, termListSupportedBy_shiftAbove, true_and]
    all_goals split <;> trivial

  theorem formulaSupportedBy_shiftAbove (parameters : List DefinitionalCnf.FreeVarParam) (amount : Nat) : ∀ formula cutoff, FormulaSupportedBy parameters formula → FormulaSupportedBy parameters (Formula.shiftAbove amount cutoff formula) := by

    intro formula cutoff hSupported
    cases formula <;> simp_all only [Formula.shiftAbove, FormulaSupportedBy, termSupportedBy_shiftAbove,
      formulaSupportedBy_shiftAbove, termListSupportedBy_shiftAbove, true_and]

  theorem termListSupportedBy_shiftAbove (parameters : List DefinitionalCnf.FreeVarParam) (amount : Nat) : ∀ terms cutoff, TermListSupportedBy parameters terms → TermListSupportedBy parameters (Term.shiftListAbove amount cutoff terms) := by

    intro terms cutoff hSupported
    cases terms <;> simp_all only [Term.shiftListAbove, TermListSupportedBy, termSupportedBy_shiftAbove,
      termListSupportedBy_shiftAbove, true_and]

end
mutual
  theorem termSupportedBy_instantiateAt (parameters : List DefinitionalCnf.FreeVarParam) (replacement : Term) (hReplacement : TermSupportedBy parameters replacement) : ∀ term depth, TermSupportedBy parameters term → TermSupportedBy parameters (Term.instantiateAt depth replacement term) := by

    intro term depth hSupported
    cases term <;> simp_all only [Term.instantiateAt, TermSupportedBy,
      termSupportedBy_instantiateAt,
      formulaSupportedBy_instantiateAt, termListSupportedBy_instantiateAt, true_and]
    all_goals split <;> first | trivial | skip
    all_goals split <;> first | trivial | exact termSupportedBy_shiftAbove parameters depth replacement 0 hReplacement

  theorem formulaSupportedBy_instantiateAt (parameters : List DefinitionalCnf.FreeVarParam) (replacement : Term) (hReplacement : TermSupportedBy parameters replacement) : ∀ formula depth, FormulaSupportedBy parameters formula → FormulaSupportedBy parameters (Formula.instantiateAt depth replacement formula) := by

    intro formula depth hSupported
    cases formula <;> simp_all only [Formula.instantiateAt, FormulaSupportedBy, termSupportedBy_instantiateAt,
      formulaSupportedBy_instantiateAt, termListSupportedBy_instantiateAt, true_and]

  theorem termListSupportedBy_instantiateAt (parameters : List DefinitionalCnf.FreeVarParam) (replacement : Term) (hReplacement : TermSupportedBy parameters replacement) : ∀ terms depth, TermListSupportedBy parameters terms → TermListSupportedBy parameters (Term.instantiateListAt depth replacement terms) := by

    intro terms depth hSupported
    cases terms <;> simp_all only [Term.instantiateListAt, TermListSupportedBy, termSupportedBy_instantiateAt,
      termListSupportedBy_instantiateAt, true_and]

end
theorem atomSupportedBy_instantiateAt (parameters : List DefinitionalCnf.FreeVarParam) (replacement : Term) (hReplacement : TermSupportedBy parameters replacement) (atom : Atom) (depth : Nat) (hSupported : AtomSupportedBy parameters atom) : AtomSupportedBy parameters (LocalSkolem.instantiateAtomAt depth replacement atom) := by
  cases atom with
  | predicate predicate args =>
      exact termListSupportedBy_instantiateAt
        parameters replacement hReplacement args depth hSupported
  | equal sort left right =>
      exact ⟨termSupportedBy_instantiateAt parameters replacement hReplacement left depth hSupported.1, termSupportedBy_instantiateAt
          parameters replacement hReplacement right depth hSupported.2⟩
  | boolTerm term =>
      exact termSupportedBy_instantiateAt
        parameters replacement hReplacement term depth hSupported
theorem nnfSupportedBy_instantiateAt (parameters : List DefinitionalCnf.FreeVarParam) (replacement : Term) (hReplacement : TermSupportedBy parameters replacement) : ∀ nnf depth, NnfSupportedBy parameters nnf → NnfSupportedBy parameters (LocalSkolem.instantiateNnfAt depth replacement nnf) := by
  intro nnf depth hSupported
  induction nnf generalizing depth with
  | trueE
  | falseE => trivial
  | lit literal =>
      exact atomSupportedBy_instantiateAt
        parameters replacement hReplacement literal.atom depth hSupported
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight => exact ⟨ihLeft depth hSupported.1, ihRight depth hSupported.2⟩
  | forallE sort body ih
  | existsE sort body ih => exact ih (depth + 1) hSupported
theorem nnfSupportedBy_instantiate (parameters : List DefinitionalCnf.FreeVarParam) (replacement : Term) (hReplacement : TermSupportedBy parameters replacement) (body : Nnf) (hBody : NnfSupportedBy parameters body) : NnfSupportedBy parameters (LocalSkolem.instantiateNnf replacement body) :=
  nnfSupportedBy_instantiateAt parameters replacement hReplacement body 0 hBody
end FreeSupport
theorem Env.FreeAgreement.merge_iff {M : Model}
    (first second : List DefinitionalCnf.FreeVarParam) (left right : Env M) :
    Env.FreeAgreement (DefinitionalCnf.FreeVarParam.merge first second) left right ↔
      Env.FreeAgreement first left right ∧ Env.FreeAgreement second left right := by
  simp only [Env.FreeAgreement, FreeSupport.mem_merge_iff, or_imp, forall_and]

theorem Env.FreeAgreement.push_iff {M : Model}
    (parameters : List DefinitionalCnf.FreeVarParam) (left right : Env M) (value : M.Carrier) :
    Env.FreeAgreement parameters (left.push value) (right.push value) ↔
      Env.FreeAgreement parameters left right := Iff.rfl

mutual
  theorem Term.eval_eq_of_freeAgreement {M : Model} (left right : Env M) (hBound : ∀ index, left.boundVal index = right.boundVal index) (term : Term) (hAgreement : Env.FreeAgreement (DefinitionalCnf.Term.freeVarParams term) left right) : Term.eval left term = Term.eval right term := by
    have hPush (value : M.Carrier) (index : Nat) :
        (left.push value).boundVal index = (right.push value).boundVal index := by
      cases index <;> simp [Env.push, hBound]
    cases term <;>
      simp only [DefinitionalCnf.Term.freeVarParams, Env.FreeAgreement.merge_iff] at hAgreement
    case fvar sort id =>
      simpa only [Term.eval] using hAgreement ⟨sort, id⟩ (List.mem_singleton_self _)
    all_goals simp only [Term.eval]
    all_goals simp_all only [← Formula.Satisfies.eq_def, Env.FreeAgreement.push_iff,
        Term.eval_eq_of_freeAgreement left right hBound,
        Formula.satisfies_iff_of_freeAgreement left right hBound,
        Term.evalList_eq_of_freeAgreement left right hBound,
        Term.eval_eq_of_freeAgreement (left.push _) (right.push _) (hPush _)]
  theorem Formula.satisfies_iff_of_freeAgreement {M : Model} (left right : Env M) (hBound : ∀ index, left.boundVal index = right.boundVal index) (formula : Formula) (hAgreement : Env.FreeAgreement (DefinitionalCnf.Formula.freeVarParams formula) left right) : Formula.Satisfies left formula ↔ Formula.Satisfies right formula := by
    have hPush (value : M.Carrier) (index : Nat) :
        (left.push value).boundVal index = (right.push value).boundVal index := by
      cases index <;> simp [Env.push, hBound]
    cases formula <;>
      simp only [DefinitionalCnf.Formula.freeVarParams, Env.FreeAgreement.merge_iff] at hAgreement
    all_goals simp only [Formula.Satisfies, Formula.eval]
    all_goals simp_all only [← Formula.Satisfies.eq_def, Env.FreeAgreement.push_iff,
        Term.eval_eq_of_freeAgreement left right hBound,
        Formula.satisfies_iff_of_freeAgreement left right hBound,
        Term.evalList_eq_of_freeAgreement left right hBound,
        Formula.satisfies_iff_of_freeAgreement (left.push _) (right.push _) (hPush _)]
  theorem Term.evalList_eq_of_freeAgreement {M : Model} (left right : Env M) (hBound : ∀ index, left.boundVal index = right.boundVal index) (terms : List Term) (hAgreement : Env.FreeAgreement (DefinitionalCnf.Term.freeVarParamsList terms) left right) : terms.map (Term.eval left) = terms.map (Term.eval right) := by
    cases terms <;>
      simp only [DefinitionalCnf.Term.freeVarParamsList, Env.FreeAgreement.merge_iff] at hAgreement
    all_goals simp_all only [List.map_nil, List.map_cons,
        Term.eval_eq_of_freeAgreement left right hBound,
        Term.evalList_eq_of_freeAgreement left right hBound]

end
namespace FreeSupport
theorem Atom.freeVarParams_toFormula (atom : Atom) : DefinitionalCnf.Formula.freeVarParams atom.toFormula = DefinitionalCnf.atomFreeVarParams atom := by
  cases atom <;>
    simp [Atom.toFormula, DefinitionalCnf.Formula.freeVarParams, DefinitionalCnf.atomFreeVarParams]
theorem Literal.freeVarParams_toFormula (literal : Literal) : DefinitionalCnf.Formula.freeVarParams literal.toFormula = DefinitionalCnf.literalFreeVarParams literal := by
  cases literal with
  | mk positive atom =>
      cases positive
      · simpa [Literal.toFormula, DefinitionalCnf.literalFreeVarParams, DefinitionalCnf.Formula.freeVarParams] using
            Atom.freeVarParams_toFormula atom
      · exact Atom.freeVarParams_toFormula atom
theorem Nnf.freeVarParams_toFormula (nnf : Nnf) : DefinitionalCnf.Formula.freeVarParams nnf.toFormula = DefinitionalCnf.nnfFreeVarParams nnf := by
  induction nnf with
  | trueE
  | falseE => rfl
  | lit literal => exact Literal.freeVarParams_toFormula literal
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight =>
      simp only [Nnf.toFormula, DefinitionalCnf.Formula.freeVarParams, DefinitionalCnf.nnfFreeVarParams]
      rw [ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih =>
      simpa [Nnf.toFormula, DefinitionalCnf.Formula.freeVarParams, DefinitionalCnf.nnfFreeVarParams] using ih
end FreeSupport
theorem Nnf.satisfies_iff_of_freeAgreement {M : Model} (left right : Env M) (hBound : ∀ index, left.boundVal index = right.boundVal index) (nnf : Nnf) (hAgreement : Env.FreeAgreement (DefinitionalCnf.nnfFreeVarParams nnf) left right) : Nnf.Satisfies left nnf ↔ Nnf.Satisfies right nnf := by
  rw [← Nnf.satisfies_toFormula, ← Nnf.satisfies_toFormula]
  apply Formula.satisfies_iff_of_freeAgreement left right hBound
  simpa [FreeSupport.Nnf.freeVarParams_toFormula] using hAgreement
namespace LocalSkolemChoice
def UniversalIntro.parameter (universal : LocalSkolem.UniversalIntro) : DefinitionalCnf.FreeVarParam where
  sort := universal.sort
  varId := universal.varId
def parameters (universals : List LocalSkolem.UniversalIntro) : List DefinitionalCnf.FreeVarParam :=
  universals.map UniversalIntro.parameter
def values {M : Model} (env : Env M) (universals : List LocalSkolem.UniversalIntro) : List M.Carrier :=
  universals.map fun universal =>
    env.freeVal universal.sort universal.varId
def SameBoundStack {M : Model} (left right : Env M) : Prop :=
  ∀ index, left.boundVal index = right.boundVal index
theorem eval_terms_eq_values {M : Model} (env : Env M) (universals : List LocalSkolem.UniversalIntro) (hWellFormed : ∀ universal ∈ universals, universal.term = Term.fvar universal.sort universal.varId) : (universals.map fun universal => universal.term).map (Term.eval env) = values env universals := by
  induction universals with
  | nil => rfl
  | cons universal universals ih =>
      have hHead :
          universal.term =
            Term.fvar universal.sort universal.varId :=
        hWellFormed universal (by simp)
      have hTail :
          ∀ candidate ∈ universals,
            candidate.term =
              Term.fvar candidate.sort candidate.varId := by
        intro candidate hCandidate
        exact hWellFormed candidate (by simp [hCandidate])
      simp [values, hHead, Term.eval, ih hTail]
theorem freeAgreement_of_values_eq {M : Model} (left right : Env M) (universals : List LocalSkolem.UniversalIntro) (hValues : values left universals = values right universals) : Env.FreeAgreement (parameters universals) left right := by
  intro parameter hParameter
  rcases List.mem_map.mp hParameter with ⟨universal, hUniversal, rfl⟩
  induction universals generalizing universal with
  | nil => simp at hUniversal
  | cons head tail ih =>
      simp only [values, List.map_cons, List.cons.injEq] at hValues
      rcases List.mem_cons.mp hUniversal with rfl | hTail
      · exact hValues.1
      · exact ih hValues.2 universal hTail (List.mem_map.mpr ⟨universal, hTail, rfl⟩)
def HasWitness {M : Model} (base : Env M) (universals : List LocalSkolem.UniversalIntro) (sort : CoreSort) (body : Nnf) (arguments : List M.Carrier) (witness : M.Carrier) : Prop :=
  M.sortInterp sort witness ∧
    ∃ witnessEnv : Env M,
      SameBoundStack witnessEnv base ∧
        values witnessEnv universals = arguments ∧
          Nnf.Satisfies (witnessEnv.push witness) body
noncomputable def chooseWitness {M : Model} (base : Env M) (universals : List LocalSkolem.UniversalIntro) (sort : CoreSort) (body : Nnf) :
    List M.Carrier → M.Carrier := by
  classical
  exact fun arguments =>
    if h : ∃ witness, HasWitness base universals sort body arguments witness then
      Classical.choose h
    else
      Classical.choose (M.sortNonempty sort)
theorem chooseWitness_spec {M : Model} (base : Env M) (universals : List LocalSkolem.UniversalIntro) (sort : CoreSort) (body : Nnf) (arguments : List M.Carrier) (hExists : ∃ witness, HasWitness base universals sort body arguments witness) : HasWitness base universals sort body arguments (chooseWitness base universals sort body arguments) := by
  classical
  rw [chooseWitness, dif_pos hExists]
  exact Classical.choose_spec hExists
theorem chooseWitness_sort {M : Model} (base : Env M) (universals : List LocalSkolem.UniversalIntro) (sort : CoreSort) (body : Nnf) (arguments : List M.Carrier) : M.sortInterp sort (chooseWitness base universals sort body arguments) := by
  classical
  by_cases hExists :
      ∃ witness, HasWitness base universals sort body arguments witness
  · exact (chooseWitness_spec base universals sort body arguments hExists).1
  · rw [chooseWitness, dif_neg hExists]
    exact Classical.choose_spec (M.sortNonempty sort)
theorem respectsFree_rebaseOverrideFunction {M : Model} {env : Env M} (hFree : Env.RespectsFree env) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) : Env.RespectsFree (Env.rebaseOverrideFunction env symbol interpretation) := by
  intro sort id
  exact hFree sort id
theorem sameBoundStack_rebaseOverrideFunction {M : Model} {left right : Env M} (hBound : SameBoundStack left right) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) : SameBoundStack (Env.rebaseOverrideFunction left symbol interpretation) (Env.rebaseOverrideFunction right symbol interpretation) := by
  intro index
  exact hBound index
theorem sameBoundStack_unbaseOverrideFunction {M : Model} {symbol : FunctionSymbol} {interpretation : List M.Carrier → M.Carrier} {left right : Env (M.overrideFunction symbol interpretation)} (hBound : SameBoundStack left right) : SameBoundStack (Env.unbaseOverrideFunction left) (Env.unbaseOverrideFunction right) := by
  intro index
  exact hBound index
end LocalSkolemChoice
namespace Freshness
theorem atomMaxFVarSucc_toFormula (atom : Atom) : LocalSkolem.formulaMaxFVarSucc atom.toFormula = LocalSkolem.atomMaxFVarSucc atom := by cases atom <;> simp [Atom.toFormula, LocalSkolem.atomMaxFVarSucc, LocalSkolem.formulaMaxFVarSucc]
theorem literalMaxFVarSucc_toFormula (literal : Literal) : LocalSkolem.formulaMaxFVarSucc literal.toFormula = LocalSkolem.literalMaxFVarSucc literal := by
  cases literal with
  | mk positive atom =>
      cases positive
      · change LocalSkolem.formulaMaxFVarSucc atom.toFormula =
          LocalSkolem.atomMaxFVarSucc atom
        exact atomMaxFVarSucc_toFormula atom
      · exact atomMaxFVarSucc_toFormula atom
theorem Nnf.maxFVarSucc_toFormula (nnf : Nnf) : LocalSkolem.formulaMaxFVarSucc nnf.toFormula = LocalSkolem.nnfMaxFVarSucc nnf := by
  induction nnf with
  | trueE | falseE => rfl
  | lit literal => exact literalMaxFVarSucc_toFormula literal
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight =>
      simp only [Nnf.toFormula, LocalSkolem.formulaMaxFVarSucc, LocalSkolem.nnfMaxFVarSucc]
      rw [ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih => exact ih
theorem atomMaxFunctionIdSucc_toFormula (atom : Atom) : LocalSkolem.formulaMaxFunctionIdSucc atom.toFormula = LocalSkolem.atomMaxFunctionIdSucc atom := by cases atom <;> simp [Atom.toFormula, LocalSkolem.atomMaxFunctionIdSucc, LocalSkolem.formulaMaxFunctionIdSucc]
theorem literalMaxFunctionIdSucc_toFormula (literal : Literal) : LocalSkolem.formulaMaxFunctionIdSucc literal.toFormula = LocalSkolem.literalMaxFunctionIdSucc literal := by
  cases literal with
  | mk positive atom =>
      cases positive
      · change LocalSkolem.formulaMaxFunctionIdSucc atom.toFormula =
          LocalSkolem.atomMaxFunctionIdSucc atom
        exact atomMaxFunctionIdSucc_toFormula atom
      · exact atomMaxFunctionIdSucc_toFormula atom
theorem Nnf.maxFunctionIdSucc_toFormula (nnf : Nnf) : LocalSkolem.formulaMaxFunctionIdSucc nnf.toFormula = LocalSkolem.nnfMaxFunctionIdSucc nnf := by
  induction nnf with
  | trueE | falseE => rfl
  | lit literal => exact literalMaxFunctionIdSucc_toFormula literal
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight =>
      simp only [Nnf.toFormula, LocalSkolem.formulaMaxFunctionIdSucc, LocalSkolem.nnfMaxFunctionIdSucc]
      rw [ihLeft, ihRight]
  | forallE sort body ih
  | existsE sort body ih => exact ih
theorem Env.rebaseOverrideFunction_push {M : Model} (env : Env M)
    (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier)
    (value : M.Carrier) :
    (Env.rebaseOverrideFunction env symbol interpretation).push value =
      Env.rebaseOverrideFunction (env.push value) symbol interpretation := rfl

mutual
  theorem Term.eval_overrideFunctionWith_of_max_le {M : Model} (env : Env M) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) (term : Term) (hMax : LocalSkolem.termMaxFunctionIdSucc term ≤ symbol.id) : Term.eval (Env.rebaseOverrideFunction env symbol interpretation) term = Term.eval env term := by
    cases term <;> simp only [LocalSkolem.termMaxFunctionIdSucc, Nat.max_le] at hMax
    case app target args =>
      have hNe : target ≠ symbol := by intro hEq; subst hEq; omega
      simp only [Term.eval, Model.overrideFunction, if_neg hNe]
      rw [Term.evalList_overrideFunctionWith_of_max_le env symbol interpretation args hMax.2]
    all_goals simp only [Term.eval, Model.overrideFunction]
    all_goals first | rfl | simp_all only [← Formula.Satisfies.eq_def, Env.rebaseOverrideFunction_push,
        Term.eval_overrideFunctionWith_of_max_le env symbol interpretation,
        Formula.satisfies_overrideFunctionWith_of_max_le env symbol interpretation,
        Term.eval_overrideFunctionWith_of_max_le (env.push _) symbol interpretation]
  theorem Formula.satisfies_overrideFunctionWith_of_max_le {M : Model} (env : Env M) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) (formula : Formula) (hMax : LocalSkolem.formulaMaxFunctionIdSucc formula ≤ symbol.id) : Formula.Satisfies (Env.rebaseOverrideFunction env symbol interpretation) formula ↔ Formula.Satisfies env formula := by
    cases formula <;> simp only [LocalSkolem.formulaMaxFunctionIdSucc, Nat.max_le] at hMax
    all_goals simp only [Formula.Satisfies, Formula.eval, Model.overrideFunction]
    all_goals first | rfl | simp_all only [← Formula.Satisfies.eq_def, Env.rebaseOverrideFunction_push,
        Term.eval_overrideFunctionWith_of_max_le env symbol interpretation,
        Formula.satisfies_overrideFunctionWith_of_max_le env symbol interpretation,
        Term.evalList_overrideFunctionWith_of_max_le env symbol interpretation,
        Formula.satisfies_overrideFunctionWith_of_max_le (env.push _) symbol interpretation]
  theorem Term.evalList_overrideFunctionWith_of_max_le {M : Model} (env : Env M) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) (terms : List Term) (hMax : LocalSkolem.termListMaxFunctionIdSucc terms ≤ symbol.id) : terms.map (Term.eval (Env.rebaseOverrideFunction env symbol interpretation)) = terms.map (Term.eval env) := by
    cases terms <;> simp only [LocalSkolem.termListMaxFunctionIdSucc, Nat.max_le] at hMax
    all_goals simp_all only [List.map_nil, List.map_cons,
        Term.eval_overrideFunctionWith_of_max_le env symbol interpretation,
        Term.evalList_overrideFunctionWith_of_max_le env symbol interpretation]

end
theorem Term.eval_overrideFunction_of_max_le {M : Model} (env : Env M) (symbol : FunctionSymbol) (value : M.Carrier) (term : Term) (hMax : LocalSkolem.termMaxFunctionIdSucc term ≤ symbol.id) : Term.eval (Env.rebaseOverride env symbol value) term = Term.eval env term :=
  Term.eval_overrideFunctionWith_of_max_le env symbol (fun _ => value) term hMax
theorem Formula.satisfies_overrideFunction_of_max_le {M : Model} (env : Env M) (symbol : FunctionSymbol) (value : M.Carrier) (formula : Formula) (hMax : LocalSkolem.formulaMaxFunctionIdSucc formula ≤ symbol.id) : Formula.Satisfies (Env.rebaseOverride env symbol value) formula ↔ Formula.Satisfies env formula :=
  Formula.satisfies_overrideFunctionWith_of_max_le
    env symbol (fun _ => value) formula hMax
theorem Term.evalList_overrideFunction_of_max_le {M : Model} (env : Env M) (symbol : FunctionSymbol) (value : M.Carrier) (terms : List Term) (hMax : LocalSkolem.termListMaxFunctionIdSucc terms ≤ symbol.id) : terms.map (Term.eval (Env.rebaseOverride env symbol value)) = terms.map (Term.eval env) :=
  Term.evalList_overrideFunctionWith_of_max_le
    env symbol (fun _ => value) terms hMax
end Freshness
namespace FreeSupport
mutual
  /-- 自由变量最大编号的数值界，等价于实际支持中每个参数的严格界。 -/
  theorem termMaxFVarSucc_le_iff (term : Term) (cutoff : Nat) :
      LocalSkolem.termMaxFVarSucc term ≤ cutoff ↔
        ∀ parameter ∈ DefinitionalCnf.Term.freeVarParams term, parameter.varId < cutoff := by
    cases term <;>
      simp [LocalSkolem.termMaxFVarSucc, DefinitionalCnf.Term.freeVarParams, mem_merge_iff,
        or_imp, forall_and, Nat.max_le, Nat.succ_le_iff, termMaxFVarSucc_le_iff,
        formulaMaxFVarSucc_le_iff, termListMaxFVarSucc_le_iff]
  theorem formulaMaxFVarSucc_le_iff (formula : Formula) (cutoff : Nat) :
      LocalSkolem.formulaMaxFVarSucc formula ≤ cutoff ↔
        ∀ parameter ∈ DefinitionalCnf.Formula.freeVarParams formula, parameter.varId < cutoff := by
    cases formula <;>
      simp [LocalSkolem.formulaMaxFVarSucc, DefinitionalCnf.Formula.freeVarParams, mem_merge_iff,
        or_imp, forall_and, Nat.max_le, termMaxFVarSucc_le_iff,
        formulaMaxFVarSucc_le_iff, termListMaxFVarSucc_le_iff]
  theorem termListMaxFVarSucc_le_iff (terms : List Term) (cutoff : Nat) :
      LocalSkolem.termListMaxFVarSucc terms ≤ cutoff ↔
        ∀ parameter ∈ DefinitionalCnf.Term.freeVarParamsList terms, parameter.varId < cutoff := by
    cases terms <;>
      simp [LocalSkolem.termListMaxFVarSucc, DefinitionalCnf.Term.freeVarParamsList, mem_merge_iff,
        or_imp, forall_and, Nat.max_le, termMaxFVarSucc_le_iff,
        termListMaxFVarSucc_le_iff]
end
end FreeSupport

theorem Env.FreeAgreement.setFree_of_lt {M : Model} (env : Env M)
    (parameters : List DefinitionalCnf.FreeVarParam) (freshSort : CoreSort)
    (freshId : VarId) (value : M.Carrier)
    (hIds : ∀ parameter ∈ parameters, parameter.varId < freshId) :
    Env.FreeAgreement parameters (env.setFree freshSort freshId value) env := by
  intro parameter hParameter
  have hNe := Nat.ne_of_lt (hIds parameter hParameter)
  simp [Env.setFree, hNe]

namespace Freshness
theorem Term.eval_setFree_of_max_le {M : Model} (env : Env M) (freshSort : CoreSort) (freshId : VarId) (value :
    M.Carrier) (term : Term) (hMax : LocalSkolem.termMaxFVarSucc term ≤ freshId) : Term.eval (env.setFree freshSort
    freshId value) term = Term.eval env term := by
  apply Term.eval_eq_of_freeAgreement (env.setFree freshSort freshId value) env (fun _ => rfl)
  exact Env.FreeAgreement.setFree_of_lt env (DefinitionalCnf.Term.freeVarParams term)
    freshSort freshId value ((FreeSupport.termMaxFVarSucc_le_iff term freshId).mp hMax)

theorem Formula.satisfies_setFree_of_max_le {M : Model} (env : Env M) (freshSort : CoreSort) (freshId : VarId) (value :
    M.Carrier) (formula : Formula) (hMax : LocalSkolem.formulaMaxFVarSucc formula ≤ freshId) : Formula.Satisfies
    (env.setFree freshSort freshId value) formula ↔ Formula.Satisfies env formula := by
  apply Formula.satisfies_iff_of_freeAgreement (env.setFree freshSort freshId value) env (fun _ => rfl)
  exact Env.FreeAgreement.setFree_of_lt env (DefinitionalCnf.Formula.freeVarParams formula)
    freshSort freshId value ((FreeSupport.formulaMaxFVarSucc_le_iff formula freshId).mp hMax)

theorem Term.evalList_setFree_of_max_le {M : Model} (env : Env M) (freshSort : CoreSort) (freshId : VarId) (value :
    M.Carrier) (terms : List Term) (hMax : LocalSkolem.termListMaxFVarSucc terms ≤ freshId) : terms.map (Term.eval
    (env.setFree freshSort freshId value)) = terms.map (Term.eval env) := by
  apply Term.evalList_eq_of_freeAgreement (env.setFree freshSort freshId value) env (fun _ => rfl)
  exact Env.FreeAgreement.setFree_of_lt env (DefinitionalCnf.Term.freeVarParamsList terms)
    freshSort freshId value ((FreeSupport.termListMaxFVarSucc_le_iff terms freshId).mp hMax)


theorem Nnf.satisfies_overrideFunctionWith_of_max_le {M : Model} (env : Env M) (symbol : FunctionSymbol) (interpretation : List M.Carrier → M.Carrier) (nnf : Nnf) (hMax : LocalSkolem.nnfMaxFunctionIdSucc nnf ≤ symbol.id) : Nnf.Satisfies (Env.rebaseOverrideFunction env symbol interpretation) nnf ↔ Nnf.Satisfies env nnf := by
  rw [← Nnf.satisfies_toFormula, ← Nnf.satisfies_toFormula]
  apply Formula.satisfies_overrideFunctionWith_of_max_le
  simpa [Nnf.maxFunctionIdSucc_toFormula] using hMax
theorem Nnf.satisfies_overrideFunction_of_max_le {M : Model} (env : Env M) (symbol : FunctionSymbol) (value : M.Carrier) (nnf : Nnf) (hMax : LocalSkolem.nnfMaxFunctionIdSucc nnf ≤ symbol.id) : Nnf.Satisfies (Env.rebaseOverride env symbol value) nnf ↔ Nnf.Satisfies env nnf := by
  rw [← Nnf.satisfies_toFormula, ← Nnf.satisfies_toFormula]
  apply Formula.satisfies_overrideFunction_of_max_le
  simpa [Nnf.maxFunctionIdSucc_toFormula] using hMax
theorem Nnf.satisfies_setFree_of_max_le {M : Model} (env : Env M) (freshSort : CoreSort) (freshId : VarId) (value : M.Carrier) (nnf : Nnf) (hMax : LocalSkolem.nnfMaxFVarSucc nnf ≤ freshId) : Nnf.Satisfies (env.setFree freshSort freshId value) nnf ↔ Nnf.Satisfies env nnf := by
  rw [← Nnf.satisfies_toFormula, ← Nnf.satisfies_toFormula]
  apply Formula.satisfies_setFree_of_max_le
  simpa [Nnf.maxFVarSucc_toFormula] using hMax
theorem openForall_satisfies {M : Model} (env : Env M) (sort : CoreSort) (body : Nnf) (freshId : VarId) (value : M.Carrier) (hSort : M.sortInterp sort value) (hFresh : LocalSkolem.nnfMaxFVarSucc body ≤ freshId) (h : Nnf.Satisfies env (Nnf.forallE sort body)) : Nnf.Satisfies (env.setFree sort freshId value) (LocalSkolem.instantiateNnf (Term.fvar sort freshId) body) := by
  have hBody := h value hSort
  have hBody' := (Nnf.satisfies_setFree_of_max_le (env.push value) sort freshId value body hFresh).mpr hBody
  apply (LocalSkolem.instantiateNnf_satisfies (env.setFree sort freshId value) (Term.fvar sort freshId) body).mpr
  rw [Semantics.Env.insertAt_zero]
  have hEval :
      Term.eval (env.setFree sort freshId value) (Term.fvar sort freshId) = value := by
    simp [Term.eval, Env.setFree]
  rw [hEval]
  simpa [Env.push, Env.setFree] using hBody'
theorem skolemizeExists_satisfies {M : Model} (env : Env M) (body : Nnf) (symbol : FunctionSymbol) (args : List Term) (witness : M.Carrier) (hFresh : LocalSkolem.nnfMaxFunctionIdSucc body ≤ symbol.id) (hBody : Nnf.Satisfies (env.push witness) body) : Nnf.Satisfies (Env.rebaseOverride env symbol witness) (LocalSkolem.instantiateNnf (Term.app symbol args) body) := by
  have hBody' := (Nnf.satisfies_overrideFunction_of_max_le (env.push witness) symbol witness body hFresh).mpr hBody
  apply (LocalSkolem.instantiateNnf_satisfies (Env.rebaseOverride env symbol witness) (Term.app symbol args) body).mpr
  rw [Semantics.Env.insertAt_zero]
  have hEval :
      Term.eval (Env.rebaseOverride env symbol witness) (Term.app symbol args) = witness := by
    simp [Term.eval, Env.rebaseOverride, Model.overrideFunctionValue, Model.overrideFunction]
  simpa [hEval] using! hBody'
theorem skolemizeExists_satisfiesWith {M : Model} (env : Env M) (body : Nnf) (symbol : FunctionSymbol) (args : List Term) (interpretation : List M.Carrier → M.Carrier) (witness : M.Carrier) (hBodyFresh :
    LocalSkolem.nnfMaxFunctionIdSucc body ≤ symbol.id) (hArgsFresh : LocalSkolem.termListMaxFunctionIdSucc args ≤ symbol.id) (hWitness : interpretation (args.map (Term.eval env)) = witness) (hBody : Nnf.Satisfies
    (env.push witness) body) : Nnf.Satisfies (Env.rebaseOverrideFunction env symbol interpretation) (LocalSkolem.instantiateNnf (Term.app symbol args) body) := by
  have hBody' := (Nnf.satisfies_overrideFunctionWith_of_max_le (env.push witness) symbol interpretation body hBodyFresh).mpr hBody
  apply (LocalSkolem.instantiateNnf_satisfies (Env.rebaseOverrideFunction env symbol interpretation) (Term.app symbol args) body).mpr
  rw [Semantics.Env.insertAt_zero]
  have hArgs :
      args.map (Term.eval (Env.rebaseOverrideFunction env symbol interpretation)) =
        args.map (Term.eval env) :=
    Term.evalList_overrideFunctionWith_of_max_le
      env symbol interpretation args hArgsFresh
  have hEval :
      Term.eval (Env.rebaseOverrideFunction env symbol interpretation) (Term.app symbol args) =
        witness := by
    simp only [Term.eval, Model.overrideFunction]
    simp only [ite_true]
    exact (congrArg interpretation hArgs).trans hWitness
  simpa [hEval] using! hBody'
theorem skolemizeExists_satisfiesWithChoice {M : Model} (base env : Env M) (sort : CoreSort) (body : Nnf) (symbol : FunctionSymbol) (universals : List LocalSkolem.UniversalIntro) (hWellFormed : ∀ universal ∈ universals,
    universal.term = Term.fvar universal.sort universal.varId) (hSupport : ∀ parameter, parameter ∈ DefinitionalCnf.nnfFreeVarParams body → parameter ∈ LocalSkolemChoice.parameters universals) (hBound :
    LocalSkolemChoice.SameBoundStack env base) (hBodyFresh : LocalSkolem.nnfMaxFunctionIdSucc body ≤ symbol.id) (hArgsFresh : LocalSkolem.termListMaxFunctionIdSucc (universals.map fun universal => universal.term) ≤
    symbol.id) (hSat : Nnf.Satisfies env (Nnf.existsE sort body)) : Nnf.Satisfies (Env.rebaseOverrideFunction env symbol (LocalSkolemChoice.chooseWitness base universals sort body)) (LocalSkolem.instantiateNnf (Term.app
    symbol (universals.map fun universal => universal.term)) body) := by
  rcases hSat with ⟨sourceWitness, hSourceSort, hSourceBody⟩
  let arguments := LocalSkolemChoice.values env universals
  have hExists :
      ∃ witness,
        LocalSkolemChoice.HasWitness
          base universals sort body arguments witness := by
    exact ⟨sourceWitness, hSourceSort, env, hBound, rfl, hSourceBody⟩
  let witness :=
    LocalSkolemChoice.chooseWitness base universals sort body arguments
  have hChosen :
      LocalSkolemChoice.HasWitness
        base universals sort body arguments witness := by
    exact LocalSkolemChoice.chooseWitness_spec
      base universals sort body arguments hExists
  rcases hChosen with
    ⟨_, witnessEnv, hWitnessBound, hWitnessValues, hWitnessBody⟩
  have hValues :
      LocalSkolemChoice.values witnessEnv universals =
        LocalSkolemChoice.values env universals := by
    simpa [arguments] using hWitnessValues
  have hAgreement :
      Env.FreeAgreement (DefinitionalCnf.nnfFreeVarParams body) witnessEnv env := by
    exact (LocalSkolemChoice.freeAgreement_of_values_eq witnessEnv env universals hValues).mono hSupport
  have hBody :
      Nnf.Satisfies (env.push witness) body := by
    exact (Nnf.satisfies_iff_of_freeAgreement (witnessEnv.push witness) (env.push witness) (by
          intro index
          cases index with
          | zero => rfl
          | succ index => exact (hWitnessBound index).trans (hBound index).symm)
        body (hAgreement.push witness)).mp hWitnessBody
  apply skolemizeExists_satisfiesWith
    env body symbol (universals.map fun universal => universal.term) (LocalSkolemChoice.chooseWitness base universals sort body)
      witness hBodyFresh hArgsFresh
  · change
      LocalSkolemChoice.chooseWitness base universals sort body ((universals.map fun universal => universal.term).map (Term.eval env)) =
        witness
    rw [LocalSkolemChoice.eval_terms_eq_values env universals hWellFormed]
  · exact hBody
end Freshness
end Semantics
namespace LocalSkolem
theorem termMaxFVarSucc_shiftAbove (amount : Nat) : ∀ term : Term, ∀ cutoff, termMaxFVarSucc (Term.shiftAbove amount cutoff term) = termMaxFVarSucc term := by
  apply Term.rec (motive_1 := fun term => ∀ cutoff, termMaxFVarSucc (Term.shiftAbove amount cutoff term) = termMaxFVarSucc term)
    (motive_2 := fun formula => ∀ cutoff, formulaMaxFVarSucc (Formula.shiftAbove amount cutoff formula) = formulaMaxFVarSucc formula)
    (motive_3 := fun terms => ∀ cutoff, termListMaxFVarSucc (Term.shiftListAbove amount cutoff terms) = termListMaxFVarSucc terms)
  all_goals intros
  all_goals simp_all [Term.shiftAbove, Formula.shiftAbove, Term.shiftListAbove, termMaxFVarSucc, formulaMaxFVarSucc, termListMaxFVarSucc]
  case bvar => split <;> rfl
theorem termMaxFunctionIdSucc_shiftAbove (amount : Nat) : ∀ term : Term, ∀ cutoff, termMaxFunctionIdSucc (Term.shiftAbove amount cutoff term) = termMaxFunctionIdSucc term := by
  apply Term.rec (motive_1 := fun term => ∀ cutoff, termMaxFunctionIdSucc (Term.shiftAbove amount cutoff term) = termMaxFunctionIdSucc term)
    (motive_2 := fun formula => ∀ cutoff, formulaMaxFunctionIdSucc (Formula.shiftAbove amount cutoff formula) = formulaMaxFunctionIdSucc formula)
    (motive_3 := fun terms => ∀ cutoff, termListMaxFunctionIdSucc (Term.shiftListAbove amount cutoff terms) = termListMaxFunctionIdSucc terms)
  all_goals intros
  all_goals simp_all [Term.shiftAbove, Formula.shiftAbove, Term.shiftListAbove, termMaxFunctionIdSucc, formulaMaxFunctionIdSucc, termListMaxFunctionIdSucc]
  case bvar => split <;> rfl
theorem formulaMaxFVarSucc_instantiateAt_of_le (replacement : Term) : ∀ formula : Formula, ∀ depth limit, formulaMaxFVarSucc formula ≤ limit → termMaxFVarSucc replacement ≤ limit → formulaMaxFVarSucc (Formula.instantiateAt depth replacement formula) ≤ limit := by
  apply Formula.rec
    (motive_1 := fun term => ∀ depth limit, termMaxFVarSucc term ≤ limit → termMaxFVarSucc replacement ≤ limit → termMaxFVarSucc (Term.instantiateAt depth replacement term) ≤ limit)
    (motive_2 := fun formula => ∀ depth limit, formulaMaxFVarSucc formula ≤ limit → termMaxFVarSucc replacement ≤ limit →
      formulaMaxFVarSucc (Formula.instantiateAt depth replacement formula) ≤ limit)
    (motive_3 := fun terms => ∀ depth limit, termListMaxFVarSucc terms ≤ limit → termMaxFVarSucc replacement ≤ limit →
      termListMaxFVarSucc (Term.instantiateListAt depth replacement terms) ≤ limit)
  case bvar =>
    intro sort index depth limit hTerm hReplacement
    by_cases hLt : index < depth
    · simp [Term.instantiateAt, termMaxFVarSucc, hLt] at hTerm ⊢
    · by_cases hEq : index = depth
      · subst index
        simpa [Term.instantiateAt, termMaxFVarSucc, hLt, Term.shift, termMaxFVarSucc_shiftAbove] using hReplacement
      · simp [Term.instantiateAt, termMaxFVarSucc, hLt, hEq] at hTerm ⊢
  all_goals intros
  all_goals simp only [Term.instantiateAt, Formula.instantiateAt, Term.instantiateListAt, termMaxFVarSucc, formulaMaxFVarSucc, termListMaxFVarSucc, Nat.max_le] at *
  all_goals grind
theorem formulaMaxFunctionIdSucc_instantiateAt_of_le (replacement : Term) : ∀ formula : Formula, ∀ depth limit, formulaMaxFunctionIdSucc formula ≤ limit → termMaxFunctionIdSucc replacement ≤ limit → formulaMaxFunctionIdSucc (Formula.instantiateAt depth replacement formula) ≤ limit := by
  apply Formula.rec (motive_1 := fun term => ∀ depth limit, termMaxFunctionIdSucc term ≤ limit → termMaxFunctionIdSucc replacement ≤ limit →
      termMaxFunctionIdSucc (Term.instantiateAt depth replacement term) ≤ limit)
    (motive_2 := fun formula => ∀ depth limit, formulaMaxFunctionIdSucc formula ≤ limit → termMaxFunctionIdSucc replacement ≤ limit →
      formulaMaxFunctionIdSucc (Formula.instantiateAt depth replacement formula) ≤
        limit)
    (motive_3 := fun terms => ∀ depth limit, termListMaxFunctionIdSucc terms ≤ limit → termMaxFunctionIdSucc replacement ≤ limit → termListMaxFunctionIdSucc
        (Term.instantiateListAt depth replacement terms) ≤ limit)
  case bvar =>
    intro sort index depth limit hTerm hReplacement
    by_cases hLt : index < depth
    · simp [Term.instantiateAt, termMaxFunctionIdSucc, hLt] at hTerm ⊢
    · by_cases hEq : index = depth
      · subst index
        simpa [Term.instantiateAt, termMaxFunctionIdSucc, hLt, Term.shift, termMaxFunctionIdSucc_shiftAbove] using hReplacement
      · simp [Term.instantiateAt, termMaxFunctionIdSucc, hLt, hEq] at hTerm ⊢
  all_goals intros
  all_goals simp only [Term.instantiateAt, Formula.instantiateAt, Term.instantiateListAt, termMaxFunctionIdSucc, formulaMaxFunctionIdSucc, termListMaxFunctionIdSucc, Nat.max_le] at *
  all_goals grind
theorem termListMaxFVarSucc_append (left right : List Term) : LocalSkolem.termListMaxFVarSucc (left ++ right) = Nat.max (LocalSkolem.termListMaxFVarSucc left) (LocalSkolem.termListMaxFVarSucc right) := by
  induction left with
  | nil => simp [LocalSkolem.termListMaxFVarSucc]
  | cons head tail ih =>
      simp only [List.cons_append, LocalSkolem.termListMaxFVarSucc]
      rw [ih]
      simp [Nat.max_assoc, Nat.max_comm]
theorem termListMaxFunctionIdSucc_append (left right : List Term) : LocalSkolem.termListMaxFunctionIdSucc (left ++ right) = Nat.max (LocalSkolem.termListMaxFunctionIdSucc left) (LocalSkolem.termListMaxFunctionIdSucc right) := by
  induction left with
  | nil => simp [LocalSkolem.termListMaxFunctionIdSucc]
  | cons head tail ih =>
      simp only [List.cons_append, LocalSkolem.termListMaxFunctionIdSucc]
      rw [ih]
      simp [Nat.max_assoc, Nat.max_comm]
namespace Context
structure Bounded (context : LocalSkolem.Context) (nextFVar : Nat) : Prop where
  args : LocalSkolem.termListMaxFVarSucc context.skolemArgs ≤ nextFVar
  wellFormed :
    ∀ universal ∈ context.universals,
      universal.term = Term.fvar universal.sort universal.varId
theorem bounded_empty : Bounded {} 0 := by
  constructor
  · exact Nat.le_refl _
  · simp
theorem bounded_empty_at (nextFVar : Nat) : Bounded {} nextFVar := by
  constructor
  · simp [LocalSkolem.Context.skolemArgs, LocalSkolem.Context.orderedUniversals, LocalSkolem.termListMaxFVarSucc]
  · simp
theorem Bounded.mono {context : LocalSkolem.Context} {left right : Nat} (h : Bounded context left) (hLe : left ≤ right) : Bounded context right where
  args := Nat.le_trans h.args hLe
  wellFormed := h.wellFormed
def parameters (context : LocalSkolem.Context) : List DefinitionalCnf.FreeVarParam :=
  Semantics.LocalSkolemChoice.parameters context.orderedUniversals.toList
def Supports (context : LocalSkolem.Context) (nnf : Nnf) : Prop :=
  Semantics.FreeSupport.NnfSupportedBy context.parameters nnf
theorem parameters_cons (context : LocalSkolem.Context) (universal : UniversalIntro) : ({ universals := universal :: context.universals } : LocalSkolem.Context).parameters =
      context.parameters ++
        [Semantics.LocalSkolemChoice.UniversalIntro.parameter universal] := by
  simp [parameters, Context.orderedUniversals, Semantics.LocalSkolemChoice.parameters]
theorem termListSupportedBy_of_wellFormed (universals : List UniversalIntro) (hWellFormed : ∀ universal ∈ universals, universal.term = Term.fvar universal.sort universal.varId) : Semantics.FreeSupport.TermListSupportedBy (Semantics.LocalSkolemChoice.parameters universals) (universals.map fun universal => universal.term) := by
  induction universals with
  | nil => trivial
  | cons universal universals ih =>
      have hHead :
          universal.term = Term.fvar universal.sort universal.varId :=
        hWellFormed universal (by simp)
      have hTail :
          ∀ candidate ∈ universals,
            candidate.term =
              Term.fvar candidate.sort candidate.varId := by
        intro candidate hCandidate
        exact hWellFormed candidate (by simp [hCandidate])
      constructor
      · change
          Semantics.FreeSupport.TermSupportedBy (Semantics.LocalSkolemChoice.parameters (universal :: universals))
            universal.term
        rw [hHead]
        exact List.mem_map.mpr ⟨universal, by simp, rfl⟩
      · exact Semantics.FreeSupport.termListSupportedBy_mono (smaller := Semantics.LocalSkolemChoice.parameters universals)
          (larger := Semantics.LocalSkolemChoice.parameters (universal :: universals)) (by
            intro parameter hParameter
            exact List.mem_map.mpr <| by
              rcases List.mem_map.mp hParameter with
                ⟨candidate, hCandidate, rfl⟩
              exact ⟨candidate, by simp [hCandidate], rfl⟩) (universals.map fun candidate => candidate.term) (ih hTail)
theorem Bounded.skolemArgsSupported {context : LocalSkolem.Context} {nextFVar : Nat} (h : Bounded context nextFVar) : Semantics.FreeSupport.TermListSupportedBy context.parameters context.skolemArgs := by
  apply termListSupportedBy_of_wellFormed
  intro universal hUniversal
  apply h.wellFormed universal
  simpa [Context.orderedUniversals] using hUniversal
theorem Supports.openForall {context : LocalSkolem.Context} {body : Nnf} (hSupported : context.Supports body) (universal : UniversalIntro) (hTerm : universal.term = Term.fvar universal.sort universal.varId) : ({ universals := universal :: context.universals } :
      LocalSkolem.Context).Supports (LocalSkolem.instantiateNnf universal.term body) := by
  rw [Supports, parameters_cons]
  apply Semantics.FreeSupport.nnfSupportedBy_instantiate
  · rw [hTerm]
    exact List.mem_append.mpr <| Or.inr (List.mem_singleton_self _)
  · exact Semantics.FreeSupport.nnfSupportedBy_mono (fun parameter hParameter => List.mem_append.mpr (Or.inl hParameter))
      body hSupported
theorem Supports.skolemizeExists {context : LocalSkolem.Context} {body : Nnf} {nextFVar : Nat} (hContext : Bounded context nextFVar) (hSupported : context.Supports body) (symbol : FunctionSymbol) : context.Supports (LocalSkolem.instantiateNnf (Term.app symbol context.skolemArgs) body) := by
  apply Semantics.FreeSupport.nnfSupportedBy_instantiate
  · exact hContext.skolemArgsSupported
  · exact hSupported
theorem bounded_cons (context : LocalSkolem.Context) (nextFVar : Nat) (h : Bounded context nextFVar) (universal : UniversalIntro) (hUniversal : universal.term = Term.fvar universal.sort universal.varId) (hVar : universal.varId = nextFVar) : Bounded { universals := universal :: context.universals } (nextFVar + 1) := by
  constructor
  · rw [show ({ universals := universal :: context.universals } : LocalSkolem.Context).skolemArgs = context.skolemArgs ++ [universal.term] by
      simp [Context.skolemArgs, Context.orderedUniversals]]
    rw [hUniversal, termListMaxFVarSucc_append]
    simp only [hVar]
    exact Nat.max_le.mpr ⟨Nat.le_trans h.args (Nat.le_succ _), Nat.le_refl _⟩
  · intro candidate hCandidate
    simp only [List.mem_cons] at hCandidate
    rcases hCandidate with rfl | hCandidate
    · exact hUniversal
    · exact h.wellFormed candidate hCandidate
end Context
theorem termListMaxFunctionIdSucc_map_fvar_zero (universals : List UniversalIntro) (hUniversal : ∀ universal ∈ universals, universal.term = Term.fvar universal.sort universal.varId) : LocalSkolem.termListMaxFunctionIdSucc (universals.map (fun universal => universal.term)) = 0 := by
  induction universals with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, LocalSkolem.termListMaxFunctionIdSucc]
      rw [hUniversal head (by simp)]
      have hTail : ∀ universal ∈ tail,
          universal.term = Term.fvar universal.sort universal.varId := by
        intro universal hMem
        exact hUniversal universal (by simp [hMem])
      rw [ih hTail]
      rfl
theorem Context.argsFunctionBounded (context : LocalSkolem.Context) (nextFVar : Nat) (h : Context.Bounded context nextFVar) : LocalSkolem.termListMaxFunctionIdSucc context.skolemArgs ≤ 0 := by
  have hReverse :
      ∀ universal ∈ context.universals.reverse,
        universal.term = Term.fvar universal.sort universal.varId := by
    intro universal hMem
    apply h.wellFormed universal
    simpa using hMem
  simpa [LocalSkolem.Context.skolemArgs, LocalSkolem.Context.orderedUniversals] using
    termListMaxFunctionIdSucc_map_fvar_zero context.universals.reverse hReverse
theorem nnfMaxFVarSucc_instantiateNnf_of_le (body : Nnf) (replacement : Term) (limit : Nat) (hBody : LocalSkolem.nnfMaxFVarSucc body ≤ limit) (hReplacement : LocalSkolem.termMaxFVarSucc replacement ≤ limit) : LocalSkolem.nnfMaxFVarSucc (LocalSkolem.instantiateNnf replacement body) ≤ limit := by
  unfold LocalSkolem.instantiateNnf
  rw [← Semantics.Freshness.Nnf.maxFVarSucc_toFormula, LocalSkolem.instantiateNnfAt_toFormula]
  apply formulaMaxFVarSucc_instantiateAt_of_le replacement body.toFormula 0 limit
  · simpa [Semantics.Freshness.Nnf.maxFVarSucc_toFormula] using hBody
  · exact hReplacement
theorem nnfMaxFunctionIdSucc_instantiateNnf_of_le (body : Nnf) (replacement : Term) (limit : Nat) (hBody : LocalSkolem.nnfMaxFunctionIdSucc body ≤ limit) (hReplacement : LocalSkolem.termMaxFunctionIdSucc replacement ≤ limit) : LocalSkolem.nnfMaxFunctionIdSucc (LocalSkolem.instantiateNnf replacement body) ≤ limit := by
  unfold LocalSkolem.instantiateNnf
  rw [← Semantics.Freshness.Nnf.maxFunctionIdSucc_toFormula, LocalSkolem.instantiateNnfAt_toFormula]
  apply formulaMaxFunctionIdSucc_instantiateAt_of_le replacement body.toFormula 0 limit
  · simpa [Semantics.Freshness.Nnf.maxFunctionIdSucc_toFormula] using hBody
  · exact hReplacement
structure RunBounds (input : BuildState) (result : Nnf) (output : BuildState) : Prop where
  fvarMono : input.nextFVar ≤ output.nextFVar
  skolemMono : input.nextSkolem ≤ output.nextSkolem
  resultFVar : nnfMaxFVarSucc result ≤ output.nextFVar
  resultFunction : nnfMaxFunctionIdSucc result ≤ output.nextSkolem
theorem skolemizeAt_bounds : ∀ (path : Path) (context : Context) (nnf : Nnf) (state : BuildState) (result : Nnf) (output : BuildState), Context.Bounded context state.nextFVar → nnfMaxFVarSucc nnf ≤ state.nextFVar → nnfMaxFunctionIdSucc nnf ≤ state.nextSkolem → (skolemizeAt path context nnf).run state = (result, output) → RunBounds state result output := by
  apply skolemizeAt.induct
  case case1 =>
    intro path context state result output hContext hFVar hFunction hRun
    rw [skolemizeAt.eq_1] at hRun
    change (Nnf.trueE, state) = (result, output) at hRun
    cases hRun
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _⟩
  case case2 =>
    intro path context state result output hContext hFVar hFunction hRun
    rw [skolemizeAt.eq_2] at hRun
    change (Nnf.falseE, state) = (result, output) at hRun
    cases hRun
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.zero_le _, Nat.zero_le _⟩
  case case3 =>
    intro path context literal state result output hContext hFVar hFunction hRun
    rw [skolemizeAt.eq_3] at hRun
    change (Nnf.lit literal, state) = (result, output) at hRun
    cases hRun
    exact ⟨Nat.le_refl _, Nat.le_refl _, hFVar, hFunction⟩
  case case4 | case5 =>
    intro path context left right ihLeft ihRight state result output
      hContext hFVar hFunction hRun
    first | rw [skolemizeAt.eq_4] at hRun
          | rw [skolemizeAt.eq_5] at hRun
    first
    | change (match (skolemizeAt (path ++ [PathStep.left]) context left).run state with
          | (leftResult, leftState) =>
            match
                (skolemizeAt (path ++ [PathStep.right]) context right).run
                  leftState with
            | (rightResult, rightState) => (Nnf.conj leftResult rightResult, rightState)) = (result, output) at hRun
    | change (match (skolemizeAt (path ++ [PathStep.left]) context left).run state with
          | (leftResult, leftState) =>
            match
                (skolemizeAt (path ++ [PathStep.right]) context right).run
                  leftState with
            | (rightResult, rightState) => (Nnf.disj leftResult rightResult, rightState)) = (result, output) at hRun
    cases hLeft : (skolemizeAt (path ++ [PathStep.left]) context left).run state with
    | mk leftResult leftState =>
      cases hRight : (skolemizeAt (path ++ [PathStep.right]) context right).run leftState with
      | mk rightResult rightState =>
        simp only [hLeft, hRight] at hRun
        cases hRun
        have hLeftFVar : nnfMaxFVarSucc left ≤ state.nextFVar :=
          Nat.le_trans (Nat.le_max_left _ _) hFVar
        have hRightFVar : nnfMaxFVarSucc right ≤ state.nextFVar :=
          Nat.le_trans (Nat.le_max_right _ _) hFVar
        have hLeftFunction : nnfMaxFunctionIdSucc left ≤ state.nextSkolem :=
          Nat.le_trans (Nat.le_max_left _ _) hFunction
        have hRightFunction : nnfMaxFunctionIdSucc right ≤ state.nextSkolem :=
          Nat.le_trans (Nat.le_max_right _ _) hFunction
        have leftBounds :=
          ihLeft state leftResult leftState hContext hLeftFVar hLeftFunction hLeft
        have rightBounds :=
          ihRight leftState rightResult output (hContext.mono leftBounds.fvarMono) (Nat.le_trans hRightFVar leftBounds.fvarMono)
            (Nat.le_trans hRightFunction leftBounds.skolemMono) hRight
        exact {
          fvarMono := Nat.le_trans leftBounds.fvarMono rightBounds.fvarMono
          skolemMono := Nat.le_trans leftBounds.skolemMono rightBounds.skolemMono
          resultFVar := Nat.max_le.mpr
            ⟨Nat.le_trans leftBounds.resultFVar rightBounds.fvarMono, rightBounds.resultFVar⟩
          resultFunction := Nat.max_le.mpr
            ⟨Nat.le_trans leftBounds.resultFunction rightBounds.skolemMono, rightBounds.resultFunction⟩
        }
  case case6 =>
    intro path context sort body ih state result output hContext hFVar hFunction hRun
    let universal : UniversalIntro := {
      index := state.universalTrace.size
      sort := sort
      varId := state.nextFVar
      term := Term.fvar sort state.nextFVar
      contextDepth := context.depth
    }
    let nextState : BuildState := {
      state with
      nextFVar := state.nextFVar + 1
      steps := state.steps.push {
        path := path
        kind := StepKind.openForall
        binderSort := sort
        body := body
        replacement := universal.term
        instantiatedBody := instantiateNnf universal.term body
        universalContext := context.orderedUniversals
        universal? := some universal
      }
      universalTrace := state.universalTrace.push universal
    }
    rw [skolemizeAt.eq_6] at hRun
    change (skolemizeAt path { universals := universal :: context.universals } (instantiateNnf universal.term body)).run nextState = (result, output) at hRun
    have hContext' :
        Context.Bounded { universals := universal :: context.universals }
          nextState.nextFVar := by
      apply Context.bounded_cons context state.nextFVar hContext universal
      · rfl
      · rfl
    have hInstFVar :
        nnfMaxFVarSucc (instantiateNnf universal.term body) ≤
          nextState.nextFVar := by
      apply nnfMaxFVarSucc_instantiateNnf_of_le body universal.term
        nextState.nextFVar
      · exact Nat.le_trans hFVar (Nat.le_succ _)
      · exact Nat.le_refl _
    have hInstFunction :
        nnfMaxFunctionIdSucc (instantiateNnf universal.term body) ≤
          nextState.nextSkolem := by
      apply nnfMaxFunctionIdSucc_instantiateNnf_of_le body universal.term
        nextState.nextSkolem
      · exact hFunction
      · exact Nat.zero_le _
    have recursiveBounds :=
      ih universal nextState result output hContext' hInstFVar hInstFunction hRun
    exact {
      fvarMono := Nat.le_trans (Nat.le_succ _) recursiveBounds.fvarMono
      skolemMono := recursiveBounds.skolemMono
      resultFVar := recursiveBounds.resultFVar
      resultFunction := recursiveBounds.resultFunction
    }
  case case7 =>
    intro path context sort body ih state result output hContext hFVar hFunction hRun
    let universalContext := context.orderedUniversals
    let universalArgs := context.skolemArgs
    let symbol : FunctionSymbol := {
      id := state.nextSkolem
      arity := universalArgs.length
      role := FunctionRole.skolem
      inputSorts := context.skolemInputSorts
      outputSort := sort
    }
    let intro : SkolemIntro := {
      index := state.skolemTrace.size
      witnessSort := sort
      symbol := symbol
      universalContext := universalContext
      universalArgs := universalArgs
      term := Term.app symbol universalArgs
      contextDepth := universalContext.size
    }
    let nextState : BuildState := {
      state with
      nextSkolem := state.nextSkolem + 1
      steps := state.steps.push {
        path := path
        kind := StepKind.skolemizeExists
        binderSort := sort
        body := body
        replacement := intro.term
        instantiatedBody := instantiateNnf intro.term body
        universalContext := universalContext
        skolem? := some intro
      }
      skolemTrace := state.skolemTrace.push intro
    }
    rw [skolemizeAt.eq_7] at hRun
    change (skolemizeAt path context (instantiateNnf intro.term body)).run nextState = (result, output) at hRun
    have hIntroFVar : termMaxFVarSucc intro.term ≤ nextState.nextFVar := by exact hContext.args
    have hIntroFunction :
        termMaxFunctionIdSucc intro.term ≤ nextState.nextSkolem := by
      change Nat.max (state.nextSkolem + 1) (termListMaxFunctionIdSucc context.skolemArgs) ≤ state.nextSkolem + 1
      apply Nat.max_le.mpr
      exact ⟨Nat.le_refl _, Nat.le_trans (Context.argsFunctionBounded context state.nextFVar hContext) (Nat.zero_le _)⟩
    have hInstFVar :
        nnfMaxFVarSucc (instantiateNnf intro.term body) ≤ nextState.nextFVar := by
      exact nnfMaxFVarSucc_instantiateNnf_of_le body intro.term
        nextState.nextFVar hFVar hIntroFVar
    have hInstFunction :
        nnfMaxFunctionIdSucc (instantiateNnf intro.term body) ≤
          nextState.nextSkolem := by
      exact nnfMaxFunctionIdSucc_instantiateNnf_of_le body intro.term
        nextState.nextSkolem (Nat.le_trans hFunction (Nat.le_succ _))
        hIntroFunction
    have recursiveBounds :=
      ih intro nextState result output hContext hInstFVar hInstFunction hRun
    exact {
      fvarMono := recursiveBounds.fvarMono
      skolemMono := Nat.le_trans (Nat.le_succ _) recursiveBounds.skolemMono
      resultFVar := recursiveBounds.resultFVar
      resultFunction := recursiveBounds.resultFunction
    }
end LocalSkolem
namespace Semantics
namespace LocalSkolemSoundness
structure UniformFrameExtension (state : LocalSkolem.BuildState) (M : Model.{x}) where
  target : Model.{x}
  rebase : Env M → Env target
  unbase : Env target → Env M
  rebase_unbase : ∀ env, rebase (unbase env) = env
  unbase_rebase : ∀ env, unbase (rebase env) = env
  unbaseRespectsFree :
    ∀ env, Env.RespectsFree env → Env.RespectsFree (unbase env)
  unbaseSameBound :
    ∀ {left right},
      LocalSkolemChoice.SameBoundStack left right →
        LocalSkolemChoice.SameBoundStack (unbase left) (unbase right)
  functionSort : (∀ symbol arguments, M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)) →
      ∀ symbol arguments,
        target.sortInterp symbol.outputSort (target.functionInterp symbol arguments)
  foolContract : FoolContract M → FoolContract target
  contract : FoolLambdaContract M → FoolLambdaContract target
  respectsFree :
    ∀ env, Env.RespectsFree env → Env.RespectsFree (rebase env)
  sameBound :
    ∀ {left right},
      LocalSkolemChoice.SameBoundStack left right →
        LocalSkolemChoice.SameBoundStack (rebase left) (rebase right)
  preserves :
    ∀ env frame,
      LocalSkolem.nnfMaxFVarSucc frame ≤ state.nextFVar →
      LocalSkolem.nnfMaxFunctionIdSucc frame ≤ state.nextSkolem →
      Nnf.Satisfies env frame →
      Nnf.Satisfies (rebase env) frame
structure UniformSoundExtension (state : LocalSkolem.BuildState) (source result : Nnf) (M : Model) (base : Env M) where
  extension : UniformFrameExtension state M
  resultSat :
    ∀ env,
      Env.RespectsFree env →
      LocalSkolemChoice.SameBoundStack env base →
      Nnf.Satisfies env source →
      Nnf.Satisfies (extension.rebase env) result
/-- 恒等模型扩张同时保持所有环境合同与有界 frame。 -/
def UniformFrameExtension.refl (state : LocalSkolem.BuildState) (M : Model) :
    UniformFrameExtension state M where
  target := M
  rebase := id
  unbase := id
  rebase_unbase := fun _ => rfl
  unbase_rebase := fun _ => rfl
  unbaseRespectsFree := fun _ h => h
  unbaseSameBound := fun h => h
  functionSort := fun h => h
  foolContract := id
  contract := id
  respectsFree := fun _ h => h
  sameBound := fun h => h
  preserves := fun _ _ _ _ h => h

/-- 两段模型扩张沿单调增长的新鲜变量和函数界复合。 -/
def UniformFrameExtension.trans {state next : LocalSkolem.BuildState} {M : Model}
    (first : UniformFrameExtension state M)
    (second : UniformFrameExtension next first.target)
    (hFVar : state.nextFVar ≤ next.nextFVar)
    (hFunction : state.nextSkolem ≤ next.nextSkolem) :
    UniformFrameExtension state M where
  target := second.target
  rebase := fun env => second.rebase (first.rebase env)
  unbase := fun env => first.unbase (second.unbase env)
  rebase_unbase := by intro env; rw [first.rebase_unbase, second.rebase_unbase]
  unbase_rebase := by intro env; rw [second.unbase_rebase, first.unbase_rebase]
  unbaseRespectsFree := fun env h => first.unbaseRespectsFree _ (second.unbaseRespectsFree env h)
  unbaseSameBound := fun h => first.unbaseSameBound (second.unbaseSameBound h)
  functionSort := fun h => second.functionSort (first.functionSort h)
  foolContract := fun h => second.foolContract (first.foolContract h)
  contract := fun h => second.contract (first.contract h)
  respectsFree := fun env h => second.respectsFree _ (first.respectsFree env h)
  sameBound := fun h => second.sameBound (first.sameBound h)
  preserves := fun env frame hf hs h => second.preserves (first.rebase env) frame
    (Nat.le_trans hf hFVar) (Nat.le_trans hs hFunction) (first.preserves env frame hf hs h)

/-- 不改变公式的步骤直接使用恒等扩张。 -/
def UniformSoundExtension.refl (state : LocalSkolem.BuildState) (formula : Nnf)
    (M : Model) (base : Env M) : UniformSoundExtension state formula formula M base where
  extension := UniformFrameExtension.refl state M
  resultSat := fun _ _ _ h => h

theorem skolemizeAt_uniformSound : ∀ (path : LocalSkolem.Path) (context : LocalSkolem.Context) (nnf : Nnf) (state : LocalSkolem.BuildState) (result : Nnf) (output : LocalSkolem.BuildState), LocalSkolem.Context.Bounded
    context state.nextFVar → LocalSkolem.Context.Supports context nnf → LocalSkolem.nnfMaxFVarSucc nnf ≤ state.nextFVar → LocalSkolem.nnfMaxFunctionIdSucc nnf ≤ state.nextSkolem → (LocalSkolem.skolemizeAt path context
    nnf).run state = (result, output) → ∀ (M : Model) (base : Env M), Nonempty (UniformSoundExtension state nnf result M base) := by
  apply LocalSkolem.skolemizeAt.induct
  case case1 =>
    intro path context state result output hContext hSupported hFVar hFunction
      hRun M base
    rw [LocalSkolem.skolemizeAt.eq_1] at hRun
    change (Nnf.trueE, state) = (result, output) at hRun
    cases hRun
    exact ⟨UniformSoundExtension.refl state _ M base⟩
  case case2 =>
    intro path context state result output hContext hSupported hFVar hFunction
      hRun M base
    rw [LocalSkolem.skolemizeAt.eq_2] at hRun
    change (Nnf.falseE, state) = (result, output) at hRun
    cases hRun
    exact ⟨UniformSoundExtension.refl state _ M base⟩
  case case3 =>
    intro path context literal state result output hContext hSupported hFVar
      hFunction hRun M base
    rw [LocalSkolem.skolemizeAt.eq_3] at hRun
    change (Nnf.lit literal, state) = (result, output) at hRun
    cases hRun
    exact ⟨UniformSoundExtension.refl state _ M base⟩
  case case4 | case5 =>
    intro path context left right ihLeft ihRight state result output
      hContext hSupported hFVar hFunction hRun M base
    first | rw [LocalSkolem.skolemizeAt.eq_4] at hRun
          | rw [LocalSkolem.skolemizeAt.eq_5] at hRun
    first
    | change (match (LocalSkolem.skolemizeAt (path ++ [LocalSkolem.PathStep.left]) context left).run state with
          | (leftResult, leftState) =>
            match
                (LocalSkolem.skolemizeAt (path ++ [LocalSkolem.PathStep.right]) context right).run
                  leftState with
            | (rightResult, rightState) => (Nnf.conj leftResult rightResult, rightState)) = (result, output) at hRun
    | change (match (LocalSkolem.skolemizeAt (path ++ [LocalSkolem.PathStep.left]) context left).run state with
          | (leftResult, leftState) =>
            match
                (LocalSkolem.skolemizeAt (path ++ [LocalSkolem.PathStep.right]) context right).run
                  leftState with
            | (rightResult, rightState) => (Nnf.disj leftResult rightResult, rightState)) = (result, output) at hRun
    cases hLeft : (LocalSkolem.skolemizeAt (path ++ [LocalSkolem.PathStep.left]) context left).run state with
    | mk leftResult leftState =>
      cases hRight : (LocalSkolem.skolemizeAt (path ++ [LocalSkolem.PathStep.right]) context right).run leftState with
      | mk rightResult rightState =>
        simp only [hLeft, hRight] at hRun
        cases hRun
        have hLeftFVar : LocalSkolem.nnfMaxFVarSucc left ≤ state.nextFVar :=
          Nat.le_trans (Nat.le_max_left _ _) hFVar
        have hRightFVar : LocalSkolem.nnfMaxFVarSucc right ≤ state.nextFVar :=
          Nat.le_trans (Nat.le_max_right _ _) hFVar
        have hLeftFunction :
            LocalSkolem.nnfMaxFunctionIdSucc left ≤ state.nextSkolem :=
          Nat.le_trans (Nat.le_max_left _ _) hFunction
        have hRightFunction :
            LocalSkolem.nnfMaxFunctionIdSucc right ≤ state.nextSkolem :=
          Nat.le_trans (Nat.le_max_right _ _) hFunction
        rcases ihLeft state leftResult leftState hContext hSupported.1
          hLeftFVar hLeftFunction hLeft M base with ⟨leftSound⟩
        have leftBounds :=
          LocalSkolem.skolemizeAt_bounds (path ++ [LocalSkolem.PathStep.left]) context left state
            leftResult leftState hContext hLeftFVar hLeftFunction hLeft
        let rightBase := leftSound.extension.rebase base
        rcases ihRight leftState rightResult output (hContext.mono leftBounds.fvarMono) hSupported.2 (Nat.le_trans hRightFVar leftBounds.fvarMono)
          (Nat.le_trans hRightFunction leftBounds.skolemMono)
          hRight leftSound.extension.target rightBase with ⟨rightSound⟩
        exact ⟨{
          extension := leftSound.extension.trans rightSound.extension
            leftBounds.fvarMono leftBounds.skolemMono
          resultSat := by
            intro env hFree hBound hSat
            first
            | have hLeftResult :=
                leftSound.resultSat env hFree hBound hSat.1
              have hRightSource :=
                leftSound.extension.preserves env right
                  hRightFVar hRightFunction hSat.2
              have hRightResult :=
                rightSound.resultSat (leftSound.extension.rebase env) (leftSound.extension.respectsFree env hFree) (leftSound.extension.sameBound hBound)
                  hRightSource
              exact ⟨ rightSound.extension.preserves (leftSound.extension.rebase env) leftResult leftBounds.resultFVar leftBounds.resultFunction hLeftResult, hRightResult⟩
            | rcases hSat with hLeftSat | hRightSat
              · have hLeftResult :=
                  leftSound.resultSat env hFree hBound hLeftSat
                exact Or.inl <|
                  rightSound.extension.preserves (leftSound.extension.rebase env) leftResult
                    leftBounds.resultFVar leftBounds.resultFunction hLeftResult
              · have hRightSource :=
                  leftSound.extension.preserves env right
                    hRightFVar hRightFunction hRightSat
                exact Or.inr <|
                  rightSound.resultSat (leftSound.extension.rebase env) (leftSound.extension.respectsFree env hFree) (leftSound.extension.sameBound hBound)
                    hRightSource
        }⟩
  case case6 =>
    intro path context sort body ih state result output
      hContext hSupported hFVar hFunction hRun M base
    let universal : LocalSkolem.UniversalIntro := {
      index := state.universalTrace.size
      sort := sort
      varId := state.nextFVar
      term := Term.fvar sort state.nextFVar
      contextDepth := context.depth
    }
    let nextState : LocalSkolem.BuildState := {
      state with
      nextFVar := state.nextFVar + 1
      steps := state.steps.push {
        path := path
        kind := LocalSkolem.StepKind.openForall
        binderSort := sort
        body := body
        replacement := universal.term
        instantiatedBody := LocalSkolem.instantiateNnf universal.term body
        universalContext := context.orderedUniversals
        universal? := some universal
      }
      universalTrace := state.universalTrace.push universal
    }
    rw [LocalSkolem.skolemizeAt.eq_6] at hRun
    change (LocalSkolem.skolemizeAt path { universals := universal :: context.universals } (LocalSkolem.instantiateNnf universal.term body)).run nextState =
          (result, output) at hRun
    have hContext' :
        LocalSkolem.Context.Bounded
          { universals := universal :: context.universals }
          nextState.nextFVar := by
      apply LocalSkolem.Context.bounded_cons context state.nextFVar hContext universal
      · rfl
      · rfl
    have hBodySupported : context.Supports body :=
      hSupported
    have hSupported' : ({ universals := universal :: context.universals } : LocalSkolem.Context).Supports (LocalSkolem.instantiateNnf universal.term body) :=
      LocalSkolem.Context.Supports.openForall hBodySupported universal rfl
    have hInstFVar :
        LocalSkolem.nnfMaxFVarSucc (LocalSkolem.instantiateNnf universal.term body) ≤
          nextState.nextFVar :=
      LocalSkolem.nnfMaxFVarSucc_instantiateNnf_of_le
        body universal.term nextState.nextFVar (Nat.le_trans hFVar (Nat.le_succ _)) (Nat.le_refl _)
    have hInstFunction :
        LocalSkolem.nnfMaxFunctionIdSucc (LocalSkolem.instantiateNnf universal.term body) ≤
          nextState.nextSkolem :=
      LocalSkolem.nnfMaxFunctionIdSucc_instantiateNnf_of_le
        body universal.term nextState.nextSkolem hFunction (Nat.zero_le _)
    rcases ih universal nextState result output hContext' hSupported'
      hInstFVar hInstFunction hRun M base with ⟨recursiveSound⟩
    exact ⟨{
      extension := {
        target := recursiveSound.extension.target
        rebase := recursiveSound.extension.rebase
        unbase := recursiveSound.extension.unbase
        rebase_unbase := recursiveSound.extension.rebase_unbase
        unbase_rebase := recursiveSound.extension.unbase_rebase
        unbaseRespectsFree := recursiveSound.extension.unbaseRespectsFree
        unbaseSameBound := recursiveSound.extension.unbaseSameBound
        functionSort := recursiveSound.extension.functionSort
        foolContract := recursiveSound.extension.foolContract
        contract := recursiveSound.extension.contract
        respectsFree := recursiveSound.extension.respectsFree
        sameBound := recursiveSound.extension.sameBound
        preserves := by
          intro env frame hFrameFVar hFrameFunction hFrame
          exact recursiveSound.extension.preserves env frame (Nat.le_trans hFrameFVar (Nat.le_succ _))
            hFrameFunction hFrame
      }
      resultSat := by
        intro env hFree hBound hSat
        let value := env.freeVal sort state.nextFVar
        have hSort : M.sortInterp sort value :=
          hFree sort state.nextFVar
        have hOpened :=
          Freshness.openForall_satisfies env sort body state.nextFVar
            value hSort hFVar hSat
        have hEnvEq :
            env.setFree sort state.nextFVar value = env := by
          exact Env.setFree_self env sort state.nextFVar
        rw [hEnvEq] at hOpened
        exact recursiveSound.resultSat env hFree hBound hOpened
    }⟩
  case case7 =>
    intro path context sort body ih state result output
      hContext hSupported hFVar hFunction hRun M base
    let universalContext := context.orderedUniversals
    let universalArgs := context.skolemArgs
    let symbol : FunctionSymbol := {
      id := state.nextSkolem
      arity := universalArgs.length
      role := FunctionRole.skolem
      inputSorts := context.skolemInputSorts
      outputSort := sort
    }
    let intro : LocalSkolem.SkolemIntro := {
      index := state.skolemTrace.size
      witnessSort := sort
      symbol := symbol
      universalContext := universalContext
      universalArgs := universalArgs
      term := Term.app symbol universalArgs
      contextDepth := universalContext.size
    }
    let nextState : LocalSkolem.BuildState := {
      state with
      nextSkolem := state.nextSkolem + 1
      steps := state.steps.push {
        path := path
        kind := LocalSkolem.StepKind.skolemizeExists
        binderSort := sort
        body := body
        replacement := intro.term
        instantiatedBody := LocalSkolem.instantiateNnf intro.term body
        universalContext := universalContext
        skolem? := some intro
      }
      skolemTrace := state.skolemTrace.push intro
    }
    rw [LocalSkolem.skolemizeAt.eq_7] at hRun
    change (LocalSkolem.skolemizeAt path context (LocalSkolem.instantiateNnf intro.term body)).run nextState = (result, output) at hRun
    have hIntroFVar :
        LocalSkolem.termMaxFVarSucc intro.term ≤ nextState.nextFVar :=
      hContext.args
    have hIntroFunction :
        LocalSkolem.termMaxFunctionIdSucc intro.term ≤ nextState.nextSkolem := by
      change Nat.max (state.nextSkolem + 1) (LocalSkolem.termListMaxFunctionIdSucc context.skolemArgs) ≤
        state.nextSkolem + 1
      apply Nat.max_le.mpr
      exact ⟨Nat.le_refl _, Nat.le_trans (LocalSkolem.Context.argsFunctionBounded context state.nextFVar hContext) (Nat.zero_le _)⟩
    have hInstFVar :=
      LocalSkolem.nnfMaxFVarSucc_instantiateNnf_of_le
        body intro.term nextState.nextFVar hFVar hIntroFVar
    have hInstFunction :=
      LocalSkolem.nnfMaxFunctionIdSucc_instantiateNnf_of_le
        body intro.term nextState.nextSkolem (Nat.le_trans hFunction (Nat.le_succ _)) hIntroFunction
    have hBodySupported : context.Supports body :=
      hSupported
    have hSupported' :
        context.Supports (LocalSkolem.instantiateNnf intro.term body) := by
      simpa [intro, universalArgs] using
        LocalSkolem.Context.Supports.skolemizeExists
          hContext hBodySupported symbol
    let interpretation :=
      LocalSkolemChoice.chooseWitness
        base universalContext.toList sort body
    let overridden := M.overrideFunction symbol interpretation
    let overriddenBase :=
      Env.rebaseOverrideFunction base symbol interpretation
    rcases ih intro nextState result output hContext hSupported'
      hInstFVar hInstFunction hRun overridden overriddenBase with
      ⟨recursiveSound⟩
    exact ⟨{
      extension := {
        target := recursiveSound.extension.target
        rebase := fun env =>
          recursiveSound.extension.rebase (Env.rebaseOverrideFunction env symbol interpretation)
        unbase := fun env =>
          Env.unbaseOverrideFunction (recursiveSound.extension.unbase env)
        rebase_unbase := by
          intro env
          rw [Env.rebaseOverrideFunction_unbaseOverrideFunction, recursiveSound.extension.rebase_unbase]
        unbase_rebase := by
          intro env
          rw [recursiveSound.extension.unbase_rebase, Env.unbaseOverrideFunction_rebaseOverrideFunction]
        unbaseRespectsFree := by
          intro env hFree
          exact Env.respectsFree_unbaseOverrideFunction <|
            recursiveSound.extension.unbaseRespectsFree env hFree
        unbaseSameBound := by
          intro left right hBound
          exact LocalSkolemChoice.sameBoundStack_unbaseOverrideFunction <|
            recursiveSound.extension.unbaseSameBound hBound
        functionSort := fun hFunction =>
          recursiveSound.extension.functionSort <|
            Model.overrideFunction_functionSort symbol interpretation hFunction
              (fun arguments => LocalSkolemChoice.chooseWitness_sort base universalContext.toList sort body arguments)
        foolContract := fun contract =>
          recursiveSound.extension.foolContract <|
            contract.overrideFunction symbol interpretation
              (fun arguments => LocalSkolemChoice.chooseWitness_sort base universalContext.toList sort body arguments)
        contract := fun contract =>
          recursiveSound.extension.contract <|
            contract.overrideFunction symbol interpretation
              (fun arguments => LocalSkolemChoice.chooseWitness_sort base universalContext.toList sort body arguments)
        respectsFree := by
          intro env hFree
          exact recursiveSound.extension.respectsFree _ (LocalSkolemChoice.respectsFree_rebaseOverrideFunction hFree symbol interpretation)
        sameBound := by
          intro left right hBound
          exact recursiveSound.extension.sameBound (LocalSkolemChoice.sameBoundStack_rebaseOverrideFunction hBound symbol interpretation)
        preserves := by
          intro env frame hFrameFVar hFrameFunction hFrame
          apply recursiveSound.extension.preserves (Env.rebaseOverrideFunction env symbol interpretation)
            frame hFrameFVar (Nat.le_trans hFrameFunction (Nat.le_succ _))
          exact (Freshness.Nnf.satisfies_overrideFunctionWith_of_max_le env symbol interpretation frame hFrameFunction).mpr hFrame
      }
      resultSat := by
        intro env hFree hBound hSat
        have hWellFormed :
            ∀ universal ∈ universalContext.toList,
              universal.term =
                Term.fvar universal.sort universal.varId := by
          intro universal hUniversal
          apply hContext.wellFormed universal
          simpa [universalContext, LocalSkolem.Context.orderedUniversals] using
            hUniversal
        have hBodySupport :
            ∀ parameter,
              parameter ∈ DefinitionalCnf.nnfFreeVarParams body →
                parameter ∈
                  LocalSkolemChoice.parameters universalContext.toList := by
          intro parameter hParameter
          exact Semantics.FreeSupport.nnf_freeVarParams_mem
            context.parameters body hBodySupported parameter hParameter
        have hArgsFresh :
            LocalSkolem.termListMaxFunctionIdSucc (universalContext.toList.map fun universal => universal.term) ≤
              symbol.id := by
          change
            LocalSkolem.termListMaxFunctionIdSucc context.skolemArgs ≤
              state.nextSkolem
          exact Nat.le_trans (LocalSkolem.Context.argsFunctionBounded context state.nextFVar hContext) (Nat.zero_le _)
        have hStep :=
          Freshness.skolemizeExists_satisfiesWithChoice
            base env sort body symbol universalContext.toList
            hWellFormed hBodySupport hBound hFunction hArgsFresh hSat
        exact recursiveSound.resultSat (Env.rebaseOverrideFunction env symbol interpretation)
          (LocalSkolemChoice.respectsFree_rebaseOverrideFunction hFree symbol interpretation)
          (LocalSkolemChoice.sameBoundStack_rebaseOverrideFunction hBound symbol interpretation)
          hStep
    }⟩
end LocalSkolemSoundness
theorem LocalSkolem.buildCore_uniformSoundExtension {source : Nnf} (M : Model) (base : Env M) (hSupported : FreeSupport.NnfSupportedBy [] source) : Nonempty (LocalSkolemSoundness.UniformSoundExtension (LocalSkolem.initialState source) source (LocalSkolem.buildCore source).result M base) := by
  cases hRun : (LocalSkolem.skolemizeAt [] {} source).run (LocalSkolem.initialState source) with
  | mk result output =>
      have hContextSupported : ({} : LocalSkolem.Context).Supports source := by
        simpa [LocalSkolem.Context.Supports, LocalSkolem.Context.parameters, LocalSkolem.Context.orderedUniversals, LocalSkolemChoice.parameters] using hSupported
      have hSound :=
        LocalSkolemSoundness.skolemizeAt_uniformSound
          [] {} source (LocalSkolem.initialState source) result output (LocalSkolem.Context.bounded_empty_at (LocalSkolem.initialState source).nextFVar)
          hContextSupported (by simp [LocalSkolem.initialState]) (by simp [LocalSkolem.initialState])
          hRun M base
      simpa [LocalSkolem.buildCore, hRun] using hSound
namespace LocalSkolemSoundness.UniformSoundExtension
theorem resultSat_of_source {state : LocalSkolem.BuildState} {source result : Nnf} {M : Model} {base : Env M} (sound : LocalSkolemSoundness.UniformSoundExtension state source result M base) (hSupported : FreeSupport.NnfSupportedBy [] source) (hSource : Nnf.Satisfies base source) (env : Env M) (hFree : Env.RespectsFree env) (hBound : LocalSkolemChoice.SameBoundStack env base) : Nnf.Satisfies (sound.extension.rebase env) result := by
  have hAgreement :
      Env.FreeAgreement (DefinitionalCnf.nnfFreeVarParams source) base env := by
    intro parameter hParameter
    have hImpossible :
        parameter ∈ ([] : List DefinitionalCnf.FreeVarParam) :=
      FreeSupport.nnf_freeVarParams_mem
        [] source hSupported parameter hParameter
    simp at hImpossible
  have hSourceEnv : Nnf.Satisfies env source := by exact (Nnf.satisfies_iff_of_freeAgreement base env (fun index => (hBound index).symm) source hAgreement).mp hSource
  exact sound.resultSat env hFree hBound hSourceEnv
end LocalSkolemSoundness.UniformSoundExtension
end Semantics
namespace LocalSkolemPayload
theorem result_eq_of_eq_true {left right : LocalSkolemPayload} (h : LocalSkolemPayload.eq left right = true) : left.result = right.result := by
  unfold LocalSkolemPayload.eq at h
  simp only [Bool.and_eq_true_iff] at h
  have h1 := h.1
  have h2 := h1.1
  have h3 := h2.1
  have h4 := h3.1
  have h5 := h4.1
  have h6 := h5.1
  have h7 := h6.1
  have h8 := h7.1
  have h9 := h8.1
  have h10 := h9.1
  have hResult := h10.2
  exact SyntaxEq.nnfEq_eq_true.mp hResult
theorem uniformSoundExtension_of_check {payload : LocalSkolemPayload} (hCheck : LocalSkolemPayload.check payload = true) (hSupported : Semantics.FreeSupport.NnfSupportedBy [] payload.source) (M : Semantics.Model) (base : Semantics.Env M) : Nonempty (Semantics.LocalSkolemSoundness.UniformSoundExtension (LocalSkolem.initialState payload.source) payload.source payload.result M base) := by
  have hShared := sharedStateSound_of_check hCheck
  have hResult :
      payload.result = (LocalSkolemPayload.build payload.config payload.source).result :=
    result_eq_of_eq_true hShared.rebuilt
  rw [hResult]
  exact Semantics.LocalSkolem.buildCore_uniformSoundExtension
    M base hSupported
end LocalSkolemPayload
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
