import YesMetaZFC.Automation.CoreNormalForm.DefinitionalCnf
import YesMetaZFC.Automation.CoreNormalForm.LocalSkolemSoundness
import YesMetaZFC.Automation.CoreNormalForm.ScopedEnvironmentSoundness

/-!
# Definitional CNF soundness

本模块证明定义性 CNF 对开放 NNF 矩阵的语义保守性。定义谓词的参数显式携带局部
上下文和 typed 自由变量；这里先建立参数环境重建与定义模型扩展，后续定理只消费
这些接口，不把开放变量错误地当作零元命题。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm
namespace Semantics

universe x

namespace Definition

/-- 从定义谓词实参中取出局部绑定变量值；越过局部上下文后保留基础环境。 -/
def boundValueFromArgsAux {M : Model} (base : Env M) :
    List CoreSort → List M.Carrier → Nat → Nat → M.Carrier
  | [], _, fallback, _ => base.boundVal fallback
  | _ :: _, [], fallback, _ => base.boundVal fallback
  | _ :: _, value :: _, _, 0 => value
  | _ :: rest, _ :: values, fallback, offset + 1 =>
      boundValueFromArgsAux base rest values fallback offset

/-- 从定义谓词实参中取出局部绑定变量值；越过局部上下文后保留基础环境。 -/
def boundValueFromArgs {M : Model} (base : Env M) :
    List CoreSort → List M.Carrier → Nat → M.Carrier :=
  fun contextSorts args index =>
    boundValueFromArgsAux base contextSorts args index index

/-- 从定义谓词实参中按参数身份取出自由变量值。 -/
def freeValueFromArgs {M : Model} (base : Env M) :
    List DefinitionalCnf.FreeVarParam → List M.Carrier →
      CoreSort → VarId → M.Carrier
  | [], _, sort, id => base.freeVal sort id
  | _ :: _, [], sort, id => base.freeVal sort id
  | parameter :: parameters, value :: values, sort, id =>
      if parameter.sort = sort ∧ parameter.varId = id then
        value
      else
        freeValueFromArgs base parameters values sort id

/-- 用定义谓词实参重建一个开放矩阵的环境。 -/
def envForArgs {M : Model} (base : Env M)
    (definition : DefinitionalCnf.Definition) (args : List M.Carrier) : Env M where
  boundVal := boundValueFromArgs base definition.contextSorts args
  freeVal := freeValueFromArgs base definition.freeVarParams
    (args.drop definition.contextSorts.length)

end Definition

namespace Model

/-- 在模型中批量解释定义谓词，其余谓词解释保持不变。 -/
def lookupDefinition? :
    List DefinitionalCnf.Definition → PredicateSymbol →
      Option DefinitionalCnf.Definition
  | [], _ => none
  | definition :: definitions, target =>
      if definition.predicate = target then
        some definition
      else
        lookupDefinition? definitions target

/-- 将定义表解释为由基础模型中的开放矩阵决定的谓词。 -/
def overrideDefinitions (M : Model) (base : Env M)
    (definitions : Array DefinitionalCnf.Definition) : Model where
  Carrier := M.Carrier
  default := M.default
  sortInterp := M.sortInterp
  sortNonempty := M.sortNonempty
  functionInterp := M.functionInterp
  predicateInterp := fun target args =>
    match lookupDefinition? definitions.toList target with
    | some definition =>
        Nnf.Satisfies (Definition.envForArgs base definition args) definition.body
    | none => M.predicateInterp target args
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

end Model

namespace FoolLambdaContract

/-- 定义谓词覆盖不改变 FOOL/lambda 运算及其语义合同。 -/
def overrideDefinitions {M : Model} (contract : FoolLambdaContract M)
    (base : Env M) (definitions : Array DefinitionalCnf.Definition) :
    FoolLambdaContract (Model.overrideDefinitions M base definitions) :=
  { contract with }

end FoolLambdaContract

namespace Env

/--
把任意环境搬到固定定义模型中。定义谓词的 fallback 环境由 `modelBase` 固定，
当前 bound/free 赋值则逐点来自 `env`。
-/
def rebaseOverrideDefinitions {M : Model} (modelBase : Env M)
    (definitions : Array DefinitionalCnf.Definition) (env : Env M) :
    Env (Model.overrideDefinitions M modelBase definitions) where
  boundVal := env.boundVal
  freeVal := env.freeVal

/-- 从定义谓词覆盖模型环境机械回拉到原模型环境。 -/
def unbaseOverrideDefinitions {M : Model} {modelBase : Env M}
    {definitions : Array DefinitionalCnf.Definition}
    (env : Env (Model.overrideDefinitions M modelBase definitions)) : Env M where
  boundVal := env.boundVal
  freeVal := env.freeVal

@[simp]
theorem rebaseOverrideDefinitions_unbaseOverrideDefinitions {M : Model}
    (modelBase : Env M) (definitions : Array DefinitionalCnf.Definition)
    (env : Env (Model.overrideDefinitions M modelBase definitions)) :
    rebaseOverrideDefinitions modelBase definitions
      (unbaseOverrideDefinitions env) = env := by
  cases env
  rfl

@[simp]
theorem unbaseOverrideDefinitions_rebaseOverrideDefinitions {M : Model}
    (modelBase : Env M) (definitions : Array DefinitionalCnf.Definition)
    (env : Env M) :
    unbaseOverrideDefinitions
      (rebaseOverrideDefinitions modelBase definitions env) = env := by
  cases env
  rfl

@[simp]
theorem rebaseOverrideDefinitions_boundVal {M : Model} (modelBase : Env M)
    (definitions : Array DefinitionalCnf.Definition) (env : Env M) (index : Nat) :
    (rebaseOverrideDefinitions modelBase definitions env).boundVal index =
      env.boundVal index :=
  rfl

@[simp]
theorem rebaseOverrideDefinitions_freeVal {M : Model} (modelBase : Env M)
    (definitions : Array DefinitionalCnf.Definition) (env : Env M)
    (sort : CoreSort) (id : VarId) :
    (rebaseOverrideDefinitions modelBase definitions env).freeVal sort id =
      env.freeVal sort id :=
  rfl

/-- 定义模型搬运保持自由变量的 sort 不变量。 -/
theorem respectsFree_rebaseOverrideDefinitions {M : Model}
    (modelBase : Env M) (definitions : Array DefinitionalCnf.Definition)
    {env : Env M} (hFree : RespectsFree env) :
    RespectsFree (rebaseOverrideDefinitions modelBase definitions env) :=
  fun sort id => hFree sort id

/-- 定义谓词覆盖模型的环境回拉保持自由变量 sort。 -/
theorem respectsFree_unbaseOverrideDefinitions {M : Model}
    {modelBase : Env M} {definitions : Array DefinitionalCnf.Definition}
    {env : Env (Model.overrideDefinitions M modelBase definitions)}
    (hFree : RespectsFree env) :
    RespectsFree (unbaseOverrideDefinitions env) :=
  fun sort id => hFree sort id

/-- 定义模型搬运保持 locally-nameless bound stack 的逐点相等关系。 -/
theorem sameBoundStack_rebaseOverrideDefinitions {M : Model}
    (modelBase : Env M) (definitions : Array DefinitionalCnf.Definition)
    {left right : Env M}
    (hBound : LocalSkolemChoice.SameBoundStack left right) :
    LocalSkolemChoice.SameBoundStack
      (rebaseOverrideDefinitions modelBase definitions left)
      (rebaseOverrideDefinitions modelBase definitions right) :=
  fun index => hBound index

/-- 定义谓词覆盖模型的环境回拉保持 bound-stack 关系。 -/
theorem sameBoundStack_unbaseOverrideDefinitions {M : Model}
    {modelBase : Env M} {definitions : Array DefinitionalCnf.Definition}
    {left right : Env (Model.overrideDefinitions M modelBase definitions)}
    (hBound : LocalSkolemChoice.SameBoundStack left right) :
    LocalSkolemChoice.SameBoundStack
      (unbaseOverrideDefinitions left)
      (unbaseOverrideDefinitions right) :=
  fun index => hBound index

end Env

namespace Model

/-- 定义表中的定义谓词若都在编号窗口之后，则不会拦截窗口内的原始谓词。 -/
theorem lookupDefinition?_none_of_id_lt
    (definitions : List DefinitionalCnf.Definition) (target : PredicateSymbol)
    (cutoff : Nat) (hId : target.id < cutoff)
    (hFresh : ∀ definition ∈ definitions, cutoff ≤ definition.predicate.id) :
    lookupDefinition? definitions target = none := by
  induction definitions with
  | nil =>
      rfl
  | cons definition definitions ih =>
      have hDefinition : cutoff ≤ definition.predicate.id :=
        hFresh definition (by simp)
      have hRest :
          ∀ candidate ∈ definitions, cutoff ≤ candidate.predicate.id := by
        intro candidate hCandidate
        exact hFresh candidate (by simp [hCandidate])
      have hNe : definition.predicate ≠ target := by
        intro hEq
        have hIdEq : definition.predicate.id = target.id :=
          congrArg PredicateSymbol.id hEq
        have hTarget : definition.predicate.id < cutoff := by
          simpa [hIdEq] using hId
        exact (Nat.not_lt_of_ge hDefinition) hTarget
      simp [lookupDefinition?, hNe, ih hRest]

/-- 谓词互异的定义表会按谓词精确命中其中的定义。 -/
theorem lookupDefinition?_eq_some_of_mem
    (definitions : List DefinitionalCnf.Definition)
    (target : DefinitionalCnf.Definition)
    (hMem : target ∈ definitions)
    (hUnique :
      definitions.Pairwise
        (fun left right => left.predicate ≠ right.predicate)) :
    lookupDefinition? definitions target.predicate = some target := by
  induction definitions with
  | nil =>
      simp at hMem
  | cons definition definitions ih =>
      rw [List.pairwise_cons] at hUnique
      rcases hUnique with ⟨hHead, hTail⟩
      by_cases hEq : definition = target
      · subst definition
        simp [lookupDefinition?]
      · have hTargetMem : target ∈ definitions := by
          simpa [hEq, Ne.symm hEq] using hMem
        have hPredicateNe : definition.predicate ≠ target.predicate :=
          hHead target hTargetMem
        simp [lookupDefinition?, hPredicateNe, ih hTargetMem hTail]

/-- 定义模型在原始谓词编号窗口内保持基础模型的解释。 -/
theorem overrideDefinitions_predicateInterp_of_id_lt
    (M : Model) (base : Env M) (definitions : Array DefinitionalCnf.Definition)
    (target : PredicateSymbol) (args : List M.Carrier) (cutoff : Nat)
    (hId : target.id < cutoff)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.predicate.id) :
    (overrideDefinitions M base definitions).predicateInterp target args =
      M.predicateInterp target args := by
  simp only [overrideDefinitions, lookupDefinition?_none_of_id_lt
    definitions.toList target cutoff hId hFresh]

end Model

mutual

theorem Term.eval_override_of_predicate_lt
    {M : Model} (base : Env M) (definitions : Array DefinitionalCnf.Definition)
    (cutoff : Nat) (env : Env M)
    (extendedEnv : Env (Model.overrideDefinitions M base definitions))
    (hBound : ∀ index, extendedEnv.boundVal index = env.boundVal index)
    (hFree : ∀ sort id, extendedEnv.freeVal sort id = env.freeVal sort id)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.predicate.id)
    (term : Term) (hMax : DefinitionalCnf.Term.maxPredicateIdSucc term ≤ cutoff) :
    Term.eval extendedEnv term = Term.eval env term := by
  cases term with
  | bvar sort index =>
      simpa [Term.eval, Model.overrideDefinitions] using hBound index
  | fvar sort id =>
      simpa [Term.eval, Model.overrideDefinitions] using hFree sort id
  | app symbol args =>
      simp only [DefinitionalCnf.Term.maxPredicateIdSucc, Term.eval,
        Model.overrideDefinitions] at hMax ⊢
      congr 1
      exact Term.evalList_override_of_predicate_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh args hMax
  | apply fn arg =>
      simp only [DefinitionalCnf.Term.maxPredicateIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Term.eval, Model.overrideDefinitions]
      congr 1
      · exact Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh fn hMax'.1
      · exact Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh arg hMax'.2
  | bool value =>
      simp [Term.eval, Model.overrideDefinitions]
  | notE body =>
      simp only [DefinitionalCnf.Term.maxPredicateIdSucc] at hMax
      simp only [Term.eval, Model.overrideDefinitions]
      congr 1
      exact Term.eval_override_of_predicate_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh body hMax
  | andE left right
  | orE left right
  | impE left right
  | iffE left right =>
      simp only [DefinitionalCnf.Term.maxPredicateIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Term.eval, Model.overrideDefinitions]
      congr 1
      · exact Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1
      · exact Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2
  | quote formula =>
      simp only [DefinitionalCnf.Term.maxPredicateIdSucc] at hMax
      simp only [Term.eval, Model.overrideDefinitions]
      congr 1
      apply propext
      exact Formula.satisfies_override_of_predicate_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh formula hMax
  | lam domain codomain body =>
      simp only [DefinitionalCnf.Term.maxPredicateIdSucc] at hMax
      simp only [Term.eval, Model.overrideDefinitions]
      congr 1
      funext value
      apply Term.eval_override_of_predicate_lt
        base definitions cutoff (env.push value) (extendedEnv.push value)
      · intro index
        cases index <;> simp [Env.push, hBound]
      · intro sort id
        simp [Env.push, hFree]
      · exact hFresh
      · exact hMax
  | ite sort condition thenTerm elseTerm =>
      simp only [DefinitionalCnf.Term.maxPredicateIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      have hMax'' := Nat.max_le.mp hMax'.2
      simp only [Term.eval, Model.overrideDefinitions]
      congr 1
      · apply propext
        exact Formula.satisfies_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh condition hMax'.1
      · exact Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh thenTerm hMax''.1
      · exact Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh elseTerm hMax''.2

theorem Formula.satisfies_override_of_predicate_lt
    {M : Model} (base : Env M) (definitions : Array DefinitionalCnf.Definition)
    (cutoff : Nat) (env : Env M)
    (extendedEnv : Env (Model.overrideDefinitions M base definitions))
    (hBound : ∀ index, extendedEnv.boundVal index = env.boundVal index)
    (hFree : ∀ sort id, extendedEnv.freeVal sort id = env.freeVal sort id)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.predicate.id)
    (formula : Formula)
    (hMax : DefinitionalCnf.Formula.maxPredicateIdSucc formula ≤ cutoff) :
    Formula.Satisfies extendedEnv formula ↔ Formula.Satisfies env formula := by
  cases formula with
  | trueE
  | falseE =>
      simp [Formula.Satisfies, Formula.eval]
  | atom predicate args =>
      simp only [DefinitionalCnf.Formula.maxPredicateIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      have hPred : predicate.id < cutoff := Nat.lt_of_succ_le hMax'.1
      have hArgs := Term.evalList_override_of_predicate_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh args hMax'.2
      simp only [Formula.Satisfies, Formula.eval]
      rw [hArgs]
      rw [Model.overrideDefinitions_predicateInterp_of_id_lt
        M base definitions predicate (args.map (Term.eval env)) cutoff hPred hFresh]
  | equal sort left right =>
      simp only [DefinitionalCnf.Formula.maxPredicateIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Formula.Satisfies, Formula.eval]
      rw [Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1,
        Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2]
      rfl
  | boolTerm term =>
      simp only [DefinitionalCnf.Formula.maxPredicateIdSucc] at hMax
      simp only [Formula.Satisfies, Formula.eval]
      rw [Term.eval_override_of_predicate_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh term hMax]
      simp [Model.overrideDefinitions]
  | neg body =>
      simp only [DefinitionalCnf.Formula.maxPredicateIdSucc] at hMax
      simp only [Formula.Satisfies, Formula.eval]
      simpa only [Formula.Satisfies] using
        not_congr (Formula.satisfies_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh body hMax)
  | imp left right
  | conj left right
  | disj left right
  | iffE left right =>
      simp only [DefinitionalCnf.Formula.maxPredicateIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Formula.Satisfies, Formula.eval]
      first
      | exact and_congr
          (Formula.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Formula.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
      | exact or_congr
          (Formula.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Formula.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
      | exact imp_congr
          (Formula.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Formula.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
      | exact iff_congr
          (Formula.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Formula.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
  | forallE sort body =>
      simp only [DefinitionalCnf.Formula.maxPredicateIdSucc] at hMax
      simp only [Formula.Satisfies, Formula.eval]
      constructor <;> intro h value hSort
      · exact (Formula.satisfies_override_of_predicate_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mp (h value hSort)
      · exact (Formula.satisfies_override_of_predicate_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mpr (h value hSort)
  | existsE sort body =>
      simp only [DefinitionalCnf.Formula.maxPredicateIdSucc] at hMax
      simp only [Formula.Satisfies, Formula.eval]
      constructor
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Formula.satisfies_override_of_predicate_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mp hBody
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Formula.satisfies_override_of_predicate_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mpr hBody

theorem Term.evalList_override_of_predicate_lt
    {M : Model} (base : Env M) (definitions : Array DefinitionalCnf.Definition)
    (cutoff : Nat) (env : Env M)
    (extendedEnv : Env (Model.overrideDefinitions M base definitions))
    (hBound : ∀ index, extendedEnv.boundVal index = env.boundVal index)
    (hFree : ∀ sort id, extendedEnv.freeVal sort id = env.freeVal sort id)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.predicate.id)
    (terms : List Term)
    (hMax : DefinitionalCnf.Term.maxPredicateListIdSucc terms ≤ cutoff) :
    terms.map (Term.eval extendedEnv) = terms.map (Term.eval env) := by
  cases terms with
  | nil =>
      rfl
  | cons head tail =>
      simp only [DefinitionalCnf.Term.maxPredicateListIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [List.map_cons]
      congr 1
      · exact Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh head hMax'.1
      · exact Term.evalList_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh tail hMax'.2

end

namespace Atom

theorem satisfies_override_of_predicate_lt
    {M : Model} (base : Env M) (definitions : Array DefinitionalCnf.Definition)
    (cutoff : Nat) (env : Env M)
    (extendedEnv : Env (Model.overrideDefinitions M base definitions))
    (hBound : ∀ index, extendedEnv.boundVal index = env.boundVal index)
    (hFree : ∀ sort id, extendedEnv.freeVal sort id = env.freeVal sort id)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.predicate.id)
    (atom : Atom) (hMax : DefinitionalCnf.atomMaxPredicateIdSucc atom ≤ cutoff) :
    Atom.Satisfies extendedEnv atom ↔ Atom.Satisfies env atom := by
  cases atom with
  | predicate predicate args =>
      simp only [DefinitionalCnf.atomMaxPredicateIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      have hPred : predicate.id < cutoff := Nat.lt_of_succ_le hMax'.1
      have hArgs := Term.evalList_override_of_predicate_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh args hMax'.2
      simp only [Atom.Satisfies]
      rw [hArgs]
      rw [Model.overrideDefinitions_predicateInterp_of_id_lt
        M base definitions predicate (args.map (Term.eval env)) cutoff hPred hFresh]
  | equal sort left right =>
      simp only [DefinitionalCnf.atomMaxPredicateIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Atom.Satisfies]
      rw [Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1,
        Term.eval_override_of_predicate_lt
          base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2]
      rfl
  | boolTerm term =>
      simp only [DefinitionalCnf.atomMaxPredicateIdSucc] at hMax
      simp only [Atom.Satisfies]
      rw [Term.eval_override_of_predicate_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh term hMax]
      simp [Model.overrideDefinitions]

end Atom

namespace Literal

theorem satisfies_override_of_predicate_lt
    {M : Model} (base : Env M) (definitions : Array DefinitionalCnf.Definition)
    (cutoff : Nat) (env : Env M)
    (extendedEnv : Env (Model.overrideDefinitions M base definitions))
    (hBound : ∀ index, extendedEnv.boundVal index = env.boundVal index)
    (hFree : ∀ sort id, extendedEnv.freeVal sort id = env.freeVal sort id)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.predicate.id)
    (literal : Literal)
    (hMax : DefinitionalCnf.literalMaxPredicateIdSucc literal ≤ cutoff) :
    Literal.Satisfies extendedEnv literal ↔ Literal.Satisfies env literal := by
  cases literal with
  | mk positive atom =>
      simp only [DefinitionalCnf.literalMaxPredicateIdSucc,
        DefinitionalCnf.atomMaxPredicateIdSucc] at hMax
      cases positive with
      | false =>
          simpa [Literal.Satisfies] using
            not_congr (Atom.satisfies_override_of_predicate_lt
              base definitions cutoff env extendedEnv hBound hFree hFresh atom hMax)
      | true =>
          simpa [Literal.Satisfies] using
            Atom.satisfies_override_of_predicate_lt
              base definitions cutoff env extendedEnv hBound hFree hFresh atom hMax

end Literal

namespace Nnf

theorem satisfies_override_of_predicate_lt
    {M : Model} (base : Env M) (definitions : Array DefinitionalCnf.Definition)
    (cutoff : Nat) (env : Env M)
    (extendedEnv : Env (Model.overrideDefinitions M base definitions))
    (hBound : ∀ index, extendedEnv.boundVal index = env.boundVal index)
    (hFree : ∀ sort id, extendedEnv.freeVal sort id = env.freeVal sort id)
    (hFresh :
      ∀ definition ∈ definitions.toList, cutoff ≤ definition.predicate.id)
    (nnf : Nnf)
    (hMax : DefinitionalCnf.nnfMaxPredicateIdSucc nnf ≤ cutoff) :
    Nnf.Satisfies extendedEnv nnf ↔ Nnf.Satisfies env nnf := by
  cases nnf with
  | trueE
  | falseE =>
      simp [Nnf.Satisfies]
  | lit literal =>
      simp only [DefinitionalCnf.nnfMaxPredicateIdSucc] at hMax
      exact Literal.satisfies_override_of_predicate_lt
        base definitions cutoff env extendedEnv hBound hFree hFresh literal hMax
  | conj left right
  | disj left right =>
      simp only [DefinitionalCnf.nnfMaxPredicateIdSucc] at hMax
      have hMax' := Nat.max_le.mp hMax
      simp only [Nnf.Satisfies]
      first
      | exact and_congr
          (Nnf.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Nnf.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
      | exact or_congr
          (Nnf.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh left hMax'.1)
          (Nnf.satisfies_override_of_predicate_lt
            base definitions cutoff env extendedEnv hBound hFree hFresh right hMax'.2)
  | forallE sort body =>
      simp only [DefinitionalCnf.nnfMaxPredicateIdSucc] at hMax
      simp only [Nnf.Satisfies]
      constructor <;> intro h value hSort
      · exact (Nnf.satisfies_override_of_predicate_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mp (h value hSort)
      · exact (Nnf.satisfies_override_of_predicate_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mpr (h value hSort)
  | existsE sort body =>
      simp only [DefinitionalCnf.nnfMaxPredicateIdSucc] at hMax
      simp only [Nnf.Satisfies]
      constructor
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Nnf.satisfies_override_of_predicate_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mp hBody
      · rintro ⟨value, hSort, hBody⟩
        refine ⟨value, hSort, ?_⟩
        exact (Nnf.satisfies_override_of_predicate_lt
          base definitions cutoff (env.push value) (extendedEnv.push value)
          (by
            intro index
            cases index <;> simp [Env.push, hBound])
          (by
            intro target id
            simp [Env.push, hFree])
          hFresh body hMax).mpr hBody

end Nnf

namespace Definition

/-- 用基础环境的绑定栈计算上下文参数。 -/
def contextValues {M : Model} (env : Env M) :
    Nat → List CoreSort → List M.Carrier
  | _, [] => []
  | index, _ :: sorts =>
      env.boundVal index :: contextValues env (index + 1) sorts

/-- 定义谓词实参在基础环境中的取值。 -/
def evaluatedArguments {M : Model} (env : Env M)
    (definition : DefinitionalCnf.Definition) : List M.Carrier :=
  contextValues env 0 definition.contextSorts ++
    definition.freeVarParams.map (fun parameter =>
      env.freeVal parameter.sort parameter.varId)

theorem boundValueFromArgs_contextValues_append {M : Model} (base : Env M)
    (start : Nat) (contextSorts : List CoreSort) (values : List M.Carrier)
    (fallback offset : Nat) :
    boundValueFromArgsAux base contextSorts
        (contextValues base start contextSorts ++ values) fallback offset =
      if offset < contextSorts.length then
        base.boundVal (start + offset)
      else
        base.boundVal fallback := by
  induction contextSorts generalizing start fallback offset with
  | nil =>
      simp [boundValueFromArgsAux]
  | cons sort contextSorts ih =>
      cases offset with
      | zero =>
          rfl
      | succ offset =>
          simp only [contextValues, List.length_cons]
          simpa [Nat.succ_lt_succ_iff, Nat.succ_add] using
            ih (start + 1) fallback offset

theorem boundValueFromArgs_contextValues {M : Model} (base : Env M)
    (contextSorts : List CoreSort) (index : Nat) :
    boundValueFromArgs base contextSorts
        (contextValues base 0 contextSorts) index =
      base.boundVal index := by
  simpa [boundValueFromArgs] using
    boundValueFromArgs_contextValues_append base 0 contextSorts [] index index

theorem freeValueFromArgs_params {M : Model} (base : Env M)
    (parameters : List DefinitionalCnf.FreeVarParam) (sort : CoreSort) (id : VarId) :
    freeValueFromArgs base parameters
        (parameters.map (fun parameter =>
          base.freeVal parameter.sort parameter.varId)) sort id =
      base.freeVal sort id := by
  induction parameters with
  | nil =>
      rfl
  | cons parameter parameters ih =>
      by_cases hSort : parameter.sort = sort
      · by_cases hId : parameter.varId = id
        · simp [freeValueFromArgs, hSort, hId]
        · simp [freeValueFromArgs, hSort, hId, ih]
      · simp [freeValueFromArgs, hSort, ih]

theorem drop_contextValues_append {M : Model} (base : Env M)
    (start : Nat) (contextSorts : List CoreSort)
    (values : List M.Carrier) :
    (contextValues base start contextSorts ++ values).drop contextSorts.length = values := by
  induction contextSorts generalizing start values with
  | nil =>
      rfl
  | cons sort contextSorts ih =>
      simp [contextValues, ih]

/-- 当前上下文内的 bound 参数由实参环境恢复，不依赖固定 fallback 环境。 -/
theorem boundValueFromArgsAux_contextValues_append_of_lookup
    {M : Model} (base env : Env M)
    (start : Nat) (contextSorts : List CoreSort) (values : List M.Carrier)
    (fallback offset : Nat) (sort : CoreSort)
    (hLookup : TypeCheck.lookupBound? contextSorts offset = some sort) :
    boundValueFromArgsAux base contextSorts
        (contextValues env start contextSorts ++ values) fallback offset =
      env.boundVal (start + offset) := by
  induction contextSorts generalizing start offset with
  | nil =>
      simp [TypeCheck.lookupBound?] at hLookup
  | cons head contextSorts ih =>
      cases offset with
      | zero =>
          simp [contextValues, boundValueFromArgsAux]
      | succ previous =>
          simp only [TypeCheck.lookupBound?] at hLookup
          simp only [contextValues, List.cons_append, boundValueFromArgsAux]
          have hResult := ih (start + 1) previous hLookup
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hResult

/-- 当前上下文内的 bound 参数由实参环境恢复，不依赖固定 fallback 环境。 -/
theorem boundValueFromArgs_contextValues_append_of_lookup
    {M : Model} (base env : Env M)
    (contextSorts : List CoreSort) (values : List M.Carrier)
    (index : Nat) (sort : CoreSort)
    (hLookup : TypeCheck.lookupBound? contextSorts index = some sort) :
    boundValueFromArgs base contextSorts
        (contextValues env 0 contextSorts ++ values) index =
      env.boundVal index := by
  simpa [boundValueFromArgs] using
    boundValueFromArgsAux_contextValues_append_of_lookup
      base env 0 contextSorts values index index sort hLookup

/-- 参数表中出现的 typed 自由变量总会从实参环境恢复。 -/
theorem freeValueFromArgs_map_of_mem
    {M : Model} (base env : Env M)
    (parameters : List DefinitionalCnf.FreeVarParam)
    (parameter : DefinitionalCnf.FreeVarParam)
    (hMem : parameter ∈ parameters) :
    freeValueFromArgs base parameters
        (parameters.map (fun current =>
          env.freeVal current.sort current.varId))
        parameter.sort parameter.varId =
      env.freeVal parameter.sort parameter.varId := by
  induction parameters with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      simp only [List.mem_cons] at hMem
      cases hMem with
      | inl hHead =>
        rw [hHead]
        simp [freeValueFromArgs]
      | inr hTail =>
        by_cases hSort : head.sort = parameter.sort
        · by_cases hId : head.varId = parameter.varId
          · have hEqual : head = parameter := by
              cases head
              cases parameter
              simp_all
            rw [hEqual]
            simp [freeValueFromArgs]
          · simp [freeValueFromArgs, hSort, hId, ih hTail]
        · simp [freeValueFromArgs, hSort, ih hTail]

/-- 定义谓词实参在统一搬运前后取值不变。 -/
theorem evaluatedArguments_rebaseOverrideDefinitions
    {M : Model} (modelBase : Env M)
    (definitions : Array DefinitionalCnf.Definition) (env : Env M)
    (definition : DefinitionalCnf.Definition) :
    evaluatedArguments
        (Env.rebaseOverrideDefinitions modelBase definitions env) definition =
      evaluatedArguments env definition := by
  have hContext :
      ∀ (contextSorts : List CoreSort) (start : Nat),
        contextValues
            (Env.rebaseOverrideDefinitions modelBase definitions env)
            start contextSorts =
          contextValues env start contextSorts := by
    intro contextSorts start
    induction contextSorts generalizing start with
    | nil =>
        rfl
    | cons sort contextSorts ih =>
        simp only [contextValues]
        rw [ih]
        rfl
  unfold evaluatedArguments
  rw [hContext]
  rfl

/--
用固定 fallback 环境重建出的 body 环境，在 body 可见的局部 bound 与自由变量支持上
和当前环境一致。
-/
theorem envForArgs_evaluatedArguments_body_iff
    {M : Model} (modelBase env : Env M)
    (definition : DefinitionalCnf.Definition)
    (hParams :
      definition.freeVarParams =
        DefinitionalCnf.nnfFreeVarParams definition.body)
    (hCheck :
      Formula.checkWith definition.contextSorts definition.body.toFormula = true) :
    Nnf.Satisfies
        (envForArgs modelBase definition (evaluatedArguments env definition))
        definition.body ↔
      Nnf.Satisfies env definition.body := by
  let reconstructed :=
    envForArgs modelBase definition (evaluatedArguments env definition)
  let currentFree : Env M := {
    boundVal := reconstructed.boundVal
    freeVal := env.freeVal
  }
  have hFreeAgreement :
      Env.FreeAgreement
        (DefinitionalCnf.nnfFreeVarParams definition.body)
        reconstructed currentFree := by
    rw [← hParams]
    intro parameter hParameter
    unfold reconstructed currentFree envForArgs evaluatedArguments
    rw [drop_contextValues_append]
    exact freeValueFromArgs_map_of_mem
      modelBase env definition.freeVarParams parameter hParameter
  have hFreeIff :
      Nnf.Satisfies reconstructed definition.body ↔
        Nnf.Satisfies currentFree definition.body :=
    Nnf.satisfies_iff_of_freeAgreement
      reconstructed currentFree (by intro index; rfl)
        definition.body hFreeAgreement
  have hScopedAgreement :
      Env.ScopedSupportAgreement definition.contextSorts currentFree env := by
    constructor
    · intro sort index hLookup
      unfold currentFree reconstructed envForArgs evaluatedArguments
      exact boundValueFromArgs_contextValues_append_of_lookup
        modelBase env definition.contextSorts
          (definition.freeVarParams.map (fun parameter =>
            env.freeVal parameter.sort parameter.varId))
          index sort hLookup
    · intro sort id
      rfl
  have hScoped :=
    Formula.wellScopedWith_of_checkWith_support
      definition.contextSorts definition.body.toFormula hCheck
  have hScopedIff :
      Nnf.Satisfies currentFree definition.body ↔
        Nnf.Satisfies env definition.body := by
    rw [← Nnf.satisfies_toFormula, ← Nnf.satisfies_toFormula]
    exact Formula.satisfies_iff_of_scopedSupportAgreement
      definition.contextSorts currentFree env hScopedAgreement
        definition.body.toFormula hScoped
  exact hFreeIff.trans hScopedIff

theorem envForArgs_evaluatedArguments {M : Model} (env : Env M)
    (definition : DefinitionalCnf.Definition) :
    envForArgs env definition (evaluatedArguments env definition) = env := by
  cases env with
  | mk boundVal freeVal =>
      cases definition with
      | mk index predicate contextSorts freeVarParams body =>
          have hBound :
              boundValueFromArgs { boundVal := boundVal, freeVal := freeVal }
                  contextSorts
                    (contextValues { boundVal := boundVal, freeVal := freeVal }
                      0 contextSorts ++
                      freeVarParams.map (fun parameter =>
                        freeVal parameter.sort parameter.varId)) =
                boundVal := by
            funext index
            simpa [boundValueFromArgs] using
              boundValueFromArgs_contextValues_append
              { boundVal := boundVal, freeVal := freeVal }
              0 contextSorts
              (freeVarParams.map (fun parameter =>
                freeVal parameter.sort parameter.varId))
              index index
          have hFree :
              freeValueFromArgs { boundVal := boundVal, freeVal := freeVal }
                  freeVarParams
                  ((contextValues { boundVal := boundVal, freeVal := freeVal }
                    0 contextSorts ++
                      freeVarParams.map (fun parameter =>
                        freeVal parameter.sort parameter.varId)).drop contextSorts.length) =
                freeVal := by
            funext sort id
            have hDrop :=
              drop_contextValues_append
                { boundVal := boundVal, freeVal := freeVal }
                0 contextSorts
                (freeVarParams.map (fun parameter =>
                  freeVal parameter.sort parameter.varId))
            rw [hDrop]
            exact freeValueFromArgs_params
              { boundVal := boundVal, freeVal := freeVal }
              freeVarParams sort id
          change
            Env.mk
                (boundValueFromArgs { boundVal := boundVal, freeVal := freeVal }
                  contextSorts
                  (contextValues { boundVal := boundVal, freeVal := freeVal }
                    0 contextSorts ++
                    freeVarParams.map (fun parameter =>
                      freeVal parameter.sort parameter.varId)))
                (freeValueFromArgs { boundVal := boundVal, freeVal := freeVal }
                  freeVarParams
                  ((contextValues { boundVal := boundVal, freeVal := freeVal }
                    0 contextSorts ++
                      freeVarParams.map (fun parameter =>
                        freeVal parameter.sort parameter.varId)).drop contextSorts.length)) =
              Env.mk boundVal freeVal
          rw [hBound, hFree]

theorem contextArgsFrom_eval {M : Model} (env : Env M)
    (index : Nat) (contextSorts : List CoreSort) :
    (FirstOrderProjection.contextArgsFrom index contextSorts).map (Term.eval env) =
      contextValues env index contextSorts := by
  induction contextSorts generalizing index with
  | nil =>
      rfl
  | cons sort contextSorts ih =>
      simp [FirstOrderProjection.contextArgsFrom, contextValues, Term.eval, ih]

theorem evaluatedArguments_eq_eval_arguments {M : Model} (env : Env M)
    (definition : DefinitionalCnf.Definition) :
    definition.arguments.map (Term.eval env) =
      evaluatedArguments env definition := by
  unfold DefinitionalCnf.Definition.arguments evaluatedArguments
  have hContext := contextArgsFrom_eval env 0 definition.contextSorts
  have hContext' :
      (FirstOrderProjection.contextArgs definition.contextSorts).map (Term.eval env) =
        contextValues env 0 definition.contextSorts := by
    simpa [FirstOrderProjection.contextArgs] using hContext
  rw [List.map_append, hContext']
  congr 1
  induction definition.freeVarParams with
  | nil =>
      rfl
  | cons parameter parameters _ =>
      simp [DefinitionalCnf.FreeVarParam.terms, DefinitionalCnf.FreeVarParam.term,
        Term.eval]

end Definition

namespace Definition

theorem stateM_run_bind_pure_snd
    {σ α β : Type} (first : StateM σ α) (last : α → β) (state : σ) :
    ((do
      let value ← first
      pure (last value)).run state).2 =
      (first.run state).2 := by
  rw [StateT.run_bind]
  cases hRun : first.run state with
  | mk value nextState =>
      change (((pure (last value) : StateM σ β).run nextState)).2 = nextState
      rw [StateT.run_pure]
      rfl

theorem stateM_run_bind3_dep_snd
    {σ α β γ : Type} (first : StateM σ α) (second : α → StateM σ β)
    (third : α → β → StateM σ γ) (state : σ)
    (firstValue : α) (firstState : σ) (secondValue : β) (secondState : σ)
    (hFirst : first.run state = (firstValue, firstState))
    (hSecond : (second firstValue).run firstState = (secondValue, secondState)) :
    ((do
      let firstValue ← first
      let secondValue ← second firstValue
      third firstValue secondValue).run state).2 =
      ((third firstValue secondValue).run secondState).2 := by
  rw [StateT.run_bind, hFirst]
  change ((do
    let secondValue ← second firstValue
    third firstValue secondValue).run firstState).2 =
      ((third firstValue secondValue).run secondState).2
  rw [StateT.run_bind, hSecond]
  change ((third firstValue secondValue).run secondState).2 =
    ((third firstValue secondValue).run secondState).2
  rfl

theorem stateM_run_bind3_dep
    {σ α β γ : Type} (first : StateM σ α) (second : α → StateM σ β)
    (third : α → β → StateM σ γ) (state : σ)
    (firstValue : α) (firstState : σ) (secondValue : β) (secondState : σ)
    (thirdValue : γ) (thirdState : σ)
    (hFirst : first.run state = (firstValue, firstState))
    (hSecond : (second firstValue).run firstState = (secondValue, secondState))
    (hThird :
      (third firstValue secondValue).run secondState = (thirdValue, thirdState)) :
    (do
      let firstValue ← first
      let secondValue ← second firstValue
      third firstValue secondValue).run state =
      (thirdValue, thirdState) := by
  rw [StateT.run_bind, hFirst]
  change (do
    let secondValue ← second firstValue
    third firstValue secondValue).run firstState =
      (thirdValue, thirdState)
  rw [StateT.run_bind, hSecond]
  change (third firstValue secondValue).run secondState =
    (thirdValue, thirdState)
  exact hThird

/-- 当前状态下一次 `freshDefinition` 将追加的定义对象。 -/
def BuildState.nextDefinition (state : DefinitionalCnf.BuildState)
    (contextSorts : List CoreSort) (body : Nnf) :
    DefinitionalCnf.Definition :=
  let freeVarParams := DefinitionalCnf.nnfFreeVarParams body
  {
    index := state.definitions.size
    predicate := {
      id := state.nextPredicate
      arity := (contextSorts ++
        DefinitionalCnf.FreeVarParam.sorts freeVarParams).length
      role := PredicateRole.definition
      inputSorts :=
        contextSorts ++ DefinitionalCnf.FreeVarParam.sorts freeVarParams
    }
    contextSorts := contextSorts
    freeVarParams := freeVarParams
    body := body
  }

/-- `freshDefinition` 的返回字面量和后态都由 `nextDefinition` 精确描述。 -/
theorem BuildState.freshDefinition_run
    (state : DefinitionalCnf.BuildState)
    (contextSorts : List CoreSort) (body : Nnf) :
    (DefinitionalCnf.freshDefinition contextSorts body).run state =
      ((BuildState.nextDefinition state contextSorts body).literal true, {
        nextPredicate := state.nextPredicate + 1
        definitions :=
          state.definitions.push
            (BuildState.nextDefinition state contextSorts body)
      }) := rfl

/-- 构造状态中所有已生成谓词的编号都位于同一 fresh 窗口内且互不重复。 -/
def BuildState.FreshFrom (cutoff : Nat) (state : DefinitionalCnf.BuildState) : Prop :=
  (∀ definition ∈ state.definitions.toList,
      cutoff ≤ definition.predicate.id ∧ definition.predicate.id < state.nextPredicate) ∧
    state.definitions.toList.Pairwise
      (fun left right => left.predicate ≠ right.predicate) ∧
    cutoff ≤ state.nextPredicate

/-- 后态保留前态中已经生成的全部定义。 -/
def BuildState.DefinitionsIncluded
    (before after : DefinitionalCnf.BuildState) : Prop :=
  ∀ definition ∈ before.definitions.toList,
    definition ∈ after.definitions.toList

theorem BuildState.definitionsIncluded_refl
    (state : DefinitionalCnf.BuildState) :
    BuildState.DefinitionsIncluded state state :=
  fun _ hDefinition => hDefinition

theorem BuildState.definitionsIncluded_trans
    {first second third : DefinitionalCnf.BuildState}
    (hFirst : BuildState.DefinitionsIncluded first second)
    (hSecond : BuildState.DefinitionsIncluded second third) :
    BuildState.DefinitionsIncluded first third :=
  fun definition hDefinition => hSecond definition (hFirst definition hDefinition)

theorem BuildState.freshFrom_empty (cutoff : Nat) :
    BuildState.FreshFrom cutoff
      ({ nextPredicate := cutoff, definitions := #[] } : DefinitionalCnf.BuildState) := by
  simp [BuildState.FreshFrom]

theorem BuildState.freshDefinition_preserves
    {cutoff : Nat} {state : DefinitionalCnf.BuildState}
    (hState : BuildState.FreshFrom cutoff state)
    (contextSorts : List CoreSort) (body : Nnf) :
    BuildState.FreshFrom cutoff
      (DefinitionalCnf.freshDefinition contextSorts body |>.run state).2 := by
  change BuildState.FreshFrom cutoff
    { nextPredicate := state.nextPredicate + 1,
      definitions := state.definitions.push _ }
  unfold BuildState.FreshFrom at hState ⊢
  simp only [Array.toList_push, List.mem_append, List.mem_singleton,
    List.pairwise_append, List.pairwise_cons]
  rcases hState with ⟨hBounds, hPairwise, hCutoff⟩
  constructor
  · intro definition hDefinition
    rcases hDefinition with hDefinition | rfl
    · rcases hBounds definition hDefinition with ⟨hLower, hUpper⟩
      exact ⟨hLower, Nat.lt_succ_of_lt hUpper⟩
    · exact ⟨hCutoff, Nat.lt_succ_self _⟩
  · constructor
    · constructor
      · exact hPairwise
      · constructor
        · constructor <;> simp
        · intro left hLeft right hRight hEqual
          have hRightId : right.predicate.id = state.nextPredicate := by
            rw [hRight]
          have hIdEq : left.predicate.id = right.predicate.id :=
            congrArg PredicateSymbol.id hEqual
          have hUpper := (hBounds left hLeft).2
          have hLeftId : left.predicate.id = state.nextPredicate :=
            hIdEq.trans hRightId
          rw [hLeftId] at hUpper
          exact (Nat.lt_irrefl _ hUpper).elim
    · exact Nat.le_trans hCutoff (Nat.le_succ _)

/-- 引入一个 fresh 定义会保留输入状态中的全部定义。 -/
theorem BuildState.freshDefinition_includes
    (state : DefinitionalCnf.BuildState)
    (contextSorts : List CoreSort) (body : Nnf) :
    BuildState.DefinitionsIncluded state
      ((DefinitionalCnf.freshDefinition contextSorts body).run state).2 := by
  intro definition hDefinition
  change definition ∈ (state.definitions.push _).toList
  simp [Array.toList_push, hDefinition]

/-- `buildCore` 的任意递归组合只追加定义，不会丢失前态定义。 -/
theorem BuildState.buildCore_includes
    (state : DefinitionalCnf.BuildState)
    (contextSorts : List CoreSort) (source : Nnf) :
    BuildState.DefinitionsIncluded state
      ((DefinitionalCnf.buildCore contextSorts source).run state).2 := by
  induction source generalizing state contextSorts with
  | trueE =>
      exact BuildState.definitionsIncluded_refl state
  | falseE =>
      exact BuildState.definitionsIncluded_refl state
  | lit literal =>
      exact BuildState.definitionsIncluded_refl state
  | forallE sort body ih =>
      exact BuildState.definitionsIncluded_refl state
  | existsE sort body ih =>
      exact BuildState.definitionsIncluded_refl state
  | conj left right leftIH rightIH =>
      cases hLeftRun : (DefinitionalCnf.buildCore contextSorts left).run state with
      | mk leftResult leftState =>
          have hLeftIncluded :
              BuildState.DefinitionsIncluded state leftState := by
            simpa [hLeftRun] using leftIH state contextSorts
          cases hRightRun :
              (DefinitionalCnf.buildCore contextSorts right).run leftState with
          | mk rightResult rightState =>
              have hRightIncluded :
                  BuildState.DefinitionsIncluded leftState rightState := by
                simpa [hRightRun] using rightIH leftState contextSorts
              let finish :
                  DefinitionalCnf.BuildCore → DefinitionalCnf.BuildCore →
                    DefinitionalCnf.BuildM DefinitionalCnf.BuildCore :=
                fun leftResult rightResult => do
                  let defLit ← DefinitionalCnf.freshDefinition contextSorts
                    (Nnf.conj left right)
                  let definitionClauses :=
                    DefinitionalCnf.conjDefinitionClauses
                      defLit leftResult.ref rightResult.ref
                  pure {
                    ref := DefinitionalCnf.Ref.lit defLit
                    clauses :=
                      leftResult.clauses ++ rightResult.clauses ++ definitionClauses
                  }
              change BuildState.DefinitionsIncluded state
                ((do
                  let leftResult ← DefinitionalCnf.buildCore contextSorts left
                  let rightResult ← DefinitionalCnf.buildCore contextSorts right
                  finish leftResult rightResult).run state).2
              rw [stateM_run_bind3_dep_snd
                (first := DefinitionalCnf.buildCore contextSorts left)
                (second := fun _ => DefinitionalCnf.buildCore contextSorts right)
                (third := finish)
                (state := state) (firstValue := leftResult)
                (firstState := leftState) (secondValue := rightResult)
                (secondState := rightState) hLeftRun hRightRun]
              unfold finish
              rw [stateM_run_bind_pure_snd]
              exact BuildState.definitionsIncluded_trans hLeftIncluded
                (BuildState.definitionsIncluded_trans hRightIncluded
                  (BuildState.freshDefinition_includes rightState contextSorts
                    (Nnf.conj left right)))
  | disj left right leftIH rightIH =>
      cases hLeftRun : (DefinitionalCnf.buildCore contextSorts left).run state with
      | mk leftResult leftState =>
          have hLeftIncluded :
              BuildState.DefinitionsIncluded state leftState := by
            simpa [hLeftRun] using leftIH state contextSorts
          cases hRightRun :
              (DefinitionalCnf.buildCore contextSorts right).run leftState with
          | mk rightResult rightState =>
              have hRightIncluded :
                  BuildState.DefinitionsIncluded leftState rightState := by
                simpa [hRightRun] using rightIH leftState contextSorts
              let finish :
                  DefinitionalCnf.BuildCore → DefinitionalCnf.BuildCore →
                    DefinitionalCnf.BuildM DefinitionalCnf.BuildCore :=
                fun leftResult rightResult => do
                  let defLit ← DefinitionalCnf.freshDefinition contextSorts
                    (Nnf.disj left right)
                  let definitionClauses :=
                    DefinitionalCnf.disjDefinitionClauses
                      defLit leftResult.ref rightResult.ref
                  pure {
                    ref := DefinitionalCnf.Ref.lit defLit
                    clauses :=
                      leftResult.clauses ++ rightResult.clauses ++ definitionClauses
                  }
              change BuildState.DefinitionsIncluded state
                ((do
                  let leftResult ← DefinitionalCnf.buildCore contextSorts left
                  let rightResult ← DefinitionalCnf.buildCore contextSorts right
                  finish leftResult rightResult).run state).2
              rw [stateM_run_bind3_dep_snd
                (first := DefinitionalCnf.buildCore contextSorts left)
                (second := fun _ => DefinitionalCnf.buildCore contextSorts right)
                (third := finish)
                (state := state) (firstValue := leftResult)
                (firstState := leftState) (secondValue := rightResult)
                (secondState := rightState) hLeftRun hRightRun]
              unfold finish
              rw [stateM_run_bind_pure_snd]
              exact BuildState.definitionsIncluded_trans hLeftIncluded
                (BuildState.definitionsIncluded_trans hRightIncluded
                  (BuildState.freshDefinition_includes rightState contextSorts
                    (Nnf.disj left right)))

/-- `buildCore` 的任意递归组合都保持定义谓词的 fresh 窗口。 -/
theorem BuildState.buildCore_preserves
    {cutoff : Nat} {state : DefinitionalCnf.BuildState}
    (contextSorts : List CoreSort) (source : Nnf)
    (hState : BuildState.FreshFrom cutoff state) :
    BuildState.FreshFrom cutoff
      ((DefinitionalCnf.buildCore contextSorts source).run state).2 := by
  induction source generalizing state contextSorts with
  | trueE =>
      simpa [DefinitionalCnf.buildCore] using hState
  | falseE =>
      simpa [DefinitionalCnf.buildCore] using hState
  | lit literal =>
      simpa [DefinitionalCnf.buildCore] using hState
  | forallE sort body ih =>
      simpa [DefinitionalCnf.buildCore] using hState
  | existsE sort body ih =>
      simpa [DefinitionalCnf.buildCore] using hState
  | conj left right leftIH rightIH =>
      cases hLeftRun : (DefinitionalCnf.buildCore contextSorts left).run state with
      | mk leftResult leftState =>
          have hLeftState : BuildState.FreshFrom cutoff leftState := by
            simpa [hLeftRun] using leftIH contextSorts hState
          cases hRightRun :
              (DefinitionalCnf.buildCore contextSorts right).run leftState with
          | mk rightResult rightState =>
              have hRightState : BuildState.FreshFrom cutoff rightState := by
                simpa [hRightRun] using rightIH contextSorts hLeftState
              let finish :
                  DefinitionalCnf.BuildCore → DefinitionalCnf.BuildCore →
                    DefinitionalCnf.BuildM DefinitionalCnf.BuildCore :=
                fun leftResult rightResult => do
                  let defLit ← DefinitionalCnf.freshDefinition contextSorts
                    (Nnf.conj left right)
                  let definitionClauses :=
                    DefinitionalCnf.conjDefinitionClauses
                      defLit leftResult.ref rightResult.ref
                  pure {
                    ref := DefinitionalCnf.Ref.lit defLit
                    clauses :=
                      leftResult.clauses ++ rightResult.clauses ++ definitionClauses
                  }
              change BuildState.FreshFrom cutoff
                ((do
                  let leftResult ← DefinitionalCnf.buildCore contextSorts left
                  let rightResult ← DefinitionalCnf.buildCore contextSorts right
                  finish leftResult rightResult).run state).2
              rw [stateM_run_bind3_dep_snd
                (first := DefinitionalCnf.buildCore contextSorts left)
                (second := fun _ => DefinitionalCnf.buildCore contextSorts right)
                (third := finish)
                (state := state) (firstValue := leftResult)
                (firstState := leftState) (secondValue := rightResult)
                (secondState := rightState) hLeftRun hRightRun]
              unfold finish
              rw [stateM_run_bind_pure_snd]
              exact
                BuildState.freshDefinition_preserves hRightState contextSorts
                  (Nnf.conj left right)
  | disj left right leftIH rightIH =>
      cases hLeftRun : (DefinitionalCnf.buildCore contextSorts left).run state with
      | mk leftResult leftState =>
          have hLeftState : BuildState.FreshFrom cutoff leftState := by
            simpa [hLeftRun] using leftIH contextSorts hState
          cases hRightRun :
              (DefinitionalCnf.buildCore contextSorts right).run leftState with
          | mk rightResult rightState =>
              have hRightState : BuildState.FreshFrom cutoff rightState := by
                simpa [hRightRun] using rightIH contextSorts hLeftState
              let finish :
                  DefinitionalCnf.BuildCore → DefinitionalCnf.BuildCore →
                    DefinitionalCnf.BuildM DefinitionalCnf.BuildCore :=
                fun leftResult rightResult => do
                  let defLit ← DefinitionalCnf.freshDefinition contextSorts
                    (Nnf.disj left right)
                  let definitionClauses :=
                    DefinitionalCnf.disjDefinitionClauses
                      defLit leftResult.ref rightResult.ref
                  pure {
                    ref := DefinitionalCnf.Ref.lit defLit
                    clauses :=
                      leftResult.clauses ++ rightResult.clauses ++ definitionClauses
                  }
              change BuildState.FreshFrom cutoff
                ((do
                  let leftResult ← DefinitionalCnf.buildCore contextSorts left
                  let rightResult ← DefinitionalCnf.buildCore contextSorts right
                  finish leftResult rightResult).run state).2
              rw [stateM_run_bind3_dep_snd
                (first := DefinitionalCnf.buildCore contextSorts left)
                (second := fun _ => DefinitionalCnf.buildCore contextSorts right)
                (third := finish)
                (state := state) (firstValue := leftResult)
                (firstState := leftState) (secondValue := rightResult)
                (secondState := rightState) hLeftRun hRightRun]
              unfold finish
              rw [stateM_run_bind_pure_snd]
              exact
                BuildState.freshDefinition_preserves hRightState contextSorts
                  (Nnf.disj left right)

end Definition

namespace Ref

/-- 引用在模型环境中的满足关系。 -/
def Satisfies {M : Model} (env : Env M) : DefinitionalCnf.Ref → Prop
  | .truth value => value = true
  | .lit literal => Literal.Satisfies env literal

@[simp]
theorem satisfies_negate_iff {M : Model} (env : Env M) (ref : DefinitionalCnf.Ref) :
    Satisfies env ref.negate ↔ ¬ Satisfies env ref := by
  cases ref with
  | truth value =>
      cases value <;> simp [DefinitionalCnf.Ref.negate, Satisfies]
  | lit literal =>
      cases literal with
      | mk positive atom =>
          cases positive <;>
            simp [DefinitionalCnf.Ref.negate, Literal.negate, Satisfies,
              Literal.Satisfies]

theorem satisfies_lit_of_true {M : Model} (env : Env M) (literal : Literal)
    (h : Literal.Satisfies env literal) :
    Satisfies env (.lit literal) := h

end Ref

namespace DefinitionalCnf

theorem clausesOfRefs_one_of {M : Model} (env : Env M)
    (ref : DefinitionalCnf.Ref)
    (h : Semantics.Ref.Satisfies env ref) :
    ClauseSet.Satisfies env (DefinitionalCnf.clausesOfRefs [ref]) := by
  cases ref with
  | truth value =>
      cases value <;>
        simp_all [DefinitionalCnf.clausesOfRefs, DefinitionalCnf.clauseOfRefs,
          DefinitionalCnf.clauseOfRefsAux, Semantics.Ref.Satisfies,
          ClauseSet.Satisfies, Clause.Satisfies]
  | lit literal =>
      simpa [DefinitionalCnf.clausesOfRefs, DefinitionalCnf.clauseOfRefs,
        DefinitionalCnf.clauseOfRefsAux, Semantics.Ref.Satisfies,
        ClauseSet.Satisfies, Clause.Satisfies] using h

theorem clausesOfRefs_two_of_or {M : Model} (env : Env M)
    (left right : DefinitionalCnf.Ref)
    (h : Semantics.Ref.Satisfies env left ∨ Semantics.Ref.Satisfies env right) :
    ClauseSet.Satisfies env (DefinitionalCnf.clausesOfRefs [left, right]) := by
  cases left with
  | truth leftValue =>
      cases right with
      | truth rightValue =>
          cases leftValue <;> cases rightValue <;>
            simp_all [DefinitionalCnf.clausesOfRefs, DefinitionalCnf.clauseOfRefs,
              DefinitionalCnf.clauseOfRefsAux, Semantics.Ref.Satisfies,
              ClauseSet.Satisfies, Clause.Satisfies]
      | lit rightLiteral =>
          cases leftValue <;>
            simp_all [DefinitionalCnf.clausesOfRefs, DefinitionalCnf.clauseOfRefs,
              DefinitionalCnf.clauseOfRefsAux, Semantics.Ref.Satisfies,
              ClauseSet.Satisfies, Clause.Satisfies]
  | lit leftLiteral =>
      cases right with
      | truth rightValue =>
          cases rightValue <;>
            simp_all [DefinitionalCnf.clausesOfRefs, DefinitionalCnf.clauseOfRefs,
              DefinitionalCnf.clauseOfRefsAux, Semantics.Ref.Satisfies,
              ClauseSet.Satisfies, Clause.Satisfies]
      | lit rightLiteral =>
          simpa [DefinitionalCnf.clausesOfRefs, DefinitionalCnf.clauseOfRefs,
            DefinitionalCnf.clauseOfRefsAux, Semantics.Ref.Satisfies,
            ClauseSet.Satisfies, Clause.Satisfies] using h

theorem clausesOfRefs_three_of_or {M : Model} (env : Env M)
    (first second third : DefinitionalCnf.Ref) :
    Semantics.Ref.Satisfies env first ∨ Semantics.Ref.Satisfies env second ∨
        Semantics.Ref.Satisfies env third →
      ClauseSet.Satisfies env
        (DefinitionalCnf.clausesOfRefs [first, second, third]) := by
  intro h
  cases first with
  | truth firstValue =>
      cases second with
      | truth secondValue =>
          cases third with
          | truth thirdValue =>
              cases firstValue <;> cases secondValue <;> cases thirdValue <;>
                simp_all [DefinitionalCnf.clausesOfRefs,
                  DefinitionalCnf.clauseOfRefs, DefinitionalCnf.clauseOfRefsAux,
                  Semantics.Ref.Satisfies, ClauseSet.Satisfies, Clause.Satisfies]
          | lit thirdLiteral =>
              cases firstValue <;> cases secondValue <;>
                simp_all [DefinitionalCnf.clausesOfRefs,
                  DefinitionalCnf.clauseOfRefs, DefinitionalCnf.clauseOfRefsAux,
                  Semantics.Ref.Satisfies, ClauseSet.Satisfies, Clause.Satisfies]
      | lit secondLiteral =>
          cases third with
          | truth thirdValue =>
              cases firstValue <;> cases thirdValue <;>
                simp_all [DefinitionalCnf.clausesOfRefs,
                  DefinitionalCnf.clauseOfRefs, DefinitionalCnf.clauseOfRefsAux,
                  Semantics.Ref.Satisfies, ClauseSet.Satisfies, Clause.Satisfies]
          | lit thirdLiteral =>
              cases firstValue <;>
                simp_all [DefinitionalCnf.clausesOfRefs,
                  DefinitionalCnf.clauseOfRefs, DefinitionalCnf.clauseOfRefsAux,
                  Semantics.Ref.Satisfies, ClauseSet.Satisfies, Clause.Satisfies]
  | lit firstLiteral =>
      cases second with
      | truth secondValue =>
          cases third with
          | truth thirdValue =>
              cases secondValue <;> cases thirdValue <;>
                simp_all [DefinitionalCnf.clausesOfRefs,
                  DefinitionalCnf.clauseOfRefs, DefinitionalCnf.clauseOfRefsAux,
                  Semantics.Ref.Satisfies, ClauseSet.Satisfies, Clause.Satisfies]
          | lit thirdLiteral =>
              cases secondValue <;>
                simp_all [DefinitionalCnf.clausesOfRefs,
                  DefinitionalCnf.clauseOfRefs, DefinitionalCnf.clauseOfRefsAux,
                  Semantics.Ref.Satisfies, ClauseSet.Satisfies, Clause.Satisfies]
      | lit secondLiteral =>
          cases third with
          | truth thirdValue =>
              cases thirdValue <;>
                simp_all [DefinitionalCnf.clausesOfRefs,
                  DefinitionalCnf.clauseOfRefs, DefinitionalCnf.clauseOfRefsAux,
                  Semantics.Ref.Satisfies, ClauseSet.Satisfies, Clause.Satisfies]
          | lit thirdLiteral =>
              simpa [DefinitionalCnf.clausesOfRefs,
                DefinitionalCnf.clauseOfRefs, DefinitionalCnf.clauseOfRefsAux,
                Semantics.Ref.Satisfies, ClauseSet.Satisfies, Clause.Satisfies]
                using h

end DefinitionalCnf

namespace ClauseSet

theorem satisfies_append {M : Model} (env : Env M) (left right : ClauseSet) :
    ClauseSet.Satisfies env (left ++ right) ↔
      ClauseSet.Satisfies env left ∧ ClauseSet.Satisfies env right := by
  simp only [ClauseSet.Satisfies, Array.toList_append, List.mem_append]
  constructor
  · intro h
    exact ⟨
      fun clause hMem => h clause (Or.inl hMem),
      fun clause hMem => h clause (Or.inr hMem)⟩
  · rintro ⟨hLeft, hRight⟩ clause (hMem | hMem)
    · exact hLeft clause hMem
    · exact hRight clause hMem

end ClauseSet

namespace DefinitionalCnf

theorem conjDefinitionClauses_satisfies {M : Model} (env : Env M)
    (defLit : Literal) (left right : DefinitionalCnf.Ref)
    (hDef :
      Literal.Satisfies env defLit ↔
        Semantics.Ref.Satisfies env left ∧ Semantics.Ref.Satisfies env right) :
    ClauseSet.Satisfies env
      (DefinitionalCnf.conjDefinitionClauses defLit left right) := by
  rw [DefinitionalCnf.conjDefinitionClauses, ClauseSet.satisfies_append,
    ClauseSet.satisfies_append]
  by_cases hDefined : Literal.Satisfies env defLit
  · rcases hDef.mp hDefined with ⟨hLeft, hRight⟩
    exact ⟨⟨
      clausesOfRefs_two_of_or env (.lit defLit.negate) left (Or.inr hLeft),
      clausesOfRefs_two_of_or env (.lit defLit.negate) right (Or.inr hRight)⟩,
      clausesOfRefs_three_of_or env (.lit defLit) left.negate right.negate
        (Or.inl hDefined)⟩
  · have hNeg : Semantics.Ref.Satisfies env (.lit defLit.negate) := by
      exact
        (Semantics.Ref.satisfies_negate_iff env (.lit defLit)).mpr hDefined
    exact ⟨⟨
      clausesOfRefs_two_of_or env (.lit defLit.negate) left (Or.inl hNeg),
      clausesOfRefs_two_of_or env (.lit defLit.negate) right (Or.inl hNeg)⟩,
      by
        by_cases hLeft : Semantics.Ref.Satisfies env left
        · have hRight : ¬Semantics.Ref.Satisfies env right := by
            intro hRight
            exact hDefined (hDef.mpr ⟨hLeft, hRight⟩)
          have hRightNeg : Semantics.Ref.Satisfies env right.negate :=
            (Semantics.Ref.satisfies_negate_iff env right).mpr hRight
          exact clausesOfRefs_three_of_or env (.lit defLit) left.negate right.negate
            (Or.inr (Or.inr hRightNeg))
        · have hLeftNeg : Semantics.Ref.Satisfies env left.negate :=
            (Semantics.Ref.satisfies_negate_iff env left).mpr hLeft
          exact clausesOfRefs_three_of_or env (.lit defLit) left.negate right.negate
            (Or.inr (Or.inl hLeftNeg))⟩

theorem disjDefinitionClauses_satisfies {M : Model} (env : Env M)
    (defLit : Literal) (left right : DefinitionalCnf.Ref)
    (hDef :
      Literal.Satisfies env defLit ↔
        Semantics.Ref.Satisfies env left ∨ Semantics.Ref.Satisfies env right) :
    ClauseSet.Satisfies env
      (DefinitionalCnf.disjDefinitionClauses defLit left right) := by
  rw [DefinitionalCnf.disjDefinitionClauses, ClauseSet.satisfies_append,
    ClauseSet.satisfies_append]
  by_cases hDefined : Literal.Satisfies env defLit
  · rcases hDef.mp hDefined with hLeft | hRight
    · have hRightClause :
          ClauseSet.Satisfies env
            (DefinitionalCnf.clausesOfRefs [.lit defLit, right.negate]) :=
        clausesOfRefs_two_of_or env (.lit defLit) right.negate (Or.inl hDefined)
      exact ⟨⟨
        clausesOfRefs_two_of_or env (.lit defLit) left.negate (Or.inl hDefined),
        hRightClause⟩,
        clausesOfRefs_three_of_or env (.lit defLit.negate) left right
          (Or.inr (Or.inl hLeft))⟩
    · exact ⟨⟨
        clausesOfRefs_two_of_or env (.lit defLit) left.negate (Or.inl hDefined),
        clausesOfRefs_two_of_or env (.lit defLit) right.negate (Or.inl hDefined)⟩,
        clausesOfRefs_three_of_or env (.lit defLit.negate) left right
          (Or.inr (Or.inr hRight))⟩
  · have hNeg : Semantics.Ref.Satisfies env (.lit defLit.negate) := by
      exact
        (Semantics.Ref.satisfies_negate_iff env (.lit defLit)).mpr hDefined
    have hNeither : ¬Semantics.Ref.Satisfies env left ∧
        ¬Semantics.Ref.Satisfies env right := by
      exact not_or.mp (mt hDef.mpr hDefined)
    have hLeftNeg : Semantics.Ref.Satisfies env left.negate :=
      (Semantics.Ref.satisfies_negate_iff env left).mpr hNeither.1
    have hRightNeg : Semantics.Ref.Satisfies env right.negate :=
      (Semantics.Ref.satisfies_negate_iff env right).mpr hNeither.2
    exact ⟨⟨
      clausesOfRefs_two_of_or env (.lit defLit) left.negate (Or.inr hLeftNeg),
      clausesOfRefs_two_of_or env (.lit defLit) right.negate (Or.inr hRightNeg)⟩,
      clausesOfRefs_three_of_or env (.lit defLit.negate) left right (Or.inl hNeg)⟩

end DefinitionalCnf

namespace Definition

/-- 在定义谓词被正确解释时，正定义字面量等价于其开放矩阵。 -/
theorem literal_satisfies_iff_of_interp {M : Model} (env : Env M)
    (definition : DefinitionalCnf.Definition)
    (hInterp :
      M.predicateInterp definition.predicate
          (definition.arguments.map (Term.eval env)) ↔
        Nnf.Satisfies env definition.body) :
    Literal.Satisfies env (definition.literal true) ↔
      Nnf.Satisfies env definition.body := by
  simpa [DefinitionalCnf.Definition.literal, Atom.Satisfies, Literal.Satisfies]
    using hInterp

/--
固定定义模型中的定义字面量，对任意当前环境都等价于同一环境下的开放 body。
显式实参恢复 body 实际读取的局部 bound 与 typed 自由变量，fallback 环境不会冻结
当前赋值。
-/
theorem literal_satisfies_iff_override_at
    {M : Model} (modelBase env : Env M)
    (definitions : Array DefinitionalCnf.Definition)
    (definition : DefinitionalCnf.Definition)
    (hMem : definition ∈ definitions.toList)
    (hUnique :
      definitions.toList.Pairwise
        (fun left right => left.predicate ≠ right.predicate))
    (hParams :
      definition.freeVarParams =
        DefinitionalCnf.nnfFreeVarParams definition.body)
    (hCheck :
      Formula.checkWith definition.contextSorts definition.body.toFormula = true) :
    Literal.Satisfies
        (Env.rebaseOverrideDefinitions modelBase definitions env)
        (definition.literal true) ↔
      Nnf.Satisfies env definition.body := by
  let extendedEnv :=
    Env.rebaseOverrideDefinitions modelBase definitions env
  have hLookup :
      Model.lookupDefinition? definitions.toList definition.predicate =
        some definition :=
    Model.lookupDefinition?_eq_some_of_mem definitions.toList definition hMem hUnique
  have hArguments :
      definition.arguments.map (Term.eval extendedEnv) =
        evaluatedArguments env definition := by
    calc
      definition.arguments.map (Term.eval extendedEnv) =
          evaluatedArguments extendedEnv definition :=
        evaluatedArguments_eq_eval_arguments extendedEnv definition
      _ = evaluatedArguments env definition := by
        exact evaluatedArguments_rebaseOverrideDefinitions
          modelBase definitions env definition
  simp only [DefinitionalCnf.Definition.literal, Literal.Satisfies,
    Atom.Satisfies]
  simp only [if_true]
  rw [hArguments]
  simp only [Model.overrideDefinitions, hLookup]
  exact envForArgs_evaluatedArguments_body_iff
    modelBase env definition hParams hCheck

end Definition

namespace DefinitionalCnf

/-- `buildCore` 在固定定义模型和任意当前环境中的递归语义结果。 -/
structure BuildCoreSound {M : Model} (base env : Env M)
    (definitions : Array DefinitionalCnf.Definition)
    (source : Nnf) (core : DefinitionalCnf.BuildCore) : Prop where
  clausesSatisfied :
    ClauseSet.Satisfies
      (Env.rebaseOverrideDefinitions base definitions env)
      core.clauses
  refIff :
    Semantics.Ref.Satisfies
        (Env.rebaseOverrideDefinitions base definitions env)
        core.ref ↔
      Nnf.Satisfies env source

/--
量词自由 `buildCore` 的子句与返回引用在任意包含其生成定义的最终定义表中都成立。
-/
theorem buildCore_sound
    {M : Model} (base env : Env M)
    (definitions : Array DefinitionalCnf.Definition)
    (cutoff : Nat)
    (hFresh :
      ∀ definition ∈ definitions.toList,
        cutoff ≤ definition.predicate.id)
    (hUnique :
      definitions.toList.Pairwise
        (fun left right => left.predicate ≠ right.predicate))
    (state : DefinitionalCnf.BuildState)
    (contextSorts : List CoreSort) (source : Nnf)
    (hMax : DefinitionalCnf.nnfMaxPredicateIdSucc source ≤ cutoff)
    (hQuantifierFree : source.quantifierFree = true)
    (hCheck : Formula.checkWith contextSorts source.toFormula = true)
    (hIncluded :
      ∀ definition ∈
          ((DefinitionalCnf.buildCore contextSorts source).run state).2.definitions.toList,
        definition ∈ definitions.toList) :
    BuildCoreSound base env definitions source
      ((DefinitionalCnf.buildCore contextSorts source).run state).1 := by
  induction source generalizing state contextSorts with
  | trueE =>
      constructor
      · change ClauseSet.Satisfies
          (Env.rebaseOverrideDefinitions base definitions env) #[]
        simp [ClauseSet.Satisfies]
      · simp [DefinitionalCnf.buildCore, Semantics.Ref.Satisfies, Nnf.Satisfies]
  | falseE =>
      constructor
      · change ClauseSet.Satisfies
          (Env.rebaseOverrideDefinitions base definitions env) #[]
        simp [ClauseSet.Satisfies]
      · simp [DefinitionalCnf.buildCore, Semantics.Ref.Satisfies, Nnf.Satisfies]
  | lit literal =>
      let extendedEnv : Env (Model.overrideDefinitions M base definitions) :=
        Env.rebaseOverrideDefinitions base definitions env
      have hLiteral :=
        Nnf.satisfies_override_of_predicate_lt
          base definitions cutoff env extendedEnv
          (by intro index; rfl)
          (by intro sort id; rfl)
          hFresh (Nnf.lit literal) hMax
      constructor
      · change ClauseSet.Satisfies
          (Env.rebaseOverrideDefinitions base definitions env) #[]
        simp [ClauseSet.Satisfies]
      · simpa [DefinitionalCnf.buildCore, Semantics.Ref.Satisfies,
          Nnf.Satisfies, extendedEnv] using hLiteral
  | forallE sort body ih =>
      change (body.quantifierCount + 1 == 0) = true at hQuantifierFree
      rw [Nat.beq_eq_true_eq] at hQuantifierFree
      omega
  | existsE sort body ih =>
      change (body.quantifierCount + 1 == 0) = true at hQuantifierFree
      rw [Nat.beq_eq_true_eq] at hQuantifierFree
      omega
  | conj left right leftIH rightIH =>
      have hBounds := Nat.max_le.mp hMax
      have hChecks :
          Formula.checkWith contextSorts left.toFormula = true ∧
            Formula.checkWith contextSorts right.toFormula = true := by
        exact Formula.checkWith_of_check_conj
          (by simpa [Nnf.toFormula] using hCheck)
      have hLeftQuantifierFree : left.quantifierFree = true := by
        change (left.quantifierCount + right.quantifierCount == 0) = true at hQuantifierFree
        rw [Nat.beq_eq_true_eq] at hQuantifierFree
        change (left.quantifierCount == 0) = true
        rw [Nat.beq_eq_true_eq]
        omega
      have hRightQuantifierFree : right.quantifierFree = true := by
        change (left.quantifierCount + right.quantifierCount == 0) = true at hQuantifierFree
        rw [Nat.beq_eq_true_eq] at hQuantifierFree
        change (right.quantifierCount == 0) = true
        rw [Nat.beq_eq_true_eq]
        omega
      cases hLeftRun : (DefinitionalCnf.buildCore contextSorts left).run state with
      | mk leftResult leftState =>
          cases hRightRun :
              (DefinitionalCnf.buildCore contextSorts right).run leftState with
          | mk rightResult rightState =>
              let definition :=
                Definition.BuildState.nextDefinition rightState contextSorts
                  (Nnf.conj left right)
              let finalState : DefinitionalCnf.BuildState := {
                nextPredicate := rightState.nextPredicate + 1
                definitions := rightState.definitions.push definition
              }
              let finalCore : DefinitionalCnf.BuildCore := {
                ref := DefinitionalCnf.Ref.lit (definition.literal true)
                clauses :=
                  leftResult.clauses ++ rightResult.clauses ++
                    DefinitionalCnf.conjDefinitionClauses
                      (definition.literal true) leftResult.ref rightResult.ref
              }
              let finish :
                  DefinitionalCnf.BuildCore → DefinitionalCnf.BuildCore →
                    DefinitionalCnf.BuildM DefinitionalCnf.BuildCore :=
                fun leftResult rightResult => do
                  let defLit ← DefinitionalCnf.freshDefinition contextSorts
                    (Nnf.conj left right)
                  pure {
                    ref := DefinitionalCnf.Ref.lit defLit
                    clauses :=
                      leftResult.clauses ++ rightResult.clauses ++
                        DefinitionalCnf.conjDefinitionClauses
                          defLit leftResult.ref rightResult.ref
                  }
              have hFinishRun :
                  (finish leftResult rightResult).run rightState =
                    (finalCore, finalState) := by
                unfold finish
                rw [StateT.run_bind,
                  Definition.BuildState.freshDefinition_run]
                rfl
              have hRun :
                  (DefinitionalCnf.buildCore contextSorts (Nnf.conj left right)).run
                      state =
                    (finalCore, finalState) := by
                change (do
                  let leftResult ← DefinitionalCnf.buildCore contextSorts left
                  let rightResult ← DefinitionalCnf.buildCore contextSorts right
                  finish leftResult rightResult).run state =
                    (finalCore, finalState)
                exact Definition.stateM_run_bind3_dep
                  (first := DefinitionalCnf.buildCore contextSorts left)
                  (second := fun _ =>
                    DefinitionalCnf.buildCore contextSorts right)
                  (third := finish)
                  (state := state) (firstValue := leftResult)
                  (firstState := leftState) (secondValue := rightResult)
                  (secondState := rightState) (thirdValue := finalCore)
                  (thirdState := finalState) hLeftRun hRightRun hFinishRun
              have hRightToFinal :
                  Definition.BuildState.DefinitionsIncluded rightState finalState := by
                simpa [Definition.BuildState.freshDefinition_run, finalState,
                  definition] using
                  Definition.BuildState.freshDefinition_includes
                    rightState contextSorts (Nnf.conj left right)
              have hLeftToRight :
                  Definition.BuildState.DefinitionsIncluded leftState rightState := by
                simpa [hRightRun] using
                  Definition.BuildState.buildCore_includes
                    leftState contextSorts right
              have hFinalIncluded :
                  ∀ candidate ∈ finalState.definitions.toList,
                    candidate ∈ definitions.toList := by
                intro candidate hCandidate
                exact hIncluded candidate (by simpa [hRun] using hCandidate)
              have hLeftSound :
                  BuildCoreSound base env definitions left leftResult := by
                simpa [hLeftRun] using
                  leftIH state contextSorts hBounds.1 hLeftQuantifierFree hChecks.1
                    (by
                      intro candidate hCandidate
                      exact hFinalIncluded candidate
                        (hRightToFinal candidate
                          (hLeftToRight candidate (by
                            simpa [hLeftRun] using hCandidate))))
              have hRightSound :
                  BuildCoreSound base env definitions right rightResult := by
                simpa [hRightRun] using
                  rightIH leftState contextSorts hBounds.2 hRightQuantifierFree
                    hChecks.2
                    (by
                      intro candidate hCandidate
                      exact hFinalIncluded candidate
                        (hRightToFinal candidate (by
                          simpa [hRightRun] using hCandidate)))
              have hDefinitionMem :
                  definition ∈ definitions.toList := by
                apply hFinalIncluded definition
                simp [finalState, Array.toList_push]
              have hDefinitionBody :
                  Literal.Satisfies
                      (Env.rebaseOverrideDefinitions base definitions env)
                      (definition.literal true) ↔
                    Nnf.Satisfies env (Nnf.conj left right) := by
                simpa [definition, Definition.BuildState.nextDefinition] using
                  Definition.literal_satisfies_iff_override_at
                    base env definitions definition hDefinitionMem hUnique rfl
                      (by simpa [Nnf.toFormula] using hCheck)
              have hDefinitionRefs :
                  Literal.Satisfies
                      (Env.rebaseOverrideDefinitions base definitions env)
                      (definition.literal true) ↔
                    Semantics.Ref.Satisfies
                        (Env.rebaseOverrideDefinitions base definitions env)
                        leftResult.ref ∧
                      Semantics.Ref.Satisfies
                        (Env.rebaseOverrideDefinitions base definitions env)
                        rightResult.ref := by
                constructor
                · intro h
                  have hBoth := hDefinitionBody.mp h
                  exact ⟨
                    hLeftSound.refIff.mpr hBoth.1,
                    hRightSound.refIff.mpr hBoth.2⟩
                · rintro ⟨hLeft, hRight⟩
                  exact hDefinitionBody.mpr ⟨
                    hLeftSound.refIff.mp hLeft,
                    hRightSound.refIff.mp hRight⟩
              rw [hRun]
              constructor
              · dsimp [finalCore]
                rw [ClauseSet.satisfies_append,
                  ClauseSet.satisfies_append]
                exact ⟨⟨
                  hLeftSound.clausesSatisfied,
                  hRightSound.clausesSatisfied⟩,
                  DefinitionalCnf.conjDefinitionClauses_satisfies
                    _ _ _ _ hDefinitionRefs⟩
              · simpa [finalCore, Semantics.Ref.Satisfies] using hDefinitionBody
  | disj left right leftIH rightIH =>
      have hBounds := Nat.max_le.mp hMax
      have hChecks :
          Formula.checkWith contextSorts left.toFormula = true ∧
            Formula.checkWith contextSorts right.toFormula = true := by
        exact Formula.checkWith_of_check_disj
          (by simpa [Nnf.toFormula] using hCheck)
      have hLeftQuantifierFree : left.quantifierFree = true := by
        change (left.quantifierCount + right.quantifierCount == 0) = true at hQuantifierFree
        rw [Nat.beq_eq_true_eq] at hQuantifierFree
        change (left.quantifierCount == 0) = true
        rw [Nat.beq_eq_true_eq]
        omega
      have hRightQuantifierFree : right.quantifierFree = true := by
        change (left.quantifierCount + right.quantifierCount == 0) = true at hQuantifierFree
        rw [Nat.beq_eq_true_eq] at hQuantifierFree
        change (right.quantifierCount == 0) = true
        rw [Nat.beq_eq_true_eq]
        omega
      cases hLeftRun : (DefinitionalCnf.buildCore contextSorts left).run state with
      | mk leftResult leftState =>
          cases hRightRun :
              (DefinitionalCnf.buildCore contextSorts right).run leftState with
          | mk rightResult rightState =>
              let definition :=
                Definition.BuildState.nextDefinition rightState contextSorts
                  (Nnf.disj left right)
              let finalState : DefinitionalCnf.BuildState := {
                nextPredicate := rightState.nextPredicate + 1
                definitions := rightState.definitions.push definition
              }
              let finalCore : DefinitionalCnf.BuildCore := {
                ref := DefinitionalCnf.Ref.lit (definition.literal true)
                clauses :=
                  leftResult.clauses ++ rightResult.clauses ++
                    DefinitionalCnf.disjDefinitionClauses
                      (definition.literal true) leftResult.ref rightResult.ref
              }
              let finish :
                  DefinitionalCnf.BuildCore → DefinitionalCnf.BuildCore →
                    DefinitionalCnf.BuildM DefinitionalCnf.BuildCore :=
                fun leftResult rightResult => do
                  let defLit ← DefinitionalCnf.freshDefinition contextSorts
                    (Nnf.disj left right)
                  pure {
                    ref := DefinitionalCnf.Ref.lit defLit
                    clauses :=
                      leftResult.clauses ++ rightResult.clauses ++
                        DefinitionalCnf.disjDefinitionClauses
                          defLit leftResult.ref rightResult.ref
                  }
              have hFinishRun :
                  (finish leftResult rightResult).run rightState =
                    (finalCore, finalState) := by
                unfold finish
                rw [StateT.run_bind,
                  Definition.BuildState.freshDefinition_run]
                rfl
              have hRun :
                  (DefinitionalCnf.buildCore contextSorts (Nnf.disj left right)).run
                      state =
                    (finalCore, finalState) := by
                change (do
                  let leftResult ← DefinitionalCnf.buildCore contextSorts left
                  let rightResult ← DefinitionalCnf.buildCore contextSorts right
                  finish leftResult rightResult).run state =
                    (finalCore, finalState)
                exact Definition.stateM_run_bind3_dep
                  (first := DefinitionalCnf.buildCore contextSorts left)
                  (second := fun _ =>
                    DefinitionalCnf.buildCore contextSorts right)
                  (third := finish)
                  (state := state) (firstValue := leftResult)
                  (firstState := leftState) (secondValue := rightResult)
                  (secondState := rightState) (thirdValue := finalCore)
                  (thirdState := finalState) hLeftRun hRightRun hFinishRun
              have hRightToFinal :
                  Definition.BuildState.DefinitionsIncluded rightState finalState := by
                simpa [Definition.BuildState.freshDefinition_run, finalState,
                  definition] using
                  Definition.BuildState.freshDefinition_includes
                    rightState contextSorts (Nnf.disj left right)
              have hLeftToRight :
                  Definition.BuildState.DefinitionsIncluded leftState rightState := by
                simpa [hRightRun] using
                  Definition.BuildState.buildCore_includes
                    leftState contextSorts right
              have hFinalIncluded :
                  ∀ candidate ∈ finalState.definitions.toList,
                    candidate ∈ definitions.toList := by
                intro candidate hCandidate
                exact hIncluded candidate (by simpa [hRun] using hCandidate)
              have hLeftSound :
                  BuildCoreSound base env definitions left leftResult := by
                simpa [hLeftRun] using
                  leftIH state contextSorts hBounds.1 hLeftQuantifierFree hChecks.1
                    (by
                      intro candidate hCandidate
                      exact hFinalIncluded candidate
                        (hRightToFinal candidate
                          (hLeftToRight candidate (by
                            simpa [hLeftRun] using hCandidate))))
              have hRightSound :
                  BuildCoreSound base env definitions right rightResult := by
                simpa [hRightRun] using
                  rightIH leftState contextSorts hBounds.2 hRightQuantifierFree
                    hChecks.2
                    (by
                      intro candidate hCandidate
                      exact hFinalIncluded candidate
                        (hRightToFinal candidate (by
                          simpa [hRightRun] using hCandidate)))
              have hDefinitionMem :
                  definition ∈ definitions.toList := by
                apply hFinalIncluded definition
                simp [finalState, Array.toList_push]
              have hDefinitionBody :
                  Literal.Satisfies
                      (Env.rebaseOverrideDefinitions base definitions env)
                      (definition.literal true) ↔
                    Nnf.Satisfies env (Nnf.disj left right) := by
                simpa [definition, Definition.BuildState.nextDefinition] using
                  Definition.literal_satisfies_iff_override_at
                    base env definitions definition hDefinitionMem hUnique rfl
                      (by simpa [Nnf.toFormula] using hCheck)
              have hDefinitionRefs :
                  Literal.Satisfies
                      (Env.rebaseOverrideDefinitions base definitions env)
                      (definition.literal true) ↔
                    Semantics.Ref.Satisfies
                        (Env.rebaseOverrideDefinitions base definitions env)
                        leftResult.ref ∨
                      Semantics.Ref.Satisfies
                        (Env.rebaseOverrideDefinitions base definitions env)
                        rightResult.ref := by
                constructor
                · intro h
                  rcases hDefinitionBody.mp h with hLeft | hRight
                  · exact Or.inl (hLeftSound.refIff.mpr hLeft)
                  · exact Or.inr (hRightSound.refIff.mpr hRight)
                · intro h
                  apply hDefinitionBody.mpr
                  rcases h with hLeft | hRight
                  · exact Or.inl (hLeftSound.refIff.mp hLeft)
                  · exact Or.inr (hRightSound.refIff.mp hRight)
              rw [hRun]
              constructor
              · dsimp [finalCore]
                rw [ClauseSet.satisfies_append,
                  ClauseSet.satisfies_append]
                exact ⟨⟨
                  hLeftSound.clausesSatisfied,
                  hRightSound.clausesSatisfied⟩,
                  DefinitionalCnf.disjDefinitionClauses_satisfies
                    _ _ _ _ hDefinitionRefs⟩
              · simpa [finalCore, Semantics.Ref.Satisfies] using hDefinitionBody

/-- `buildCoreResult` 的最终 root 在定义模型中精确等价于源 NNF。 -/
theorem buildCoreResult_root_iff
    {M : Model} (base env : Env M)
    (contextSorts : List CoreSort) (source : Nnf)
    (hQuantifierFree : source.quantifierFree = true)
    (hCheck : Formula.checkWith contextSorts source.toFormula = true) :
    let result := DefinitionalCnf.buildCoreResult contextSorts source
    Semantics.Ref.Satisfies
        (Env.rebaseOverrideDefinitions base result.definitions env)
        result.root ↔
      Nnf.Satisfies env source := by
  let cutoff := DefinitionalCnf.nnfMaxPredicateIdSucc source
  let initial : DefinitionalCnf.BuildState := {
    nextPredicate := cutoff
    definitions := #[]
  }
  cases hRun :
      (DefinitionalCnf.buildCore contextSorts source).run initial with
  | mk core finalState =>
      have hFinalFresh :
          Definition.BuildState.FreshFrom cutoff finalState := by
        simpa [initial, hRun] using
          Definition.BuildState.buildCore_preserves contextSorts source
            (Definition.BuildState.freshFrom_empty cutoff)
      rcases hFinalFresh with ⟨hBounds, hUnique, hCutoff⟩
      have hCoreSound :
          BuildCoreSound base env finalState.definitions source core := by
        simpa [initial, hRun] using
          buildCore_sound base env finalState.definitions cutoff
            (fun definition hDefinition => (hBounds definition hDefinition).1)
            hUnique initial contextSorts source (Nat.le_refl cutoff)
            hQuantifierFree hCheck
            (by
              intro definition hDefinition
              simpa [initial, hRun] using hDefinition)
      have hResult :
          DefinitionalCnf.buildCoreResult contextSorts source = {
            root := core.ref
            clauses := core.clauses ++ DefinitionalCnf.clausesOfRefs [core.ref]
            definitions := finalState.definitions
          } := by
        simp [DefinitionalCnf.buildCoreResult, initial, cutoff, hRun]
      rw [hResult]
      exact hCoreSound.refIff

/-- 源 NNF 成立时，`buildCoreResult` 的全部定义子句和 root 子句同时成立。 -/
theorem buildCoreResult_clauses_satisfied
    {M : Model} (base env : Env M)
    (contextSorts : List CoreSort) (source : Nnf)
    (hQuantifierFree : source.quantifierFree = true)
    (hCheck : Formula.checkWith contextSorts source.toFormula = true)
    (hSource : Nnf.Satisfies env source) :
    let result := DefinitionalCnf.buildCoreResult contextSorts source
    ClauseSet.Satisfies
      (Env.rebaseOverrideDefinitions base result.definitions env)
      result.clauses := by
  let cutoff := DefinitionalCnf.nnfMaxPredicateIdSucc source
  let initial : DefinitionalCnf.BuildState := {
    nextPredicate := cutoff
    definitions := #[]
  }
  cases hRun :
      (DefinitionalCnf.buildCore contextSorts source).run initial with
  | mk core finalState =>
      have hFinalFresh :
          Definition.BuildState.FreshFrom cutoff finalState := by
        simpa [initial, hRun] using
          Definition.BuildState.buildCore_preserves contextSorts source
            (Definition.BuildState.freshFrom_empty cutoff)
      rcases hFinalFresh with ⟨hBounds, hUnique, hCutoff⟩
      have hCoreSound :
          BuildCoreSound base env finalState.definitions source core := by
        simpa [initial, hRun] using
          buildCore_sound base env finalState.definitions cutoff
            (fun definition hDefinition => (hBounds definition hDefinition).1)
            hUnique initial contextSorts source (Nat.le_refl cutoff)
            hQuantifierFree hCheck
            (by
              intro definition hDefinition
              simpa [initial, hRun] using hDefinition)
      let extendedEnv : Env
          (Model.overrideDefinitions M base finalState.definitions) := {
        boundVal := env.boundVal
        freeVal := env.freeVal
      }
      have hRoot : Semantics.Ref.Satisfies extendedEnv core.ref :=
        hCoreSound.refIff.mpr hSource
      have hRootClause :
          ClauseSet.Satisfies extendedEnv
            (DefinitionalCnf.clausesOfRefs [core.ref]) :=
        DefinitionalCnf.clausesOfRefs_one_of extendedEnv core.ref hRoot
      have hResult :
          DefinitionalCnf.buildCoreResult contextSorts source = {
            root := core.ref
            clauses := core.clauses ++ DefinitionalCnf.clausesOfRefs [core.ref]
            definitions := finalState.definitions
          } := by
        simp [DefinitionalCnf.buildCoreResult, initial, cutoff, hRun]
      rw [hResult]
      rw [ClauseSet.satisfies_append]
      exact ⟨hCoreSound.clausesSatisfied, hRootClause⟩

/-- `buildCoreResult` 的定义表共享同一个 fresh 窗口，并且定义谓词两两不同。 -/
theorem buildCoreResult_definitions_sound
    (contextSorts : List CoreSort) (source : Nnf) :
    let result := DefinitionalCnf.buildCoreResult contextSorts source
    (∀ definition ∈ result.definitions.toList,
        DefinitionalCnf.nnfMaxPredicateIdSucc source ≤ definition.predicate.id) ∧
      result.definitions.toList.Pairwise
        (fun left right => left.predicate ≠ right.predicate) := by
  let cutoff := DefinitionalCnf.nnfMaxPredicateIdSucc source
  let initial : DefinitionalCnf.BuildState := {
    nextPredicate := cutoff
    definitions := #[]
  }
  cases hRun :
      (DefinitionalCnf.buildCore contextSorts source).run initial with
  | mk core finalState =>
      have hFinalFresh :
          Definition.BuildState.FreshFrom cutoff finalState := by
        simpa [initial, hRun] using
          Definition.BuildState.buildCore_preserves contextSorts source
            (Definition.BuildState.freshFrom_empty cutoff)
      rcases hFinalFresh with ⟨hBounds, hUnique, hCutoff⟩
      simpa [DefinitionalCnf.buildCoreResult, initial, cutoff, hRun] using
        And.intro (fun definition hDefinition =>
          (hBounds definition hDefinition).1) hUnique

namespace Definition

/-- 通过定义 checker 的记录精确携带 body 的 typed 自由变量支持。 -/
theorem freeVarParams_eq_of_check (definition : DefinitionalCnf.Definition)
    (hCheck : definition.check = true) :
    definition.freeVarParams =
      DefinitionalCnf.nnfFreeVarParams definition.body := by
  unfold DefinitionalCnf.Definition.check at hCheck
  simp only [Bool.and_eq_true_iff, beq_iff_eq] at hCheck
  simp_all only

/-- 通过定义 checker 的 body 在记录的局部上下文中良定。 -/
theorem body_checkWith_of_check (definition : DefinitionalCnf.Definition)
    (hCheck : definition.check = true) :
    Formula.checkWith definition.contextSorts definition.body.toFormula = true := by
  unfold DefinitionalCnf.Definition.check at hCheck
  simp only [Bool.and_eq_true_iff, beq_iff_eq] at hCheck
  simp_all only

end Definition

/-- 定义性 CNF 的统一环境族模型扩张证书。 -/
structure UniformSoundExtension (contextSorts : List CoreSort) (source : Nnf)
    (root : DefinitionalCnf.Ref) (clauses : ClauseSet)
    (definitions : Array DefinitionalCnf.Definition)
    (M : Model) (base : Env M) : Prop where
  definitionsFresh :
    ∀ definition ∈ definitions.toList,
      DefinitionalCnf.nnfMaxPredicateIdSucc source ≤ definition.predicate.id
  definitionsUnique :
    definitions.toList.Pairwise
      (fun left right => left.predicate ≠ right.predicate)
  definitionIff :
    ∀ env definition, definition ∈ definitions.toList →
      (Literal.Satisfies
            (Env.rebaseOverrideDefinitions base definitions env)
            (definition.literal true) ↔
          Nnf.Satisfies env definition.body)
  rootIff :
    ∀ env,
      Semantics.Ref.Satisfies
          (Env.rebaseOverrideDefinitions base definitions env) root ↔
        Nnf.Satisfies env source
  clausesSatisfied :
    ∀ env, Nnf.Satisfies env source →
      ClauseSet.Satisfies
        (Env.rebaseOverrideDefinitions base definitions env) clauses

/--
量词自由源公式的整张定义表在一个固定扩张模型中，同时服务任意当前环境。
-/
theorem buildCoreResult_uniformSoundExtension
    {M : Model} (base : Env M)
    (contextSorts : List CoreSort) (source : Nnf)
    (hQuantifierFree : source.quantifierFree = true)
    (hCheck : Formula.checkWith contextSorts source.toFormula = true)
    (hDefinitionsChecked :
      let result := DefinitionalCnf.buildCoreResult contextSorts source
      result.definitions.toList.all DefinitionalCnf.Definition.check = true) :
    let result := DefinitionalCnf.buildCoreResult contextSorts source
    UniformSoundExtension contextSorts source result.root result.clauses
      result.definitions M base := by
  let result := DefinitionalCnf.buildCoreResult contextSorts source
  have hDefinitions :=
    buildCoreResult_definitions_sound contextSorts source
  refine {
    definitionsFresh := hDefinitions.1
    definitionsUnique := hDefinitions.2
    definitionIff := ?_
    rootIff := ?_
    clausesSatisfied := ?_
  }
  · intro env definition
    intro hDefinition
    have hDefinitionCheck : definition.check = true := by
      have hAll :
          result.definitions.toList.all DefinitionalCnf.Definition.check = true := by
        simpa [result] using hDefinitionsChecked
      have hAll' :
          ∀ candidate ∈ result.definitions.toList, candidate.check = true := by
        simpa only [List.all_eq_true] using hAll
      exact hAll' definition hDefinition
    exact Definition.literal_satisfies_iff_override_at
      base env result.definitions definition hDefinition hDefinitions.2
      (Definition.freeVarParams_eq_of_check definition hDefinitionCheck)
      (Definition.body_checkWith_of_check definition hDefinitionCheck)
  · intro env
    simpa [result] using
      buildCoreResult_root_iff
        base env contextSorts source hQuantifierFree hCheck
  · intro env hSource
    simpa [result] using
      buildCoreResult_clauses_satisfied
        base env contextSorts source hQuantifierFree hCheck hSource

end DefinitionalCnf

theorem DefinitionalCnf.buildCoreResult_satisfiable
    {contextSorts : List CoreSort} {source : Nnf}
    (hQuantifierFree : source.quantifierFree = true)
    (hCheck : Formula.checkWith contextSorts source.toFormula = true)
    (hSource : Nnf.Satisfiable.{x} source) :
    ClauseSet.Satisfiable.{x}
      (DefinitionalCnf.buildCoreResult contextSorts source).clauses := by
  rcases hSource with ⟨M, base, hSource⟩
  let result := DefinitionalCnf.buildCoreResult contextSorts source
  let env : Env (Model.overrideDefinitions M base result.definitions) := {
    boundVal := base.boundVal
    freeVal := base.freeVal
  }
  have hClauses :
    ClauseSet.Satisfies env result.clauses :=
    DefinitionalCnf.buildCoreResult_clauses_satisfied
      base base contextSorts source hQuantifierFree hCheck hSource
  exact ⟨Model.overrideDefinitions M base result.definitions, env,
    by simpa [result] using hClauses⟩

namespace DefinitionalCnfPayload

namespace DefinitionalCnf.Ref

theorem eq_eq_true {left right : DefinitionalCnf.Ref} :
    DefinitionalCnf.Ref.eq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp [DefinitionalCnf.Ref.eq, SyntaxEq.literalEq_eq_true, beq_iff_eq]

end DefinitionalCnf.Ref

namespace DefinitionalCnf.Definition

theorem eq_eq_true {left right : DefinitionalCnf.Definition} :
    DefinitionalCnf.Definition.eq left right = true ↔ left = right := by
  cases left
  cases right
  simp [DefinitionalCnf.Definition.eq, SyntaxEq.nnfEq_eq_true, beq_iff_eq, and_assoc]

theorem listEq_eq_true {left right : List DefinitionalCnf.Definition} :
    DefinitionalCnf.Definition.listEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [DefinitionalCnf.Definition.listEq]
  | cons head tail ih =>
      cases right with
      | nil =>
          simp [DefinitionalCnf.Definition.listEq]
      | cons head' tail' =>
          simp [DefinitionalCnf.Definition.listEq, eq_eq_true, ih]

end DefinitionalCnf.Definition

private theorem literalListEq_eq_true {left right : List Literal} :
    SyntaxEq.literalListEq left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [SyntaxEq.literalListEq]
  | cons head tail ih =>
      cases right with
      | nil =>
          simp [SyntaxEq.literalListEq]
      | cons head' tail' =>
          simp [SyntaxEq.literalListEq, SyntaxEq.literalEq_eq_true, ih]

private theorem array_eq_of_toList_eq {α : Type} {left right : Array α}
    (h : left.toList = right.toList) : left = right :=
  Array.toList_inj.mp h

theorem DefinitionalCnf.Definition.arrayEq_eq_true
    {left right : Array DefinitionalCnf.Definition} :
    DefinitionalCnf.Definition.arrayEq left right = true ↔ left = right := by
  unfold DefinitionalCnf.Definition.arrayEq
  constructor
  · exact fun h =>
      array_eq_of_toList_eq
        (DefinitionalCnf.Definition.listEq_eq_true.mp h)
  · intro h
    subst right
    exact DefinitionalCnf.Definition.listEq_eq_true.mpr rfl

private theorem clauseEq_eq_true {left right : Clause} :
    Clause.eq left right = true ↔ left = right := by
  rw [Clause.eq]
  constructor
  · exact fun h => array_eq_of_toList_eq (literalListEq_eq_true.mp h)
  · intro h
    subst right
    exact literalListEq_eq_true.mpr rfl

private theorem clauseSetGo_eq_true {left right : List Clause} :
    ClauseSet.eq.go left right = true ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp [ClauseSet.eq.go]
  | cons head tail ih =>
      cases right with
      | nil =>
          simp [ClauseSet.eq.go]
      | cons head' tail' =>
          simp [ClauseSet.eq.go, clauseEq_eq_true, ih]

theorem ClauseSet.eq_eq_true {left right : ClauseSet} :
    ClauseSet.eq left right = true ↔ left = right := by
  unfold ClauseSet.eq
  constructor
  · exact fun h => array_eq_of_toList_eq (clauseSetGo_eq_true.mp h)
  · intro h
    subst right
    exact clauseSetGo_eq_true.mpr rfl

/-- 定义性 CNF 的内核语义字段满足结构自反性。 -/
theorem semanticEq_self (payload : DefinitionalCnfPayload) :
    DefinitionalCnfPayload.semanticEq payload payload = true := by
  unfold DefinitionalCnfPayload.semanticEq
  exact Bool.and_eq_true_iff.mpr
    ⟨DefinitionalCnf.Ref.eq_eq_true.mpr rfl,
      Bool.and_eq_true_iff.mpr
        ⟨ClauseSet.eq_eq_true.mpr rfl,
          DefinitionalCnf.Definition.arrayEq_eq_true.mpr rfl⟩⟩

/--
定义性 CNF 构造结果的三个本地条件合成总 checker。

`build` 产生的 root、字句集和定义表使用语义结构自反性关闭，避免回放阶段重新
归约整份 CNF 来证明它与自身相等。
-/
theorem check_build_eq_true_of_components
    (config : DefinitionalCnf.Config) (contextSorts : List CoreSort)
    (source : Nnf)
    (hQuantifierFree : source.quantifierFree = true)
    (hSourceCheck : Formula.checkWith contextSorts source.toFormula = true)
    (hDefinitionsChecked :
      (DefinitionalCnfPayload.build config contextSorts source).definitions.toList.all
        DefinitionalCnf.Definition.check = true) :
    DefinitionalCnfPayload.check
      (DefinitionalCnfPayload.build config contextSorts source) = true := by
  unfold DefinitionalCnfPayload.check
  exact Bool.and_eq_true_iff.mpr
    ⟨hQuantifierFree,
      Bool.and_eq_true_iff.mpr
        ⟨hSourceCheck,
          Bool.and_eq_true_iff.mpr
            ⟨hDefinitionsChecked,
              semanticEq_self
                (DefinitionalCnfPayload.build config contextSorts source)⟩⟩⟩

theorem clauses_eq_of_semanticEq_true {left right : DefinitionalCnfPayload}
    (h : DefinitionalCnfPayload.semanticEq left right = true) :
    left.clauses = right.clauses := by
  have hRest := Bool.and_eq_true_iff.mp h
  have hClauses := Bool.and_eq_true_iff.mp hRest.2
  exact ClauseSet.eq_eq_true.mp hClauses.1

theorem root_eq_of_semanticEq_true {left right : DefinitionalCnfPayload}
    (h : DefinitionalCnfPayload.semanticEq left right = true) :
    left.root = right.root := by
  have hRoot := (Bool.and_eq_true_iff.mp h).1
  exact DefinitionalCnf.Ref.eq_eq_true.mp hRoot

theorem definitions_eq_of_semanticEq_true {left right : DefinitionalCnfPayload}
    (h : DefinitionalCnfPayload.semanticEq left right = true) :
    left.definitions = right.definitions := by
  have hRest := Bool.and_eq_true_iff.mp h
  have hDefinitions := (Bool.and_eq_true_iff.mp hRest.2).2
  exact DefinitionalCnf.Definition.arrayEq_eq_true.mp hDefinitions

/--
checked payload 复算出的 root、定义表和字句集在同一个固定模型中服务全部环境。
-/
theorem uniformSoundExtension_of_check {payload : DefinitionalCnfPayload}
    (hCheck : DefinitionalCnfPayload.check payload = true)
    {M : Semantics.Model} (base : Semantics.Env M) :
    Semantics.DefinitionalCnf.UniformSoundExtension
      payload.contextSorts payload.source
      payload.root payload.clauses payload.definitions M base := by
  have hCheck' := hCheck
  unfold DefinitionalCnfPayload.check at hCheck'
  have hQuantifierFree := (Bool.and_eq_true_iff.mp hCheck').1
  have hSourceRest := (Bool.and_eq_true_iff.mp hCheck').2
  have hSourceCheck := (Bool.and_eq_true_iff.mp hSourceRest).1
  have hDefinitionsRest := (Bool.and_eq_true_iff.mp hSourceRest).2
  have hDefinitionsChecked := (Bool.and_eq_true_iff.mp hDefinitionsRest).1
  let expected :=
    DefinitionalCnfPayload.build payload.config payload.contextSorts payload.source
  have hEq : DefinitionalCnfPayload.semanticEq payload expected = true := by
    exact (Bool.and_eq_true_iff.mp hDefinitionsRest).2
  have hRoot : payload.root = expected.root :=
    root_eq_of_semanticEq_true hEq
  have hClauses : payload.clauses = expected.clauses :=
    clauses_eq_of_semanticEq_true hEq
  have hDefinitions : payload.definitions = expected.definitions :=
    definitions_eq_of_semanticEq_true hEq
  have hExpectedDefinitionsChecked :
      expected.definitions.toList.all DefinitionalCnf.Definition.check = true := by
    simpa [← hDefinitions] using hDefinitionsChecked
  rw [hRoot, hClauses, hDefinitions]
  simpa [expected, DefinitionalCnfPayload.build] using
    (Semantics.DefinitionalCnf.buildCoreResult_uniformSoundExtension
      base payload.contextSorts payload.source hQuantifierFree hSourceCheck
        (by simpa [expected] using hExpectedDefinitionsChecked))

theorem satisfiable_of_check {payload : DefinitionalCnfPayload}
    (hCheck : DefinitionalCnfPayload.check payload = true)
    (hSource : Nnf.Satisfiable.{x} payload.source) :
    ClauseSet.Satisfiable.{x} payload.clauses := by
  have hCheck' := hCheck
  unfold DefinitionalCnfPayload.check at hCheck'
  have hQuantifierFree := (Bool.and_eq_true_iff.mp hCheck').1
  have hSourceRest := (Bool.and_eq_true_iff.mp hCheck').2
  have hSourceCheck := (Bool.and_eq_true_iff.mp hSourceRest).1
  have hDefinitionsRest := (Bool.and_eq_true_iff.mp hSourceRest).2
  have hEq : DefinitionalCnfPayload.semanticEq payload
      (DefinitionalCnfPayload.build payload.config payload.contextSorts payload.source) = true := by
    exact (Bool.and_eq_true_iff.mp hDefinitionsRest).2
  have hBuilt :
      ClauseSet.Satisfiable.{x}
        (DefinitionalCnfPayload.build payload.config payload.contextSorts payload.source).clauses :=
    by
      simpa [DefinitionalCnfPayload.build] using
        (DefinitionalCnf.buildCoreResult_satisfiable
          (contextSorts := payload.contextSorts)
          hQuantifierFree hSourceCheck hSource)
  have hClauses :
      payload.clauses =
        (DefinitionalCnfPayload.build
          payload.config payload.contextSorts payload.source).clauses := by
    exact clauses_eq_of_semanticEq_true hEq
  simpa [hClauses] using hBuilt

end DefinitionalCnfPayload

namespace ClauseSet

/-- 字句集结构相等 checker 的公共反射定理。 -/
theorem eq_eq_true {left right : _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.ClauseSet} :
    _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.ClauseSet.eq left right = true ↔
      left = right :=
  DefinitionalCnfPayload.ClauseSet.eq_eq_true

end ClauseSet

end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
