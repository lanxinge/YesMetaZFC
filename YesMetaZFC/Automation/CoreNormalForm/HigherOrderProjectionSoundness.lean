import YesMetaZFC.Automation.CoreNormalForm.FirstOrderProjectionSoundness
import YesMetaZFC.Automation.HOSearchMaterialization

/-!
# Core 字句到原生 HO-DAG 的语义投影

这一层只接受已经消去 FOOL 辅助项、但仍可保留 `apply/lam` 的原生高阶片段。
它不做 lambda lifting，也不把高阶项擦除成一阶函数符号；投影后的项结构直接由
`Logic.HigherOrder.Term` 解释。
-/

namespace YesMetaZFC
namespace Automation
namespace HOSearchMaterialization
namespace CoreProjectionSoundness

open CoreSyntax
open CoreSyntax.NormalForm

/-! ## 原生 HO 能力边界 -/

namespace Native

mutual
  /-- 原生 HO-DAG 可直接解释的 core 项。 -/
  def term : CoreSyntax.Term → Bool
    | .bvar .. | .fvar .. => true
    | .app symbol arguments =>
        decide (symbol.role ≠ FunctionRole.extensionalWitness) &&
          termList arguments
    | .apply function argument => term function && term argument
    | .lam _ _ body => term body
    | _ => false

  /-- 原生 HO-DAG 可直接解释的 core 项列表。 -/
  def termList : List CoreSyntax.Term → Bool
    | [] => true
    | head :: tail => term head && termList tail
end

/-- 原生 HO-DAG 可直接解释的 core 原子。 -/
def atom : CoreSyntax.NormalForm.Atom → Bool
  | .predicate _ arguments => termList arguments
  | .equal _ left right => term left && term right
  | .boolTerm input => term input

/-- 原生 HO-DAG 可直接解释的 core 文字。 -/
def literal (input : CoreSyntax.NormalForm.Literal) : Bool :=
  atom input.atom

/-- 原生 HO-DAG 可直接解释的 core 字句。 -/
def clause (input : CoreSyntax.NormalForm.Clause) : Bool :=
  input.all literal

/-- 原生 HO-DAG 可直接解释的 core 字句集。 -/
def clauseSet (input : CoreSyntax.NormalForm.ClauseSet) : Bool :=
  input.all clause

end Native

/-! ## 结构保持翻译 -/

mutual
  /--
  core 项到 HO 项的总翻译。

  非原生构造只给出不可达占位值；所有公开语义定理都要求 `Native.term = true`。
  -/
  def coreTerm : CoreSyntax.Term → Term
    | .bvar sort index => .var (.bvar (simpleType sort) index)
    | .fvar sort id => .var (.fvar (simpleType sort) id)
    | .app symbol arguments =>
        .app (FirstOrderProjection.functionSymbol symbol)
          (coreTermList arguments)
    | .apply function argument => .apply (coreTerm function) (coreTerm argument)
    | .lam domain codomain body =>
        .lam (simpleType domain) (simpleType codomain) (coreTerm body)
    | _ => .var (.fvar (.base .object) 0)

  /-- core 项列表到 HO 项列表的逐项翻译。 -/
  def coreTermList : List CoreSyntax.Term → List Term
    | [] => []
    | head :: tail => coreTerm head :: coreTermList tail
end

/-- core 原子到原生 HO 原子的翻译。 -/
def coreAtom : CoreSyntax.NormalForm.Atom → Atom
  | .predicate predicate arguments =>
      .rel (.predicate predicate) (coreTermList arguments)
  | .equal sort left right =>
      .equal (simpleType sort) (coreTerm left) (coreTerm right)
  | .boolTerm input =>
      .rel .boolHolds [coreTerm input]

/-- core 文字到原生 HO 文字的翻译。 -/
def coreLiteral (literal : CoreSyntax.NormalForm.Literal) : Literal :=
  { polarity := literal.positive, atom := coreAtom literal.atom }

/-- core 字句到原生 HO 字句的翻译。 -/
def coreClause (clause : CoreSyntax.NormalForm.Clause) : Clause :=
  { literals := clause.map coreLiteral }

/-- core 字句集到原生 HO 初始问题的翻译。 -/
def coreProblem (clauses : CoreSyntax.NormalForm.ClauseSet) : Problem :=
  { initialClauses := clauses.map coreClause }

@[simp]
theorem coreSort_simpleType (sort : CoreSort) :
    coreSort (simpleType sort) = sort := by
  induction sort with
  | object | bool | prop | named => rfl
  | arrow domain codomain ihDomain ihCodomain =>
      simp [simpleType, coreSort, ihDomain, ihCodomain]

/-! ## 模型与环境翻译 -/

/-- 把最终 core 模型直接解释成原生 HO 搜索签名模型。 -/
def searchStructure (M : Semantics.Model)
    (contract : Semantics.FoolLambdaContract M)
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)) :
    Logic.HigherOrder.Structure SearchSignature where
  Domain := M.Carrier
  nonempty := ⟨M.default⟩
  sortInterp := fun sort => M.sortInterp (coreSort sort)
  sortNonempty := fun sort => M.sortNonempty (coreSort sort)
  funcInterp := fun symbol arguments =>
    M.functionInterp symbol.toCore arguments
  funcSort := by
    intro symbol arguments _hArguments
    simpa [SearchSignature] using functionSort symbol.toCore arguments
  relInterp := fun symbol arguments =>
    match symbol with
    | .member =>
        M.predicateInterp
          { id := 1, arity := 2, role := PredicateRole.membership,
            inputSorts := [CoreSort.object, CoreSort.object] }
          arguments
    | .boolHolds =>
        match arguments with
        | [value] => M.boolHolds value
        | _ => False
    | .definition id arity =>
        M.predicateInterp
          { id := id, arity := arity, role := PredicateRole.definition }
          arguments
    | .predicate predicate =>
        M.predicateInterp predicate arguments
  applyInterp := M.applyInterp
  applySort := by
    intro domain codomain functionValue argumentValue hFunction hArgument
    simpa using
      contract.apply_sort (coreSort domain) (coreSort codomain)
        functionValue argumentValue hFunction hArgument
  lambdaInterp := fun domain codomain body =>
    M.lambdaValue (coreSort domain) (coreSort codomain) body
  lambdaSort := by
    intro domain codomain body hBody
    simpa using
      contract.lambda_sort (coreSort domain) (coreSort codomain) body hBody

/-- core FOOL/lambda 合同直接给出原生 HO βη 与外延合同。 -/
def extensionalContract (M : Semantics.Model)
    (contract : Semantics.FoolLambdaContract M)
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)) :
    Logic.HigherOrder.ExtensionalContract (searchStructure M contract functionSort) where
  lambdaCongr := by
    intro domain codomain left right hPointwise
    exact contract.lambda_congr (coreSort domain) (coreSort codomain)
      left right hPointwise
  beta := by
    intro domain codomain body argument hBody hArgument
    exact contract.beta (coreSort domain) (coreSort codomain) body argument
      hBody hArgument
  eta := by
    intro domain codomain functionValue hFunction
    exact contract.eta (coreSort domain) (coreSort codomain) functionValue hFunction
  functionExtensionality := by
    intro domain codomain left right hLeft hRight
    exact contract.function_extensionality
      (coreSort domain) (coreSort codomain) left right hLeft hRight

/-- 从 HO 环境恢复 core 环境。 -/
def coreEnv {M : Semantics.Model}
    {contract : Semantics.FoolLambdaContract M}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (env : Logic.HigherOrder.Env (searchStructure M contract functionSort)) :
    Semantics.Env M where
  boundVal := env.boundVal
  freeVal := fun sort id => env.freeVal (simpleType sort) id

/-- 用固定 core bound stack 和目标 HO 自由变量环境构造对齐环境。 -/
def alignedEnv {M : Semantics.Model}
    {contract : Semantics.FoolLambdaContract M}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (base : Semantics.Env M)
    (env : Logic.HigherOrder.Env (searchStructure M contract functionSort)) :
    Logic.HigherOrder.Env (searchStructure M contract functionSort) where
  boundVal := base.boundVal
  freeVal := env.freeVal

mutual
  /-- 原生 core-to-HO 项翻译保持解释。 -/
  theorem coreTerm_eval {M : Semantics.Model}
      {contract : Semantics.FoolLambdaContract M}
      {functionSort :
        ∀ symbol arguments,
          M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
      (env : Logic.HigherOrder.Env (searchStructure M contract functionSort)) :
      ∀ term, Native.term term = true →
        Logic.HigherOrder.Term.eval env (coreTerm term) =
          Semantics.Term.eval (coreEnv env) term
    | .bvar sort index, _ => by
        simp [coreTerm, Logic.HigherOrder.Term.eval, Semantics.Term.eval, coreEnv]
    | .fvar sort id, _ => by
        simp [coreTerm, Logic.HigherOrder.Term.eval, Semantics.Term.eval, coreEnv]
    | .app symbol arguments, hNative => by
        simp only [Native.term, Bool.and_eq_true_iff] at hNative
        simp only [coreTerm, Logic.HigherOrder.Term.eval, Semantics.Term.eval,
          searchStructure]
        rw [SearchMaterialization.CoreProjectionSoundness.functionSymbol_toCore]
        exact congrArg (M.functionInterp symbol)
          (coreTermList_eval env arguments hNative.2)
    | .apply function argument, hNative => by
        simp only [Native.term, Bool.and_eq_true_iff] at hNative
        simp only [coreTerm, Logic.HigherOrder.Term.eval, Semantics.Term.eval,
          searchStructure]
        calc
          M.applyInterp (Logic.HigherOrder.Term.eval env (coreTerm function))
              (Logic.HigherOrder.Term.eval env (coreTerm argument)) =
            M.applyInterp (Semantics.Term.eval (coreEnv env) function)
              (Logic.HigherOrder.Term.eval env (coreTerm argument)) :=
            congrArg
              (fun value =>
                M.applyInterp value
                  (Logic.HigherOrder.Term.eval env (coreTerm argument)))
              (coreTerm_eval env function hNative.1)
          _ =
            M.applyInterp (Semantics.Term.eval (coreEnv env) function)
              (Semantics.Term.eval (coreEnv env) argument) :=
            congrArg (M.applyInterp (Semantics.Term.eval (coreEnv env) function))
              (coreTerm_eval env argument hNative.2)
    | .lam domain codomain body, hNative => by
        simp only [Native.term] at hNative
        simp only [coreTerm, Logic.HigherOrder.Term.eval, Semantics.Term.eval,
          searchStructure]
        simp only [coreSort_simpleType]
        congr 1
        funext value
        simpa [coreEnv, Logic.HigherOrder.Env.push, Semantics.Env.push] using
          coreTerm_eval (env.push value) body hNative
    | .bool .., hNative
    | .notE .., hNative
    | .andE .., hNative
    | .orE .., hNative
    | .impE .., hNative
    | .iffE .., hNative
    | .quote .., hNative
    | .ite .., hNative => by
        simp [Native.term] at hNative

  /-- 原生 core-to-HO 项列表翻译保持逐项解释。 -/
  theorem coreTermList_eval {M : Semantics.Model}
      {contract : Semantics.FoolLambdaContract M}
      {functionSort :
        ∀ symbol arguments,
          M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
      (env : Logic.HigherOrder.Env (searchStructure M contract functionSort)) :
      ∀ terms, Native.termList terms = true →
        (coreTermList terms).map (Logic.HigherOrder.Term.eval env) =
          terms.map (Semantics.Term.eval (coreEnv env))
    | [], _ => rfl
    | head :: tail, hNative => by
        simp only [Native.termList, Bool.and_eq_true_iff] at hNative
        simp only [coreTermList, List.map_cons]
        calc
          Logic.HigherOrder.Term.eval env (coreTerm head) ::
              List.map (Logic.HigherOrder.Term.eval env) (coreTermList tail) =
            Semantics.Term.eval (coreEnv env) head ::
              List.map (Logic.HigherOrder.Term.eval env) (coreTermList tail) :=
            congrArg
              (fun value =>
                value :: List.map (Logic.HigherOrder.Term.eval env) (coreTermList tail))
              (coreTerm_eval env head hNative.1)
          _ =
            Semantics.Term.eval (coreEnv env) head ::
              List.map (Semantics.Term.eval (coreEnv env)) tail :=
            congrArg (List.cons (Semantics.Term.eval (coreEnv env) head))
              (coreTermList_eval env tail hNative.2)
end

/-- 原生 core-to-HO 原子翻译保持满足关系。 -/
theorem coreAtom_satisfies {M : Semantics.Model}
    {contract : Semantics.FoolLambdaContract M}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (env : Logic.HigherOrder.Env (searchStructure M contract functionSort))
    (atom : CoreSyntax.NormalForm.Atom)
    (hNative : Native.atom atom = true) :
    HODAGCertificate.Atom.Satisfies env (coreAtom atom) ↔
      Semantics.Atom.Satisfies (coreEnv env) atom := by
  cases atom with
  | predicate predicate arguments =>
      simp only [Native.atom] at hNative
      simp only [coreAtom, HODAGCertificate.Atom.Satisfies,
        Semantics.Atom.Satisfies, searchStructure]
      exact iff_of_eq <| congrArg (M.predicateInterp predicate)
        (coreTermList_eval env arguments hNative)
  | equal sort left right =>
      simp only [Native.atom, Bool.and_eq_true_iff] at hNative
      simp only [coreAtom, HODAGCertificate.Atom.Satisfies,
        Semantics.Atom.Satisfies]
      constructor
      · intro hEqual
        rw [coreTerm_eval env left hNative.1,
          coreTerm_eval env right hNative.2] at hEqual
        exact hEqual
      · intro hEqual
        rw [coreTerm_eval env left hNative.1,
          coreTerm_eval env right hNative.2]
        exact hEqual
  | boolTerm input =>
      simp only [Native.atom] at hNative
      simp only [coreAtom, HODAGCertificate.Atom.Satisfies,
        Semantics.Atom.Satisfies, searchStructure, List.map_cons, List.map_nil]
      exact iff_of_eq <| congrArg M.boolHolds (coreTerm_eval env input hNative)

/-- 原生 core-to-HO 文字翻译保持满足关系。 -/
theorem coreLiteral_satisfies {M : Semantics.Model}
    {contract : Semantics.FoolLambdaContract M}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (env : Logic.HigherOrder.Env (searchStructure M contract functionSort))
    (literal : CoreSyntax.NormalForm.Literal)
    (hNative : Native.literal literal = true) :
    HODAGCertificate.Literal.Satisfies env (coreLiteral literal) ↔
      Semantics.Literal.Satisfies (coreEnv env) literal := by
  cases literal with
  | mk positive atom =>
      have hAtom := coreAtom_satisfies env atom hNative
      cases positive with
      | false =>
          exact not_congr hAtom
      | true =>
          exact hAtom

/-- core 字句成立时，其原生 HO 翻译也成立。 -/
theorem coreClause_satisfies {M : Semantics.Model}
    {contract : Semantics.FoolLambdaContract M}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (env : Logic.HigherOrder.Env (searchStructure M contract functionSort))
    (clause : CoreSyntax.NormalForm.Clause)
    (hNative : Native.clause clause = true)
    (hClause : Semantics.Clause.Satisfies (coreEnv env) clause) :
    HODAGCertificate.Clause.Satisfies env (coreClause clause) := by
  rcases hClause with ⟨literal, hMem, hLiteral⟩
  have hLiteralNative : Native.literal literal = true := by
    have hAll := Array.all_eq_true.mp hNative
    rcases Array.mem_iff_getElem.mp (Array.mem_def.mpr hMem) with
      ⟨index, hIndex, hGet⟩
    simpa [hGet] using hAll index hIndex
  refine ⟨coreLiteral literal, ?_, ?_⟩
  · apply Array.mem_def.mpr
    simpa [coreClause, Array.toList_map] using
      (List.mem_map.mpr ⟨literal, hMem, rfl⟩)
  · exact (coreLiteral_satisfies env literal hLiteralNative).mpr hLiteral

/--
原生 HO 初始问题在任意 typed free 环境下都由 checked preprocessing 的 core 字句语义支持。
-/
theorem coreProblem_valid {M : Semantics.Model}
    (contract : Semantics.FoolLambdaContract M)
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments))
    (base : Semantics.Env M)
    (clauses : CoreSyntax.NormalForm.ClauseSet)
    (hNative : Native.clauseSet clauses = true)
    (hChecks :
      (coreProblem clauses).initialClauses.all HODAGCertificate.Clause.check = true)
    (hClauses :
      ∀ env, Semantics.Env.RespectsFree env →
        Semantics.LocalSkolemChoice.SameBoundStack env base →
          Semantics.ClauseSet.Satisfies env clauses) :
    (coreProblem clauses).Valid (searchStructure M contract functionSort) := by
  intro targetEnv hTargetEnv
  intro index targetClause hTargetClause
  unfold coreProblem at hTargetClause
  rw [Array.getElem?_map] at hTargetClause
  cases hCoreGet : clauses[index]? with
  | none =>
      simp [hCoreGet] at hTargetClause
  | some coreClauseValue =>
      simp only [hCoreGet, Option.map_some, Option.some.injEq] at hTargetClause
      subst targetClause
      rcases Array.getElem?_eq_some_iff.mp hCoreGet with ⟨hIndex, hGet⟩
      let sourceEnv := alignedEnv base targetEnv
      have hSourceFree : Semantics.Env.RespectsFree (coreEnv sourceEnv) := by
        intro sort id
        simpa [coreEnv, sourceEnv, alignedEnv, searchStructure, coreSort_simpleType] using
          hTargetEnv.2 (simpleType sort) id
      have hSourceBound :
          Semantics.LocalSkolemChoice.SameBoundStack (coreEnv sourceEnv) base := by
        intro boundIndex
        rfl
      have hCoreSat : Semantics.Clause.Satisfies (coreEnv sourceEnv) coreClauseValue := by
        have hAllClauses := hClauses (coreEnv sourceEnv) hSourceFree hSourceBound
        apply hAllClauses coreClauseValue
        exact Array.mem_def.mp <| by
          rw [← hGet]
          exact Array.getElem_mem hIndex
      have hAllNative := Array.all_eq_true.mp hNative
      have hCoreNative : Native.clause coreClauseValue = true := by
        simpa [hGet] using hAllNative index hIndex
      have hAlignedSat :
          HODAGCertificate.Clause.Satisfies sourceEnv (coreClause coreClauseValue) :=
        coreClause_satisfies sourceEnv coreClauseValue hCoreNative hCoreSat
      have hAllChecks := Array.all_eq_true.mp hChecks
      have hClauseCheck :
          HODAGCertificate.Clause.check (coreClause coreClauseValue) = true := by
        have hMappedIndex : index < (coreProblem clauses).initialClauses.size := by
          simpa [coreProblem] using hIndex
        simpa [coreProblem, hGet] using hAllChecks index hMappedIndex
      have hWellFormed :=
        HODAGCertificate.Clause.checkWith_sound (context := [])
          (clause := coreClause coreClauseValue) hClauseCheck
      exact
        (HODAGCertificate.Clause.satisfies_iff_of_wellFormed_env
          (env₁ := sourceEnv) (env₂ := targetEnv) hWellFormed
          (by
            intro boundIndex sort hLookup
            cases boundIndex <;> simp [Logic.HigherOrder.Context.lookup?] at hLookup)
          (by
            intro sort id
            rfl)).mp hAlignedSat

end CoreProjectionSoundness
end HOSearchMaterialization
end Automation
end YesMetaZFC
