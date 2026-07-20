import YesMetaZFC.Automation.SearchMaterialization

/-!
# 一阶投影到 DAG 初始字句的语义保持

本模块只消费 `FirstOrderProjection.Projectable` 已检查片段。搜索层仍可使用紧凑的二元
literal 表面，但可信语义直接落在 `SearchMaterialization.coreClauseSet` 的 canonical
翻译上，不依赖 tuple wrapper 或搜索器内部约定。
-/

namespace YesMetaZFC
namespace Automation
namespace SearchMaterialization
namespace CoreProjectionSoundness

universe x

open CoreSyntax
open CoreSyntax.NormalForm

/-- 把最终 core 模型直接解释成一阶 DAG 搜索签名的模型。 -/
def searchStructure (M : Semantics.Model.{x})
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)) :
    LogicSoundness.SetLevel.StructureAt.{x} SearchSignature where
  Domain := M.Carrier
  nonempty := ⟨M.default⟩
  sortInterp := M.sortInterp
  sortNonempty := M.sortNonempty
  funcInterp := fun symbol arguments =>
    M.functionInterp symbol.toCore arguments
  funcSort := by
    intro symbol arguments _
    simpa [SearchSignature, CoreSyntax.Search.FunctionSymbol.toCore] using
      functionSort symbol.toCore arguments
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

/-- core 函数符号投影到搜索层后再恢复，不丢失任何角色与 sort 信息。 -/
@[simp]
theorem functionSymbol_toCore (symbol : CoreSyntax.FunctionSymbol) :
    (FirstOrderProjection.functionSymbol symbol).toCore = symbol := by
  cases symbol with
  | mk id arity role inputSorts outputSort =>
      cases role <;> rfl

/-- 用一阶环境的自由变量部分和给定 core bound stack 组装 core 环境。 -/
def coreEnv {M : Semantics.Model.{x}}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (base : Semantics.Env M)
    (env : LogicSoundness.SetLevel.EnvAt.{x} (searchStructure M functionSort)) :
    Semantics.Env M where
  boundVal := base.boundVal
  freeVal := env.freeVal

@[simp]
theorem coreEnv_boundVal {M : Semantics.Model.{x}}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (base : Semantics.Env M)
    (env : LogicSoundness.SetLevel.EnvAt.{x} (searchStructure M functionSort))
    (index : Nat) :
    (coreEnv base env).boundVal index = base.boundVal index :=
  rfl

@[simp]
theorem coreEnv_freeVal {M : Semantics.Model.{x}}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (base : Semantics.Env M)
    (env : LogicSoundness.SetLevel.EnvAt.{x} (searchStructure M functionSort))
    (sort : CoreSort) (id : VarId) :
    (coreEnv base env).freeVal sort id = env.freeVal sort id :=
  rfl

/-- 从 core 环境构造一个 canonical 一阶环境。 -/
noncomputable def searchEnv {M : Semantics.Model.{x}}
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments))
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) :
    LogicSoundness.SetLevel.EnvAt.{x} (searchStructure M functionSort) where
  boundVal := fun sort _ => Classical.choose (M.sortNonempty sort)
  freeVal := env.freeVal
  boundSort := fun sort _ => Classical.choose_spec (M.sortNonempty sort)
  freeSort := hFree

mutual
  /-- canonical 项翻译保持解释。 -/
  theorem coreTerm_eval {M : Semantics.Model.{x}}
      {functionSort :
        ∀ symbol arguments,
          M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
      (base : Semantics.Env M)
      (env : LogicSoundness.SetLevel.EnvAt.{x} (searchStructure M functionSort)) :
      ∀ term, FirstOrderProjection.Projectable.term term = true →
        Logic.FirstOrder.Term.eval env (coreTerm term) =
          Semantics.Term.eval (coreEnv base env) term
    | .fvar sort id, _ => by
        simp [coreTerm, Logic.FirstOrder.Term.eval, Semantics.Term.eval,
          coreEnv]
    | .app symbol arguments, hProjectable => by
        simp only [FirstOrderProjection.Projectable.term] at hProjectable
        simp only [coreTerm, Logic.FirstOrder.Term.eval, Semantics.Term.eval,
          searchStructure]
        rw [functionSymbol_toCore]
        exact congrArg (M.functionInterp symbol)
          (coreTermList_eval base env arguments hProjectable)
    | .bvar .., hProjectable
    | .apply .., hProjectable
    | .bool .., hProjectable
    | .notE .., hProjectable
    | .andE .., hProjectable
    | .orE .., hProjectable
    | .impE .., hProjectable
    | .iffE .., hProjectable
    | .quote .., hProjectable
    | .lam .., hProjectable
    | .ite .., hProjectable => by
        simp [FirstOrderProjection.Projectable.term] at hProjectable

  /-- canonical 项列表翻译保持逐项解释。 -/
  theorem coreTermList_eval {M : Semantics.Model.{x}}
      {functionSort :
        ∀ symbol arguments,
          M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
      (base : Semantics.Env M)
      (env : LogicSoundness.SetLevel.EnvAt.{x} (searchStructure M functionSort)) :
      ∀ terms, FirstOrderProjection.Projectable.termList terms = true →
        (terms.map coreTerm).map (Logic.FirstOrder.Term.eval env) =
          terms.map (Semantics.Term.eval (coreEnv base env))
    | [], _ => rfl
    | head :: tail, hProjectable => by
        simp only [FirstOrderProjection.Projectable.termList,
          Bool.and_eq_true_iff] at hProjectable
        simp only [List.map_cons]
        rw [coreTerm_eval base env head hProjectable.1,
          coreTermList_eval base env tail hProjectable.2]
        rfl
end

/-- canonical 原子翻译保持满足关系。 -/
theorem coreAtom_satisfies {M : Semantics.Model.{x}}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (base : Semantics.Env M)
    (env : LogicSoundness.SetLevel.EnvAt.{x} (searchStructure M functionSort))
    (atom : CoreSyntax.NormalForm.Atom)
    (hProjectable : FirstOrderProjection.Projectable.atom atom = true) :
    Logic.FirstOrder.Formula.satisfies env (coreAtom atom) ↔
      Semantics.Atom.Satisfies (coreEnv base env) atom := by
  cases atom with
  | predicate predicate arguments =>
      simp only [FirstOrderProjection.Projectable.atom] at hProjectable
      simp only [coreAtom, Logic.FirstOrder.Formula.satisfies,
        Semantics.Atom.Satisfies, searchStructure]
      have hArguments :=
        coreTermList_eval base env arguments hProjectable
      exact iff_of_eq (congrArg (M.predicateInterp predicate) hArguments)
  | equal sort left right =>
      simp only [FirstOrderProjection.Projectable.atom,
        Bool.and_eq_true_iff] at hProjectable
      simp only [coreAtom, Logic.FirstOrder.Formula.satisfies,
        Semantics.Atom.Satisfies]
      rw [coreTerm_eval base env left hProjectable.1,
        coreTerm_eval base env right hProjectable.2]
      exact Iff.rfl
  | boolTerm term =>
      simp only [FirstOrderProjection.Projectable.atom] at hProjectable
      simp only [coreAtom, Logic.FirstOrder.Formula.satisfies,
        Semantics.Atom.Satisfies, searchStructure]
      simp only [List.map_cons, List.map_nil]
      have hTerm := coreTerm_eval base env term hProjectable
      exact iff_of_eq (congrArg M.boolHolds hTerm)

/-- canonical 文字翻译保持满足关系。 -/
theorem coreLiteral_satisfies {M : Semantics.Model.{x}}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (base : Semantics.Env M)
    (env : LogicSoundness.SetLevel.EnvAt.{x} (searchStructure M functionSort))
    (literal : CoreSyntax.NormalForm.Literal)
    (hProjectable : FirstOrderProjection.Projectable.literal literal = true) :
    DAGCertificate.Literal.Satisfies env (coreLiteral literal) ↔
      Semantics.Literal.Satisfies (coreEnv base env) literal := by
  cases literal with
  | mk positive atom =>
      have hAtom :
          Logic.FirstOrder.Formula.satisfies env (coreAtom atom) ↔
            Semantics.Atom.Satisfies (coreEnv base env) atom := by
        exact coreAtom_satisfies base env atom <| by
          simpa [FirstOrderProjection.Projectable.literal] using hProjectable
      cases positive with
      | false =>
          change (¬ Logic.FirstOrder.Formula.satisfies env (coreAtom atom)) ↔
            ¬ Semantics.Atom.Satisfies (coreEnv base env) atom
          exact not_congr hAtom
      | true =>
          exact hAtom

/-- core 字句成立时，其 canonical DAG 翻译也成立。 -/
theorem coreClause_satisfies {M : Semantics.Model.{x}}
    {functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)}
    (base : Semantics.Env M)
    (env : LogicSoundness.SetLevel.EnvAt.{x} (searchStructure M functionSort))
    (clause : CoreSyntax.NormalForm.Clause)
    (hProjectable : FirstOrderProjection.Projectable.clause clause = true)
    (hClause : Semantics.Clause.Satisfies (coreEnv base env) clause) :
    DAGCertificate.Clause.Satisfies env (coreClause clause) := by
  rcases hClause with ⟨literal, hMem, hLiteral⟩
  have hLiteralProjectable :
      FirstOrderProjection.Projectable.literal literal = true := by
    have hAll := Array.all_eq_true.mp hProjectable
    rcases Array.mem_iff_getElem.mp (Array.mem_def.mpr hMem) with
      ⟨index, hIndex, hGet⟩
    simpa [hGet] using hAll index hIndex
  apply DAGCertificate.Clause.satisfies_iff_exists_literal.mpr
  refine ⟨coreLiteral literal, ?_, ?_⟩
  · change coreLiteral literal ∈ (clause.map coreLiteral).toList
    rw [Array.toList_map]
    exact List.mem_map.mpr ⟨literal, hMem, rfl⟩
  · exact
      (coreLiteral_satisfies base env literal hLiteralProjectable).mpr hLiteral

/-- canonical 初始字句表在任意自由变量环境下都由 core 字句集语义支持。 -/
theorem coreClauseSet_valid {M : Semantics.Model.{x}}
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments))
    (base : Semantics.Env M) (hBaseFree : Semantics.Env.RespectsFree base)
    (clauses : CoreSyntax.NormalForm.ClauseSet)
    (hProjectable :
      FirstOrderProjection.Projectable.clauseSet clauses = true)
    (hClauses :
      ∀ env, Semantics.Env.RespectsFree env →
        Semantics.LocalSkolemChoice.SameBoundStack env base →
          Semantics.ClauseSet.Satisfies env clauses) :
    (DAGCertificate.ClauseProblem.mk (coreClauseSet clauses)).Valid
      (searchEnv functionSort base hBaseFree) := by
  intro targetEnv _
  intro index clause hClause
  rw [coreClauseSet, Array.getElem?_map] at hClause
  cases hCoreGet : clauses[index]? with
  | none =>
      simp [hCoreGet] at hClause
  | some coreClause =>
    simp only [hCoreGet, Option.map_some, Option.some.injEq] at hClause
    subst clause
    rcases Array.getElem?_eq_some_iff.mp hCoreGet with ⟨hIndex, hGet⟩
    let sourceEnv : Semantics.Env M := coreEnv base targetEnv
    have hSourceFree : Semantics.Env.RespectsFree sourceEnv := by
      intro sort id
      exact targetEnv.freeSort sort id
    have hSourceBound :
        Semantics.LocalSkolemChoice.SameBoundStack sourceEnv base := by
      intro boundIndex
      rfl
    have hAllClauses := hClauses sourceEnv hSourceFree hSourceBound
    have hCoreSat : Semantics.Clause.Satisfies sourceEnv coreClause := by
      apply hAllClauses coreClause
      exact Array.mem_def.mp <| by
        rw [← hGet]
        exact Array.getElem_mem hIndex
    have hAllProjectable := Array.all_eq_true.mp hProjectable
    have hCoreProjectable :
        FirstOrderProjection.Projectable.clause coreClause = true := by
      simpa [hGet] using hAllProjectable index hIndex
    exact coreClause_satisfies base targetEnv coreClause hCoreProjectable hCoreSat

end CoreProjectionSoundness
end SearchMaterialization
end Automation
end YesMetaZFC
