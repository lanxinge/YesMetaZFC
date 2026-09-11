import YesMetaZFC.Automation.DAGCertificate.CompileDAG
import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-!
# raw substitution 到内在 typed substitution 的编译

目标与源 free 上下文统一使用整图 replay registry。替换项的排序和作用域由返回类型
保证；缺失映射直接编译为同一 registry 变量的恒等项。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace Compile

open _root_.YesMetaZFC.Logic

variable {σ : Signature}

/-- raw free 变量替换直接通过 substitution lookup 化简。 -/
@[simp] theorem Term.applySubstitution_fvar_lookup
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (sort : σ.SortSymbol) (id : Nat) :
    Term.applySubstitution substitution (.var (.fvar sort id)) =
      match substitution.lookup sort id with
      | none => .var (.fvar sort id)
      | some replacement => replacement := by
  unfold Term.applySubstitution TermSubstitution.lookup
  cases hFind : List.find? (fun entry =>
      decide (entry.1 = sort) && entry.2.1 == id) substitution <;>
    rfl

@[simp] theorem Formula.applySubstitution_neg
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (body : Formula σ) :
    Formula.applySubstitution substitution (.neg body) =
      .neg (Formula.applySubstitution substitution body) :=
  rfl

@[simp] theorem Formula.applySubstitution_conj
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (left right : Formula σ) :
    Formula.applySubstitution substitution (.conj left right) =
      .conj (Formula.applySubstitution substitution left)
        (Formula.applySubstitution substitution right) :=
  rfl

@[simp] theorem Formula.applySubstitution_disj
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (left right : Formula σ) :
    Formula.applySubstitution substitution (.disj left right) =
      .disj (Formula.applySubstitution substitution left)
        (Formula.applySubstitution substitution right) :=
  rfl

@[simp] theorem Formula.applySubstitution_imp
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (left right : Formula σ) :
    Formula.applySubstitution substitution (.imp left right) =
      .imp (Formula.applySubstitution substitution left)
        (Formula.applySubstitution substitution right) :=
  rfl

@[simp] theorem Formula.applySubstitution_iff
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (left right : Formula σ) :
    Formula.applySubstitution substitution (.iff left right) =
      .iff (Formula.applySubstitution substitution left)
        (Formula.applySubstitution substitution right) :=
  rfl

@[simp] theorem Formula.applySubstitution_forallE
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (sort : σ.SortSymbol)
    (body : Formula σ) :
    Formula.applySubstitution substitution (.forallE sort body) =
      .forallE sort (Formula.applySubstitution substitution body) :=
  rfl

@[simp] theorem Formula.applySubstitution_existsE
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (sort : σ.SortSymbol)
    (body : Formula σ) :
    Formula.applySubstitution substitution (.existsE sort body) =
      .existsE sort (Formula.applySubstitution substitution body) :=
  rfl

/-- raw 析取列表逐项替换。 -/
theorem Formula.applySubstitution_disjunctionList
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) :
    ∀ formulas : List (Formula σ),
      Formula.applySubstitution substitution
          (Formula.disjunctionList formulas) =
        Formula.disjunctionList
          (formulas.map (Formula.applySubstitution substitution))
  | [] => rfl
  | [formula] => rfl
  | formula :: next :: rest => by
      simp [Formula.disjunctionList,
        Formula.applySubstitution_disjunctionList substitution
          (next :: rest)]

/-- 字面极性与 raw 替换交换。 -/
theorem Literal.toFormula_applySubstitution
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (literal : Literal σ) :
    (literal.applySubstitution substitution).toFormula =
      Formula.applySubstitution substitution literal.toFormula := by
  rcases literal with ⟨polarity, atom⟩
  cases polarity <;> rfl

/-- 字句析取公式与 raw 替换交换。 -/
theorem Clause.toFormula_applySubstitution
    [DecidableEq σ.SortSymbol]
    (substitution : TermSubstitution σ) (clause : Clause σ) :
    (clause.applySubstitution substitution).toFormula =
      Formula.applySubstitution substitution clause.toFormula := by
  rcases clause with ⟨literals⟩
  simp only [Clause.applySubstitution, Clause.toFormula, Array.toList_map,
    Formula.applySubstitution_disjunctionList, List.map_map]
  apply congrArg Formula.disjunctionList
  apply List.map_congr_left
  intro literal _hLiteral
  exact Literal.toFormula_applySubstitution substitution literal

/-- 单个 raw free 变量在替换下的 typed 目标项。 -/
def substitutionTerm? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    (sort : σ.SortSymbol) (id : Nat) :
    Option (Logic.FirstOrder.Term σ [] registry.context sort) :=
  match substitution.lookup sort id with
  | none => do
      let entry ← registry.find? sort id
      pure (.fvar entry)
  | some raw => do
      let compiled ← term? registry [] raw
      if hSort : compiled.sort = sort then
        pure (hSort ▸ compiled.term)
      else
        none

/-- 按 registry entries 的内在顺序构造 typed free substitution。 -/
private def compileSubstitutionIn?
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ) :
    (entries : List (σ.SortSymbol × Nat)) →
      Option (Logic.FirstOrder.VariableSubstitution σ
        (entries.map Prod.fst) [] registry.context)
  | [] =>
      some (show Logic.FirstOrder.VariableSubstitution σ [] []
          registry.context from
        fun {_sort} entry => nomatch entry)
  | (sort, id) :: rest => do
      let head ← substitutionTerm? registry substitution sort id
      let tail ← compileSubstitutionIn? registry substitution rest
      pure (show Logic.FirstOrder.VariableSubstitution σ
          (((sort, id) :: rest).map Prod.fst) [] registry.context from
        fun {_targetSort} entry =>
          match entry with
          | .here => head
          | .there previous => tail previous)

/-- 整图 registry 上的 typed free substitution。 -/
def compileSubstitution? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ) :
    Option (Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context) :=
  compileSubstitutionIn? registry substitution registry.entries

/-- lookup 成功的替换项确实来自原替换表中的同键条目。 -/
theorem TermSubstitution.lookup_mem
    [DecidableEq σ.SortSymbol]
    {substitution : TermSubstitution σ} {sort : σ.SortSymbol}
    {id : Nat} {replacement : Term σ}
    (hLookup : substitution.lookup sort id = some replacement) :
    (sort, id, replacement) ∈ substitution := by
  induction substitution with
  | nil =>
      simp [TermSubstitution.lookup] at hLookup
  | cons head tail ih =>
      rcases head with ⟨headSort, headId, headTerm⟩
      by_cases hMatch :
          (decide (headSort = sort) && headId == id) = true
      · have hParts : headSort = sort ∧ headId = id := by
          simpa using hMatch
        rcases hParts with ⟨rfl, rfl⟩
        have hTerm : headTerm = replacement := by
          simpa [TermSubstitution.lookup, hMatch] using hLookup
        subst replacement
        simp
      · have hTail :
            TermSubstitution.lookup tail sort id = some replacement := by
          simpa [TermSubstitution.lookup, hMatch] using hLookup
        exact List.mem_cons_of_mem _ (ih hTail)

/-- 单个 registry 键在排序正确且支持集已覆盖时必有 typed 替换项。 -/
private theorem substitutionTerm?_exists_of_wellSorted_of_support
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    (hWellSorted : TermSubstitution.WellSorted substitution)
    (hSupport : ∀ entry, entry ∈ substitution.freeSupport →
      entry ∈ registry.entries)
    {sort : σ.SortSymbol} {id : Nat}
    (hRegistry : (sort, id) ∈ registry.entries) :
    ∃ term, substitutionTerm? registry substitution sort id = some term := by
  cases hLookup : substitution.lookup sort id with
  | none =>
      rcases registry.find?_exists_of_mem_entries hRegistry with
        ⟨entry, hFind⟩
      exact ⟨.fvar entry, by simp [substitutionTerm?, hLookup, hFind]⟩
  | some replacement =>
      have hReplacementMem : (sort, id, replacement) ∈ substitution :=
        TermSubstitution.lookup_mem hLookup
      have hReplacementCheck : Term.check sort replacement = true :=
        List.all_eq_true.mp hWellSorted _ hReplacementMem
      have hReplacementInfer :
          Term.inferSortWith [] replacement = some sort := by
        simpa [Term.check, Term.checkAt] using hReplacementCheck
      have hReplacementSupport :
          ∀ entry, entry ∈ replacement.freeSupport →
            entry ∈ registry.entries := by
        intro entry hEntry
        apply hSupport entry
        exact List.mem_flatMap.mpr
          ⟨(sort, id, replacement), hReplacementMem, hEntry⟩
      rcases term?_exists_of_inferSortWith registry [] replacement sort
          hReplacementInfer hReplacementSupport with
        ⟨term, hCompile⟩
      exact ⟨term, by simp [substitutionTerm?, hLookup, hCompile]⟩

/-- 任意 registry 子列表上的 typed substitution 编译完备性。 -/
private theorem compileSubstitutionIn?_exists_of_wellSorted_of_support
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    (hWellSorted : TermSubstitution.WellSorted substitution)
    (hSupport : ∀ entry, entry ∈ substitution.freeSupport →
      entry ∈ registry.entries) :
    ∀ entries,
      (∀ entry, entry ∈ entries → entry ∈ registry.entries) →
      ∃ target,
        compileSubstitutionIn? registry substitution entries = some target
  | [], _hEntries => by
      refine ⟨(fun {_sort} entry => nomatch entry), ?_⟩
      rfl
  | (sort, id) :: rest, hEntries => by
      have hRegistry : (sort, id) ∈ registry.entries :=
        hEntries (sort, id) (by simp)
      rcases substitutionTerm?_exists_of_wellSorted_of_support
          registry substitution hWellSorted hSupport hRegistry with
        ⟨head, hHead⟩
      rcases compileSubstitutionIn?_exists_of_wellSorted_of_support
          registry substitution hWellSorted hSupport rest
          (by
            intro entry hEntry
            exact hEntries entry (by simp [hEntry])) with
        ⟨tail, hTail⟩
      refine ⟨(fun {_targetSort} entry =>
        match entry with
        | .here => head
        | .there previous => tail previous), ?_⟩
      simp [compileSubstitutionIn?, hHead, hTail]

/-- 排序检查与 registry 支持覆盖足以构造整图 typed substitution。 -/
theorem compileSubstitution?_exists_of_wellSorted_of_support
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    (hWellSorted : TermSubstitution.WellSorted substitution)
    (hSupport : ∀ entry, entry ∈ substitution.freeSupport →
      entry ∈ registry.entries) :
    ∃ target,
      compileSubstitution? registry substitution = some target := by
  apply compileSubstitutionIn?_exists_of_wellSorted_of_support
    registry substitution hWellSorted hSupport registry.entries
  intro entry hEntry
  exact hEntry

/-- entries 级编译与稳定变量查找逐点一致。 -/
private theorem compileSubstitutionIn?_findEntries?
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ) :
    ∀ entries target,
      compileSubstitutionIn? registry substitution entries = some target →
      ∀ {sort id entry},
        FreeRegistry.findEntries? entries sort id = some entry →
        ∃ term,
          substitutionTerm? registry substitution sort id = some term ∧
            target entry = term
  | [], target, hCompile, sort, id, entry, hFind => by
      simp [FreeRegistry.findEntries?] at hFind
  | (headSort, headId) :: rest, target, hCompile,
      sort, id, entry, hFind => by
      cases hHead : substitutionTerm? registry substitution headSort headId with
      | none =>
          simp [compileSubstitutionIn?, hHead] at hCompile
      | some headTerm =>
          cases hTail : compileSubstitutionIn? registry substitution rest with
          | none =>
              simp [compileSubstitutionIn?, hHead, hTail] at hCompile
          | some tail =>
              simp [compileSubstitutionIn?, hHead, hTail] at hCompile
              subst target
              simp only [FreeRegistry.findEntries?] at hFind
              split at hFind
              · subst sort
                split at hFind
                · subst id
                  simp at hFind
                  subst entry
                  exact ⟨headTerm, hHead, rfl⟩
                · cases hRest :
                    FreeRegistry.findEntries? rest headSort id with
                  | none => simp [hRest] at hFind
                  | some previous =>
                      simp [hRest] at hFind
                      subst entry
                      exact compileSubstitutionIn?_findEntries? registry
                        substitution rest tail hTail hRest
              · cases hRest : FreeRegistry.findEntries? rest sort id with
                | none => simp [hRest] at hFind
                | some previous =>
                    simp [hRest] at hFind
                    subst entry
                    exact compileSubstitutionIn?_findEntries? registry
                      substitution rest tail hTail hRest

/-- 成功编译对每个 registry 变量都产生唯一 typed 替换项。 -/
theorem compileSubstitution?_find?_exists
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    {target : Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context}
    (hCompile : compileSubstitution? registry substitution =
      @some (Logic.FirstOrder.VariableSubstitution σ
        registry.context [] registry.context) target)
    {sort id entry}
    (hFind : registry.find? sort id = some entry) :
    ∃ term,
      substitutionTerm? registry substitution sort id = some term ∧
        target entry = term :=
  compileSubstitutionIn?_findEntries? registry substitution
    registry.entries target hCompile hFind

/-- 整图 typed substitution 与 registry.find? 的逐点语义。 -/
theorem compileSubstitution?_find?
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    {target : Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context}
    (hCompile : compileSubstitution? registry substitution =
      @some (Logic.FirstOrder.VariableSubstitution σ
        registry.context [] registry.context) target)
    {sort id entry term}
    (hFind : registry.find? sort id = some entry)
    (hTerm : substitutionTerm? registry substitution sort id = some term) :
    target entry = term := by
  rcases compileSubstitution?_find?_exists registry substitution hCompile hFind with
    ⟨compiledTerm, hCompiledTerm, hTarget⟩
  exact hTarget.trans (Option.some.inj (hCompiledTerm.symm.trans hTerm))

mutual

/-- 从空 bound 上下文成功编译的 raw 项可规范嵌入任意 binder 上下文。 -/
theorem term?_embedBoundClosed
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (targetBound : Logic.FirstOrder.SortContext σ) :
    ∀ (raw : Term σ) (source : SomeTerm σ [] registry.context),
      term? registry [] raw = some source →
      term? registry targetBound raw =
        some ⟨source.sort, source.term.embedBoundClosed targetBound⟩
  | .var (.bvar sort index), source, hSource => by
      simp [boundVariable?] at hSource
  | .var (.fvar sort id), source, hSource => by
      cases hFind : registry.find? sort id with
      | none =>
          simp [hFind] at hSource
      | some entry =>
          simp [hFind] at hSource
          subst source
          simp [hFind]
  | .app function arguments, source, hSource => by
      cases hArguments : arguments? registry []
          (σ.funcDomain function) arguments with
      | none =>
          simp [hArguments] at hSource
      | some compiledArguments =>
          simp [hArguments] at hSource
          subst source
          rw [term?_app,
            arguments?_embedBoundClosed registry targetBound
              (σ.funcDomain function) arguments compiledArguments hArguments]
          simp
  termination_by raw source _ => raw.weight
  decreasing_by
    simp [Term.weight]

/-- 空 bound 上下文编译的参数列可规范嵌入任意 binder 上下文。 -/
theorem arguments?_embedBoundClosed
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (targetBound : Logic.FirstOrder.SortContext σ) :
    ∀ (sorts : List σ.SortSymbol) (raw : List (Term σ))
      (source : Logic.FirstOrder.Arguments σ [] registry.context sorts),
      arguments? registry [] sorts raw = some source →
      arguments? registry targetBound sorts raw =
        some (source.embedBoundClosed targetBound)
  | [], [], source, hSource => by
      simp at hSource
      subst source
      simp
  | [], _ :: _, source, hSource => by
      simp at hSource
  | _ :: _, [], source, hSource => by
      simp at hSource
  | sort :: sorts, head :: tail, source, hSource => by
      cases hHead : term? registry [] head with
      | none =>
          simp [hHead] at hSource
      | some compiledHead =>
          cases hTail : arguments? registry [] sorts tail with
          | none =>
              simp [hHead, hTail] at hSource
          | some compiledTail =>
              have hSort : compiledHead.sort = sort := by
                by_cases h : compiledHead.sort = sort
                · exact h
                · simp [arguments?_cons, hHead, hTail, h] at hSource
              simp [arguments?_cons, hHead, hTail, hSort] at hSource
              cases hSort
              subst source
              rw [arguments?_cons,
                term?_embedBoundClosed registry targetBound
                  head compiledHead hHead,
                arguments?_embedBoundClosed registry targetBound
                  sorts tail compiledTail hTail]
              simp
  termination_by sorts raw source _ => Term.weightList raw
  decreasing_by
    all_goals simp [Term.weightList]
    all_goals omega

end

mutual

/-- raw 项替换与内在 typed free 替换严格交换。 -/
theorem term?_applySubstitution
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    (bound : Logic.FirstOrder.SortContext σ)
    {target : Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context}
    (hCompile : compileSubstitution? registry substitution =
      @some (Logic.FirstOrder.VariableSubstitution σ
        registry.context [] registry.context) target) :
    ∀ (raw : Term σ) (source : SomeTerm σ bound registry.context),
      term? registry bound raw = some source →
      term? registry bound (raw.applySubstitution substitution) =
        some ⟨source.sort,
          Logic.FirstOrder.Term.substituteFree
            (Logic.FirstOrder.VariableSubstitution.embedBoundClosed
              bound target)
            source.term⟩
  | .var (.bvar sort index), source, hSource => by
      cases hEntry : boundVariable? bound sort index with
      | none =>
          simp [hEntry] at hSource
      | some entry =>
          simp [hEntry] at hSource
          subst source
          simp [Term.applySubstitution, hEntry,
            Logic.FirstOrder.Term.substituteFree,
            Logic.FirstOrder.Substitution.free_map,
            Logic.FirstOrder.VariableSubstitution.boundId,
            Logic.FirstOrder.Term.substitute,
            Logic.FirstOrder.Term.substituteMapped]
  | .var (.fvar sort id), source, hSource => by
      cases hFind : registry.find? sort id with
      | none =>
          simp [ hFind] at hSource
      | some entry =>
          simp [ hFind] at hSource
          subst source
          rcases compileSubstitution?_find?_exists registry substitution
              hCompile hFind with
            ⟨targetTerm, hTargetTerm, hTarget⟩
          cases hLookup : substitution.lookup sort id with
          | none =>
              have hIdentity : target entry = .fvar entry := by
                apply hTarget.trans
                exact Option.some.inj (hTargetTerm.symm.trans (by
                  simp [substitutionTerm?, hLookup, hFind]))
              rw [Term.applySubstitution_fvar_lookup, hLookup]
              simp [hFind, Logic.FirstOrder.Term.substituteFree,
                Logic.FirstOrder.Substitution.free_map,
                Logic.FirstOrder.Term.substitute,
                Logic.FirstOrder.Term.substituteMapped,
                Logic.FirstOrder.VariableSubstitution.embedBoundClosed,
                hIdentity]
          | some replacement =>
              cases hReplacement : term? registry [] replacement with
              | none =>
                  simp [substitutionTerm?, hLookup, hReplacement] at hTargetTerm
              | some compiledReplacement =>
                  have hSort : compiledReplacement.sort = sort := by
                    by_cases h : compiledReplacement.sort = sort
                    · exact h
                    · simp [substitutionTerm?, hLookup, hReplacement, h] at hTargetTerm
                  simp [substitutionTerm?, hLookup, hReplacement, hSort] at hTargetTerm
                  cases hSort
                  have hReplacementTerm :
                      target entry = compiledReplacement.term := by
                    exact hTarget.trans hTargetTerm.symm
                  have hReplacementBound :=
                    term?_embedBoundClosed registry bound replacement
                      compiledReplacement hReplacement
                  rw [Term.applySubstitution_fvar_lookup, hLookup,
                    hReplacementBound]
                  simp [
                    Logic.FirstOrder.Term.substituteFree,
                    Logic.FirstOrder.Substitution.free_map,
                    Logic.FirstOrder.Term.substitute,
                    Logic.FirstOrder.Term.substituteMapped,
                    Logic.FirstOrder.VariableSubstitution.embedBoundClosed,
                    hReplacementTerm]
  | .app function arguments, source, hSource => by
      cases hArguments : arguments? registry bound
          (σ.funcDomain function) arguments with
      | none =>
          simp [ hArguments] at hSource
      | some compiledArguments =>
          simp [ hArguments] at hSource
          subst source
          rw [Term.applySubstitution, term?_app,
            arguments?_applySubstitution registry substitution bound hCompile
              (σ.funcDomain function) arguments compiledArguments hArguments]
          rfl
  termination_by raw source _ => raw.weight
  decreasing_by
    simp [Term.weight]

/-- raw 项列表替换与内在异质参数列替换严格交换。 -/
theorem arguments?_applySubstitution
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    (bound : Logic.FirstOrder.SortContext σ)
    {target : Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context}
    (hCompile : compileSubstitution? registry substitution =
      @some (Logic.FirstOrder.VariableSubstitution σ
        registry.context [] registry.context) target) :
    ∀ (sorts : List σ.SortSymbol) (raw : List (Term σ))
      (source : Logic.FirstOrder.Arguments σ bound registry.context sorts),
      arguments? registry bound sorts raw = some source →
      arguments? registry bound sorts
          (Term.applySubstitutionList substitution raw) =
        some (Logic.FirstOrder.Arguments.substituteFree
          (Logic.FirstOrder.VariableSubstitution.embedBoundClosed
            bound target)
          source)
  | [], [], source, hSource => by
      simp at hSource
      subst source
      simp [Term.applySubstitutionList,
        Logic.FirstOrder.Arguments.substituteFree,
        Logic.FirstOrder.Substitution.free_map,
        Logic.FirstOrder.Arguments.substitute,
        Logic.FirstOrder.Arguments.substituteMapped]
  | [], _ :: _, source, hSource => by
      simp at hSource
  | _ :: _, [], source, hSource => by
      simp at hSource
  | sort :: sorts, head :: tail, source, hSource => by
      cases hHead : term? registry bound head with
      | none =>
          simp [ hHead] at hSource
      | some compiledHead =>
          cases hTail : arguments? registry bound sorts tail with
          | none =>
              simp [ hHead, hTail] at hSource
          | some compiledTail =>
              have hSort : compiledHead.sort = sort := by
                by_cases h : compiledHead.sort = sort
                · exact h
                · simp [arguments?_cons, hHead, hTail, h] at hSource
              simp [arguments?_cons, hHead, hTail, hSort] at hSource
              cases hSort
              subst source
              rw [Term.applySubstitutionList,
                arguments?_cons,
                term?_applySubstitution registry substitution bound hCompile
                  head compiledHead hHead,
                arguments?_applySubstitution registry substitution bound hCompile
                  sorts tail compiledTail hTail]
              simp [Logic.FirstOrder.Arguments.substituteFree,
                Logic.FirstOrder.Substitution.free_map,
                Logic.FirstOrder.Arguments.substitute,
                Logic.FirstOrder.Arguments.substituteMapped,
                Logic.FirstOrder.Term.substituteFree,
                Logic.FirstOrder.Term.substitute]
  termination_by sorts raw source _ => Term.weightList raw
  decreasing_by
    all_goals simp [Term.weightList]
    all_goals omega

end

/-- raw 公式替换与内在 typed free 替换严格交换。 -/
theorem formula?_applySubstitution
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    {target : Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context}
    (hCompile : compileSubstitution? registry substitution =
      @some (Logic.FirstOrder.VariableSubstitution σ
        registry.context [] registry.context) target) :
    ∀ (bound : Logic.FirstOrder.SortContext σ) (raw : Formula σ)
      (source : Logic.FirstOrder.Formula σ bound registry.context),
      formula? registry bound raw = some source →
      formula? registry bound (raw.applySubstitution substitution) =
        some (Logic.FirstOrder.Formula.substituteFree
          (Logic.FirstOrder.VariableSubstitution.embedBoundClosed
            bound target)
          source)
  | bound, .falsum, source, hSource => by
      simp [formula?] at hSource
      subst source
      rfl
  | bound, .truth, source, hSource => by
      simp [formula?] at hSource
      subst source
      rfl
  | bound, .rel relation arguments, source, hSource => by
      cases hArguments : arguments? registry bound
          (σ.relDomain relation) arguments with
      | none =>
          simp [formula?, hArguments] at hSource
      | some compiledArguments =>
          simp [formula?, hArguments] at hSource
          subst source
          rw [Formula.applySubstitution, Formula.mapTerms,
            ← Term.applySubstitutionList_eq_map substitution arguments,
            formula?,
            arguments?_applySubstitution registry substitution bound hCompile
              (σ.relDomain relation) arguments compiledArguments hArguments]
          simp [Logic.FirstOrder.Formula.substituteFree,
            Logic.FirstOrder.Substitution.free_map,
            Logic.FirstOrder.Formula.substitute,
            Logic.FirstOrder.Formula.substituteMapped,
            Logic.FirstOrder.Arguments.substituteFree,
            Logic.FirstOrder.Arguments.substitute]
  | bound, .equal left right, source, hSource => by
      cases hLeft : term? registry bound left with
      | none =>
          simp [formula?, hLeft] at hSource
      | some compiledLeft =>
          cases hRight : term? registry bound right with
          | none =>
              simp [formula?, hLeft, hRight] at hSource
          | some compiledRight =>
              rcases compiledLeft with ⟨leftSort, leftTerm⟩
              rcases compiledRight with ⟨rightSort, rightTerm⟩
              have hSort : leftSort = rightSort := by
                by_cases h : leftSort = rightSort
                · exact h
                · simp [formula?, hLeft, hRight, h] at hSource
              simp [formula?, hLeft, hRight, hSort] at hSource
              cases hSort
              subst source
              rw [Formula.applySubstitution, Formula.mapTerms, formula?,
                term?_applySubstitution registry substitution bound hCompile
                  left ⟨leftSort, leftTerm⟩ hLeft,
                term?_applySubstitution registry substitution bound hCompile
                  right ⟨leftSort, rightTerm⟩ hRight]
              simp [Logic.FirstOrder.Formula.substituteFree,
                Logic.FirstOrder.Substitution.free_map,
                Logic.FirstOrder.Formula.substitute,
                Logic.FirstOrder.Formula.substituteMapped,
                Logic.FirstOrder.Term.substituteFree,
                Logic.FirstOrder.Term.substitute]
  | bound, .neg body, source, hSource => by
      cases hBody : formula? registry bound body with
      | none =>
          simp [formula?, hBody] at hSource
      | some compiledBody =>
          simp [formula?, hBody] at hSource
          subst source
          rw [Formula.applySubstitution_neg, formula?,
            formula?_applySubstitution registry substitution hCompile
            bound body compiledBody hBody]
          rfl
  | bound, .conj left right, source, hSource
  | bound, .disj left right, source, hSource
  | bound, .imp left right, source, hSource
  | bound, .iff left right, source, hSource => by
      cases hLeft : formula? registry bound left with
      | none =>
          simp [formula?, hLeft] at hSource
      | some compiledLeft =>
          cases hRight : formula? registry bound right with
          | none =>
              simp [formula?, hLeft, hRight] at hSource
          | some compiledRight =>
              simp [formula?, hLeft, hRight] at hSource
              subst source
              first
              | rw [Formula.applySubstitution_conj]
              | rw [Formula.applySubstitution_disj]
              | rw [Formula.applySubstitution_imp]
              | rw [Formula.applySubstitution_iff]
              rw [formula?,
                formula?_applySubstitution registry substitution hCompile
                  bound left compiledLeft hLeft,
                formula?_applySubstitution registry substitution hCompile
                  bound right compiledRight hRight]
              rfl
  | bound, .forallE sort body, source, hSource
  | bound, .existsE sort body, source, hSource => by
      cases hBody : formula? registry (sort :: bound) body with
      | none =>
          simp [formula?, hBody] at hSource
      | some compiledBody =>
          simp [formula?, hBody] at hSource
          subst source
          first
          | rw [Formula.applySubstitution_forallE]
          | rw [Formula.applySubstitution_existsE]
          rw [formula?,
            formula?_applySubstitution registry substitution hCompile
            (sort :: bound) body compiledBody hBody]
          simp [Logic.FirstOrder.Formula.substituteFree,
            Logic.FirstOrder.Substitution.free_map,
            Logic.FirstOrder.Formula.substitute,
            Logic.FirstOrder.Formula.substituteMapped]

/-- raw 字句替换编译为内在开公式替换。 -/
theorem clauseFormula?_applySubstitution
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (substitution : TermSubstitution σ)
    {target : Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context}
    (hCompile : compileSubstitution? registry substitution =
      @some (Logic.FirstOrder.VariableSubstitution σ
        registry.context [] registry.context) target)
    (clause : Clause σ)
    {source : Logic.FirstOrder.OpenFormula σ registry.context}
    (hSource : clauseFormula? registry clause = some source) :
    clauseFormula? registry (clause.applySubstitution substitution) =
      some (Logic.FirstOrder.Formula.substituteFree target source) := by
  unfold clauseFormula? at hSource ⊢
  rw [Clause.toFormula_applySubstitution,
    formula?_applySubstitution registry substitution hCompile
      [] clause.toFormula source hSource]
  simp

/-- 目标编译字句是源编译公式的唯一 typed 替换结果。 -/
theorem CompiledClause.formula_eq_substituteFree
    [DecidableEq σ.SortSymbol]
    {registry : FreeRegistry σ}
    (source targetClause : CompiledClause registry)
    (substitution : TermSubstitution σ)
    {target : Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context}
    (hCompile : compileSubstitution? registry substitution =
      @some (Logic.FirstOrder.VariableSubstitution σ
        registry.context [] registry.context) target)
    (hRaw : targetClause.raw =
      source.raw.applySubstitution substitution) :
    targetClause.formula =
      Logic.FirstOrder.Formula.substituteFree target source.formula := by
  apply Option.some.inj
  calc
    some targetClause.formula =
        clauseFormula? registry targetClause.raw :=
      targetClause.compiled.symm
    _ = clauseFormula? registry
        (source.raw.applySubstitution substitution) := by rw [hRaw]
    _ = some (Logic.FirstOrder.Formula.substituteFree
        target source.formula) :=
      clauseFormula?_applySubstitution registry substitution hCompile
        source.raw source.compiled

/-- 成功编译的 raw substitution。 -/
structure CheckedSubstitution [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (raw : TermSubstitution σ) where
  private mkInternal ::
  substitution : Logic.FirstOrder.VariableSubstitution σ
    registry.context [] registry.context
  compiled : compileSubstitution? registry raw =
    @some (Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context) substitution

namespace CheckedSubstitution

def compile? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (raw : TermSubstitution σ) :
    Option (CheckedSubstitution registry raw) :=
  match hCompile : compileSubstitution? registry raw with
  | none => none
  | some substitution => some ⟨substitution, hCompile⟩

def of_compilation [DecidableEq σ.SortSymbol]
    {registry : FreeRegistry σ} {raw : TermSubstitution σ}
    {substitution : Logic.FirstOrder.VariableSubstitution σ
      registry.context [] registry.context}
    (hCompile : compileSubstitution? registry raw =
      @some (Logic.FirstOrder.VariableSubstitution σ
        registry.context [] registry.context) substitution) :
    CheckedSubstitution registry raw :=
  ⟨substitution, hCompile⟩

end CheckedSubstitution

end Compile
end DAGCertificate
end Automation
end YesMetaZFC
