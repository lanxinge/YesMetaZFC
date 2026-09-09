import YesMetaZFC.Automation.DAGCertificate.CompileDAG
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Semantics

/-!
# raw offset 改名到内在 typed free-renaming 的编译

标准化改名只作用于指定支持集；registry 中其余变量走恒等快路径。这样得到的总
`VariableRenaming` 可直接作用于内在 AST，而不需要构造 raw substitution 中间层。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace Compile

open _root_.YesMetaZFC.Logic

universe x

variable {σ : Signature}

@[simp] theorem Formula.renameFreeVars_neg (offset : Nat)
    (body : Formula σ) :
    Formula.renameFreeVars offset (.neg body) =
      .neg (Formula.renameFreeVars offset body) :=
  rfl

@[simp] theorem Formula.renameFreeVars_conj (offset : Nat)
    (left right : Formula σ) :
    Formula.renameFreeVars offset (.conj left right) =
      .conj (Formula.renameFreeVars offset left)
        (Formula.renameFreeVars offset right) :=
  rfl

@[simp] theorem Formula.renameFreeVars_disj (offset : Nat)
    (left right : Formula σ) :
    Formula.renameFreeVars offset (.disj left right) =
      .disj (Formula.renameFreeVars offset left)
        (Formula.renameFreeVars offset right) :=
  rfl

@[simp] theorem Formula.renameFreeVars_imp (offset : Nat)
    (left right : Formula σ) :
    Formula.renameFreeVars offset (.imp left right) =
      .imp (Formula.renameFreeVars offset left)
        (Formula.renameFreeVars offset right) :=
  rfl

@[simp] theorem Formula.renameFreeVars_iff (offset : Nat)
    (left right : Formula σ) :
    Formula.renameFreeVars offset (.iff left right) =
      .iff (Formula.renameFreeVars offset left)
        (Formula.renameFreeVars offset right) :=
  rfl

@[simp] theorem Formula.renameFreeVars_forallE (offset : Nat)
    (sort : σ.SortSymbol) (body : Formula σ) :
    Formula.renameFreeVars offset (.forallE sort body) =
      .forallE sort (Formula.renameFreeVars offset body) :=
  rfl

@[simp] theorem Formula.renameFreeVars_existsE (offset : Nat)
    (sort : σ.SortSymbol) (body : Formula σ) :
    Formula.renameFreeVars offset (.existsE sort body) =
      .existsE sort (Formula.renameFreeVars offset body) :=
  rfl

private def offsetEntry (offset : Nat) (entry : σ.SortSymbol × Nat) :
    σ.SortSymbol × Nat :=
  (entry.1, entry.2 + offset)

/-- `flatMap` 后逐点映射等于先逐段映射再拼接。 -/
private theorem flatMap_map_right
    {α β γ : Type} (segments : α → List β) (transform : β → γ) :
    ∀ input : List α,
      input.flatMap (fun item => (segments item).map transform) =
        (input.flatMap segments).map transform
  | [] => rfl
  | head :: tail => by
      simp [flatMap_map_right segments transform tail]

mutual

/-- 项改名把 free 支持逐点映射到 offset 后的键。 -/
theorem Term.freeSupport_renameFreeVars (offset : Nat) :
    ∀ term : Term σ,
      (term.renameFreeVars offset).freeSupport =
        term.freeSupport.map (offsetEntry offset)
  | .var (.fvar sort id) => by
      simp [Term.renameFreeVars, Term.freeSupport, offsetEntry]
  | .var (.bvar sort index) => by
      simp [Term.renameFreeVars, Term.freeSupport]
  | .app function arguments => by
      simp [Term.renameFreeVars, Term.freeSupport,
        Term.freeSupportList_renameFreeVars offset arguments]

/-- 参数列改名把联合 free 支持逐点映射到 offset 后的键。 -/
theorem Term.freeSupportList_renameFreeVars (offset : Nat) :
    ∀ terms : List (Term σ),
      (Term.renameFreeVarsList offset terms).flatMap Term.freeSupport =
        (terms.flatMap Term.freeSupport).map (offsetEntry offset)
  | [] => rfl
  | term :: rest => by
      simp [Term.renameFreeVarsList,
        Term.freeSupport_renameFreeVars offset term,
        Term.freeSupportList_renameFreeVars offset rest]

end

/-- 公式改名把 free 支持逐点映射到 offset 后的键。 -/
theorem Formula.freeSupport_renameFreeVars (offset : Nat) :
    ∀ formula : Formula σ,
      (formula.renameFreeVars offset).freeSupport =
        formula.freeSupport.map (offsetEntry offset)
  | .falsum => rfl
  | .truth => rfl
  | .rel relation arguments => by
      simp [Formula.renameFreeVars, Formula.mapTerms, Formula.freeSupport,
        ← Term.renameFreeVarsList_eq_map offset arguments,
        Term.freeSupportList_renameFreeVars offset arguments]
  | .equal left right => by
      simp [Formula.renameFreeVars, Formula.mapTerms, Formula.freeSupport,
        Term.freeSupport_renameFreeVars offset left,
        Term.freeSupport_renameFreeVars offset right]
  | .neg body => by
      simpa [Formula.freeSupport] using
        Formula.freeSupport_renameFreeVars offset body
  | .conj left right => by
      simp [Formula.freeSupport,
        Formula.freeSupport_renameFreeVars offset left,
        Formula.freeSupport_renameFreeVars offset right]
  | .disj left right => by
      simp [Formula.freeSupport,
        Formula.freeSupport_renameFreeVars offset left,
        Formula.freeSupport_renameFreeVars offset right]
  | .imp left right => by
      simp [Formula.freeSupport,
        Formula.freeSupport_renameFreeVars offset left,
        Formula.freeSupport_renameFreeVars offset right]
  | .iff left right => by
      simp [Formula.freeSupport,
        Formula.freeSupport_renameFreeVars offset left,
        Formula.freeSupport_renameFreeVars offset right]
  | .forallE sort body => by
      simpa [Formula.freeSupport] using
        Formula.freeSupport_renameFreeVars offset body
  | .existsE sort body => by
      simpa [Formula.freeSupport] using
        Formula.freeSupport_renameFreeVars offset body

/-- 字面改名把 free 支持逐点映射到 offset 后的键。 -/
theorem Literal.freeSupport_renameFreeVars
    (offset : Nat) (literal : Literal σ) :
    (literal.renameFreeVars offset).freeSupport =
      literal.freeSupport.map (offsetEntry offset) := by
  rcases literal with ⟨polarity, atom⟩
  exact Formula.freeSupport_renameFreeVars offset atom

/-- 字句改名把 free 支持逐点映射到 offset 后的键。 -/
theorem Clause.freeSupport_renameFreeVars
    (offset : Nat) (clause : Clause σ) :
    (clause.renameFreeVars offset).freeSupport =
      clause.freeSupport.map (offsetEntry offset) := by
  rcases clause with ⟨literals⟩
  simp [Clause.renameFreeVars, Clause.freeSupport, Array.toList_map,
    List.flatMap_map, Literal.freeSupport_renameFreeVars,
    flatMap_map_right]

/-- 原字句中的每个 free 键在 offset 改名后都出现为对应目标键。 -/
theorem Clause.mem_freeSupport_renameFreeVars
    (offset : Nat) (clause : Clause σ)
    {entry : σ.SortSymbol × Nat}
    (hEntry : entry ∈ clause.freeSupport) :
    (entry.1, entry.2 + offset) ∈
      (clause.renameFreeVars offset).freeSupport := by
  rw [Clause.freeSupport_renameFreeVars]
  exact List.mem_map.mpr ⟨entry, hEntry, rfl⟩

/-- raw 析取列表逐项 offset 改名。 -/
theorem Formula.renameFreeVars_disjunctionList (offset : Nat) :
    ∀ formulas : List (Formula σ),
      Formula.renameFreeVars offset
          (Formula.disjunctionList formulas) =
        Formula.disjunctionList
          (formulas.map (Formula.renameFreeVars offset))
  | [] => rfl
  | [formula] => rfl
  | formula :: next :: rest => by
      change Formula.disj (Formula.renameFreeVars offset formula)
          (Formula.renameFreeVars offset
            (Formula.disjunctionList (next :: rest))) =
        Formula.disj (Formula.renameFreeVars offset formula)
          (Formula.disjunctionList
            ((next :: rest).map (Formula.renameFreeVars offset)))
      rw [Formula.renameFreeVars_disjunctionList offset (next :: rest)]

/-- raw 析取列表的 free 支持是逐项支持之和。 -/
theorem Formula.freeSupport_disjunctionList :
    ∀ formulas : List (Formula σ),
      (Formula.disjunctionList formulas).freeSupport =
        formulas.flatMap Formula.freeSupport
  | [] => rfl
  | [formula] => by simp [Formula.disjunctionList]
  | formula :: next :: rest => by
      change formula.freeSupport ++
          (Formula.disjunctionList (next :: rest)).freeSupport =
        formula.freeSupport ++
          (next :: rest).flatMap Formula.freeSupport
      rw [Formula.freeSupport_disjunctionList (next :: rest)]

/-- 字面极性与 raw offset 改名交换。 -/
theorem Literal.toFormula_renameFreeVars
    (offset : Nat) (literal : Literal σ) :
    (literal.renameFreeVars offset).toFormula =
      Formula.renameFreeVars offset literal.toFormula := by
  rcases literal with ⟨polarity, atom⟩
  cases polarity <;> rfl

/-- 字面公式不改变原子的 free 支持。 -/
theorem Literal.toFormula_freeSupport (literal : Literal σ) :
    literal.toFormula.freeSupport = literal.freeSupport := by
  rcases literal with ⟨polarity, atom⟩
  cases polarity <;> rfl

/-- 字句析取公式与 raw offset 改名交换。 -/
theorem Clause.toFormula_renameFreeVars
    (offset : Nat) (clause : Clause σ) :
    (clause.renameFreeVars offset).toFormula =
      Formula.renameFreeVars offset clause.toFormula := by
  rcases clause with ⟨literals⟩
  simp only [Clause.renameFreeVars, Clause.toFormula, Array.toList_map,
    Formula.renameFreeVars_disjunctionList, List.map_map]
  apply congrArg Formula.disjunctionList
  apply List.map_congr_left
  intro literal _hLiteral
  exact Literal.toFormula_renameFreeVars offset literal

/-- 字句析取公式与字句本身具有相同 free 支持。 -/
theorem Clause.toFormula_freeSupport (clause : Clause σ) :
    clause.toFormula.freeSupport = clause.freeSupport := by
  rcases clause with ⟨literals⟩
  simp [Clause.toFormula, Clause.freeSupport,
    Formula.freeSupport_disjunctionList, List.flatMap_map,
    Literal.toFormula_freeSupport]

/-- 单个 registry 键的选择性 offset 目标。 -/
def renamingVariable? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    (sort : σ.SortSymbol) (id : Nat) :
    Option (Logic.FirstOrder.Variable registry.context sort) :=
  if support.contains (sort, id) then
    registry.find? sort (id + offset)
  else
    registry.find? sort id

/-- 按 registry entries 的内在顺序构造总 free-renaming。 -/
private def compileRenamingIn?
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat) :
    (entries : List (σ.SortSymbol × Nat)) →
      Option (Logic.FirstOrder.VariableRenaming
        (entries.map Prod.fst) registry.context)
  | [] => some (fun entry => nomatch entry)
  | (sort, id) :: rest =>
      match renamingVariable? registry support offset sort id,
          compileRenamingIn? registry support offset rest with
      | some head, some tail =>
          some (fun entry =>
            match entry with
            | .here => head
            | .there previous => tail previous)
      | _, _ => none

/-- 固定 registry 上的选择性 offset free-renaming。 -/
def compileRenaming? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat) :
    Option (Logic.FirstOrder.VariableRenaming
      registry.context registry.context) :=
  compileRenamingIn? registry support offset registry.entries

/-- entries 级编译与稳定变量查找逐点一致。 -/
private theorem compileRenamingIn?_findEntries?
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat) :
    ∀ entries ρ,
      compileRenamingIn? registry support offset entries =
        @some (Logic.FirstOrder.VariableRenaming
          (entries.map Prod.fst) registry.context) ρ →
      ∀ {sort id entry},
        FreeRegistry.findEntries? entries sort id = some entry →
        ∃ target,
          renamingVariable? registry support offset sort id = some target ∧
            ρ entry = target
  | [], ρ, hCompile, sort, id, entry, hFind => by
      simp [FreeRegistry.findEntries?] at hFind
  | (headSort, headId) :: rest, ρ, hCompile,
      sort, id, entry, hFind => by
      cases hHead : renamingVariable? registry support offset
          headSort headId with
      | none =>
          simp [compileRenamingIn?, hHead] at hCompile
      | some headTarget =>
          cases hTail : compileRenamingIn? registry support offset rest with
          | none =>
              simp [compileRenamingIn?, hHead, hTail] at hCompile
          | some tail =>
              simp [compileRenamingIn?, hHead, hTail] at hCompile
              subst ρ
              simp only [FreeRegistry.findEntries?] at hFind
              split at hFind
              · subst sort
                split at hFind
                · subst id
                  simp at hFind
                  subst entry
                  exact ⟨headTarget, hHead, rfl⟩
                · cases hRest : FreeRegistry.findEntries? rest headSort id with
                  | none => simp [hRest] at hFind
                  | some previous =>
                      simp [hRest] at hFind
                      subst entry
                      exact compileRenamingIn?_findEntries? registry support
                        offset rest tail hTail hRest
              · cases hRest : FreeRegistry.findEntries? rest sort id with
                | none => simp [hRest] at hFind
                | some previous =>
                    simp [hRest] at hFind
                    subst entry
                    exact compileRenamingIn?_findEntries? registry support
                      offset rest tail hTail hRest

/-- 成功编译的 free-renaming 在任一 registry 变量上与单键选择一致。 -/
theorem compileRenaming?_find?
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    {ρ : Logic.FirstOrder.VariableRenaming
      registry.context registry.context}
    (hCompile : compileRenaming? registry support offset =
      @some (Logic.FirstOrder.VariableRenaming
        registry.context registry.context) ρ)
    {sort id source target}
    (hSource : registry.find? sort id = some source)
    (hTarget : renamingVariable? registry support offset sort id = some target) :
    ρ source = target := by
  rcases compileRenamingIn?_findEntries? registry support offset
      registry.entries ρ hCompile hSource with
    ⟨compiledTarget, hCompiledTarget, hRename⟩
  exact hRename.trans <| Option.some.inj
    (hCompiledTarget.symm.trans hTarget)

/-- 单键目标在源键已注册且 offset 支持已覆盖时必存在。 -/
private theorem renamingVariable?_exists_of_support
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    {sort : σ.SortSymbol} {id : Nat}
    (hSource : (sort, id) ∈ registry.entries)
    (hTargetSupport : ∀ entry, entry ∈ support →
      (entry.1, entry.2 + offset) ∈ registry.entries) :
    ∃ target, renamingVariable? registry support offset sort id = some target := by
  by_cases hMem : (sort, id) ∈ support
  · have hContains : support.contains (sort, id) = true := by
      simpa using hMem
    rcases registry.find?_exists_of_mem_entries
        (hTargetSupport (sort, id) hMem) with
      ⟨target, hFind⟩
    refine ⟨target, ?_⟩
    unfold renamingVariable?
    rw [hContains]
    exact hFind
  · have hContains : support.contains (sort, id) = false := by
      cases hValue : support.contains (sort, id) <;> simp_all
    rcases registry.find?_exists_of_mem_entries hSource with
      ⟨target, hFind⟩
    refine ⟨target, ?_⟩
    unfold renamingVariable?
    rw [hContains]
    exact hFind

/-- 选择性 offset-renaming 的编译完备性。 -/
theorem compileRenaming?_exists_of_support
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    (hTargetSupport : ∀ entry, entry ∈ support →
      (entry.1, entry.2 + offset) ∈ registry.entries) :
    ∃ ρ,
      compileRenaming? registry support offset =
        @some (Logic.FirstOrder.VariableRenaming
          registry.context registry.context) ρ := by
  suffices hComplete : ∀ entries,
      (∀ entry, entry ∈ entries → entry ∈ registry.entries) →
      ∃ ρ,
        compileRenamingIn? registry support offset entries =
          @some (Logic.FirstOrder.VariableRenaming
            (entries.map Prod.fst) registry.context) ρ by
    exact hComplete registry.entries (fun _ hEntry => hEntry)
  intro entries hEntries
  induction entries with
  | nil =>
      refine ⟨(fun entry => nomatch entry), ?_⟩
      rfl
  | cons head rest ih =>
      rcases head with ⟨sort, id⟩
      rcases renamingVariable?_exists_of_support registry support offset
          (hEntries (sort, id) (by simp)) hTargetSupport with
        ⟨headTarget, hHead⟩
      rcases ih (by
          intro entry hEntry
          exact hEntries entry (by simp [hEntry])) with
        ⟨tail, hTail⟩
      refine ⟨(fun entry =>
        match entry with
        | .here => headTarget
        | .there previous => tail previous), ?_⟩
      simp [compileRenamingIn?, hHead, hTail]
      apply funext
      intro resultSort
      apply funext
      intro entry
      cases entry <;> rfl

mutual

/-- raw offset 项改名与内在 typed free-renaming 严格交换。 -/
theorem term?_renameFreeVars
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    {ρ : Logic.FirstOrder.VariableRenaming
      registry.context registry.context}
    (hCompile : compileRenaming? registry support offset =
      @some (Logic.FirstOrder.VariableRenaming
        registry.context registry.context) ρ) :
    ∀ (bound : Logic.FirstOrder.SortContext σ) (raw : Term σ)
      (source : SomeTerm σ bound registry.context),
      term? registry bound raw = some source →
      (∀ entry, entry ∈ raw.freeSupport → entry ∈ support) →
      term? registry bound (raw.renameFreeVars offset) =
        some ⟨source.sort, source.term.renameFree ρ⟩
  | bound, .var (.bvar sort index), source, hSource, _hSupport => by
      cases hFind : boundVariable? bound sort index with
      | none => simp [hFind] at hSource
      | some entry =>
          simp [hFind] at hSource
          subst source
          change term? registry bound (.var (.bvar sort index)) =
            some ⟨sort, (Logic.FirstOrder.Term.bvar entry).renameFree ρ⟩
          rw [term?_bvar, hFind]
          rfl
  | bound, .var (.fvar sort id), source, hSource, hSupport => by
      cases hFind : registry.find? sort id with
      | none => simp [hFind] at hSource
      | some sourceEntry =>
          simp [hFind] at hSource
          subst source
          have hMem : (sort, id) ∈ support :=
            hSupport (sort, id) (by simp [Term.freeSupport])
          have hContains : support.contains (sort, id) = true := by
            simpa using hMem
          cases hTarget : registry.find? sort (id + offset) with
          | none =>
              rcases compileRenamingIn?_findEntries? registry support offset
                  registry.entries ρ hCompile hFind with
                ⟨target, hTargetCompile, _hRename⟩
              simp [renamingVariable?, hMem, hTarget] at hTargetCompile
          | some targetEntry =>
              have hRename : ρ sourceEntry = targetEntry :=
                compileRenaming?_find? registry support offset hCompile hFind
                  (by simp [renamingVariable?, hMem, hTarget])
              change term? registry bound (.var (.fvar sort (id + offset))) =
                some ⟨sort,
                  (Logic.FirstOrder.Term.fvar sourceEntry).renameFree ρ⟩
              rw [term?_fvar, hTarget]
              simp [Logic.FirstOrder.Term.renameFree,
                Logic.FirstOrder.Term.rename, Logic.FirstOrder.Renaming.free,
                Logic.FirstOrder.Term.renameMapped, hRename]
  | bound, .app function arguments, source, hSource, hSupport => by
      cases hArguments : arguments? registry bound
          (σ.funcDomain function) arguments with
      | none => simp [hArguments] at hSource
      | some compiledArguments =>
          simp [hArguments] at hSource
          subst source
          change term? registry bound
              (.app function (Term.renameFreeVarsList offset arguments)) =
            some ⟨σ.funcCodomain function,
              (Logic.FirstOrder.Term.app function compiledArguments).renameFree ρ⟩
          rw [term?_app,
            arguments?_renameFreeVars registry support offset (ρ := ρ)
              hCompile bound
              (σ.funcDomain function) arguments compiledArguments hArguments
              (by simpa [Term.freeSupport] using hSupport)]
          rfl
  termination_by bound raw source _ _ => raw.weight
  decreasing_by
    simp [Term.weight]

/-- raw offset 参数列改名与内在 typed free-renaming 严格交换。 -/
theorem arguments?_renameFreeVars
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    {ρ : Logic.FirstOrder.VariableRenaming
      registry.context registry.context}
    (hCompile : compileRenaming? registry support offset =
      @some (Logic.FirstOrder.VariableRenaming
        registry.context registry.context) ρ) :
    ∀ (bound : Logic.FirstOrder.SortContext σ)
      (sorts : List σ.SortSymbol) (raw : List (Term σ))
      (source : Logic.FirstOrder.Arguments σ bound registry.context sorts),
      arguments? registry bound sorts raw = some source →
      (∀ entry, entry ∈ raw.flatMap Term.freeSupport → entry ∈ support) →
      arguments? registry bound sorts (Term.renameFreeVarsList offset raw) =
        some (source.renameFree ρ)
  | bound, [], [], source, hSource, _hSupport => by
      simp at hSource
      subst source
      change arguments? registry bound [] [] =
        some ((Logic.FirstOrder.Arguments.nil).renameFree ρ)
      rw [arguments?_nil]
      rfl
  | bound, [], _ :: _, source, hSource, _hSupport => by
      simp at hSource
  | bound, _ :: _, [], source, hSource, _hSupport => by
      simp at hSource
  | bound, sort :: sorts, head :: tail, source, hSource, hSupport => by
      cases hHead : term? registry bound head with
      | none => simp [hHead] at hSource
      | some compiledHead =>
          cases hTail : arguments? registry bound sorts tail with
          | none => simp [hHead, hTail] at hSource
          | some compiledTail =>
              have hSort : compiledHead.sort = sort := by
                by_cases h : compiledHead.sort = sort
                · exact h
                · simp [arguments?_cons, hHead, hTail, h] at hSource
              simp [arguments?_cons, hHead, hTail, hSort] at hSource
              cases hSort
              subst source
              change arguments? registry bound (compiledHead.sort :: sorts)
                  (Term.renameFreeVars offset head ::
                    Term.renameFreeVarsList offset tail) =
                some ((Logic.FirstOrder.Arguments.cons
                  compiledHead.term compiledTail).renameFree ρ)
              rw [arguments?_cons,
                term?_renameFreeVars registry support offset (ρ := ρ)
                  hCompile bound
                  head compiledHead hHead
                  (by
                    intro entry hEntry
                    apply hSupport entry
                    simp [hEntry]),
                arguments?_renameFreeVars registry support offset (ρ := ρ)
                  hCompile
                  bound sorts tail compiledTail hTail
                  (by
                    intro entry hEntry
                    apply hSupport entry
                    simp [hEntry])]
              simp [Logic.FirstOrder.Arguments.renameFree,
                Logic.FirstOrder.Arguments.rename,
                Logic.FirstOrder.Renaming.free,
                Logic.FirstOrder.Arguments.renameMapped,
                Logic.FirstOrder.Term.renameFree,
                Logic.FirstOrder.Term.rename]
  termination_by bound sorts raw source _ _ => Term.weightList raw
  decreasing_by
    all_goals simp [Term.weightList]
    all_goals omega

end

/-- raw 公式 offset 改名与内在 typed free-renaming 严格交换。 -/
theorem formula?_renameFreeVars
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    {ρ : Logic.FirstOrder.VariableRenaming
      registry.context registry.context}
    (hCompile : compileRenaming? registry support offset =
      @some (Logic.FirstOrder.VariableRenaming
        registry.context registry.context) ρ) :
    ∀ (bound : Logic.FirstOrder.SortContext σ) (raw : Formula σ)
      (source : Logic.FirstOrder.Formula σ bound registry.context),
      formula? registry bound raw = some source →
      (∀ entry, entry ∈ raw.freeSupport → entry ∈ support) →
      formula? registry bound (raw.renameFreeVars offset) =
        some (source.renameFree ρ)
  | bound, .falsum, source, hSource, _hSupport => by
      simp [formula?] at hSource
      subst source
      rfl
  | bound, .truth, source, hSource, _hSupport => by
      simp [formula?] at hSource
      subst source
      rfl
  | bound, .rel relation arguments, source, hSource, hSupport => by
      cases hArguments : arguments? registry bound
          (σ.relDomain relation) arguments with
      | none =>
          simp [formula?, hArguments] at hSource
      | some compiledArguments =>
          simp [formula?, hArguments] at hSource
          subst source
          rw [Formula.renameFreeVars, Formula.mapTerms,
            ← Term.renameFreeVarsList_eq_map offset arguments,
            formula?,
            arguments?_renameFreeVars registry support offset (ρ := ρ)
              hCompile bound (σ.relDomain relation) arguments
              compiledArguments hArguments
              (by simpa [Formula.freeSupport] using hSupport)]
          simp [Logic.FirstOrder.Formula.renameFree,
            Logic.FirstOrder.Formula.rename,
            Logic.FirstOrder.Renaming.free,
            Logic.FirstOrder.Formula.renameMapped,
            Logic.FirstOrder.Arguments.renameFree,
            Logic.FirstOrder.Arguments.rename]
  | bound, .equal left right, source, hSource, hSupport => by
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
              rw [Formula.renameFreeVars, Formula.mapTerms, formula?,
                term?_renameFreeVars registry support offset (ρ := ρ)
                  hCompile bound left ⟨leftSort, leftTerm⟩ hLeft
                  (by
                    intro entry hEntry
                    apply hSupport entry
                    simp [Formula.freeSupport, hEntry]),
                term?_renameFreeVars registry support offset (ρ := ρ)
                  hCompile bound right ⟨leftSort, rightTerm⟩ hRight
                  (by
                    intro entry hEntry
                    apply hSupport entry
                    simp [Formula.freeSupport, hEntry])]
              simp [Logic.FirstOrder.Formula.renameFree,
                Logic.FirstOrder.Formula.rename,
                Logic.FirstOrder.Renaming.free,
                Logic.FirstOrder.Formula.renameMapped,
                Logic.FirstOrder.Term.renameFree,
                Logic.FirstOrder.Term.rename]
  | bound, .neg body, source, hSource, hSupport => by
      cases hBody : formula? registry bound body with
      | none =>
          simp [formula?, hBody] at hSource
      | some compiledBody =>
          simp [formula?, hBody] at hSource
          subst source
          rw [Formula.renameFreeVars_neg, formula?,
            formula?_renameFreeVars registry support offset hCompile
              bound body compiledBody hBody
              (by simpa [Formula.freeSupport] using hSupport)]
          rfl
  | bound, .conj left right, source, hSource, hSupport
  | bound, .disj left right, source, hSource, hSupport
  | bound, .imp left right, source, hSource, hSupport
  | bound, .iff left right, source, hSource, hSupport => by
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
              | rw [Formula.renameFreeVars_conj]
              | rw [Formula.renameFreeVars_disj]
              | rw [Formula.renameFreeVars_imp]
              | rw [Formula.renameFreeVars_iff]
              rw [formula?,
                formula?_renameFreeVars registry support offset hCompile
                  bound left compiledLeft hLeft
                  (by
                    intro entry hEntry
                    apply hSupport entry
                    simp [Formula.freeSupport, hEntry]),
                formula?_renameFreeVars registry support offset hCompile
                  bound right compiledRight hRight
                  (by
                    intro entry hEntry
                    apply hSupport entry
                    simp [Formula.freeSupport, hEntry])]
              rfl
  | bound, .forallE sort body, source, hSource, hSupport
  | bound, .existsE sort body, source, hSource, hSupport => by
      cases hBody : formula? registry (sort :: bound) body with
      | none =>
          simp [formula?, hBody] at hSource
      | some compiledBody =>
          simp [formula?, hBody] at hSource
          subst source
          first
          | rw [Formula.renameFreeVars_forallE]
          | rw [Formula.renameFreeVars_existsE]
          rw [formula?,
            formula?_renameFreeVars registry support offset hCompile
              (sort :: bound) body compiledBody hBody
              (by simpa [Formula.freeSupport] using hSupport)]
          simp [Logic.FirstOrder.Formula.renameFree,
            Logic.FirstOrder.Formula.rename,
            Logic.FirstOrder.Renaming.free,
            Logic.FirstOrder.Formula.renameMapped]

/-- raw 字句 offset 改名编译为内在开公式 free-renaming。 -/
theorem clauseFormula?_renameFreeVars
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    {ρ : Logic.FirstOrder.VariableRenaming
      registry.context registry.context}
    (hCompile : compileRenaming? registry support offset =
      @some (Logic.FirstOrder.VariableRenaming
        registry.context registry.context) ρ)
    (clause : Clause σ)
    {source : Logic.FirstOrder.OpenFormula σ registry.context}
    (hSource : clauseFormula? registry clause = some source)
    (hSupport : ∀ entry, entry ∈ clause.freeSupport → entry ∈ support) :
    clauseFormula? registry (clause.renameFreeVars offset) =
      some (source.renameFree ρ) := by
  unfold clauseFormula? at hSource ⊢
  rw [Clause.toFormula_renameFreeVars,
    formula?_renameFreeVars registry support offset hCompile
      [] clause.toFormula source hSource]
  intro entry hEntry
  exact hSupport entry (Clause.toFormula_freeSupport clause ▸ hEntry)

/-- 目标编译字句是源编译公式的唯一 typed free-renaming 结果。 -/
theorem CompiledClause.formula_eq_renameFree
    [DecidableEq σ.SortSymbol]
    {registry : FreeRegistry σ}
    (source target : CompiledClause registry)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    {ρ : Logic.FirstOrder.VariableRenaming
      registry.context registry.context}
    (hCompile : compileRenaming? registry support offset =
      @some (Logic.FirstOrder.VariableRenaming
        registry.context registry.context) ρ)
    (hSupport : ∀ entry, entry ∈ source.raw.freeSupport → entry ∈ support)
    (hRaw : target.raw = source.raw.renameFreeVars offset) :
    target.formula = source.formula.renameFree ρ := by
  apply Option.some.inj
  calc
    some target.formula = clauseFormula? registry target.raw :=
      target.compiled.symm
    _ = clauseFormula? registry (source.raw.renameFreeVars offset) := by
      rw [hRaw]
    _ = some (source.formula.renameFree ρ) :=
      clauseFormula?_renameFreeVars registry support offset hCompile
        source.raw source.compiled hSupport

/-- 全称有效的开公式在任意 typed free-renaming 下仍全称有效。 -/
theorem universallyValid_renameFree
    {M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ}
    {free : Logic.FirstOrder.SortContext σ}
    {formula : Logic.FirstOrder.OpenFormula σ free}
    (hValid : UniversallyValid M formula)
    (ρ : Logic.FirstOrder.VariableRenaming free free) :
    UniversallyValid M (formula.renameFree ρ) := by
  intro assignment
  unfold Logic.FirstOrder.Formula.renameFree
  rw [Logic.FirstOrder.Formula.satisfies_rename]
  let pulledAssignment : Logic.FirstOrder.Assignment M free :=
    fun entry => assignment (ρ entry)
  have hEnv :
      openEnv pulledAssignment =
        (openEnv assignment).pullbackRenaming
          (Logic.FirstOrder.Renaming.free ρ) := by
    apply Logic.FirstOrder.Env.ext
    · intro sort entry
      cases entry
    · intro sort entry
      rfl
  rw [← hEnv]
  exact hValid pulledAssignment

/-- offset 改名后的 compiled 字句继承源字句的全称真实性。 -/
theorem CompiledClause.trueIn_renameFreeVars
    [DecidableEq σ.SortSymbol]
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {registry : FreeRegistry σ}
    (source target : CompiledClause registry)
    (support : List (σ.SortSymbol × Nat)) (offset : Nat)
    {ρ : Logic.FirstOrder.VariableRenaming
      registry.context registry.context}
    (hCompile : compileRenaming? registry support offset =
      @some (Logic.FirstOrder.VariableRenaming
        registry.context registry.context) ρ)
    (hSupport : ∀ entry, entry ∈ source.raw.freeSupport → entry ∈ support)
    (hRaw : target.raw = source.raw.renameFreeVars offset)
    (hSource : source.TrueIn M) :
    target.TrueIn M := by
  apply (forallFree_trueIn_iff target.formula).mpr
  rw [source.formula_eq_renameFree target support offset
    hCompile hSupport hRaw]
  exact universallyValid_renameFree
    ((forallFree_trueIn_iff source.formula).mp hSource) ρ

end Compile
end DAGCertificate
end Automation
end YesMetaZFC
