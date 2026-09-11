import YesMetaZFC.Automation.DAGCertificate.CompileRenaming
import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Avatar
import YesMetaZFC.Model.FirstOrder.FreeVariableSupport

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace Compile

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

variable {σ : Signature}

theorem formula_exists_of_checkWith [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    ∀ (bound : SortContext σ) (raw : Formula σ),
      Formula.checkWith bound raw = true →
        (∀ entry, entry ∈ raw.freeSupport → entry ∈ registry.entries) →
          ∃ formula : Logic.FirstOrder.Formula σ bound registry.context,
            formula? registry bound raw = some formula := by
  intro bound raw
  induction raw generalizing bound with
  | falsum =>
      intro _hCheck _hSupport
      exact ⟨.falsum, by simp [formula?]⟩
  | truth =>
      intro _hCheck _hSupport
      exact ⟨.truth, by simp [formula?]⟩
  | rel relation arguments =>
      intro hCheck hSupport
      have hInfer :
          Term.inferSortListWith bound arguments =
            some (σ.relDomain relation) := by
        simpa [Formula.checkWith] using hCheck
      rcases arguments?_exists_of_inferSortListWith registry bound arguments
          (σ.relDomain relation) hInfer
          (by
            intro entry hEntry
            exact hSupport entry (by simp [Formula.freeSupport, hEntry])) with
        ⟨compiled, hCompiled⟩
      exact ⟨.rel relation compiled, by simp [formula?, hCompiled]⟩
  | equal left right =>
      intro hCheck hSupport
      unfold Formula.checkWith at hCheck
      cases hLeft : Term.inferSortWith bound left with
      | none => simp [hLeft] at hCheck
      | some leftSort =>
          cases hRight : Term.inferSortWith bound right with
          | none => simp [hLeft, hRight] at hCheck
          | some rightSort =>
              have hSort : leftSort = rightSort := by
                simpa [hLeft, hRight] using hCheck
              rcases term?_exists_of_inferSortWith registry bound left leftSort
                  hLeft (by
                    intro entry hEntry
                    exact hSupport entry
                      (by simp [Formula.freeSupport, hEntry])) with
                ⟨compiledLeft, hCompiledLeft⟩
              rcases term?_exists_of_inferSortWith registry bound right rightSort
                  hRight (by
                    intro entry hEntry
                    exact hSupport entry
                      (by simp [Formula.freeSupport, hEntry])) with
                ⟨compiledRight, hCompiledRight⟩
              subst rightSort
              exact ⟨.equal compiledLeft compiledRight, by
                simp [formula?, hCompiledLeft, hCompiledRight]⟩
  | neg body ih =>
      intro hCheck hSupport
      rcases ih bound (by simpa [Formula.checkWith] using hCheck)
          (by simpa [Formula.freeSupport] using hSupport) with
        ⟨compiled, hCompiled⟩
      exact ⟨.neg compiled, by simp [formula?, hCompiled]⟩
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      intro hCheck hSupport
      have hParts := Bool.and_eq_true_iff.mp hCheck
      have hLeftSupport : ∀ entry, entry ∈ left.freeSupport →
          entry ∈ registry.entries := by
        intro entry hEntry
        exact hSupport entry (by simp [Formula.freeSupport, hEntry])
      have hRightSupport : ∀ entry, entry ∈ right.freeSupport →
          entry ∈ registry.entries := by
        intro entry hEntry
        exact hSupport entry (by simp [Formula.freeSupport, hEntry])
      rcases ihLeft bound hParts.1 hLeftSupport with
        ⟨compiledLeft, hCompiledLeft⟩
      rcases ihRight bound hParts.2 hRightSupport with
        ⟨compiledRight, hCompiledRight⟩
      simp [formula?, hCompiledLeft, hCompiledRight]
  | forallE sort body ih =>
      intro hCheck hSupport
      rcases ih (sort :: bound)
          (by simpa [Formula.checkWith] using hCheck)
          (by simpa [Formula.freeSupport] using hSupport) with
        ⟨compiled, hCompiled⟩
      exact ⟨.forallE sort compiled, by simp [formula?, hCompiled]⟩
  | existsE sort body ih =>
      intro hCheck hSupport
      rcases ih (sort :: bound)
          (by simpa [Formula.checkWith] using hCheck)
          (by simpa [Formula.freeSupport] using hSupport) with
        ⟨compiled, hCompiled⟩
      exact ⟨.existsE sort compiled, by simp [formula?, hCompiled]⟩

theorem clauseFormula_exists_of_check [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) (clause : Clause σ)
    (hCheck : Clause.check clause = true)
    (hSupport : ∀ entry, entry ∈ clause.freeSupport →
      entry ∈ registry.entries) :
    ∃ formula : OpenFormula σ registry.context,
      clauseFormula? registry clause = some formula := by
  have hLiteralChecks :
      ∀ literal ∈ clause.literals.toList, Literal.check literal = true := by
    intro literal hLiteral
    exact array_check_of_mem (by simpa [Clause.check] using hCheck)
      hLiteral
  have hFormulaChecks :
      ∀ formula ∈ clause.literals.toList.map Literal.toFormula,
        Formula.check formula = true := by
    intro formula hFormula
    rcases List.mem_map.mp hFormula with ⟨literal, hLiteral, rfl⟩
    simp only [Literal.check] at hLiteralChecks ⊢
    cases hPolarity : literal.polarity with
    | false =>
        simpa [Literal.toFormula, hPolarity, Formula.check,
          Formula.checkWith] using hLiteralChecks literal hLiteral
    | true =>
        simpa [Literal.toFormula, hPolarity, Formula.check,
          Formula.checkWith] using hLiteralChecks literal hLiteral
  have hFormulaCheckList :
      ∀ formulas : List (Formula σ),
        (∀ formula ∈ formulas, Formula.check formula = true) →
          Formula.check (Formula.disjunctionList formulas) = true := by
    intro formulas
    induction formulas with
    | nil =>
        intro _
        rfl
    | cons head tail ih =>
        intro hFormulas
        cases tail with
        | nil =>
            exact hFormulas head (by simp)
        | cons next rest =>
            simp only [Formula.disjunctionList, Formula.check,
              Formula.checkWith]
            apply Bool.and_eq_true_iff.mpr
            constructor
            · exact hFormulas head (by simp)
            · exact ih (by
                intro formula hFormula
                exact hFormulas formula (by simp [hFormula]))
  have hFormulaCheck : Formula.check clause.toFormula = true := by
    exact hFormulaCheckList
      (clause.literals.toList.map Literal.toFormula) hFormulaChecks
  rcases formula_exists_of_checkWith registry [] clause.toFormula
      hFormulaCheck (by
        intro entry hEntry
        apply hSupport entry
        exact Clause.toFormula_freeSupport clause ▸ hEntry) with
    ⟨formula, hFormula⟩
  exact ⟨formula, hFormula⟩

private theorem variable_context_getElem?_eq {S : Type} {Γ : List S} {s : S}
    (entry : Logic.FirstOrder.Variable Γ s) :
    Γ[entry.position]? = some s := by
  induction entry with
  | here => simp [Logic.FirstOrder.Variable.position, Logic.FirstOrder.Variable.index]
  | there entry ih =>
      simpa [Logic.FirstOrder.Variable.position,
        Logic.FirstOrder.Variable.index] using ih

private theorem variable_eq_of_position_eq {S : Type} {Γ : List S} {s : S}
    (left right : Logic.FirstOrder.Variable Γ s)
    (h : left.position = right.position) : left = right := by
  induction left with
  | here =>
      cases right with
      | here => rfl
      | there right =>
          simp [Logic.FirstOrder.Variable.position,
            Logic.FirstOrder.Variable.index] at h
  | there left ih =>
      cases right with
      | here =>
          simp [Logic.FirstOrder.Variable.position,
            Logic.FirstOrder.Variable.index] at h
      | there right =>
          apply congrArg (fun value => Logic.FirstOrder.Variable.there value)
          apply ih
          simpa [Logic.FirstOrder.Variable.position,
            Logic.FirstOrder.Variable.index] using h

private theorem variable_sigma_eq_of_position_eq {S : Type} {Γ : List S} {s t : S}
    (left : Logic.FirstOrder.Variable Γ s)
    (right : Logic.FirstOrder.Variable Γ t)
    (h : left.position = right.position) :
    Sigma.mk s left = Sigma.mk t right := by
  have hLeft := variable_context_getElem?_eq left
  have hRight := variable_context_getElem?_eq right
  have hAt : Γ[left.position]? = Γ[right.position]? :=
    congrArg (fun p => Γ[p]?) h
  have hSort : s = t :=
    Option.some.inj (hLeft.symm.trans (hAt.trans hRight))
  cases hSort
  have hEq := variable_eq_of_position_eq left right h
  cases hEq
  rfl

mutual

theorem term_support_of_compile
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    ∀ (bound : Logic.FirstOrder.SortContext σ) (raw : Term σ)
      (source : SomeTerm σ bound registry.context),
      term? registry bound raw = some source →
        ∀ {sort : σ.SortSymbol}
          (entry : Logic.FirstOrder.Variable registry.context sort),
          Logic.FirstOrder.Term.freeSupport source.term
              |>.Contains entry.position →
            ∃ id, (sort, id) ∈ raw.freeSupport ∧
              registry.find? sort id = some entry
  | bound, .var (.bvar rawSort index), source, hCompile => by
      cases hBound : boundVariable? bound rawSort index with
      | none => simp [ hBound] at hCompile
      | some found =>
          simp [ hBound] at hCompile
          subst source
          intro entry hSupport
          exact False.elim <| by
            simp [Logic.FirstOrder.Term.freeSupport,
              Logic.FirstOrder.FreeSupport.Contains,
              Logic.FirstOrder.FreeSupport.empty] at hSupport
  | bound, .var (.fvar rawSort id), source, hCompile => by
      cases hFind : registry.find? rawSort id with
      | none => simp [ hFind] at hCompile
      | some found =>
          simp [ hFind] at hCompile
          subst source
          intro entry hSupport
          have hSigma := variable_sigma_eq_of_position_eq entry found
            (by
              simpa [Logic.FirstOrder.Term.freeSupport,
                Logic.FirstOrder.FreeSupport.Contains,
                Logic.FirstOrder.FreeSupport.singleton] using hSupport)
          cases hSigma
          refine ⟨id, ?_, hFind⟩
          simp [Term.freeSupport]
  | bound, .app function arguments, source, hCompile => by
      cases hArguments : arguments? registry bound
          (σ.funcDomain function) arguments with
      | none => simp [ hArguments] at hCompile
      | some compiledArguments =>
          simp [ hArguments] at hCompile
          subst source
          intro entry hSupport
          have hArgsSupport :
              Logic.FirstOrder.Arguments.freeSupport compiledArguments
                |>.Contains entry.position := by
            simpa [Logic.FirstOrder.Term.freeSupport] using hSupport
          rcases arguments_support_of_compile registry bound
              (σ.funcDomain function) arguments compiledArguments hArguments
              entry hArgsSupport with
            ⟨rawTerm, hRawTerm, id, hId, hFind⟩
          refine ⟨id, ?_, hFind⟩
          simpa [YesMetaZFC.Automation.DAGCertificate.Term.freeSupport] using
            (List.mem_flatMap.mpr ⟨rawTerm, hRawTerm, hId⟩)

theorem arguments_support_of_compile
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    ∀ (bound : Logic.FirstOrder.SortContext σ)
      (sorts : List σ.SortSymbol) (raw : List (Term σ))
      (source : Logic.FirstOrder.Arguments σ bound registry.context sorts),
      arguments? registry bound sorts raw = some source →
        ∀ {sort : σ.SortSymbol}
          (entry : Logic.FirstOrder.Variable registry.context sort),
          Logic.FirstOrder.Arguments.freeSupport source
              |>.Contains entry.position →
            ∃ rawTerm, rawTerm ∈ raw ∧
              ∃ id, (sort, id) ∈ rawTerm.freeSupport ∧
                registry.find? sort id = some entry
  | bound, [], [], .nil, hCompile => by
      intro entry hSupport
      exact False.elim <| by
        simp [Logic.FirstOrder.Arguments.freeSupport,
        Logic.FirstOrder.FreeSupport.Contains,
        Logic.FirstOrder.FreeSupport.empty] at hSupport
  | bound, sort :: sorts, rawHead :: rawTail, source, hCompile => by
      cases hHead : term? registry bound rawHead with
      | none => simp [ hHead] at hCompile
      | some compiledHead =>
          cases hTail : arguments? registry bound sorts rawTail with
          | none => simp [ hHead, hTail] at hCompile
          | some compiledTail =>
              have hSort : compiledHead.sort = sort := by
                by_cases h : compiledHead.sort = sort
                · exact h
                · simp [ hHead, hTail, h] at hCompile
              simp [ hHead, hTail, hSort] at hCompile
              cases hSort
              subst source
              intro entry hSupport
              have hParts :
                  compiledHead.term.freeSupport.Contains entry.position ∨
                    compiledTail.freeSupport.Contains entry.position := by
                simpa [Logic.FirstOrder.Arguments.freeSupport,
                  Logic.FirstOrder.FreeSupport.Contains,
                  Logic.FirstOrder.FreeSupport.union,
                  Bool.or_eq_true] using hSupport
              rcases hParts with hHeadSupport | hTailSupport
              · rcases term_support_of_compile registry bound rawHead
                    ⟨compiledHead.sort, compiledHead.term⟩ hHead
                    entry hHeadSupport with
                  ⟨id, hId, hFind⟩
                exact ⟨rawHead, by simp, id, hId, hFind⟩
              · rcases arguments_support_of_compile registry bound sorts rawTail
                    compiledTail hTail entry hTailSupport with
                  ⟨rawTerm, hRawTerm, id, hId, hFind⟩
                exact ⟨rawTerm, by simp [hRawTerm], id, hId, hFind⟩
  | bound, [], _ :: _, source, hCompile => by
      simp at hCompile
  | bound, _ :: _, [], source, hCompile => by
      simp at hCompile

theorem formula_support_of_compile
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    ∀ (bound : Logic.FirstOrder.SortContext σ) (raw : Formula σ)
      (source : Logic.FirstOrder.Formula σ bound registry.context),
      formula? registry bound raw = some source →
        ∀ {sort : σ.SortSymbol}
          (entry : Logic.FirstOrder.Variable registry.context sort),
          Logic.FirstOrder.Formula.freeSupport source
              |>.Contains entry.position →
            ∃ id, (sort, id) ∈ raw.freeSupport ∧
              registry.find? sort id = some entry
  | bound, .falsum, source, hCompile => by
      simp [formula?] at hCompile
      subst source
      intro entry hSupport
      exact False.elim <| by
        simp [Logic.FirstOrder.Formula.freeSupport,
          Logic.FirstOrder.FreeSupport.Contains,
          Logic.FirstOrder.FreeSupport.empty] at hSupport
  | bound, .truth, source, hCompile => by
      simp [formula?] at hCompile
      subst source
      intro entry hSupport
      exact False.elim <| by
        simp [Logic.FirstOrder.Formula.freeSupport,
          Logic.FirstOrder.FreeSupport.Contains,
          Logic.FirstOrder.FreeSupport.empty] at hSupport
  | bound, .rel relation arguments, source, hCompile => by
      cases hArgs : arguments? registry bound
          (σ.relDomain relation) arguments with
      | none => simp [formula?, hArgs] at hCompile
      | some compiledArgs =>
          simp [formula?, hArgs] at hCompile
          subst source
          intro entry hSupport
          have hArgSupport :
              compiledArgs.freeSupport.Contains entry.position := by
            simpa [Logic.FirstOrder.Formula.freeSupport] using hSupport
          rcases arguments_support_of_compile registry bound
              (σ.relDomain relation) arguments compiledArgs hArgs
              entry hArgSupport with
            ⟨rawTerm, hRawTerm, id, hId, hFind⟩
          refine ⟨id, ?_, hFind⟩
          change (_, id) ∈ arguments.flatMap Term.freeSupport
          exact List.mem_flatMap.mpr ⟨rawTerm, hRawTerm, hId⟩
  | bound, .equal left right, source, hCompile => by
      cases hLeft : term? registry bound left with
      | none => simp [formula?, hLeft] at hCompile
      | some compiledLeft =>
          cases hRight : term? registry bound right with
          | none => simp [formula?, hLeft, hRight] at hCompile
          | some compiledRight =>
              rcases compiledLeft with ⟨leftSort, leftTerm⟩
              rcases compiledRight with ⟨rightSort, rightTerm⟩
              have hSort : leftSort = rightSort := by
                by_cases h : leftSort = rightSort
                · exact h
                · simp [formula?, hLeft, hRight, h] at hCompile
              cases hSort
              simp [formula?, hLeft, hRight] at hCompile
              subst source
              intro entry hSupport
              have hParts :
                  leftTerm.freeSupport.Contains entry.position ∨
                    rightTerm.freeSupport.Contains entry.position := by
                simpa [Logic.FirstOrder.Formula.freeSupport,
                  Logic.FirstOrder.FreeSupport.Contains,
                  Logic.FirstOrder.FreeSupport.union,
                  Bool.or_eq_true] using hSupport
              rcases hParts with hLeftSupport | hRightSupport
              · rcases term_support_of_compile registry bound left
                    ⟨leftSort, leftTerm⟩ hLeft entry hLeftSupport with
                  ⟨id, hId, hFind⟩
                refine ⟨id, ?_, hFind⟩
                exact List.mem_append_left _ hId
              · rcases term_support_of_compile registry bound right
                    ⟨leftSort, rightTerm⟩ hRight entry hRightSupport with
                  ⟨id, hId, hFind⟩
                refine ⟨id, ?_, hFind⟩
                exact List.mem_append_right _ hId
  | bound, .neg body, source, hCompile => by
      cases hBody : formula? registry bound body with
      | none => simp [formula?, hBody] at hCompile
      | some compiledBody =>
          simp [formula?, hBody] at hCompile
          subst source
          intro entry hSupport
          exact formula_support_of_compile registry bound body compiledBody
            hBody entry hSupport
  | bound, .conj left right, source, hCompile
  | bound, .disj left right, source, hCompile
  | bound, .imp left right, source, hCompile
  | bound, .iff left right, source, hCompile => by
      cases hLeft : formula? registry bound left with
      | none => simp [formula?, hLeft] at hCompile
      | some compiledLeft =>
          cases hRight : formula? registry bound right with
          | none => simp [formula?, hLeft, hRight] at hCompile
          | some compiledRight =>
              simp [formula?, hLeft, hRight] at hCompile
              subst source
              intro entry hSupport
              have hParts :
                  compiledLeft.freeSupport.Contains entry.position ∨
                    compiledRight.freeSupport.Contains entry.position := by
                simpa [Logic.FirstOrder.Formula.freeSupport,
                  Logic.FirstOrder.FreeSupport.Contains,
                  Logic.FirstOrder.FreeSupport.union,
                  Bool.or_eq_true] using hSupport
              rcases hParts with hLeftSupport | hRightSupport
              · rcases formula_support_of_compile registry bound left compiledLeft
                    hLeft entry hLeftSupport with
                  ⟨id, hRawEntry, hFind⟩
                exact ⟨id, List.mem_append_left _ hRawEntry, hFind⟩
              · rcases formula_support_of_compile registry bound right compiledRight
                    hRight entry hRightSupport with
                  ⟨id, hRawEntry, hFind⟩
                exact ⟨id, List.mem_append_right _ hRawEntry, hFind⟩
  | bound, .forallE sort body, source, hCompile => by
      cases hBody : formula? registry (sort :: bound) body with
      | none => simp [formula?, hBody] at hCompile
      | some compiledBody =>
          simp [formula?, hBody] at hCompile
          subst source
          intro entry hSupport
          exact formula_support_of_compile registry (sort :: bound) body compiledBody
            hBody entry hSupport
  | bound, .existsE sort body, source, hCompile => by
      cases hBody : formula? registry (sort :: bound) body with
      | none => simp [formula?, hBody] at hCompile
      | some compiledBody =>
          simp [formula?, hBody] at hCompile
          subst source
          intro entry hSupport
          exact formula_support_of_compile registry (sort :: bound) body compiledBody
            hBody entry hSupport

end

def RawAssignmentAgrees [DecidableEq σ.SortSymbol]
    {M : Structure.{0, 0, 0, x} σ}
    (registry : FreeRegistry σ)
  (support : List (σ.SortSymbol × Nat))
    (left right : Assignment M registry.context) : Prop :=
  ∀ {sort : σ.SortSymbol} {id : Nat}
    {entry : Logic.FirstOrder.Variable registry.context sort},
    (sort, id) ∈ support →
      registry.find? sort id = some entry →
        left entry = right entry

def assignmentEnv
    {M : Structure.{0, 0, 0, x} σ}
    {registry : FreeRegistry σ} {bound : SortContext σ}
    (boundAssignment : Assignment M bound)
    (freeAssignment : Assignment M registry.context) :
    Env M bound registry.context where
  boundVal := boundAssignment
  freeVal := freeAssignment

theorem env_agreesOn_of_rawAssignmentAgrees [DecidableEq σ.SortSymbol]
    {M : Structure.{0, 0, 0, x} σ}
    (registry : FreeRegistry σ)
    {bound : SortContext σ} (raw : Formula σ)
    (source : Logic.FirstOrder.Formula σ bound registry.context)
    (hCompile : formula? registry bound raw = some source)
    (boundAssignment : Assignment M bound)
    (left right : Assignment M registry.context)
    (hRaw : RawAssignmentAgrees registry raw.freeSupport left right) :
    Env.AgreesOn source.freeSupport
      (assignmentEnv boundAssignment left)
      (assignmentEnv boundAssignment right) := by
  constructor
  · intro sort entry
    rfl
  · intro sort entry hSupport
    rcases formula_support_of_compile registry bound raw source hCompile
        entry hSupport with
      ⟨id, hRawSupport, hFind⟩
    change left entry = right entry
    exact (show ∀ {sort : σ.SortSymbol} {id : Nat}
      {entry : Logic.FirstOrder.Variable registry.context sort},
      (sort, id) ∈ raw.freeSupport →
        registry.find? sort id = some entry →
          left entry = right entry from hRaw) hRawSupport hFind

theorem clause_env_agreesOn_of_rawAssignmentAgrees [DecidableEq σ.SortSymbol]
    {M : Structure.{0, 0, 0, x} σ}
    (registry : FreeRegistry σ) (clause : Clause σ)
    (formula : OpenFormula σ registry.context)
    (hCompile : clauseFormula? registry clause = some formula)
    (boundAssignment : Assignment M [])
    (left right : Assignment M registry.context)
    (hRaw : RawAssignmentAgrees registry clause.freeSupport left right) :
    Env.AgreesOn formula.freeSupport
      (assignmentEnv boundAssignment left)
      (assignmentEnv boundAssignment right) := by
  have hRaw' :
      RawAssignmentAgrees registry clause.toFormula.freeSupport left right := by
    intro sort id entry hSupport hFind
    change left entry = right entry
    apply (show ∀ {sort : σ.SortSymbol} {id : Nat}
      {entry : Logic.FirstOrder.Variable registry.context sort},
      (sort, id) ∈ clause.freeSupport →
        registry.find? sort id = some entry →
          left entry = right entry from hRaw)
    · simpa [Clause.toFormula_freeSupport] using hSupport
    · exact hFind
  exact env_agreesOn_of_rawAssignmentAgrees registry clause.toFormula formula
    (by simpa [clauseFormula?] using hCompile)
    boundAssignment left right hRaw'

private theorem findEntries?_getElem?_eq
    [DecidableEq σ.SortSymbol] :
    ∀ {entries : List (σ.SortSymbol × Nat)} {sort : σ.SortSymbol} {id : Nat}
      {entry : Logic.FirstOrder.Variable (entries.map Prod.fst) sort},
      FreeRegistry.findEntries? entries sort id = some entry →
        entries[entry.position]? = some (sort, id)
  | [], sort, id, entry, hFind => by
      simp [FreeRegistry.findEntries?] at hFind
  | (headSort, headId) :: tail, sort, id, entry, hFind => by
      simp only [FreeRegistry.findEntries?] at hFind
      split at hFind
      · subst sort
        split at hFind
        · subst id
          simp at hFind
          subst entry
          rfl
        · cases hTail : FreeRegistry.findEntries? tail headSort id with
          | none => simp [hTail] at hFind
          | some previous =>
              simp [hTail] at hFind
              subst entry
              have hPrevious :=
                findEntries?_getElem?_eq (entries := tail)
                  (sort := headSort) (id := id) hTail
              simpa [Logic.FirstOrder.Variable.position] using! hPrevious
      · cases hTail : FreeRegistry.findEntries? tail sort id with
        | none => simp [hTail] at hFind
        | some previous =>
            simp [hTail] at hFind
            subst entry
            have hPrevious :=
              findEntries?_getElem?_eq (entries := tail)
                (sort := sort) (id := id) hTail
            simpa [Logic.FirstOrder.Variable.position] using! hPrevious

private theorem find?_key_eq_of_same_entry [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    {sort : σ.SortSymbol} {leftId rightId : Nat}
    {left right : Logic.FirstOrder.Variable registry.context sort}
    (hLeft : registry.find? sort leftId = some left)
    (hRight : registry.find? sort rightId = some right)
    (hEntry : left = right) :
    leftId = rightId := by
  have hLeftPosition :=
    findEntries?_getElem?_eq (entries := registry.entries)
      (sort := sort) (id := leftId) hLeft
  have hRightPosition :=
    findEntries?_getElem?_eq (entries := registry.entries)
      (sort := sort) (id := rightId) hRight
  cases hEntry
  exact Prod.mk.inj
    (Option.some.inj (hLeftPosition.symm.trans hRightPosition)) |>.2

private theorem variable_exists_of_position {S : Type}
    (Γ : List S) (position : Fin Γ.length) :
    ∃ s, ∃ entry : Logic.FirstOrder.Variable Γ s,
      entry.position = position := by
  induction Γ with
  | nil => exact Fin.elim0 position
  | cons head tail ih =>
      refine Fin.cases ?_ ?_ position
      · exact ⟨head, .here, rfl⟩
      · intro previous
        rcases ih previous with ⟨sort, entry, hEntry⟩
        refine ⟨sort, .there entry, ?_⟩
        simpa [Logic.FirstOrder.Variable.position] using!
          congrArg Fin.succ hEntry

theorem compiled_support_disjoint_of_raw [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    {left right : Clause σ}
    {leftFormula rightFormula : OpenFormula σ registry.context}
    (hLeftCompile : clauseFormula? registry left = some leftFormula)
    (hRightCompile : clauseFormula? registry right = some rightFormula)
    (hRaw : Clause.SupportDisjoint left right) :
    Logic.FirstOrder.FreeSupport.Disjoint
      leftFormula.freeSupport rightFormula.freeSupport := by
  intro position hLeft hRight
  rcases variable_exists_of_position registry.context position with
    ⟨sort, entry, hPosition⟩
  have hLeftEntry : leftFormula.freeSupport.Contains entry.position := by
    simpa [hPosition] using hLeft
  have hRightEntry : rightFormula.freeSupport.Contains entry.position := by
    simpa [hPosition] using hRight
  rcases formula_support_of_compile registry [] left.toFormula leftFormula
      (by simpa [clauseFormula?] using hLeftCompile) entry hLeftEntry with
    ⟨leftId, hLeftRaw, hLeftFind⟩
  rcases formula_support_of_compile registry [] right.toFormula rightFormula
      (by simpa [clauseFormula?] using hRightCompile) entry hRightEntry with
    ⟨rightId, hRightRaw, hRightFind⟩
  have hId : leftId = rightId :=
    find?_key_eq_of_same_entry registry hLeftFind hRightFind rfl
  subst rightId
  apply hRaw (sort, leftId)
  · simpa [Clause.toFormula_freeSupport] using hLeftRaw
  · simpa [Clause.toFormula_freeSupport] using hRightRaw

theorem compiled_formula_satisfies_iff_exists_component
    [DecidableEq σ.SortSymbol]
    {M : Structure.{0, 0, 0, x} σ}
    {registry : FreeRegistry σ}
    (source : CompiledClause registry)
    (components : List (CompiledClause registry))
    (hCovers : Clause.Covers source.raw (components.map CompiledClause.raw))
    (env : Env M [] registry.context) :
    source.formula.satisfies env ↔
      ∃ component, component ∈ components ∧
        component.formula.satisfies env := by
  rcases source.literal_view with
    ⟨sourceFormulas, hSourceCompile, hSourceFormula⟩
  constructor
  · intro hSourceSat
    rw [hSourceFormula,
      Logic.FirstOrder.Formula.satisfies_disjunctionList_iff] at hSourceSat
    rcases hSourceSat with ⟨sourceFormula, hSourceMem, hSourceFormulaSat⟩
    rcases literalList?_raw_of_mem registry hSourceCompile hSourceMem with
      ⟨literal, hLiteralSource, hLiteralCompile⟩
    rcases hCovers.1 literal hLiteralSource with
      ⟨componentRaw, hComponentRaw, hLiteralComponent⟩
    rcases List.mem_map.mp hComponentRaw with
      ⟨component, hComponentMem, rfl⟩
    rcases component.literal_view with
      ⟨componentFormulas, hComponentCompile, hComponentFormula⟩
    rcases literalList?_compiled_of_mem registry hComponentCompile
        hLiteralComponent with
      ⟨componentFormula, hComponentFormulaMem, hComponentLiteralCompile⟩
    have hFormulaEq : componentFormula = sourceFormula :=
      Option.some.inj (hComponentLiteralCompile.symm.trans hLiteralCompile)
    refine ⟨component, hComponentMem, ?_⟩
    rw [hComponentFormula,
      Logic.FirstOrder.Formula.satisfies_disjunctionList_iff]
    exact ⟨componentFormula, hComponentFormulaMem,
      hFormulaEq ▸ hSourceFormulaSat⟩
  · rintro ⟨component, hComponentMem, hComponentSat⟩
    rcases component.literal_view with
      ⟨componentFormulas, hComponentCompile, hComponentFormula⟩
    rw [hComponentFormula,
      Logic.FirstOrder.Formula.satisfies_disjunctionList_iff] at hComponentSat
    rcases hComponentSat with
      ⟨componentFormula, hComponentFormulaMem, hComponentFormulaSat⟩
    rcases literalList?_raw_of_mem registry hComponentCompile
        hComponentFormulaMem with
      ⟨literal, hLiteralComponent, hLiteralCompile⟩
    have hComponentRaw : component.raw ∈
        (components.map CompiledClause.raw) :=
      List.mem_map.mpr ⟨component, hComponentMem, rfl⟩
    have hLiteralSource : literal ∈ source.raw.literals.toList :=
      hCovers.2 component.raw hComponentRaw literal hLiteralComponent
    rcases literalList?_compiled_of_mem registry hSourceCompile
        hLiteralSource with
      ⟨sourceFormula, hSourceFormulaMem, hSourceLiteralCompile⟩
    have hFormulaEq : sourceFormula = componentFormula :=
      Option.some.inj (hSourceLiteralCompile.symm.trans hLiteralCompile)
    rw [hSourceFormula,
      Logic.FirstOrder.Formula.satisfies_disjunctionList_iff]
    exact ⟨sourceFormula, hSourceFormulaMem,
      hFormulaEq ▸ hComponentFormulaSat⟩

private theorem compiled_exists_counterexample_of_not_trueIn
    [DecidableEq σ.SortSymbol]
    {M : Structure.{0, 0, 0, x} σ}
    {registry : FreeRegistry σ}
    (component : CompiledClause registry)
    (hNot : ¬ component.TrueIn M) :
    ∃ env : Env M [] registry.context,
      ¬ component.formula.satisfies env := by
  have hNotValid :
      ¬ ∀ assignment : Assignment M registry.context,
        component.formula.satisfies (openEnv assignment) := by
    intro hValid
    exact hNot ((forallFree_trueIn_iff component.formula).mpr hValid)
  classical
  apply Classical.byContradiction
  intro hNoCounterexample
  apply hNotValid
  intro assignment
  apply Classical.byContradiction
  intro hFalse
  apply hNoCounterexample
  exact ⟨openEnv assignment, hFalse⟩

private theorem compiled_exists_common_counterexample
    [DecidableEq σ.SortSymbol]
    {M : Structure.{0, 0, 0, x} σ}
    {registry : FreeRegistry σ}
    (base : Env M [] registry.context)
    (components : List (CompiledClause registry))
    (hDisjoint : Clause.PairwiseSupportDisjoint
      (components.map CompiledClause.raw))
    (hNotValid : ∀ component, component ∈ components →
      ¬ component.TrueIn M) :
    ∃ env : Env M [] registry.context,
      Env.SameBoundStack env base ∧
        ∀ component, component ∈ components →
          ¬ component.formula.satisfies env := by
  induction components generalizing base with
  | nil =>
      exact ⟨base, Env.SameBoundStack.refl base, by
        intro component hMem
        cases hMem⟩
  | cons firstComponent tail ih =>
      rcases hDisjoint with ⟨hHeadDisjoint, hTailDisjoint⟩
      rcases compiled_exists_counterexample_of_not_trueIn firstComponent
          (hNotValid firstComponent List.mem_cons_self) with
        ⟨headEnv, hHeadFalse⟩
      have hTailNotValid : ∀ component, component ∈ tail →
          ¬ component.TrueIn M := by
        intro component hMem
        exact hNotValid component (List.mem_cons_of_mem firstComponent hMem)
      rcases ih base hTailDisjoint hTailNotValid with
        ⟨tailEnv, hTailBound, hTailFalse⟩
      let headFormula := firstComponent.formula
      let headRaw := firstComponent.raw
      let headCompiled := firstComponent.compiled
      let merged := Env.overlay headFormula.freeSupport headEnv tailEnv
      refine ⟨merged, hTailBound, ?_⟩
      intro component hMem
      rcases List.mem_cons.mp hMem with rfl | hTailMem
      · intro hSat
        have hHeadBound : Env.SameBoundStack headEnv base := by
          intro sort entry
          cases entry
        have hBound : Env.SameBoundStack tailEnv headEnv :=
          hTailBound.trans hHeadBound.symm
        have hAgree : Env.AgreesOn headFormula.freeSupport
            merged headEnv := by
          simpa [merged] using
            (Env.overlay_agreesOn_source
              (support := headFormula.freeSupport) hBound)
        exact hHeadFalse ((Formula.satisfies_iff_of_agreesOn
          headFormula hAgree).mp hSat)
      · intro hSat
        have hComponentRawMem : component.raw ∈
            (tail.map CompiledClause.raw) :=
          List.mem_map.mpr ⟨component, hTailMem, rfl⟩
        have hRawDisjoint : Clause.SupportDisjoint
            headRaw component.raw :=
          hHeadDisjoint component.raw hComponentRawMem
        have hTypedDisjoint := compiled_support_disjoint_of_raw registry
          headCompiled component.compiled hRawDisjoint
        have hAgree : Env.AgreesOn component.formula.freeSupport
            merged tailEnv := by
          simpa [merged] using
            (Env.overlay_agreesOn_base_of_disjoint
              (source := headEnv) (base := tailEnv) hTypedDisjoint)
        exact hTailFalse component hTailMem
          ((Formula.satisfies_iff_of_agreesOn component.formula hAgree).mp hSat)

theorem compiled_trueIn_iff_exists_component
    [DecidableEq σ.SortSymbol]
    {M : Structure.{0, 0, 0, x} σ}
    {registry : FreeRegistry σ}
    (source : CompiledClause registry)
    (components : List (CompiledClause registry))
    (hCovers : Clause.Covers source.raw (components.map CompiledClause.raw))
    (hDisjoint : Clause.PairwiseSupportDisjoint
      (components.map CompiledClause.raw)) :
    source.TrueIn M ↔
      ∃ component, component ∈ components ∧ component.TrueIn M := by
  constructor
  · intro hSource
    classical
    apply Classical.byContradiction
    intro hNoComponent
    have hNotValid : ∀ component, component ∈ components →
        ¬ component.TrueIn M := by
      intro component hMem hValid
      exact hNoComponent ⟨component, hMem, hValid⟩
    rcases IntrinsicReplay.assignmentNonempty M registry.context with
      ⟨baseAssignment⟩
    rcases compiled_exists_common_counterexample
        (base := openEnv baseAssignment)
        components hDisjoint hNotValid with
      ⟨env, hBound, hFalse⟩
    have hOpenEnv : openEnv env.freeVal = env := by
      apply Env.ext
      · intro sort entry
        cases entry
      · intro sort entry
        rfl
    have hSourceSat : source.formula.satisfies env := by
      rw [← hOpenEnv]
      exact (forallFree_trueIn_iff source.formula).mp hSource env.freeVal
    rcases (compiled_formula_satisfies_iff_exists_component
      source components hCovers env).mp hSourceSat with
      ⟨component, hMem, hSat⟩
    exact hFalse component hMem hSat
  · rintro ⟨component, hMem, hValid⟩
    apply (forallFree_trueIn_iff source.formula).mpr
    intro assignment
    have hComponentSat :=
      (forallFree_trueIn_iff component.formula).mp hValid assignment
    exact (compiled_formula_satisfies_iff_exists_component
      source components hCovers (openEnv assignment)).mpr
      ⟨component, hMem, hComponentSat⟩

theorem literalList?_exists_of_mem_source
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    {sourceLiterals : List (Literal σ)}
    {sourceFormulas : List (OpenFormula σ registry.context)}
    (hSource : literalList? registry sourceLiterals = some sourceFormulas) :
    ∀ targetLiterals,
      (∀ literal, literal ∈ targetLiterals → literal ∈ sourceLiterals) →
        ∃ targetFormulas,
          literalList? registry targetLiterals = some targetFormulas := by
  intro targetLiterals
  induction targetLiterals with
  | nil =>
      intro _hSubset
      exact ⟨[], rfl⟩
  | cons head tail ih =>
      intro hSubset
      rcases literalList?_compiled_of_mem registry hSource
          (hSubset head (by simp)) with
        ⟨headFormula, _hHeadMem, hHeadCompile⟩
      rcases ih (by
          intro literal hLiteral
          exact hSubset literal (by simp [hLiteral])) with
        ⟨tailFormulas, hTailCompile⟩
      refine ⟨headFormula :: tailFormulas, ?_⟩
      simp [literalList?, hHeadCompile, hTailCompile]

theorem formula_exists_of_literalList?
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    ∀ {literals : List (Literal σ)} {formulas},
      literalList? registry literals = some formulas →
        ∃ formula : OpenFormula σ registry.context,
          formula? registry []
              (Formula.disjunctionList (literals.map Literal.toFormula)) =
            some formula := by
  intro literals
  induction literals with
  | nil =>
      intro formulas hCompile
      exact ⟨.falsum, by simp [Formula.disjunctionList, formula?]⟩
  | cons head tail ih =>
      intro formulas hCompile
      cases hHead : formula? registry [] head.toFormula with
      | none =>
          simp [literalList?, hHead] at hCompile
      | some headFormula =>
          cases hTail : literalList? registry tail with
          | none =>
              simp [literalList?, hHead, hTail] at hCompile
          | some tailFormulas =>
              have hTailFormula := ih hTail
              rcases hTailFormula with ⟨tailFormula, hTailFormula⟩
              cases tail with
              | nil =>
                  exact ⟨headFormula, by
                    simp [Formula.disjunctionList, hHead]⟩
              | cons next rest =>
                  refine ⟨.disj headFormula tailFormula, ?_⟩
                  change formula? registry []
                    (.disj head.toFormula
                      (Formula.disjunctionList
                        ((next :: rest).map Literal.toFormula))) =
                    some (.disj headFormula tailFormula)
                  simp only [formula?]
                  rw [hHead, hTailFormula]
                  rfl

theorem clauseFormula_exists_of_literal_subset
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (source : CompiledClause registry)
    (target : Clause σ)
    (hSubset : ∀ literal, literal ∈ target.literals.toList →
      literal ∈ source.raw.literals.toList) :
    ∃ formula : OpenFormula σ registry.context,
      clauseFormula? registry target = some formula := by
  rcases source.literal_view with
    ⟨sourceFormulas, hSourceCompile, _hSourceFormula⟩
  rcases literalList?_exists_of_mem_source registry hSourceCompile
      target.literals.toList hSubset with
    ⟨targetFormulas, hTargetCompile⟩
  exact formula_exists_of_literalList? registry hTargetCompile

theorem compiledClauses_exists_of_literal_subset
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    (source : CompiledClause registry)
    (targets : List (Clause σ))
    (hSubset : ∀ target, target ∈ targets →
      ∀ literal, literal ∈ target.literals.toList →
        literal ∈ source.raw.literals.toList) :
    ∃ compiledTargets : List (CompiledClause registry),
      compiledTargets.map CompiledClause.raw = targets := by
  induction targets with
  | nil =>
      exact ⟨[], rfl⟩
  | cons head tail ih =>
      rcases clauseFormula_exists_of_literal_subset registry source head
          (hSubset head (by simp)) with
        ⟨formula, hFormula⟩
      rcases ih (by
          intro target hTarget literal hLiteral
          exact hSubset target (by simp [hTarget]) literal hLiteral) with
        ⟨compiledTail, hTail⟩
      refine ⟨⟨head, formula, hFormula⟩ :: compiledTail, ?_⟩
      simp [hTail]

end Compile

namespace IntrinsicReplay

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]

theorem avatarSplit_conclusion_eq_source
    (cert : CheckedDAG (σ := σ))
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    (hNode : cert.dag.node? splitId = some splitNode)
    (hPayload : splitNode.payload = .avatarSplit payload) :
    splitNode.conclusion = payload.source.clause := by
  rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
  have hNodeAt : cert.dag.nodeAt splitId hIndex = splitNode := by
    simpa [DAG.nodeAt, DAG.graphView] using! hGet
  have hPayloadAt :
      (cert.dag.nodeAt splitId hIndex).payload = .avatarSplit payload := by
    simpa [hNodeAt] using hPayload
  have hPayloadCheck :=
    payloadCheck_of_payload_eq cert splitId hIndex hPayloadAt
  have hSplitCheck :
      payload.check (cert.dag.nodeAt splitId hIndex).parents
        (cert.dag.nodeAt splitId hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold AvatarSplitPayload.check at hSplitCheck
  have hParts := Bool.and_eq_true_iff.mp hSplitCheck
  have hConclusion :
      (cert.dag.nodeAt splitId hIndex).conclusion = payload.source.clause :=
    (Clause.eq_sound payload.source.clause
      (cert.dag.nodeAt splitId hIndex).conclusion hParts.2).symm
  exact hNodeAt ▸ hConclusion

theorem avatarComponentSemantics_of_checked_registry
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (registry : AvatarSelectorComponent.Registry σ)
    (hRegistry : DAG.avatarRegistryCheckWith cert.dag registry = true) :
    AvatarComponentSemantics M compiled
      (avatarSelectorValuation M compiled cert.dag.avatarSelectorRegistry) := by
  intro splitId splitNode splitPayload componentIndex indices selector
    hNode hPayload hIndices hSelector
  let entry : AvatarSelectorComponent σ :=
    ⟨selector, Clause.atIndices splitNode.conclusion indices⟩
  have hEntryLocal :
      (⟨selector, Clause.atIndices splitPayload.source.clause indices⟩ :
        AvatarSelectorComponent σ) ∈ splitPayload.selectorComponents :=
    AvatarSplitPayload.selectorComponent_mem hIndices hSelector
  have hEntryGlobal :
      (⟨selector, Clause.atIndices splitPayload.source.clause indices⟩ :
        AvatarSelectorComponent σ) ∈ cert.dag.avatarSelectorRegistry :=
    DAG.mem_avatarSelectorRegistry_of_split hNode hPayload hEntryLocal
  have hSourceEq : splitNode.conclusion = splitPayload.source.clause :=
    avatarSplit_conclusion_eq_source cert hNode hPayload
  have hEntry : entry ∈ cert.dag.avatarSelectorRegistry := by
    simpa [entry, hSourceEq] using hEntryGlobal
  exact avatarSelector_holds_iff_trueIn M compiled
    cert.dag.avatarSelectorRegistry
    (DAG.avatarSelectorRegistry_positive hRegistry)
    (DAG.avatarSelectorRegistry_compatible hRegistry) hEntry

theorem avatarSelectorClause_satisfies_iff_exists_component
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (registry : AvatarSelectorComponent.Registry σ)
    (hRegistry : DAG.avatarRegistryCheckWith cert.dag registry = true)
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    (hNode : cert.dag.node? splitId = some splitNode)
    (hPayload : splitNode.payload = .avatarSplit payload) :
    PropResolution.Clause.Satisfies
        (avatarSelectorValuation M compiled cert.dag.avatarSelectorRegistry)
        (PropResolution.canonicalClause payload.selectors) ↔
      ∃ entry, entry ∈ payload.selectorComponents ∧
        AvatarClauseTrueIn M compiled entry.component := by
  have hContract := DAG.avatarSplitRegistryContract hRegistry hNode hPayload
  have hProjection :
      payload.selectorComponents.map AvatarSelectorComponent.selector =
        payload.selectors.toList := by
    simpa [AvatarSplitPayload.selectorComponents] using
      AvatarSelectorComponent.selectors_ofLists hContract.aligned
  have hPositive := DAG.avatarSelectorRegistry_positive hRegistry
  have hCompatible := DAG.avatarSelectorRegistry_compatible hRegistry
  constructor
  · rintro ⟨selector, hSelectorMem, hSelector⟩
    have hSelectorRaw : selector ∈ payload.selectors.toList := by
      apply PropResolution.mem_of_mem_canonicalClauseList
      simpa [PropResolution.canonicalClause] using hSelectorMem
    have hMapped : selector ∈
        payload.selectorComponents.map AvatarSelectorComponent.selector := by
      rw [hProjection]
      exact hSelectorRaw
    rcases List.mem_map.mp hMapped with ⟨entry, hEntry, rfl⟩
    have hEntryGlobal : entry ∈ cert.dag.avatarSelectorRegistry :=
      DAG.mem_avatarSelectorRegistry_of_split hNode hPayload hEntry
    exact ⟨entry, hEntry,
      (avatarSelector_holds_iff_trueIn M compiled
        cert.dag.avatarSelectorRegistry hPositive hCompatible hEntryGlobal).mp hSelector⟩
  · rintro ⟨entry, hEntry, hTrue⟩
    have hEntryGlobal : entry ∈ cert.dag.avatarSelectorRegistry :=
      DAG.mem_avatarSelectorRegistry_of_split hNode hPayload hEntry
    have hSelector : entry.selector.Holds
        (avatarSelectorValuation M compiled cert.dag.avatarSelectorRegistry) :=
      (avatarSelector_holds_iff_trueIn M compiled
        cert.dag.avatarSelectorRegistry hPositive hCompatible hEntryGlobal).mpr hTrue
    have hMapped : entry.selector ∈
        payload.selectorComponents.map AvatarSelectorComponent.selector :=
      List.mem_map.mpr ⟨entry, hEntry, rfl⟩
    have hSelectorRaw : entry.selector ∈ payload.selectors.toList := by
      rw [← hProjection]
      exact hMapped
    exact ⟨entry.selector,
      PropResolution.mem_canonicalClause_of_mem hSelectorRaw, hSelector⟩

theorem avatarSplitSemantics_of_checked_registry
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (registry : AvatarSelectorComponent.Registry σ)
    (hRegistry : DAG.avatarRegistryCheckWith cert.dag registry = true) :
    AvatarSplitSemantics M compiled
      (avatarSelectorValuation M compiled cert.dag.avatarSelectorRegistry) := by
  intro splitId splitNode splitPayload hNode hPayload
  rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
  have hNodeAt : cert.dag.nodeAt splitId hIndex = splitNode := by
    simpa [DAG.nodeAt, DAG.graphView] using! hGet
  have hSourceEq : splitNode.conclusion = splitPayload.source.clause :=
    avatarSplit_conclusion_eq_source cert hNode hPayload
  let source := compiled.nodeAt splitId hIndex
  have hSourceRaw : source.raw = splitPayload.source.clause := by
    calc
      source.raw = (cert.dag.nodeAt splitId hIndex).conclusion :=
        compiled.nodeAt_raw splitId hIndex
      _ = splitNode.conclusion := by rw [hNodeAt]
      _ = splitPayload.source.clause := hSourceEq
  have hNodeRaw : source.raw = splitNode.conclusion :=
    hSourceRaw.trans hSourceEq.symm
  have hSubset :
      ∀ target, target ∈ splitPayload.componentClauses →
        ∀ literal, literal ∈ target.literals.toList →
          literal ∈ source.raw.literals.toList := by
    intro target hTarget literal hLiteral
    have hSourceLiteral :=
      (DAG.avatarSplitRegistryContract hRegistry hNode hPayload).covers.2
        target hTarget literal hLiteral
    simpa [hSourceRaw] using hSourceLiteral
  rcases Compile.compiledClauses_exists_of_literal_subset
      compiled.compilation.registry source splitPayload.componentClauses hSubset with
    ⟨components, hComponentsRaw⟩
  have hCovers : Clause.Covers source.raw
      (components.map Compile.CompiledClause.raw) := by
    rw [hComponentsRaw]
    simpa [hSourceRaw] using
      (DAG.avatarSplitRegistryContract hRegistry hNode hPayload).covers
  have hDisjoint : Clause.PairwiseSupportDisjoint
      (components.map Compile.CompiledClause.raw) := by
    rw [hComponentsRaw]
    exact (DAG.avatarSplitRegistryContract hRegistry hNode hPayload).pairwiseDisjoint
  have hSourceComponents :=
    Compile.compiled_trueIn_iff_exists_component (M := M)
      source components hCovers hDisjoint
  have hComponentProjection :
      splitPayload.selectorComponents.map AvatarSelectorComponent.component =
        splitPayload.componentClauses := by
    simpa [AvatarSplitPayload.selectorComponents] using
      AvatarSelectorComponent.components_ofLists
        (DAG.avatarSplitRegistryContract hRegistry hNode hPayload).aligned
  have hSourceAvatar :
      AvatarClauseTrueIn M compiled splitNode.conclusion ↔ source.TrueIn M := by
    constructor
    · rintro ⟨sourceClause, hRaw, hTrue⟩
      exact (Compile.CompiledClause.trueIn_iff_of_raw_eq M
        (hRaw.trans hNodeRaw.symm)).mp hTrue
    · intro hTrue
      exact ⟨source, hNodeRaw, hTrue⟩
  have hSelectorComponents :=
    avatarSelectorClause_satisfies_iff_exists_component M cert compiled registry
      hRegistry hNode hPayload
  constructor
  · intro hSourceTrue
    have hTypedSource : source.TrueIn M := hSourceAvatar.mp hSourceTrue
    rcases hSourceComponents.mp hTypedSource with
      ⟨component, hComponentMem, hComponentTrue⟩
    have hComponentRawMem : component.raw ∈ splitPayload.componentClauses := by
      rw [← hComponentsRaw]
      exact List.mem_map.mpr ⟨component, hComponentMem, rfl⟩
    have hEntryComponentMem : component.raw ∈
        splitPayload.selectorComponents.map AvatarSelectorComponent.component := by
      rw [hComponentProjection]
      exact hComponentRawMem
    rcases List.mem_map.mp hEntryComponentMem with
      ⟨entry, hEntry, hEntryComponent⟩
    have hEntryTrue : AvatarClauseTrueIn M compiled entry.component := by
      exact ⟨component, hEntryComponent.symm, hComponentTrue⟩
    exact hSelectorComponents.mpr ⟨entry, hEntry, hEntryTrue⟩
  · intro hSelectors
    rcases hSelectorComponents.mp hSelectors with
      ⟨entry, hEntry, hEntryTrue⟩
    rcases hEntryTrue with ⟨entryClause, hEntryRaw, hEntryClauseTrue⟩
    have hTypedComponentRaw : entry.component ∈
        components.map Compile.CompiledClause.raw := by
      rw [hComponentsRaw, ← hComponentProjection]
      exact List.mem_map.mpr ⟨entry, hEntry, rfl⟩
    rcases List.mem_map.mp hTypedComponentRaw with
      ⟨component, hComponentMem, hComponentRaw⟩
    have hComponentTrue : component.TrueIn M :=
      (Compile.CompiledClause.trueIn_iff_of_raw_eq M
        (hEntryRaw.trans hComponentRaw.symm)).mp hEntryClauseTrue
    have hTypedSource : source.TrueIn M :=
      hSourceComponents.mpr ⟨component, hComponentMem, hComponentTrue⟩
    exact hSourceAvatar.mpr hTypedSource

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
