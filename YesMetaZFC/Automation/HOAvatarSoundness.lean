import YesMetaZFC.Automation.HODAGCertificate
import YesMetaZFC.Automation.Guards
/-!
# 原生高阶 AVATAR 的 component 语义
本模块只证明 HO-AVATAR 所需的语义合同：typed 自由变量支持控制环境影响，
component 的 literal 覆盖给出字句析取等价，selector registry 则把命题文字解释为
component 的全环境有效性。DAG 拓扑回放与双核协议在此合同之上继续实现。
-/
namespace YesMetaZFC
namespace Automation
namespace HODAGCertificate
open Logic.HigherOrder
section HOAvatarSoundnessSignature
variable {σ : Signature.{u, v, w}}
namespace Avatar
def SupportContains  [DecidableEq σ.BaseSort] (support : Array (FreeVariable σ)) (candidate : FreeVariable σ) : Prop :=
  candidate ∈ support.toList
def SupportDisjoint  [DecidableEq σ.BaseSort] (left right : Array (FreeVariable σ)) : Prop :=
  ∀ candidate, SupportContains left candidate →
    ¬ SupportContains right candidate
def SameBoundStack  {M : Structure.{u, v, w, x} σ} (left right : Env M) : Prop :=
  ∀ index, left.boundVal index = right.boundVal index
namespace SameBoundStack
theorem refl  {M : Structure.{u, v, w, x} σ} (env : Env M) : SameBoundStack env env :=
  fun _ => rfl
theorem symm  {M : Structure.{u, v, w, x} σ}
    {left right : Env M} (hBound : SameBoundStack left right) :
    SameBoundStack right left :=
  fun index => (hBound index).symm
theorem trans  {M : Structure.{u, v, w, x} σ}
    {left middle right : Env M} (hLeft : SameBoundStack left middle) (hRight : SameBoundStack middle right) :
    SameBoundStack left right :=
  fun index => (hLeft index).trans (hRight index)
end SameBoundStack
def EnvAgreesOn  [DecidableEq σ.BaseSort]
    {M : Structure σ} (support : Array (FreeVariable σ)) (left right : Env M) : Prop :=
  SameBoundStack left right ∧
    ∀ candidate, SupportContains support candidate →
      left.freeVal candidate.sort candidate.id =
        right.freeVal candidate.sort candidate.id
theorem freeVariableEq_sound
    [DecidableEq σ.BaseSort] {left right : FreeVariable σ} (hEq : FreeVariable.eq left right = true) : left = right := by
  cases left with
  | mk leftSort leftId =>
      cases right with
      | mk rightSort rightId =>
          simp [FreeVariable.eq] at hEq
          rcases hEq with ⟨hSort, hId⟩
          cases hSort
          cases hId
          rfl
def supportContainsCheck  [DecidableEq σ.BaseSort] (support : Array (FreeVariable σ)) (candidate : FreeVariable σ) : Bool :=
  support.any (FreeVariable.eq · candidate)
theorem supportContainsCheck_true_of_contains
    [DecidableEq σ.BaseSort] {support : Array (FreeVariable σ)}
    {candidate : FreeVariable σ} (hContains : SupportContains support candidate) :
    supportContainsCheck support candidate = true := by
  have hArray : candidate ∈ support := Array.mem_def.mpr hContains
  rcases Array.mem_iff_getElem.mp hArray with ⟨index, hIndex, hGet⟩
  unfold supportContainsCheck
  apply Array.any_eq_true.mpr
  refine ⟨index, hIndex, ?_⟩
  simp [hGet, FreeVariable.eq]
theorem supportContains_of_eq_true
    [DecidableEq σ.BaseSort] {support : Array (FreeVariable σ)}
    {candidate : FreeVariable σ} (hContains : supportContainsCheck support candidate = true) :
    SupportContains support candidate := by
  rcases Array.any_eq_true.mp hContains with ⟨index, hIndex, hEq⟩
  have hExisting : support[index] = candidate := freeVariableEq_sound hEq
  have hMem : SupportContains support support[index] :=
    Array.mem_def.mp (Array.getElem_mem hIndex)
  simpa [hExisting] using hMem
theorem pushFreeVariableUnique_contains
    [DecidableEq σ.BaseSort] {support : Array (FreeVariable σ)}
    {candidate : FreeVariable σ} :
    candidate ∈ (pushFreeVariableUnique support candidate).toList := by
  by_cases hAny : support.any (FreeVariable.eq · candidate) = true
  · rcases Array.any_eq_true.mp hAny with ⟨index, hIndex, hEq⟩
    have hExisting : support[index] = candidate := freeVariableEq_sound hEq
    have hMem : support[index] ∈ support.toList :=
      Array.mem_def.mp (Array.getElem_mem hIndex)
    simpa [pushFreeVariableUnique, hAny, hExisting] using hMem
  · simp [pushFreeVariableUnique, hAny]
theorem foldlSupportContains
    [DecidableEq σ.BaseSort] :
    ∀ (items : List (FreeVariable σ)) (support : Array (FreeVariable σ)) (candidate : FreeVariable σ), candidate ∈ support.toList →
        candidate ∈ (items.foldl pushFreeVariableUnique support).toList
  | [], support, candidate, hCandidate => hCandidate
  | head :: tail, support, candidate, hCandidate => by
      apply foldlSupportContains tail (pushFreeVariableUnique support head) candidate
      by_cases hAny : support.any (FreeVariable.eq · head) = true
      · simpa [pushFreeVariableUnique, hAny] using hCandidate
      · simpa [pushFreeVariableUnique, hAny] using (show candidate ∈ support.toList ∨ candidate = head from Or.inl hCandidate)
theorem foldlSupportContains_right
    [DecidableEq σ.BaseSort] :
    ∀ (items : List (FreeVariable σ)) (candidate : FreeVariable σ),
      candidate ∈ items → ∀ (support : Array (FreeVariable σ)),
        candidate ∈ (items.foldl pushFreeVariableUnique support).toList
  | [], candidate, hCandidate, support => by
      simp at hCandidate
  | head :: tail, candidate, hCandidate, support => by
      rcases List.mem_cons.mp hCandidate with hHead | hTail
      · subst candidate
        exact foldlSupportContains tail (pushFreeVariableUnique support head) head (pushFreeVariableUnique_contains (support := support) (candidate := head))
      · exact foldlSupportContains_right tail candidate hTail (pushFreeVariableUnique support head)
theorem supportContains_merge_left
    [DecidableEq σ.BaseSort] {left right : Array (FreeVariable σ)}
    {candidate : FreeVariable σ} (hCandidate : SupportContains left candidate) :
    SupportContains (mergeFreeSupport left right) candidate :=
  foldlSupportContains right.toList left candidate hCandidate
theorem supportContains_merge_right
    [DecidableEq σ.BaseSort] {left right : Array (FreeVariable σ)}
    {candidate : FreeVariable σ} (hCandidate : SupportContains right candidate) :
    SupportContains (mergeFreeSupport left right) candidate := by
  unfold SupportContains at hCandidate
  exact foldlSupportContains_right right.toList candidate
    hCandidate left
theorem supportsOverlap_false_sound
    [DecidableEq σ.BaseSort] {left right : Array (FreeVariable σ)} (hOverlap : supportsOverlap left right = false) :
    SupportDisjoint left right := by
  intro candidate hLeft hRight
  have hLeftArray : candidate ∈ left := Array.mem_def.mpr hLeft
  have hRightArray : candidate ∈ right := Array.mem_def.mpr hRight
  rcases Array.mem_iff_getElem.mp hLeftArray with
    ⟨leftIndex, hLeftIndex, hLeftGet⟩
  rcases Array.mem_iff_getElem.mp hRightArray with
    ⟨rightIndex, hRightIndex, hRightGet⟩
  have hTrue : supportsOverlap left right = true := by
    unfold supportsOverlap
    apply Array.any_eq_true.mpr
    refine ⟨leftIndex, hLeftIndex, ?_⟩
    apply Array.any_eq_true.mpr
    refine ⟨rightIndex, hRightIndex, ?_⟩
    simp [hLeftGet, hRightGet, FreeVariable.eq]
  simp [hOverlap] at hTrue
def overlay  [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (support : Array (FreeVariable σ)) (source base : Env M) : Env M where
  boundVal := base.boundVal
  freeVal := fun sort id =>
    if supportContainsCheck support { sort := sort, id := id } then
      source.freeVal sort id
    else
      base.freeVal sort id
theorem overlay_sameBoundStack_base
    [DecidableEq σ.BaseSort] {M : Structure.{u, v, w, x} σ}
    {support : Array (FreeVariable σ)} {source base : Env M} :
    SameBoundStack (overlay support source base) base := by
  intro index
  rfl
theorem overlay_wellSorted
    [DecidableEq σ.BaseSort] {M : Structure.{u, v, w, x} σ}
    {support : Array (FreeVariable σ)} {source base : Env M} (hSource : source.WellSorted []) (hBase : base.WellSorted []) :
    (overlay support source base).WellSorted [] := by
  constructor
  · intro index sort hLookup
    simp [Context.lookup?] at hLookup
  · intro sort id
    cases hMem : supportContainsCheck support { sort := sort, id := id }
    · simpa [overlay, hMem] using hBase.2 sort id
    · simpa [overlay, hMem] using hSource.2 sort id
noncomputable def canonicalOnBoundStack (M : Structure.{u, v, w, x} σ) (base : Env M) : Env M where
  boundVal := base.boundVal
  freeVal := fun sort _ => Classical.choose (M.sortNonempty sort)
theorem canonicalOnBoundStack_wellSorted
    {M : Structure.{u, v, w, x} σ} (base : Env M) : (canonicalOnBoundStack M base).WellSorted [] := by
  constructor
  · intro index sort hLookup
    simp [Context.lookup?] at hLookup
  · intro sort id
    exact Classical.choose_spec (M.sortNonempty sort)
theorem canonicalOnBoundStack_sameBoundStack
    {M : Structure.{u, v, w, x} σ} (base : Env M) :
    SameBoundStack (canonicalOnBoundStack M base) base := by
  intro index
  rfl
theorem overlay_agreesOn_source
    [DecidableEq σ.BaseSort] {M : Structure.{u, v, w, x} σ}
    {support : Array (FreeVariable σ)} {source base : Env M} (hBound : SameBoundStack base source) :
    EnvAgreesOn support (overlay support source base) source := by
  constructor
  · exact hBound
  · intro candidate hCandidate
    have hCheck := supportContainsCheck_true_of_contains hCandidate
    simp [overlay, hCheck]
theorem overlay_agreesOn_base_of_disjoint
    [DecidableEq σ.BaseSort] {M : Structure.{u, v, w, x} σ}
    {overlaySupport support : Array (FreeVariable σ)}
    {source base : Env M} (hDisjoint : SupportDisjoint overlaySupport support) :
    EnvAgreesOn support (overlay overlaySupport source base) base := by
  constructor
  · intro index
    rfl
  · intro candidate hCandidate
    have hMissing : ¬ SupportContains overlaySupport candidate :=
      fun hOverlay => hDisjoint candidate hOverlay hCandidate
    have hCheck : supportContainsCheck overlaySupport candidate = false := by
      cases hContains : supportContainsCheck overlaySupport candidate
      · rfl
      · exact False.elim (hMissing (supportContains_of_eq_true hContains))
    simp [overlay, hCheck]
theorem termEval_eq_of_envAgreesOn_aux
    [DecidableEq σ.BaseSort] {M : Structure σ} :
    ∀ (term : Term σ) (left right : Env M), (∀ index, left.boundVal index = right.boundVal index) → (∀ candidate,
          SupportContains (termFreeSupport term) candidate →
            left.freeVal candidate.sort candidate.id =
              right.freeVal candidate.sort candidate.id) →
        Term.eval left term = Term.eval right term := by
  intro term
  refine Logic.HigherOrder.Term.rec (motive_1 := fun term =>
      ∀ (left right : Env M), (∀ index, left.boundVal index = right.boundVal index) → (∀ candidate,
            SupportContains (termFreeSupport term) candidate →
              left.freeVal candidate.sort candidate.id =
                right.freeVal candidate.sort candidate.id) →
          Term.eval left term = Term.eval right term) (motive_2 := fun terms =>
      ∀ (left right : Env M), (∀ index, left.boundVal index = right.boundVal index) → (∀ candidate,
            SupportContains (termListFreeSupport terms) candidate →
              left.freeVal candidate.sort candidate.id =
                right.freeVal candidate.sort candidate.id) →
          terms.map (Term.eval left) = terms.map (Term.eval right))
    ?_ ?_ ?_ ?_ ?_ ?_ term
  · intro value left right hBound hFree
    cases value with
    | bvar sort index =>
        simpa [Term.eval] using hBound index
    | fvar sort id =>
        have hEq := hFree { sort := sort, id := id } (by simp [SupportContains, termFreeSupport])
        simpa [Term.eval] using hEq
  · intro symbol arguments ihArguments left right hBound hFree
    simp only [Term.eval]
    congr 1
    apply ihArguments left right hBound
    intro candidate hCandidate
    exact hFree candidate hCandidate
  · intro function argument ihFunction ihArgument left right hBound hFree
    simp only [Term.eval]
    rw [ihFunction left right hBound (fun candidate hCandidate =>
        hFree candidate (supportContains_merge_left (right := termFreeSupport argument) hCandidate)),
      ihArgument left right hBound (fun candidate hCandidate =>
        hFree candidate (supportContains_merge_right (left := termFreeSupport function) hCandidate))]
  · intro domain codomain body ihBody left right hBound hFree
    simp only [Term.eval]
    congr 1
    funext value
    apply ihBody (left.push value) (right.push value)
    · intro index
      cases index with
      | zero => rfl
      | succ previous => exact hBound previous
    · intro candidate hCandidate
      exact hFree candidate hCandidate
  · intro left right hBound hFree
    rfl
  · intro head tail ihHead ihTail left right hBound hFree
    simp only [List.map_cons]
    rw [ihHead left right hBound (fun candidate hCandidate =>
        hFree candidate (supportContains_merge_left (right := termListFreeSupport tail) hCandidate)),
      ihTail left right hBound (fun candidate hCandidate =>
        hFree candidate (supportContains_merge_right (left := termFreeSupport head) hCandidate))]
theorem termEval_eq_of_envAgreesOn
    [DecidableEq σ.BaseSort] {M : Structure σ} :
    ∀ (left right : Env M) (term : Term σ), (∀ index, left.boundVal index = right.boundVal index) → (∀ candidate,
          SupportContains (termFreeSupport term) candidate →
            left.freeVal candidate.sort candidate.id =
              right.freeVal candidate.sort candidate.id) →
        Term.eval left term = Term.eval right term :=
  fun left right term hBound hFree =>
    termEval_eq_of_envAgreesOn_aux term left right hBound hFree
theorem termListEval_eq_of_envAgreesOn
    [DecidableEq σ.BaseSort] {M : Structure σ} :
    ∀ (left right : Env M) (terms : List (Term σ)),
      SameBoundStack left right → (∀ candidate,
          SupportContains (termListFreeSupport terms) candidate →
            left.freeVal candidate.sort candidate.id =
              right.freeVal candidate.sort candidate.id) →
        terms.map (Term.eval left) = terms.map (Term.eval right)
  | left, right, [], _hBound, _hFree => rfl
  | left, right, head :: tail, hBound, hFree => by
      simp only [List.map_cons]
      rw [termEval_eq_of_envAgreesOn left right head hBound (fun candidate hCandidate =>
            hFree candidate (supportContains_merge_left (right := termListFreeSupport tail) hCandidate)),
        termListEval_eq_of_envAgreesOn left right tail hBound (fun candidate hCandidate =>
            hFree candidate (supportContains_merge_right (left := termFreeSupport head) hCandidate))]
theorem foldlLiteralSupportContains
    [DecidableEq σ.BaseSort] :
    ∀ (literals : List (Literal σ)) (support : Array (FreeVariable σ)) (candidate : FreeVariable σ), SupportContains support candidate →
        SupportContains (literals.foldl (fun current literal =>
              mergeFreeSupport current (literalFreeSupport literal))
            support)
          candidate
  | [], support, candidate, hCandidate => hCandidate
  | head :: tail, support, candidate, hCandidate => by
      apply foldlLiteralSupportContains tail (mergeFreeSupport support (literalFreeSupport head)) candidate
      exact supportContains_merge_left hCandidate
theorem foldlLiteralSupportContains_right
    [DecidableEq σ.BaseSort] :
    ∀ (literals : List (Literal σ)) (literal : Literal σ),
      literal ∈ literals → ∀ (candidate : FreeVariable σ),
        SupportContains (literalFreeSupport literal) candidate →
          ∀ support : Array (FreeVariable σ),
            SupportContains (literals.foldl (fun current item =>
                  mergeFreeSupport current (literalFreeSupport item))
                support)
              candidate
  | [], literal, hLiteral, candidate, hCandidate, support => by
      simp at hLiteral
  | head :: tail, literal, hLiteral, candidate, hCandidate, support => by
      rcases List.mem_cons.mp hLiteral with hHead | hTail
      · subst literal
        apply foldlLiteralSupportContains tail (mergeFreeSupport support (literalFreeSupport head)) candidate
        exact supportContains_merge_right hCandidate
      · exact foldlLiteralSupportContains_right tail literal hTail candidate
          hCandidate (mergeFreeSupport support (literalFreeSupport head))
theorem literalSupport_subset_clauseSupport
    [DecidableEq σ.BaseSort] {clause : Clause σ} {literal : Literal σ} (hLiteral : literal ∈ clause.literals.toList) :
    ∀ candidate, SupportContains (literalFreeSupport literal) candidate →
      SupportContains (clauseFreeSupport clause) candidate :=
  fun candidate hCandidate =>
    foldlLiteralSupportContains_right clause.literals.toList literal
    hLiteral candidate hCandidate #[]
theorem atomSatisfies_iff_of_envAgreesOn
    [DecidableEq σ.BaseSort] {M : Structure σ}
    {left right : Env M} (atom : Atom σ) (hEnv : EnvAgreesOn (atomFreeSupport atom) left right) :
    atom.Satisfies left ↔ atom.Satisfies right := by
  cases atom with
  | rel symbol arguments =>
      have hArguments :=
        termListEval_eq_of_envAgreesOn left right arguments hEnv.1 (fun candidate hCandidate => hEnv.2 candidate hCandidate)
      simp [Atom.Satisfies, hArguments]
  | equal sort leftTerm rightTerm =>
      have hLeft :=
        termEval_eq_of_envAgreesOn left right leftTerm hEnv.1 (fun candidate hCandidate =>
            hEnv.2 candidate (supportContains_merge_left (right := termFreeSupport rightTerm) hCandidate))
      have hRight :=
        termEval_eq_of_envAgreesOn left right rightTerm hEnv.1 (fun candidate hCandidate =>
            hEnv.2 candidate (supportContains_merge_right (left := termFreeSupport leftTerm) hCandidate))
      simp [Atom.Satisfies, hLeft, hRight]
theorem literalSatisfies_iff_of_envAgreesOn
    [DecidableEq σ.BaseSort] {M : Structure σ}
    {left right : Env M} (literal : Literal σ) (hEnv : EnvAgreesOn (literalFreeSupport literal) left right) :
    literal.Satisfies left ↔ literal.Satisfies right := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · exact not_congr (atomSatisfies_iff_of_envAgreesOn atom hEnv)
      · exact atomSatisfies_iff_of_envAgreesOn atom hEnv
end Avatar
namespace Clause
def Covers  (source : Clause σ) (components : List (Clause σ)) : Prop := (∀ literal, literal ∈ source.literals.toList →
    ∃ component, component ∈ components ∧
      literal ∈ component.literals.toList) ∧
  ∀ component, component ∈ components →
    ∀ literal, literal ∈ component.literals.toList →
      literal ∈ source.literals.toList
def PairwiseSupportDisjoint
    [DecidableEq σ.BaseSort] : List (Clause σ) → Prop
  | [] => True
  | clause :: rest =>
      (∀ other, other ∈ rest →
        Avatar.SupportDisjoint (Avatar.clauseFreeSupport clause) (Avatar.clauseFreeSupport other)) ∧
        PairwiseSupportDisjoint rest
def ValidOnBoundStack
    [DecidableEq σ.BaseSort] {M : Structure σ} (base : Env M) (clause : Clause σ) : Prop :=
  ∀ env, env.WellSorted [] → Avatar.SameBoundStack env base →
    clause.Satisfies env
theorem satisfies_iff_of_envAgreesOn
    [DecidableEq σ.BaseSort] {M : Structure σ} {left right : Env M} (clause : Clause σ)
    (hEnv : Avatar.EnvAgreesOn (Avatar.clauseFreeSupport clause) left right) :
    clause.Satisfies left ↔ clause.Satisfies right := by
  constructor
  · rintro ⟨literal, hLiteral, hSat⟩
    refine ⟨literal, hLiteral, ?_⟩
    apply (Avatar.literalSatisfies_iff_of_envAgreesOn literal ?_).mp hSat
    constructor
    · exact hEnv.1
    · intro candidate hCandidate
      exact hEnv.2 candidate (Avatar.literalSupport_subset_clauseSupport (Array.mem_def.mp hLiteral) candidate hCandidate)
  · rintro ⟨literal, hLiteral, hSat⟩
    refine ⟨literal, hLiteral, ?_⟩
    apply (Avatar.literalSatisfies_iff_of_envAgreesOn literal ?_).mpr hSat
    constructor
    · exact hEnv.1
    · intro candidate hCandidate
      exact hEnv.2 candidate (Avatar.literalSupport_subset_clauseSupport (Array.mem_def.mp hLiteral) candidate hCandidate)
theorem containsLiteral_sound
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {clause : Clause σ} {literal : Literal σ} (hCheck : containsLiteral clause literal = true) :
    ∃ found, found ∈ clause.literals.toList ∧ found = literal :=
  containsLiteralList_sound (by
    simpa [containsLiteral] using hCheck)
theorem coversCheck_sound
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {source : Clause σ}
    {components : List (Clause σ)} (hCheck : coversCheck source components = true) :
    Covers source components := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hForward, hBackward⟩
  constructor
  · intro literal hLiteral
    have hAny := List.all_eq_true.mp hForward literal hLiteral
    rcases List.any_eq_true.mp hAny with
      ⟨component, hComponent, hContains⟩
    rcases containsLiteral_sound hContains with
      ⟨found, hFound, hFoundEq⟩
    subst found
    exact ⟨component, hComponent, hFound⟩
  · intro component hComponent literal hLiteral
    have hCovered := List.all_eq_true.mp hBackward component hComponent
    rcases allLiteralsCovered_sound hCovered hLiteral with
      ⟨found, hFound, hFoundEq⟩
    simpa [hFoundEq] using hFound
theorem pairwiseSupportDisjoint_sound
    [DecidableEq σ.BaseSort] {components : List (Clause σ)} (hCheck : Avatar.pairwiseSupportDisjoint components = true) :
    PairwiseSupportDisjoint components := by
  induction components with
  | nil =>
      trivial
  | cons head rest ih =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hRest⟩
      constructor
      · intro other hOther
        have hAt := List.all_eq_true.mp hHead other hOther
        have hNoOverlap :
            Avatar.supportsOverlap (Avatar.clauseFreeSupport head) (Avatar.clauseFreeSupport other) =
              false := by
          simpa using hAt
        exact Avatar.supportsOverlap_false_sound hNoOverlap
      · exact ih hRest
theorem satisfies_iff_exists_component_of_covers
    {M : Structure σ} {env : Env M} {source : Clause σ}
    {components : List (Clause σ)} (hCovers : Covers source components) :
    source.Satisfies env ↔
      ∃ component, component ∈ components ∧ component.Satisfies env := by
  constructor
  · rintro ⟨literal, hLiteral, hSat⟩
    rcases hCovers.1 literal (Array.mem_def.mp hLiteral) with
      ⟨component, hComponent, hComponentLiteral⟩
    exact ⟨component, hComponent, ⟨literal,
      Array.mem_def.mpr hComponentLiteral, hSat⟩⟩
  · rintro ⟨component, hComponent, ⟨literal, hLiteral, hSat⟩⟩
    exact ⟨literal,
      Array.mem_def.mpr (hCovers.2 component hComponent literal (Array.mem_def.mp hLiteral)), hSat⟩
private theorem exists_counterexample_of_not_valid
     [DecidableEq σ.BaseSort]
    {M : Structure σ} {base : Env M} {clause : Clause σ} (hNotValid : ¬ ValidOnBoundStack base clause) :
    ∃ env, env.WellSorted [] ∧ Avatar.SameBoundStack env base ∧
      ¬ clause.Satisfies env := by
  apply Classical.byContradiction
  intro hNoCounterexample
  apply hNotValid
  intro env hWellSorted hBound
  apply Classical.byContradiction
  intro hNotSat
  exact hNoCounterexample ⟨env, hWellSorted, hBound, hNotSat⟩
/--
若两两 typed 支持不交的所有 components 都不是固定 bound 栈有效的，则可合并各自
反例环境，得到一个同时否定全部 components 的类型正确共同环境。
-/
theorem exists_common_counterexample
    [DecidableEq σ.BaseSort] {M : Structure σ} (base : Env M) (components : List (Clause σ)) (hDisjoint : PairwiseSupportDisjoint components)
    (hNotValid : ∀ component, component ∈ components →
      ¬ ValidOnBoundStack base component) :
    ∃ env, env.WellSorted [] ∧ Avatar.SameBoundStack env base ∧
      ∀ component, component ∈ components → ¬ component.Satisfies env := by
  induction components with
  | nil =>
      exact ⟨Avatar.canonicalOnBoundStack M base,
        Avatar.canonicalOnBoundStack_wellSorted base,
        Avatar.canonicalOnBoundStack_sameBoundStack base, by
          intro component hMem
          cases hMem⟩
  | cons head tail ih =>
      rcases hDisjoint with ⟨hHeadDisjoint, hTailDisjoint⟩
      rcases exists_counterexample_of_not_valid (hNotValid head List.mem_cons_self) with
        ⟨headEnv, hHeadWellSorted, hHeadBound, hHeadFalse⟩
      have hTailNotValid :
          ∀ component, component ∈ tail →
            ¬ ValidOnBoundStack base component := by
        intro component hComponent
        exact hNotValid component (List.mem_cons_of_mem head hComponent)
      rcases ih hTailDisjoint hTailNotValid with
        ⟨tailEnv, hTailWellSorted, hTailBound, hTailFalse⟩
      let merged :=
        Avatar.overlay (Avatar.clauseFreeSupport head) headEnv tailEnv
      refine ⟨merged, ?_, ?_, ?_⟩
      · exact Avatar.overlay_wellSorted hHeadWellSorted hTailWellSorted
      · exact Avatar.SameBoundStack.trans
          Avatar.overlay_sameBoundStack_base hTailBound
      · intro component hComponent
        rcases List.mem_cons.mp hComponent with hHead | hTail
        · subst component
          intro hSat
          have hBound : Avatar.SameBoundStack tailEnv headEnv :=
            Avatar.SameBoundStack.trans hTailBound hHeadBound.symm
          have hAgree :=
            Avatar.overlay_agreesOn_source (support := Avatar.clauseFreeSupport head) hBound
          exact hHeadFalse ((satisfies_iff_of_envAgreesOn head hAgree).mp hSat)
        · intro hSat
          have hAgree :=
            Avatar.overlay_agreesOn_base_of_disjoint (source := headEnv) (base := tailEnv) (hHeadDisjoint component hTail)
          exact hTailFalse component hTail ((satisfies_iff_of_envAgreesOn component hAgree).mp hSat)
/--
HO-AVATAR fixed-bound-stack component decomposition 主定理。
当 components 双向覆盖 source 且 typed 自由变量支持两两不交时，source 对固定
bound 栈上的所有类型正确自由变量环境有效，当且仅当某个 component 具有同一性质。
-/
theorem validOnBoundStack_iff_exists_component
    [DecidableEq σ.BaseSort] {M : Structure σ} (base : Env M) (source : Clause σ) (components : List (Clause σ)) (hCovers : Covers source components)
    (hDisjoint : PairwiseSupportDisjoint components) :
    ValidOnBoundStack base source ↔
      ∃ component, component ∈ components ∧
        ValidOnBoundStack base component := by
  constructor
  · intro hSource
    apply Classical.byContradiction
    intro hNoComponent
    have hNotValid :
        ∀ component, component ∈ components →
          ¬ ValidOnBoundStack base component := by
      intro component hComponent hValid
      exact hNoComponent ⟨component, hComponent, hValid⟩
    rcases exists_common_counterexample base components hDisjoint hNotValid with
      ⟨env, hWellSorted, hBound, hFalse⟩
    have hSourceSat := hSource env hWellSorted hBound
    rcases (satisfies_iff_exists_component_of_covers hCovers).mp hSourceSat with
      ⟨component, hComponent, hSat⟩
    exact hFalse component hComponent hSat
  · rintro ⟨component, hComponent, hValid⟩ env hWellSorted hBound
    apply (satisfies_iff_exists_component_of_covers hCovers).mpr
    exact ⟨component, hComponent, hValid env hWellSorted hBound⟩
end Clause
namespace AvatarSelectorComponent
theorem selectors_ofLists  :
    ∀ {selectors : List GuardLit} {components : List (Clause σ)},
      selectors.length = components.length → (ofLists selectors components).map AvatarSelectorComponent.selector =
          selectors
  | [], [], _hLength => rfl
  | [], _ :: _, hLength => by simp at hLength
  | _ :: _, [], hLength => by simp at hLength
  | selector :: selectors, component :: components, hLength => by
      simp only [List.length_cons, Nat.succ.injEq] at hLength
      simp [ofLists, selectors_ofLists hLength]
theorem components_ofLists  :
    ∀ {selectors : List GuardLit} {components : List (Clause σ)},
      selectors.length = components.length → (ofLists selectors components).map AvatarSelectorComponent.component =
          components
  | [], [], _hLength => rfl
  | [], _ :: _, hLength => by simp at hLength
  | _ :: _, [], hLength => by simp at hLength
  | selector :: selectors, component :: components, hLength => by
      simp only [List.length_cons, Nat.succ.injEq] at hLength
      simp [ofLists, components_ofLists hLength]
theorem getElem?_ofLists
    {selectors : List GuardLit} {components : List (Clause σ)}
    {index : Nat} {selector : GuardLit} {component : Clause σ} (hSelector : selectors[index]? = some selector)
    (hComponent : components[index]? = some component) : (ofLists selectors components)[index]? =
      some ⟨selector, component⟩ := by
  induction index generalizing selectors components with
  | zero =>
      cases selectors <;> cases components <;>
        simp [ofLists] at hSelector hComponent ⊢
      exact ⟨hSelector, hComponent⟩
  | succ index ih =>
      cases selectors <;> cases components <;>
        simp [ofLists] at hSelector hComponent ⊢
      exact ih hSelector hComponent
def selectorClause (entries : List (AvatarSelectorComponent σ)) : PropResolution.Clause := (entries.map AvatarSelectorComponent.selector).toArray
def Compatible (entries : List (AvatarSelectorComponent σ)) : Prop :=
  ∀ left, left ∈ entries → ∀ right, right ∈ entries →
    left.selector.var = right.selector.var → left.component = right.component
theorem compatibleCheck_sound
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {entries : List (AvatarSelectorComponent σ)} (hCheck : compatibleCheck entries = true) :
    Compatible entries := by
  intro left hLeft right hRight hVariable
  have hLeftCheck := List.all_eq_true.mp hCheck left hLeft
  have hRightCheck := List.all_eq_true.mp hLeftCheck right hRight
  have hComponentCheck : left.component.eq right.component = true := by
    simpa [compatibleCheck, hVariable] using hRightCheck
  exact Clause.eq_sound left.component right.component hComponentCheck
/--
固定模型与 bound 栈上的 HO-AVATAR selector valuation。
selector 为真，当且仅当 registry 中同变量的某个 component 对所有同 bound 栈的
类型正确自由变量环境有效。
-/
def valuation  [DecidableEq σ.BaseSort]
    {M : Structure σ} (base : Env M) (entries : List (AvatarSelectorComponent σ)) :
    PropResolution.Valuation :=
  fun selectorVar =>
    ∃ entry, entry ∈ entries ∧ entry.selector.var = selectorVar ∧
      Clause.ValidOnBoundStack base entry.component
theorem holds_valuation_iff_component_valid
    [DecidableEq σ.BaseSort] {M : Structure σ} (base : Env M) (entries : List (AvatarSelectorComponent σ))
    (hPositive : ∀ item, item ∈ entries → item.selector.positive = true) (hCompatible : Compatible entries) {entry : AvatarSelectorComponent σ}
    (hEntry : entry ∈ entries) :
    entry.selector.Holds (valuation base entries) ↔
      Clause.ValidOnBoundStack base entry.component := by
  constructor
  · intro hSelector
    have hValue : valuation base entries entry.selector.var := by
      simpa [PropResolution.Lit.Holds, hPositive entry hEntry] using hSelector
    rcases hValue with
      ⟨validEntry, hValidEntry, hVariable, hValid⟩
    have hComponent : validEntry.component = entry.component :=
      hCompatible validEntry hValidEntry entry hEntry hVariable
    simpa only [hComponent] using hValid
  · intro hValid
    have hValue : valuation base entries entry.selector.var :=
      ⟨entry, hEntry, rfl, hValid⟩
    simpa [PropResolution.Lit.Holds, hPositive entry hEntry] using hValue
theorem selectorClause_satisfies_iff_exists_valid_in_registry
     [DecidableEq σ.BaseSort]
    {M : Structure σ} (base : Env M) (registry entries : List (AvatarSelectorComponent σ)) (hPositive :
      ∀ entry, entry ∈ registry → entry.selector.positive = true) (hCompatible : Compatible registry) (hSubset : ∀ entry, entry ∈ entries → entry ∈ registry) :
    PropResolution.Clause.Satisfies (valuation base registry) (selectorClause entries) ↔
      ∃ entry, entry ∈ entries ∧
        Clause.ValidOnBoundStack base entry.component := by
  constructor
  · rintro ⟨selector, hSelectorMem, hSelector⟩
    have hSelectorMem' :
        selector ∈ entries.map AvatarSelectorComponent.selector := by
      simpa [selectorClause] using hSelectorMem
    rcases List.mem_map.mp hSelectorMem' with
      ⟨entry, hEntry, hSelectorEq⟩
    subst selector
    have hEntryRegistry := hSubset entry hEntry
    exact ⟨entry, hEntry, (holds_valuation_iff_component_valid
        base registry hPositive hCompatible hEntryRegistry).mp hSelector⟩
  · rintro ⟨entry, hEntry, hValid⟩
    have hEntryRegistry := hSubset entry hEntry
    refine ⟨entry.selector, ?_, ?_⟩
    · have hMapped :
          entry.selector ∈ entries.map AvatarSelectorComponent.selector :=
        List.mem_map.mpr ⟨entry, hEntry, rfl⟩
      simpa [selectorClause] using hMapped
    · exact (holds_valuation_iff_component_valid
          base registry hPositive hCompatible hEntryRegistry).mpr hValid
end AvatarSelectorComponent
namespace AvatarSplitPayload
structure RegistryContract
    [DecidableEq σ.BaseSort] (payload : AvatarSplitPayload σ) : Prop where
  aligned :
    payload.selectors.toList.length = payload.componentClauses.length
  covers :
    Clause.Covers payload.source.clause payload.componentClauses
  pairwiseDisjoint :
    Clause.PairwiseSupportDisjoint payload.componentClauses
  selectorsPositive :
    ∀ selector, selector ∈ payload.selectors.toList →
      selector.positive = true
theorem registryContract_of_check
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {parents : Array Nat}
    {payload : AvatarSplitPayload σ} (hCheck : payload.check parents = true) :
    RegistryContract payload := by
  simp only [AvatarSplitPayload.check, Bool.and_eq_true_iff] at hCheck
  rcases hCheck with
    ⟨⟨⟨⟨⟨⟨_hSize, _hParent⟩, _hClause⟩, _hPartition⟩,
      hSelectors⟩, hDisjoint⟩, hCovers⟩
  simp only [Automation.AvatarSplit.selectorsOk,
    Bool.and_eq_true_iff] at hSelectors
  have hAlignedSize :
      payload.selectors.size = payload.partitions.size :=
    beq_iff_eq.mp hSelectors.1.1
  exact {
    aligned := by
      simpa [AvatarSplitPayload.componentClauses] using hAlignedSize
    covers := Clause.coversCheck_sound hCovers
    pairwiseDisjoint := Clause.pairwiseSupportDisjoint_sound hDisjoint
    selectorsPositive := by
      intro selector hSelector
      have hArray : selector ∈ payload.selectors :=
        Array.mem_def.mpr hSelector
      rcases Array.mem_iff_getElem.mp hArray with
        ⟨index, hIndex, hGet⟩
      have hAt := Array.all_eq_true.mp hSelectors.1.2 index hIndex
      simpa [hGet] using hAt
  }
theorem selectorClause_selectorComponents
    {payload : AvatarSplitPayload σ} (hAligned :
      payload.selectors.toList.length = payload.componentClauses.length) :
    AvatarSelectorComponent.selectorClause payload.selectorComponents =
      payload.selectors := by
  unfold selectorComponents AvatarSelectorComponent.selectorClause
  rw [AvatarSelectorComponent.selectors_ofLists hAligned]
theorem components_selectorComponents
    {payload : AvatarSplitPayload σ} (hAligned :
      payload.selectors.toList.length = payload.componentClauses.length) :
    payload.selectorComponents.map AvatarSelectorComponent.component =
      payload.componentClauses :=
  AvatarSelectorComponent.components_ofLists hAligned
theorem RegistryContract.selectorComponentsPositive
     [DecidableEq σ.BaseSort]
    {payload : AvatarSplitPayload σ} (hContract : RegistryContract payload) :
    ∀ entry, entry ∈ payload.selectorComponents →
      entry.selector.positive = true := by
  intro entry hEntry
  apply hContract.selectorsPositive
  have hMapped :
      entry.selector ∈
        payload.selectorComponents.map AvatarSelectorComponent.selector :=
    List.mem_map.mpr ⟨entry, hEntry, rfl⟩
  have hProjection :
      payload.selectorComponents.map AvatarSelectorComponent.selector =
        payload.selectors.toList := by
    simpa [selectorComponents] using
      AvatarSelectorComponent.selectors_ofLists hContract.aligned
  rw [hProjection] at hMapped
  exact hMapped
theorem selectorComponent_mem
    {payload : AvatarSplitPayload σ}
    {index : Nat} {indices : Array Nat} {selector : GuardLit} (hIndices : payload.partitions[index]? = some indices) (hSelector :
      Automation.AvatarSplit.selectorAt? payload.selectors index =
        some selector) :
    ⟨selector, Avatar.clauseAtIndices payload.source.clause indices⟩ ∈
      payload.selectorComponents := by
  have hSelectorList :
      payload.selectors.toList[index]? = some selector := by
    simpa [Automation.AvatarSplit.selectorAt?] using hSelector
  have hComponentList :
      payload.componentClauses[index]? =
        some (Avatar.clauseAtIndices payload.source.clause indices) := by
    have hPartitionList :
        payload.partitions.toList[index]? = some indices := by
      simpa using hIndices
    simp [AvatarSplitPayload.componentClauses, hPartitionList]
  have hEntryGet :
      payload.selectorComponents[index]? =
        some
          ⟨selector, Avatar.clauseAtIndices payload.source.clause indices⟩ :=
    AvatarSelectorComponent.getElem?_ofLists
      hSelectorList hComponentList
  rcases List.getElem?_eq_some_iff.mp hEntryGet with
    ⟨hIndex, hGet⟩
  rw [← hGet]
  exact List.getElem_mem hIndex
theorem source_valid_iff_selectors_satisfy_in_registry
     [DecidableEq σ.BaseSort]
    {M : Structure σ} (base : Env M) (payload : AvatarSplitPayload σ) (hContract : RegistryContract payload) (registry : List (AvatarSelectorComponent σ))
    (hPositive :
      ∀ entry, entry ∈ registry → entry.selector.positive = true) (hCompatible : AvatarSelectorComponent.Compatible registry) (hSubset :
      ∀ entry, entry ∈ payload.selectorComponents → entry ∈ registry) :
    Clause.ValidOnBoundStack base payload.source.clause ↔
      PropResolution.Clause.Satisfies (AvatarSelectorComponent.valuation base registry)
        payload.selectors := by
  have hComponents :=
    components_selectorComponents (payload := payload) hContract.aligned
  have hSelectors :=
    selectorClause_selectorComponents (payload := payload) hContract.aligned
  rw [← hSelectors]
  constructor
  · intro hSource
    rcases (Clause.validOnBoundStack_iff_exists_component
          base payload.source.clause payload.componentClauses
          hContract.covers hContract.pairwiseDisjoint).mp hSource with
      ⟨component, hComponentMem, hValid⟩
    have hEntryComponents :
        component ∈
          payload.selectorComponents.map
            AvatarSelectorComponent.component := by
      simpa [hComponents] using hComponentMem
    rcases List.mem_map.mp hEntryComponents with
      ⟨entry, hEntry, hComponentEq⟩
    cases hComponentEq
    exact (AvatarSelectorComponent.selectorClause_satisfies_iff_exists_valid_in_registry
          base registry payload.selectorComponents
          hPositive hCompatible hSubset).mpr
        ⟨entry, hEntry, hValid⟩
  · intro hSkeleton
    rcases (AvatarSelectorComponent.selectorClause_satisfies_iff_exists_valid_in_registry
            base registry payload.selectorComponents
            hPositive hCompatible hSubset).mp hSkeleton with
      ⟨entry, hEntry, hValid⟩
    apply (Clause.validOnBoundStack_iff_exists_component
        base payload.source.clause payload.componentClauses
        hContract.covers hContract.pairwiseDisjoint).mpr
    exact
      ⟨entry.component, by
        rw [← hComponents]
        exact List.mem_map.mpr ⟨entry, hEntry, rfl⟩, hValid⟩
end AvatarSplitPayload
namespace DAG
theorem avatarSelectorComponents_split
    {payload : Payload σ} {entry : AvatarSelectorComponent σ} (hEntry : entry ∈ avatarSelectorComponents payload) :
    ∃ split, payload = .avatarSplit split ∧
      entry ∈ split.selectorComponents := by
  cases payload <;> simp [avatarSelectorComponents] at hEntry ⊢
  exact hEntry
theorem mem_avatarSelectorRegistry_of_split
    {dag : DAG σ} {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    {entry : AvatarSelectorComponent σ} (hNode : dag.node? splitId = some splitNode) (hPayload : splitNode.payload = .avatarSplit payload)
    (hEntry : entry ∈ payload.selectorComponents) :
    entry ∈ dag.avatarSelectorRegistry := by
  have hNodeMem : splitNode ∈ dag.nodes.toList := by
    rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
    have hArray : splitNode ∈ dag.nodes := by
      rw [← hGet]
      exact Array.getElem_mem hIndex
    exact Array.mem_def.mp hArray
  unfold avatarSelectorRegistry
  apply List.mem_flatMap.mpr
  exact ⟨splitNode, hNodeMem, by
    simpa [avatarSelectorComponents, hPayload] using hEntry⟩
end DAG
namespace CheckedDAG
theorem avatarSplitRegistryContract
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ} (hNode : cert.dag.node? splitId = some splitNode) (hPayload : splitNode.payload = .avatarSplit payload) :
    AvatarSplitPayload.RegistryContract payload := by
  rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
  have hNodeAt : cert.dag.nodeAt splitId hIndex = splitNode := by
    simpa [DAG.nodeAt] using! hGet
  have hNodeCheck := (cert.contract.node_contract splitId hIndex).node_checked
  rw [hNodeAt] at hNodeCheck
  have hPayloadCheck : payload.check splitNode.parents = true := by
    simpa [Node.check, Payload.ruleCheck, hPayload] using
      Payload.ruleCheck_of_check hNodeCheck
  exact AvatarSplitPayload.registryContract_of_check hPayloadCheck
theorem avatarSelectorRegistry_positive
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ)) :
    ∀ entry, entry ∈ cert.dag.avatarSelectorRegistry →
      entry.selector.positive = true := by
  intro entry hEntry
  rcases List.mem_flatMap.mp hEntry with
    ⟨node, hNodeMem, hPayloadEntry⟩
  rcases DAG.avatarSelectorComponents_split hPayloadEntry with
    ⟨split, hPayload, hEntryLocal⟩
  have hArray : node ∈ cert.dag.nodes := Array.mem_def.mpr hNodeMem
  rcases Array.mem_iff_getElem.mp hArray with ⟨index, hIndex, hGet⟩
  have hNodeAt : cert.dag.nodeAt index hIndex = node := by
    simpa [DAG.nodeAt] using! hGet
  have hNodeCheck := (cert.contract.node_contract index hIndex).node_checked
  rw [hNodeAt] at hNodeCheck
  have hSplitCheck : split.check node.parents = true := by
    simpa [Node.check, Payload.ruleCheck, hPayload] using
      Payload.ruleCheck_of_check hNodeCheck
  exact
    AvatarSplitPayload.RegistryContract.selectorComponentsPositive (AvatarSplitPayload.registryContract_of_check hSplitCheck)
      entry hEntryLocal
end CheckedDAG
def AvatarComponentSelectorSemantics
    [DecidableEq σ.BaseSort] {M : Structure σ} (dag : DAG σ) (base : Env M) (valuation : PropResolution.Valuation) : Prop :=
  ∀ {splitId splitNode splitPayload componentIndex indices selector},
    dag.node? splitId = some splitNode →
      splitNode.payload = .avatarSplit splitPayload →
        splitPayload.partitions[componentIndex]? = some indices →
          Automation.AvatarSplit.selectorAt? splitPayload.selectors
              componentIndex =
            some selector → (selector.Holds valuation ↔
              Clause.ValidOnBoundStack base (Avatar.clauseAtIndices
                  splitPayload.source.clause indices))
def AvatarSplitSelectorSemantics
    [DecidableEq σ.BaseSort] {M : Structure σ} (dag : DAG σ) (base : Env M) (valuation : PropResolution.Valuation) : Prop :=
  ∀ {splitId splitNode splitPayload},
    dag.node? splitId = some splitNode →
      splitNode.payload = .avatarSplit splitPayload → (Clause.ValidOnBoundStack base splitPayload.source.clause ↔
          PropResolution.Clause.Satisfies valuation splitPayload.selectors)
namespace CheckedAvatarDAG
def selectorValuation
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : Structure σ} (base : Env M) : PropResolution.Valuation :=
  AvatarSelectorComponent.valuation base cert.checked.dag.avatarSelectorRegistry
theorem avatarSelectorRegistry_compatible
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ)) :
    AvatarSelectorComponent.Compatible
      cert.checked.dag.avatarSelectorRegistry :=
  AvatarSelectorComponent.compatibleCheck_sound cert.registryChecked
theorem componentSelectorSemantics
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : Structure σ} (base : Env M) :
    AvatarComponentSelectorSemantics cert.checked.dag base (cert.selectorValuation base) := by
  intro splitId splitNode splitPayload componentIndex indices selector
    hNode hPayload hIndices hSelector
  let entry : AvatarSelectorComponent σ :=
    ⟨selector,
      Avatar.clauseAtIndices splitPayload.source.clause indices⟩
  have hEntryLocal : entry ∈ splitPayload.selectorComponents := by
    exact AvatarSplitPayload.selectorComponent_mem hIndices hSelector
  have hEntryGlobal :
      entry ∈ cert.checked.dag.avatarSelectorRegistry :=
    DAG.mem_avatarSelectorRegistry_of_split
      hNode hPayload hEntryLocal
  exact
    AvatarSelectorComponent.holds_valuation_iff_component_valid
      base cert.checked.dag.avatarSelectorRegistry
      cert.checked.avatarSelectorRegistry_positive
      cert.avatarSelectorRegistry_compatible hEntryGlobal
theorem splitSelectorSemantics
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : Structure σ} (base : Env M) :
    AvatarSplitSelectorSemantics cert.checked.dag base (cert.selectorValuation base) := by
  intro splitId splitNode splitPayload hNode hPayload
  have hContract :=
    cert.checked.avatarSplitRegistryContract hNode hPayload
  have hSubset :
      ∀ entry, entry ∈ splitPayload.selectorComponents →
        entry ∈ cert.checked.dag.avatarSelectorRegistry := by
    intro entry hEntry
    exact DAG.mem_avatarSelectorRegistry_of_split
      hNode hPayload hEntry
  exact
    AvatarSplitPayload.source_valid_iff_selectors_satisfy_in_registry
      base splitPayload hContract
      cert.checked.dag.avatarSelectorRegistry
      cert.checked.avatarSelectorRegistry_positive
      cert.avatarSelectorRegistry_compatible hSubset
end CheckedAvatarDAG
/-! ## HO-AVATAR fixed-bound-stack 拓扑 soundness -/
namespace Node
/--
HO-AVATAR 的 fixed-bound-stack guarded 不变量。
selector 的语义依赖一个固定 bound 栈；自由变量仍在所有类型正确环境上量化。
-/
def BoundStackGuardedInvariant
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {M : Structure σ} (base : Env M) (valuation : PropResolution.Valuation) (problem : Problem σ) (node : Node σ) : Prop :=
  ∃ conclusion, node.conclusion? problem = some conclusion ∧
    ∀ env : Env M, env.WellSorted [] → Avatar.SameBoundStack env base →
      GuardsHold valuation node.guards → conclusion.Satisfies env
theorem boundStackGuardedInvariant_of_selector
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (base : Env M) (valuation : PropResolution.Valuation) (problem : Problem σ) (node : Node σ) (conclusion : Clause σ)
    (hConclusion : node.conclusion? problem = some conclusion) (selector : GuardLit) (hGuardEq : Guards.eq node.guards #[selector] = true) (hSemantic :
      selector.Holds valuation ↔
        Clause.ValidOnBoundStack base conclusion) :
    BoundStackGuardedInvariant base valuation problem node := by
  refine ⟨conclusion, hConclusion, ?_⟩
  intro env hEnv hBound hGuards
  have hSingleton : GuardsHold valuation #[selector] :=
    GuardsHold.of_guardSetEq hGuardEq hGuards
  have hSelectorMem :
      selector ∈ (Guards.canonical #[selector]).toList := by
    apply PropResolution.mem_canonicalClause_of_mem
    simp
  exact (hSemantic.mp (hSingleton selector hSelectorMem)) env hEnv hBound
end Node
namespace AvatarSplitPayload
theorem source_mem_of_check
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {parents : Array Nat}
    {payload : AvatarSplitPayload σ} (hCheck : payload.check parents = true) :
    payload.source.id ∈ parents.toList := by
  simp only [AvatarSplitPayload.check, Bool.and_eq_true_iff] at hCheck
  rcases hCheck with
    ⟨⟨⟨⟨⟨⟨_hSize, hParent⟩, _hClause⟩, _hPartition⟩,
      _hSelectors⟩, _hDisjoint⟩, _hCovers⟩
  exact ParentClause.mem_toList_of_idIn hParent
end AvatarSplitPayload
private theorem guardLit_eq_of_beq_eq_true {left right : GuardLit} (hEq : (left == right) = true) : left = right := by
  cases left with
  | mk leftVar leftPositive =>
      cases right with
      | mk rightVar rightPositive =>
          change ((leftVar == rightVar) && (leftPositive == rightPositive)) =
              true at hEq
          simp only [Bool.and_eq_true_iff, beq_iff_eq] at hEq
          cases hEq.1
          cases hEq.2
          rfl
namespace DAG
theorem avatarSplitNodeOk_sound
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {node : Node σ}
    {payload : AvatarSplitPayload σ} (hOk : dag.avatarSplitNodeOk node payload = true) :
    node.unguarded = true ∧
      dag.parentSnapshotChecked payload.source = true ∧
        ∃ sourceNode initialIndex,
          dag.node? payload.source.id = some sourceNode ∧
            sourceNode.unguarded = true ∧
              sourceNode.payload = .source initialIndex := by
  unfold avatarSplitNodeOk at hOk
  split at hOk <;> simp_all
  split at hOk <;> simp_all
theorem avatarComponentNodeOk_sound
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {node : Node σ}
    {payload : AvatarComponentPayload σ} (hOk : dag.avatarComponentNodeOk node payload = true) :
    dag.parentSnapshotChecked payload.split = true ∧
      ∃ splitNode splitPayload indices selector,
        dag.node? payload.split.id = some splitNode ∧
          splitNode.unguarded = true ∧
            splitNode.payload = .avatarSplit splitPayload ∧
              splitPayload.partitions[payload.componentIndex]? = some indices ∧
                Automation.AvatarSplit.selectorAt? splitPayload.selectors
                    payload.componentIndex =
                  some selector ∧
                  payload.component =
                    Avatar.clauseAtIndices splitPayload.source.clause indices ∧
                    payload.selector = selector ∧
                      Guards.eq node.guards #[selector] = true := by
  unfold avatarComponentNodeOk at hOk
  split at hOk <;> simp_all
  split at hOk <;> simp_all
  split at hOk <;> simp_all
  exact
    ⟨Clause.eq_sound _ _ hOk.2.2.1.1,
      guardLit_eq_of_beq_eq_true hOk.2.2.1.2⟩
theorem propAvatarSkeletonInitialLinkOk_sound
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} {parents : Array Nat} {link : PropAvatarSkeletonLink} (hOk : dag.propAvatarSkeletonInitialLinkOk parents link = true) :
    ∃ parentNode splitPayload,
      dag.node? link.parent = some parentNode ∧
        parentNode.unguarded = true ∧
          parentNode.payload = .avatarSplit splitPayload ∧
            link.skeleton =
              PropResolution.canonicalClause splitPayload.selectors := by
  unfold propAvatarSkeletonInitialLinkOk at hOk
  split at hOk <;> simp_all
  split at hOk <;> simp_all
  exact PropResolution.clauseEq_eq.mp hOk.2.2
end DAG
namespace CheckedDAG
theorem parentClauseSatisfiesOnBoundStack
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ)) (base : Env M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (parent : ParentClause σ) (hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList) (hParentSize : parent.id < cert.dag.nodes.size)
    (hSnapshotCheck : cert.dag.parentSnapshotChecked parent = true) (hParentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt parent.id hParentSize).guards) (env : Env M) (hEnv : env.WellSorted [])
    (hBound : Avatar.SameBoundStack env base) :
    parent.clause.Satisfies env := by
  have hInvariant := hParents parent.id hParentMem
  rcases DAG.parentSnapshotChecked_sound hSnapshotCheck with
    ⟨snapshotNode, snapshotConclusion, hNodeLookup,
      hSnapshotConclusion, hClauseEq⟩
  have hActualLookup :
      cert.dag.node? parent.id =
        some (cert.dag.nodeAt parent.id hParentSize) :=
    cert.dag.node?_eq_some_nodeAt hParentSize
  have hNodeEq :
      snapshotNode = cert.dag.nodeAt parent.id hParentSize :=
    Option.some.inj (hNodeLookup.symm.trans hActualLookup)
  subst snapshotNode
  rcases hInvariant with
    ⟨invariantConclusion, hInvariantConclusion, hSatisfies⟩
  have hConclusionEq : invariantConclusion = snapshotConclusion :=
    Option.some.inj (hInvariantConclusion.symm.trans hSnapshotConclusion)
  subst invariantConclusion
  simpa [hClauseEq] using
    hSatisfies env hEnv hBound hParentGuards
theorem avatarSplitBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ)) (base : Env M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : AvatarSplitPayload σ) (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .avatarSplit payload) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hNodeCheck := (cert.contract.node_contract index hIndex).node_checked
  rw [Node.check, hPayload] at hNodeCheck
  have hSplitCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents = true := by
    simpa [Payload.ruleCheck] using Payload.ruleCheck_of_check hNodeCheck
  have hSourceMem := AvatarSplitPayload.source_mem_of_check hSplitCheck
  have hSourceSize : payload.source.id < cert.dag.nodes.size :=
    Nat.lt_trans (cert.contract.parents_before index hIndex payload.source.id hSourceMem) hIndex
  have hNodeOk :
      cert.dag.avatarSplitNodeOk (cert.dag.nodeAt index hIndex) payload = true := by
    have hGuards := (cert.contract.node_contract index hIndex).guards_checked
    simpa [DAG.localNodeGuardsOk, hPayload] using! hGuards
  rcases DAG.avatarSplitNodeOk_sound hNodeOk with
    ⟨_hSplitUnguarded, hSnapshot, sourceNode, _initialIndex,
      hSourceLookup, hSourceUnguarded, _hSourcePayload⟩
  have hSourceNodeEq :
      sourceNode = cert.dag.nodeAt payload.source.id hSourceSize :=
    Option.some.inj (hSourceLookup.symm.trans (cert.dag.node?_eq_some_nodeAt hSourceSize))
  have hSourceGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt payload.source.id hSourceSize).guards :=
    Node.GuardsHold.of_isEmpty (by
      simpa [← hSourceNodeEq, Node.unguarded] using hSourceUnguarded)
  refine
    ⟨payload.source.clause,
      by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
  intro env hEnv hBound _hCurrentGuards
  exact cert.parentClauseSatisfiesOnBoundStack
    base valuation index hIndex hParents payload.source hSourceMem
    hSourceSize hSnapshot hSourceGuards env hEnv hBound
theorem avatarComponentBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ)) (base : Env M) (valuation : PropResolution.Valuation) (hSelectorSemantics :
      AvatarComponentSelectorSemantics cert.dag base valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size) (payload : AvatarComponentPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
        .avatarComponent payload) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hNodeOk :
      cert.dag.avatarComponentNodeOk (cert.dag.nodeAt index hIndex) payload = true := by
    have hGuards := (cert.contract.node_contract index hIndex).guards_checked
    simpa [DAG.localNodeGuardsOk, hPayload] using! hGuards
  rcases DAG.avatarComponentNodeOk_sound hNodeOk with
    ⟨_hSnapshot, splitNode, splitPayload, indices, selector,
      hSplitLookup, _hSplitUnguarded, hSplitPayload, hIndices,
      hSelector, hComponent, hPayloadSelector, hGuardEq⟩
  have hSemanticSource :=
    hSelectorSemantics hSplitLookup hSplitPayload hIndices hSelector
  have hSemantic :
      selector.Holds valuation ↔
        Clause.ValidOnBoundStack base payload.component := by
    simpa [hComponent] using hSemanticSource
  apply Node.boundStackGuardedInvariant_of_selector
    base valuation cert.dag.problem (cert.dag.nodeAt index hIndex)
    payload.component
  · simp [Node.conclusion?, hPayload, Payload.conclusion?]
  · simpa [hPayloadSelector] using hGuardEq
  · exact hSemantic
end CheckedDAG
namespace CheckedAvatarDAG
/--
checked HO-AVATAR split 的 selector skeleton 在 canonical registry valuation 下成立。
该定理同时消费 residual initial 的局部检查与整图 split 链接，因而不能伪造
selector skeleton，也不会把对象 atom-map 变量误当作 AVATAR selector。
-/
theorem avatarSkeletonInitialSatisfies
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ)) (base : Env M) (index : Nat) (hIndex : index < cert.checked.dag.nodes.size) (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.checked.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem (cert.checked.dag.nodeAt parent (Nat.lt_trans
              (cert.checked.contract.parents_before index hIndex parent hParent)
              hIndex))) (payload : PropositionalClosurePayload σ) (initial : PropResolution.InitialClause) (link : PropAvatarSkeletonLink) (env : Env M)
    (hLinkCheck :
      link.check (cert.checked.dag.nodeAt index hIndex).parents
        payload.atomMap initial = true) (hDagOk :
      cert.checked.dag.propAvatarSkeletonInitialLinkOk (cert.checked.dag.nodeAt index hIndex).parents link = true) :
    PropResolution.Clause.Satisfies (PropLiteralLink.valuation (cert.selectorValuation base) payload.atomMap env)
      initial.clause := by
  unfold PropAvatarSkeletonLink.check at hLinkCheck
  rcases Bool.and_eq_true_iff.mp hLinkCheck with
    ⟨hLinkPrefix, hInitialEqBool⟩
  rcases Bool.and_eq_true_iff.mp hLinkPrefix with
    ⟨hParentContains, hOutside⟩
  have hInitialEq : initial.clause = link.skeleton :=
    PropResolution.clauseEq_eq.mp hInitialEqBool
  have hParentMem :
      link.parent ∈ (cert.checked.dag.nodeAt index hIndex).parents.toList := by
    exact Array.mem_def.mp (by simpa using hParentContains)
  have hParentSize : link.parent < cert.checked.dag.nodes.size :=
    Nat.lt_trans (cert.checked.contract.parents_before index hIndex link.parent hParentMem)
      hIndex
  rcases DAG.propAvatarSkeletonInitialLinkOk_sound hDagOk with
    ⟨parentNode, splitPayload, hParentLookup, hParentUnguarded,
      hParentPayload, hSkeletonEq⟩
  have hParentNodeEq :
      parentNode = cert.checked.dag.nodeAt link.parent hParentSize :=
    Option.some.inj (hParentLookup.symm.trans (cert.checked.dag.node?_eq_some_nodeAt hParentSize))
  have hParentPayload' : (cert.checked.dag.nodeAt link.parent hParentSize).payload =
        .avatarSplit splitPayload := by
    simpa [← hParentNodeEq] using hParentPayload
  have hParentGuards :
      Node.GuardsHold (cert.selectorValuation base) (cert.checked.dag.nodeAt link.parent hParentSize).guards :=
    Node.GuardsHold.of_isEmpty (by
      simpa [← hParentNodeEq, Node.unguarded] using hParentUnguarded)
  rcases hParents link.parent hParentMem with
    ⟨parentConclusion, hParentConclusion, hParentSatisfies⟩
  have hParentConclusionEq :
      parentConclusion = splitPayload.source.clause := by
    rw [Node.conclusion?, hParentPayload', Payload.conclusion?]
      at hParentConclusion
    exact Option.some.inj hParentConclusion.symm
  have hSourceValid :
      Clause.ValidOnBoundStack base splitPayload.source.clause := by
    intro sourceEnv hSourceEnv hBound
    simpa [hParentConclusionEq] using
      hParentSatisfies sourceEnv hSourceEnv hBound hParentGuards
  have hSkeletonBase :
      PropResolution.Clause.Satisfies (cert.selectorValuation base) link.skeleton := by
    have hSelectors := (cert.splitSelectorSemantics base
        hParentLookup hParentPayload).mp hSourceValid
    rw [hSkeletonEq]
    exact PropResolution.Clause.satisfies_canonical_iff.mpr hSelectors
  rw [hInitialEq]
  exact hSkeletonBase.transfer fun lit hMem hHolds =>
    (PropLiteralLink.holds_valuation_iff_of_outsideAtomMap
      (Array.all_eq_true'.mp hOutside lit (Array.mem_def.mpr hMem))).mpr hHolds

theorem avatarSplitBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ)) (base : Env M) (index : Nat) (hIndex : index < cert.checked.dag.nodes.size) (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.checked.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem (cert.checked.dag.nodeAt parent (Nat.lt_trans
              (cert.checked.contract.parents_before index hIndex parent hParent)
              hIndex))) (payload : AvatarSplitPayload σ) (hPayload : (cert.checked.dag.nodeAt index hIndex).payload =
        .avatarSplit payload) :
    Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem (cert.checked.dag.nodeAt index hIndex) :=
  cert.checked.avatarSplitBoundStackGuardedTopologicalStep
    base (cert.selectorValuation base) index hIndex hParents payload hPayload
theorem avatarComponentBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ)) (base : Env M) (index : Nat) (hIndex : index < cert.checked.dag.nodes.size)
    (payload : AvatarComponentPayload σ) (hPayload : (cert.checked.dag.nodeAt index hIndex).payload =
        .avatarComponent payload) :
    Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem (cert.checked.dag.nodeAt index hIndex) :=
  cert.checked.avatarComponentBoundStackGuardedTopologicalStep
    base (cert.selectorValuation base) (cert.componentSelectorSemantics base)
    index hIndex payload hPayload
end CheckedAvatarDAG
/-! ## HO-AVATAR 专用整图支持边界 -/
namespace PropInitialJustification
def avatarSoundnessSupported  :
    PropInitialJustification σ → Bool
  | .parentClause _ => true
  | .guardActivationClause _ => true
  | .propLearnedClause _ => true
  | .avatarSkeleton _ => true
end PropInitialJustification
namespace PropositionalClosurePayload
def avatarSoundnessSupported (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialJustifications.all
    PropInitialJustification.avatarSoundnessSupported
end PropositionalClosurePayload
namespace Payload
/--
HO-AVATAR fixed-bound-stack 整图允许的 payload。
这是独立于通用 `guardedSoundnessSupported` 的专用边界；新增 payload 时必须在本模块
提供对应拓扑证明后才能加入。
-/
def avatarSoundnessSupported  : Payload σ → Bool
  | .residualCdcl payload => payload.avatarSoundnessSupported
  | _ => true
end Payload
namespace DAG
def avatarSoundnessSupported  (dag : DAG σ) : Bool :=
  dag.nodes.all fun node => node.payload.avatarSoundnessSupported
def BoundStackGuardedInvariant
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {M : Structure σ} (dag : DAG σ) (base : Env M) (valuation : PropResolution.Valuation) : Prop :=
  ∀ index (hIndex : index < dag.nodes.size),
    Node.BoundStackGuardedInvariant base valuation dag.problem (dag.nodeAt index hIndex)
theorem avatarSoundnessSupported_of_eq_true
     {dag : DAG σ} (hSupported : dag.avatarSoundnessSupported = true) :
    ∀ index (hIndex : index < dag.nodes.size), (dag.nodeAt index hIndex).payload.avatarSoundnessSupported = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hSupported
  simpa [avatarSoundnessSupported, nodeAt] using! hAll index hIndex
end DAG
namespace CheckedDAG
/--
当前节点 guards 成立时，fixed-bound-stack 父不变量可回放任意 payload 父快照。
-/
theorem parentClauseSatisfiesOnBoundStackOfGuards
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ)) (base : Env M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hMerge :
      DAG.payloadMergesParentGuards (cert.dag.nodeAt index hIndex).payload = true) (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (hCurrentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards) (parent : ParentClause σ) (hParent :
      parent ∈ (cert.dag.nodeAt index hIndex).payload.parentClauses.toList) (env : Env M) (hEnv : env.WellSorted []) (hBound : Avatar.SameBoundStack env base) :
    parent.clause.Satisfies env := by
  have hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    Payload.parentIdsIn_of_check ((cert.contract.node_contract index hIndex).node_checked) parent hParent
  have hParentSize : parent.id < cert.dag.nodes.size :=
    Nat.lt_trans (cert.contract.parents_before index hIndex parent.id hParentMem) hIndex
  have hParentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt parent.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex hMerge
      parent.id hParentMem hParentSize hCurrentGuards
  have hSnapshot :
      cert.dag.parentSnapshotChecked parent = true :=
    DAG.parentSnapshotChecked_of_eq_true cert.contract.parent_snapshots_checked
      index hIndex parent hParent
  exact cert.parentClauseSatisfiesOnBoundStack
    base valuation index hIndex hParents parent hParentMem hParentSize
    hSnapshot hParentGuards env hEnv hBound
theorem sourceBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ)) (base : Env M) (valuation : PropResolution.Valuation) (hProblem : cert.dag.problem.Valid M)
    (index : Nat) (hIndex : index < cert.dag.nodes.size) (initialIndex : Nat) (hSource : (cert.dag.nodeAt index hIndex).payload = .source initialIndex) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hNodeCheck := (cert.contract.node_contract index hIndex).node_checked
  rw [Node.check, hSource] at hNodeCheck
  cases hLookup :
      cert.dag.problem.initialClauses[initialIndex]? with
  | none =>
      have hRuleCheck := Payload.ruleCheck_of_check hNodeCheck
      simp [Payload.ruleCheck, hLookup] at hRuleCheck
  | some initial =>
      refine
        ⟨initial,
          by simp [Node.conclusion?, hSource, Payload.conclusion?, hLookup],
          ?_⟩
      intro env hEnv _hBound _hGuards
      exact hProblem env hEnv initialIndex initial hLookup
/--
通用 HO payload 在 fixed-bound-stack 上的一步 guarded 回放。
substitution 与 standardize-apart 通过保持 bound 栈的语义环境消费父不变量；其余规则
在当前环境中直接消费通过快照复核的父字句。
-/
theorem ordinaryBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ)) (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M) (base : Env M) (valuation : PropResolution.Valuation)
    (hProblem : cert.dag.problem.Valid M) (index : Nat) (hIndex : index < cert.dag.nodes.size) (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (hPayloadSupported :
      (cert.dag.nodeAt index hIndex).payload.soundnessSupported = true) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hMergeOfParent :
      ∀ parent,
        parent ∈ (cert.dag.nodeAt index hIndex).payload.parentClauses.toList →
          DAG.payloadMergesParentGuards (cert.dag.nodeAt index hIndex).payload = true := by
    intro parent hParent
    cases hPayload : (cert.dag.nodeAt index hIndex).payload <;>
      simp [hPayload, Payload.parentClauses, Payload.soundnessSupported,
        Payload.soundnessSupportedWithWitness, DAG.payloadMergesParentGuards]
        at hParent hPayloadSupported ⊢
  have hParentSat :
      ∀ parent,
        parent ∈ (cert.dag.nodeAt index hIndex).payload.parentClauses.toList →
          ∀ env : Env M, env.WellSorted [] →
            Avatar.SameBoundStack env base →
              Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
                parent.clause.Satisfies env := by
    intro parent hParent env hEnv hBound hGuards
    exact cert.parentClauseSatisfiesOnBoundStackOfGuards
      base valuation index hIndex (hMergeOfParent parent hParent)
      hParents hGuards parent hParent env hEnv hBound
  have hNodeCheck := (cert.contract.node_contract index hIndex).node_checked
  have hRuleCheck := Payload.ruleCheck_of_check hNodeCheck
  cases hPayload : (cert.dag.nodeAt index hIndex).payload
  case source initialIndex =>
    exact cert.sourceBoundStackGuardedTopologicalStep
      base valuation hProblem index hIndex initialIndex hPayload
  case avatarSplit | avatarComponent | theoryConflict | propositionalLearnedClause | residualCdcl =>
    simp [hPayload, Payload.soundnessSupported,
      Payload.soundnessSupportedWithWitness] at hPayloadSupported
  all_goals
    refine ⟨_, by simp only [Node.conclusion?, hPayload, Payload.conclusion?]; rfl, ?_⟩
    intro env hEnv hBound hGuards
    simp only [hPayload, Payload.ruleCheck] at hRuleCheck
  case betaEta payload =>
    have hPayloadCheck : payload.check = true := (Bool.and_eq_true_iff.mp hRuleCheck).2
    exact BetaEta.Payload.sound contract payload env hEnv hPayloadCheck
  case substitution evidence =>
    simp only [Substitution.Evidence.check, Bool.and_eq_true_iff]
      at hRuleCheck
    rcases hRuleCheck with
      ⟨⟨⟨_hParent, _hParentCheck⟩, hSubstitutionCheck⟩,
        _hConclusionCheck⟩
    have hAdmissible : evidence.substitution.Admissible :=
      TermSubstitution.check_sound hSubstitutionCheck
    let targetEnv :=
      TermSubstitution.semanticEnv evidence.substitution env
    have hTargetEnv : targetEnv.WellSorted [] :=
      TermSubstitution.semanticEnv_wellSorted hAdmissible hEnv
    have hEnvMatches :=
      TermSubstitution.semanticEnv_matches (substitution := evidence.substitution) (sourceEnv := env)
    have hTargetBound :
        Avatar.SameBoundStack targetEnv base := by
      intro boundIndex
      exact (hEnvMatches.1 boundIndex).trans (hBound boundIndex)
    have hParent :=
      hParentSat evidence.parent (by simp [hPayload, Payload.parentClauses])
        targetEnv hTargetEnv hTargetBound hGuards
    exact (Clause.satisfies_applySubstitution_iff_of_envMatches
        hAdmissible hEnvMatches evidence.parent.clause).mpr hParent
  case standardizeApart evidence =>
    let targetEnv :=
      FreeVarRenaming.semanticEnv evidence.offset env
    have hTargetEnv : targetEnv.WellSorted [] :=
      FreeVarRenaming.semanticEnv_wellSorted hEnv
    have hEnvMatches :=
      FreeVarRenaming.semanticEnv_matches (offset := evidence.offset) (sourceEnv := env)
    have hTargetBound :
        Avatar.SameBoundStack targetEnv base := by
      intro boundIndex
      exact (hEnvMatches.1 boundIndex).trans (hBound boundIndex)
    have hParent :=
      hParentSat evidence.parent (by simp [hPayload, Payload.parentClauses])
        targetEnv hTargetEnv hTargetBound hGuards
    exact (Clause.satisfies_renameFreeVars_iff_of_envMatches
        hEnvMatches evidence.parent.clause).mpr hParent
  case resolution evidence =>
    exact Clause.satisfies_resolutionResult (hParentSat evidence.left (by simp [hPayload, Payload.parentClauses])
        env hEnv hBound hGuards) (hParentSat evidence.right (by simp [hPayload, Payload.parentClauses])
        env hEnv hBound hGuards)
  case factoring evidence =>
    simp only [Factoring.Evidence.check, Bool.and_eq_true_iff]
      at hRuleCheck
    have hCovered :
        evidence.parent.clause.allLiteralsCovered evidence.conclusion =
          true :=
      hRuleCheck.1.2.2
    exact Clause.satisfies_of_allLiteralsCovered hCovered (hParentSat evidence.parent (by simp [hPayload, Payload.parentClauses])
        env hEnv hBound hGuards)
  case equalityResolution evidence =>
    simp only [EqualityResolution.Evidence.check,
      Bool.and_eq_true_iff] at hRuleCheck
    have hTerm :
        StructuralEq.term evidence.left evidence.right = true :=
      hRuleCheck.1.2.1
    exact Clause.satisfies_equalityResolutionResult hTerm (hParentSat evidence.parent (by simp [hPayload, Payload.parentClauses])
        env hEnv hBound hGuards)
  case booleanExtensionality evidence =>
    apply Clause.satisfies_normalize
    exact Clause.satisfies_replaceLiteralAtEnd (evidence.selected_of_check hRuleCheck) ((evidence.satisfies_iff_replacement
        contract hRuleCheck env hEnv).mp) (hParentSat evidence.parent (by simp [hPayload, Payload.parentClauses])
        env hEnv hBound hGuards)
  case rewrite kind evidence =>
    exact evidence.sound contract hRuleCheck (hParentSat evidence.equality (by simp [hPayload, Payload.parentClauses])
        env hEnv hBound hGuards) (hParentSat evidence.target (by simp [hPayload, Payload.parentClauses])
        env hEnv hBound hGuards)
  case argumentCongruence evidence =>
    exact evidence.sound (hParentSat evidence.parent (by simp [hPayload, Payload.parentClauses])
        env hEnv hBound hGuards)
  case functionExtensionality evidence =>
    exact evidence.sound witnessContract hEnv hRuleCheck (hParentSat evidence.parent (by simp [hPayload, Payload.parentClauses])
        env hEnv hBound hGuards)

theorem theoryConflictBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ)) (base : Env M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : TheoryConflictPayload σ) (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hCheck := (cert.contract.node_contract index hIndex).node_checked
  rw [Node.check, hPayload] at hCheck
  have hConflictCheck :
      payload.conflict.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
        payload.conflict.clause.isEmpty = true := by
    simpa [Payload.ruleCheck, TheoryConflictPayload.check] using
      Bool.and_eq_true_iff.mp (Payload.ruleCheck_of_check hCheck)
  have hParentMem :
      payload.conflict.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hConflictCheck.1
  have hParentSize : payload.conflict.id < cert.dag.nodes.size :=
    Nat.lt_trans (cert.contract.parents_before index hIndex payload.conflict.id hParentMem)
      hIndex
  have hSnapshot :
      cert.dag.parentSnapshotChecked payload.conflict = true :=
    DAG.parentSnapshotChecked_of_eq_true cert.contract.parent_snapshots_checked
      index hIndex payload.conflict (by
        simp [hPayload, Payload.parentClauses,
          TheoryConflictPayload.parentClauses])
  refine
    ⟨{ literals := #[] },
      by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
  intro env hEnv hBound hCurrentGuards
  have hParentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt payload.conflict.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex (by simp [hPayload, DAG.payloadMergesParentGuards])
      payload.conflict.id hParentMem hParentSize hCurrentGuards
  have hParentSat :=
    cert.parentClauseSatisfiesOnBoundStack
      base valuation index hIndex hParents payload.conflict hParentMem
      hParentSize hSnapshot hParentGuards env hEnv hBound
  exact False.elim (Clause.not_satisfies_of_isEmpty hConflictCheck.2 hParentSat)
theorem propositionalLearnedClauseBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ)) (base : Env M) (valuation : PropResolution.Valuation) (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt parent (Nat.lt_trans
              (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : PropositionalLearnedClausePayload) (hPayload :
      (cert.dag.nodeAt index hIndex).payload =
        .propositionalLearnedClause payload) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hCheck := (cert.contract.node_contract index hIndex).node_checked
  rw [Node.check, hPayload] at hCheck
  have hParentIn : (cert.dag.nodeAt index hIndex).parents.contains payload.conflict =
        true := by
    simpa [Payload.ruleCheck, PropositionalLearnedClausePayload.check] using
      Payload.ruleCheck_of_check hCheck
  have hParentMem :
      payload.conflict ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    Array.mem_def.mp (by simpa using hParentIn)
  have hParentSize : payload.conflict < cert.dag.nodes.size :=
    Nat.lt_trans (cert.contract.parents_before index hIndex payload.conflict hParentMem)
      hIndex
  have hGuardCheck := (cert.contract.node_contract index hIndex).guards_checked
  have hParentLookup :
      cert.dag.node? payload.conflict =
        some (cert.dag.nodeAt payload.conflict hParentSize) :=
    cert.dag.node?_eq_some_nodeAt hParentSize
  unfold DAG.localNodeGuardsOk at hGuardCheck
  rw [if_neg (by simp [hPayload, DAG.payloadMergesParentGuards])]
    at hGuardCheck
  simp only [hPayload] at hGuardCheck
  rw [hParentLookup] at hGuardCheck
  rcases Bool.and_eq_true_iff.mp hGuardCheck with
    ⟨hPrefix, _hLearned⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with
    ⟨hConflictPrefix, hGuardEq⟩
  rcases Bool.and_eq_true_iff.mp hConflictPrefix with
    ⟨_hArtifact, hTheory⟩
  refine
    ⟨{ literals := #[] },
      by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
  intro env hEnv hBound hCurrentGuards
  have hParentGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt payload.conflict hParentSize).guards :=
    Node.GuardsHold.of_guardSetEq hGuardEq hCurrentGuards
  rcases hParents payload.conflict hParentMem with
    ⟨parentConclusion, hParentConclusion, hParentSat⟩
  have hParentEmpty : parentConclusion.isEmpty = true := by
    have hParentTheory : (cert.dag.nodeAt payload.conflict hParentSize).theoryConflict
          cert.dag.problem = true :=
      hTheory
    unfold Node.theoryConflict at hParentTheory
    rw [hParentConclusion] at hParentTheory
    exact (Bool.and_eq_true_iff.mp hParentTheory).2
  exact False.elim (Clause.not_satisfies_of_isEmpty hParentEmpty (hParentSat env hEnv hBound hParentGuards))
end CheckedDAG
namespace CheckedAvatarDAG
private theorem avatarPropClosureJustificationCheckAt
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {payload : PropositionalClosurePayload σ} (hCheck : payload.justificationsCheck parents = true)
    {slot : Nat} (hSlot : slot < payload.initialClauses.size) :
    ∃ hJust : slot < payload.initialJustifications.size,
      payload.initialJustifications[slot].check parents payload.atomMap
        payload.initialClauses[slot] = true := by
  unfold PropositionalClosurePayload.justificationsCheck at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with
    ⟨hSizeBool, hAllBool⟩
  have hSizeEq :
      payload.initialClauses.size =
        payload.initialJustifications.size :=
    beq_iff_eq.mp hSizeBool
  have hJust : slot < payload.initialJustifications.size := by
    simpa [hSizeEq] using hSlot
  refine ⟨hJust, ?_⟩
  have hAt := (Array.all_eq_true.mp hAllBool) slot (by
      simpa [Array.size_mapIdx] using hSlot)
  have hJustGet :
      payload.initialJustifications[slot]? =
        some payload.initialJustifications[slot] :=
    Array.getElem?_eq_some_iff.mpr ⟨hJust, rfl⟩
  simpa [Array.getElem_mapIdx, hJustGet] using hAt
private theorem avatarPropClosureJustificationSupportedAt
    {payload : PropositionalClosurePayload σ} (hSupported : payload.avatarSoundnessSupported = true)
    {slot : Nat} (hSlot : slot < payload.initialJustifications.size) :
    payload.initialJustifications[slot].avatarSoundnessSupported = true := by
  have hAll := Array.all_eq_true.mp hSupported
  simpa [PropositionalClosurePayload.avatarSoundnessSupported] using
    hAll slot hSlot
/--
HO-AVATAR residual CDCL 的 fixed-bound-stack 拓扑步骤。
parent、activation 与 learned initial 消费对象 DAG 父不变量；selector skeleton initial
只通过 checked registry 与真实 split descriptor 的专用语义入口。
-/
theorem residualCdclBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ)) (base : Env M) (index : Nat) (hIndex : index < cert.checked.dag.nodes.size) (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.checked.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem (cert.checked.dag.nodeAt parent (Nat.lt_trans
              (cert.checked.contract.parents_before index hIndex parent hParent)
              hIndex))) (payload : PropositionalClosurePayload σ) (hPayload : (cert.checked.dag.nodeAt index hIndex).payload =
        .residualCdcl payload) (hPayloadSupported : payload.avatarSoundnessSupported = true) :
    Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem (cert.checked.dag.nodeAt index hIndex) := by
  have hCheck := (cert.checked.contract.node_contract index hIndex).node_checked
  rw [Node.check, hPayload] at hCheck
  have hResidualCheck : (!((cert.checked.dag.nodeAt index hIndex).parents.isEmpty) &&
        payload.check (cert.checked.dag.nodeAt index hIndex).parents) = true := by
    simpa [Payload.ruleCheck] using Payload.ruleCheck_of_check hCheck
  have hClosureCheck :
      payload.check (cert.checked.dag.nodeAt index hIndex).parents = true := (Bool.and_eq_true_iff.mp hResidualCheck).2
  have hCheckedUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof =
        true := (Bool.and_eq_true_iff.mp hClosureCheck).1
  have hJustifications :
      payload.justificationsCheck (cert.checked.dag.nodeAt index hIndex).parents = true := (Bool.and_eq_true_iff.mp hClosureCheck).2
  have hInitialLinks := (cert.checked.contract.node_contract index hIndex).prop_initial_links_checked
  have hDagInitials :
      payload.initialJustifications.all (fun justification =>
          cert.checked.dag.propInitialJustificationDagOk (cert.checked.dag.nodeAt index hIndex).parents
            justification) = true := by
    simpa [DAG.propInitialLinksOk, hPayload] using hInitialLinks
  refine
    ⟨{ literals := #[] },
      by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
  intro env hEnv hBound _hCurrentGuards
  let checkedCert : PropResolution.CheckedUnsatCertificate := {
    initialClauses := payload.initialClauses
    proof := payload.proof
    checked := hCheckedUnsat
  }
  apply False.elim
  apply checkedCert.sound (valuation :=
      PropLiteralLink.valuation (cert.selectorValuation base) payload.atomMap env)
  intro initial hInitialMem
  have hInitialArray : initial ∈ payload.initialClauses :=
    Array.mem_def.mpr hInitialMem
  rcases Array.mem_iff_getElem.mp hInitialArray with
    ⟨slot, hSlot, hInitialGet⟩
  rcases avatarPropClosureJustificationCheckAt hJustifications hSlot with
    ⟨hJustSlot, hJustificationCheck⟩
  have hDagOk := (Array.all_eq_true.mp hDagInitials) slot hJustSlot
  have _hJustificationSupported :=
    avatarPropClosureJustificationSupportedAt
      hPayloadSupported hJustSlot
  cases hJustification : payload.initialJustifications[slot] with
  | parentClause link =>
      have hLinkCheck :
          link.check (cert.checked.dag.nodeAt index hIndex).parents
            payload.atomMap initial = true := by
        simpa [PropInitialJustification.check, hJustification, hInitialGet]
          using hJustificationCheck
      unfold PropParentClauseLink.check at hLinkCheck
      rcases Bool.and_eq_true_iff.mp hLinkCheck with
        ⟨hPrefix, hLiteralChecks⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hPrefix, hInitialEqBool⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hParentInBool, hObjectEqBool⟩
      have hInitialEq : initial.clause = link.encodedClause :=
        PropResolution.clauseEq_eq.mp hInitialEqBool
      have hObjectEq : link.parent.clause = link.objectClause :=
        Clause.eq_sound
          link.parent.clause link.objectClause hObjectEqBool
      have hDagParent :
          cert.checked.dag.propParentInitialLinkOk (cert.checked.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using
          hDagOk
      unfold DAG.propParentInitialLinkOk at hDagParent
      rcases Bool.and_eq_true_iff.mp hDagParent with
        ⟨hDagPrefix, hParentUnguardedCheck⟩
      rcases Bool.and_eq_true_iff.mp hDagPrefix with
        ⟨_hDagParentIn, hSnapshot⟩
      have hParentMem :
          link.parent.id ∈ (cert.checked.dag.nodeAt index hIndex).parents.toList :=
        ParentClause.mem_toList_of_idIn hParentInBool
      have hParentSize :
          link.parent.id < cert.checked.dag.nodes.size :=
        Nat.lt_trans (cert.checked.contract.parents_before
            index hIndex link.parent.id hParentMem)
          hIndex
      have hParentLookup :
          cert.checked.dag.node? link.parent.id =
            some (cert.checked.dag.nodeAt link.parent.id hParentSize) :=
        cert.checked.dag.node?_eq_some_nodeAt hParentSize
      rw [hParentLookup] at hParentUnguardedCheck
      have hParentGuards :
          Node.GuardsHold (cert.selectorValuation base) (cert.checked.dag.nodeAt
              link.parent.id hParentSize).guards :=
        Node.GuardsHold.of_isEmpty hParentUnguardedCheck
      have hObjectSat : link.objectClause.Satisfies env := by
        have hParentSat :=
          cert.checked.parentClauseSatisfiesOnBoundStack
            base (cert.selectorValuation base) index hIndex hParents
            link.parent hParentMem hParentSize hSnapshot hParentGuards
            env hEnv hBound
        simpa [hObjectEq] using hParentSat
      simpa [hInitialEq] using
        PropParentClauseLink.encodedClause_satisfies_of_object (base := cert.selectorValuation base) (env := env)
          hLiteralChecks hObjectSat
  | guardActivationClause link =>
      have hLinkCheck :
          link.check (cert.checked.dag.nodeAt index hIndex).parents
            payload.atomMap initial = true := by
        simpa [PropInitialJustification.check, hJustification, hInitialGet]
          using hJustificationCheck
      unfold PropGuardActivationLink.check at hLinkCheck
      rcases Bool.and_eq_true_iff.mp hLinkCheck with
        ⟨hPrefix, hLiteralChecks⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hPrefix, hGuardChecks⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hPrefix, hInitialEqBool⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hParentInBool, hObjectEqBool⟩
      have hInitialEq : initial.clause = link.encodedClause :=
        PropResolution.clauseEq_eq.mp hInitialEqBool
      have hObjectEq : link.parent.clause = link.objectClause :=
        Clause.eq_sound
          link.parent.clause link.objectClause hObjectEqBool
      have hDagActivation :
          cert.checked.dag.propGuardActivationInitialLinkOk (cert.checked.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using
          hDagOk
      unfold DAG.propGuardActivationInitialLinkOk at hDagActivation
      rcases Bool.and_eq_true_iff.mp hDagActivation with
        ⟨hDagPrefix, hParentFields⟩
      rcases Bool.and_eq_true_iff.mp hDagPrefix with
        ⟨_hDagParentIn, hSnapshot⟩
      have hParentMem :
          link.parent.id ∈ (cert.checked.dag.nodeAt index hIndex).parents.toList :=
        ParentClause.mem_toList_of_idIn hParentInBool
      have hParentSize :
          link.parent.id < cert.checked.dag.nodes.size :=
        Nat.lt_trans (cert.checked.contract.parents_before
            index hIndex link.parent.id hParentMem)
          hIndex
      have hParentLookup :
          cert.checked.dag.node? link.parent.id =
            some (cert.checked.dag.nodeAt link.parent.id hParentSize) :=
        cert.checked.dag.node?_eq_some_nodeAt hParentSize
      rw [hParentLookup] at hParentFields
      rcases Bool.and_eq_true_iff.mp hParentFields with
        ⟨_hGuarded, hGuardEq⟩
      have hActivationSat :=
        PropGuardActivationLink.encodedClause_satisfies (base := cert.selectorValuation base) (env := env)
          hGuardChecks hLiteralChecks (fun hLinkGuards => by
            have hParentGuards :
                Node.GuardsHold (cert.selectorValuation base) (cert.checked.dag.nodeAt
                    link.parent.id hParentSize).guards :=
              Node.GuardsHold.of_guardSetEq hGuardEq hLinkGuards
            have hParentSat :=
              cert.checked.parentClauseSatisfiesOnBoundStack
                base (cert.selectorValuation base) index hIndex hParents
                link.parent hParentMem hParentSize hSnapshot
                hParentGuards env hEnv hBound
            simpa [hObjectEq] using hParentSat)
      simpa [hInitialEq] using hActivationSat
  | propLearnedClause link =>
      have hLinkCheck :
          link.check (cert.checked.dag.nodeAt index hIndex).parents
            payload.atomMap initial = true := by
        simpa [PropInitialJustification.check, hJustification, hInitialGet]
          using hJustificationCheck
      unfold PropLearnedClauseLink.check at hLinkCheck
      rcases Bool.and_eq_true_iff.mp hLinkCheck with
        ⟨hPrefix, hInitialEqBool⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hPrefix, hLearnedEqBool⟩
      rcases Bool.and_eq_true_iff.mp hPrefix with
        ⟨hParentInBool, hOutside⟩
      have hInitialEq : initial.clause = link.clause :=
        PropResolution.clauseEq_eq.mp hInitialEqBool
      have hLearnedEq :
          link.clause = Guards.learnedClause link.guards :=
        PropResolution.clauseEq_eq.mp hLearnedEqBool
      have hDagLearned :
          cert.checked.dag.propLearnedInitialLinkOk (cert.checked.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using
          hDagOk
      unfold DAG.propLearnedInitialLinkOk at hDagLearned
      have hParentMem :
          link.parent ∈ (cert.checked.dag.nodeAt index hIndex).parents.toList :=
        Array.mem_def.mp (by
          simpa using (Bool.and_eq_true_iff.mp hDagLearned).1)
      have hParentSize : link.parent < cert.checked.dag.nodes.size :=
        Nat.lt_trans (cert.checked.contract.parents_before
            index hIndex link.parent hParentMem)
          hIndex
      have hParentLookup :
          cert.checked.dag.node? link.parent =
            some (cert.checked.dag.nodeAt link.parent hParentSize) :=
        cert.checked.dag.node?_eq_some_nodeAt hParentSize
      rw [hParentLookup] at hDagLearned
      rcases Bool.and_eq_true_iff.mp hDagLearned with
        ⟨_hParentIn, hParentPayloadCheck⟩
      cases hParentPayload : (cert.checked.dag.nodeAt link.parent hParentSize).payload
      case propositionalLearnedClause learnedPayload =>
          simp [hParentPayload] at hParentPayloadCheck
          rcases hParentPayloadCheck with
            ⟨hGuardEq, _hClauseEq⟩
          by_cases hGuards :
              Node.GuardsHold (cert.selectorValuation base) link.guards
          · have hParentGuards :
                Node.GuardsHold (cert.selectorValuation base) (cert.checked.dag.nodeAt
                    link.parent hParentSize).guards :=
              Node.GuardsHold.of_guardSetEq hGuardEq hGuards
            rcases hParents link.parent hParentMem with
              ⟨parentConclusion, hParentConclusion, hParentSat⟩
            have hParentEmpty :
                parentConclusion.isEmpty = true := by
              rw [Node.conclusion?, hParentPayload, Payload.conclusion?]
                at hParentConclusion
              have hEq :
                  parentConclusion = { literals := #[] } :=
                Option.some.inj hParentConclusion.symm
              subst parentConclusion
              simp [Clause.isEmpty]
            exact False.elim (Clause.not_satisfies_of_isEmpty hParentEmpty (hParentSat env hEnv hBound hParentGuards))
          · simpa [hInitialEq] using
              PropLearnedClauseLink.satisfies_of_not_guards (base := cert.selectorValuation base) (env := env)
                hLearnedEq hOutside hGuards
      all_goals simp [hParentPayload] at hParentPayloadCheck
  | avatarSkeleton link =>
      have hLinkCheck :
          link.check (cert.checked.dag.nodeAt index hIndex).parents
            payload.atomMap initial = true := by
        simpa [PropInitialJustification.check, hJustification, hInitialGet]
          using hJustificationCheck
      have hDagSkeleton :
          cert.checked.dag.propAvatarSkeletonInitialLinkOk (cert.checked.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using
          hDagOk
      exact cert.avatarSkeletonInitialSatisfies
        base index hIndex hParents payload initial link env
        hLinkCheck hDagSkeleton
theorem avatarBoundStackGuardedTopologicalStep
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ)) (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M) (base : Env M) (hProblem : cert.checked.dag.problem.Valid M)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) (index : Nat) (hIndex : index < cert.checked.dag.nodes.size) (hParents :
      ∀ parent (hParent :
          parent ∈ (cert.checked.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem (cert.checked.dag.nodeAt parent (Nat.lt_trans
              (cert.checked.contract.parents_before index hIndex parent hParent)
              hIndex))) :
    Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem (cert.checked.dag.nodeAt index hIndex) := by
  have hNodeSupported :=
    DAG.avatarSoundnessSupported_of_eq_true hSupported index hIndex
  cases hPayload : (cert.checked.dag.nodeAt index hIndex).payload
  case source initialIndex =>
      exact cert.checked.sourceBoundStackGuardedTopologicalStep
        base (cert.selectorValuation base) hProblem
        index hIndex initialIndex hPayload
  case avatarSplit payload =>
      exact cert.avatarSplitBoundStackGuardedTopologicalStep
        base index hIndex hParents payload hPayload
  case avatarComponent payload =>
      exact cert.avatarComponentBoundStackGuardedTopologicalStep
        base index hIndex payload hPayload
  case theoryConflict payload =>
      exact
        cert.checked.theoryConflictBoundStackGuardedTopologicalStep
          base (cert.selectorValuation base) index hIndex hParents
          payload hPayload
  case propositionalLearnedClause payload =>
      exact
        cert.checked.propositionalLearnedClauseBoundStackGuardedTopologicalStep
          base (cert.selectorValuation base) index hIndex hParents
          payload hPayload
  case residualCdcl payload =>
      have hPayloadSupported :
          payload.avatarSoundnessSupported = true := by
        simpa [hPayload, Payload.avatarSoundnessSupported] using
          hNodeSupported
      exact cert.residualCdclBoundStackGuardedTopologicalStep
        base index hIndex hParents payload hPayload hPayloadSupported
  all_goals
    exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
      contract witnessContract base (cert.selectorValuation base)
      hProblem index hIndex hParents (by
        simp [hPayload, Payload.soundnessSupported,
          Payload.soundnessSupportedWithWitness])
theorem rootBoundStackGuardedInvariant
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ)) (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M) (base : Env M) (hProblem : cert.checked.dag.problem.Valid M)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) :
    Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem (cert.checked.dag.nodeAt
        cert.checked.dag.root cert.checked.contract.root_exists) :=
  cert.checked.rootByTopologicalInduction (P := fun _ _ node =>
      Node.BoundStackGuardedInvariant base (cert.selectorValuation base) cert.checked.dag.problem node) (fun index hIndex hParents =>
      cert.avatarBoundStackGuardedTopologicalStep
        contract witnessContract base hProblem hSupported
        index hIndex hParents)
/--
HO-AVATAR residual CDCL 的专用空根矛盾。
root checker 保证结论为空且没有 guard；canonical selector valuation 下的整图
fixed-bound-stack 不变量因而否定当前模型中的问题有效性。
-/
theorem rootEmptyContradiction
     [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ)) (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M) (base : Env M) (hBase : base.WellSorted []) (hProblem : cert.checked.dag.problem.Valid M)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) :
    False := by
  have hRootInvariant :=
    cert.rootBoundStackGuardedInvariant
      contract witnessContract base hProblem hSupported
  rcases cert.checked.contract.root_conclusion with
    ⟨rootConclusion, hRootConclusion, hRootEmpty⟩
  rcases hRootInvariant with
    ⟨invariantConclusion, hInvariantConclusion, hSatisfies⟩
  have hConclusionEq : invariantConclusion = rootConclusion :=
    Option.some.inj (hInvariantConclusion.symm.trans hRootConclusion)
  subst rootConclusion
  have hRootGuards :
      Node.GuardsHold (cert.selectorValuation base) (cert.checked.dag.nodeAt
          cert.checked.dag.root cert.checked.contract.root_exists).guards :=
    Node.GuardsHold.of_isEmpty cert.checked.contract.root_unguarded
  exact Clause.not_satisfies_of_isEmpty hRootEmpty (hSatisfies base hBase (Avatar.SameBoundStack.refl base) hRootGuards)
end CheckedAvatarDAG
end HOAvatarSoundnessSignature
end HODAGCertificate
end Automation
end YesMetaZFC
