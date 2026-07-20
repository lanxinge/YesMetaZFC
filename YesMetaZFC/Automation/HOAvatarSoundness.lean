import YesMetaZFC.Automation.HODAGCertificate

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

namespace Avatar

/-- typed 自由变量支持中的成员关系。 -/
def SupportContains {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (support : Array (FreeVariable σ)) (candidate : FreeVariable σ) : Prop :=
  candidate ∈ support.toList

/-- 两个 typed 自由变量支持没有公共成员。 -/
def SupportDisjoint {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (left right : Array (FreeVariable σ)) : Prop :=
  ∀ candidate, SupportContains left candidate →
    ¬ SupportContains right candidate

/-- 两个高阶环境具有相同的统一 de Bruijn bound 栈。 -/
def SameBoundStack {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (left right : Env M) : Prop :=
  ∀ index, left.boundVal index = right.boundVal index

namespace SameBoundStack

/-- bound 栈一致性的自反性。 -/
theorem refl {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Env M) : SameBoundStack env env :=
  fun _ => rfl

/-- bound 栈一致性的对称性。 -/
theorem symm {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {left right : Env M} (hBound : SameBoundStack left right) :
    SameBoundStack right left :=
  fun index => (hBound index).symm

/-- bound 栈一致性的传递性。 -/
theorem trans {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {left middle right : Env M} (hLeft : SameBoundStack left middle)
    (hRight : SameBoundStack middle right) :
    SameBoundStack left right :=
  fun index => (hLeft index).trans (hRight index)

end SameBoundStack

/-- 两个环境在 typed 支持上相等。 -/
def EnvAgreesOn {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure σ} (support : Array (FreeVariable σ))
    (left right : Env M) : Prop :=
  SameBoundStack left right ∧
    ∀ candidate, SupportContains support candidate →
      left.freeVal candidate.sort candidate.id =
        right.freeVal candidate.sort candidate.id

/-- typed 自由变量比较成功时恢复结构相等。 -/
theorem freeVariableEq_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {left right : FreeVariable σ}
    (hEq : FreeVariable.eq left right = true) : left = right := by
  cases left with
  | mk leftSort leftId =>
      cases right with
      | mk rightSort rightId =>
          simp [FreeVariable.eq] at hEq
          rcases hEq with ⟨hSort, hId⟩
          cases hSort
          cases hId
          rfl

/-- typed 支持成员的可计算检查。 -/
def supportContainsCheck {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    (support : Array (FreeVariable σ)) (candidate : FreeVariable σ) : Bool :=
  support.any (FreeVariable.eq · candidate)

/-- Prop 成员合同推出可计算成员检查。 -/
theorem supportContainsCheck_true_of_contains {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {support : Array (FreeVariable σ)}
    {candidate : FreeVariable σ} (hContains : SupportContains support candidate) :
    supportContainsCheck support candidate = true := by
  have hArray : candidate ∈ support := Array.mem_def.mpr hContains
  rcases Array.mem_iff_getElem.mp hArray with ⟨index, hIndex, hGet⟩
  unfold supportContainsCheck
  apply Array.any_eq_true.mpr
  refine ⟨index, hIndex, ?_⟩
  simp [hGet, FreeVariable.eq]

/-- typed 支持数组成员可以从可计算检查恢复。 -/
theorem supportContains_of_eq_true {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {support : Array (FreeVariable σ)}
    {candidate : FreeVariable σ}
    (hContains : supportContainsCheck support candidate = true) :
    SupportContains support candidate := by
  rcases Array.any_eq_true.mp hContains with ⟨index, hIndex, hEq⟩
  have hExisting : support[index] = candidate := freeVariableEq_sound hEq
  have hMem : SupportContains support support[index] :=
    Array.mem_def.mp (Array.getElem_mem hIndex)
  simpa [hExisting] using hMem

/-- 向支持中插入一个变量后，候选变量仍然属于新支持。 -/
theorem pushFreeVariableUnique_contains {σ : Signature.{u, v, w}}
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

/-- 支持折叠过程中保留左侧已有成员。 -/
theorem foldlSupportContains {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] :
    ∀ (items : List (FreeVariable σ)) (support : Array (FreeVariable σ))
      (candidate : FreeVariable σ), candidate ∈ support.toList →
        candidate ∈ (items.foldl pushFreeVariableUnique support).toList
  | [], support, candidate, hCandidate => hCandidate
  | head :: tail, support, candidate, hCandidate => by
      apply foldlSupportContains tail (pushFreeVariableUnique support head) candidate
      by_cases hAny : support.any (FreeVariable.eq · head) = true
      · simpa [pushFreeVariableUnique, hAny] using hCandidate
      · simpa [pushFreeVariableUnique, hAny] using
          (show candidate ∈ support.toList ∨ candidate = head from Or.inl hCandidate)

/-- 支持折叠过程中把右侧列表成员带入结果。 -/
theorem foldlSupportContains_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] :
    ∀ (items : List (FreeVariable σ)) (candidate : FreeVariable σ),
      candidate ∈ items → ∀ (support : Array (FreeVariable σ)),
        candidate ∈ (items.foldl pushFreeVariableUnique support).toList
  | [], candidate, hCandidate, support => by
      simp at hCandidate
  | head :: tail, candidate, hCandidate, support => by
      rcases List.mem_cons.mp hCandidate with hHead | hTail
      · subst candidate
        exact foldlSupportContains tail (pushFreeVariableUnique support head) head
          (pushFreeVariableUnique_contains (support := support) (candidate := head))
      · exact foldlSupportContains_right tail candidate hTail
          (pushFreeVariableUnique support head)

/-- 支持数组合并保留左侧成员。 -/
theorem supportContains_merge_left {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {left right : Array (FreeVariable σ)}
    {candidate : FreeVariable σ}
    (hCandidate : SupportContains left candidate) :
    SupportContains (mergeFreeSupport left right) candidate :=
  foldlSupportContains right.toList left candidate hCandidate

/-- 支持数组合并保留右侧成员。 -/
theorem supportContains_merge_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {left right : Array (FreeVariable σ)}
    {candidate : FreeVariable σ}
    (hCandidate : SupportContains right candidate) :
    SupportContains (mergeFreeSupport left right) candidate := by
  unfold SupportContains at hCandidate
  exact foldlSupportContains_right right.toList candidate
    hCandidate left

/-- 布尔 overlap 检查为假时，两个 typed 支持确实不交。 -/
theorem supportsOverlap_false_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {left right : Array (FreeVariable σ)}
    (hOverlap : supportsOverlap left right = false) :
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

/-- typed 环境 overlay：只在指定支持上采用 source 的自由变量赋值。 -/
def overlay {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure.{u, v, w, x} σ} (support : Array (FreeVariable σ))
    (source base : Env M) : Env M where
  boundVal := base.boundVal
  freeVal := fun sort id =>
    if supportContainsCheck support { sort := sort, id := id } then
      source.freeVal sort id
    else
      base.freeVal sort id

/-- overlay 保留 base 的完整 bound 栈。 -/
theorem overlay_sameBoundStack_base {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure.{u, v, w, x} σ}
    {support : Array (FreeVariable σ)} {source base : Env M} :
    SameBoundStack (overlay support source base) base := by
  intro index
  rfl

/-- 两个输入环境类型正确时，typed overlay 仍然类型正确。 -/
theorem overlay_wellSorted {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure.{u, v, w, x} σ}
    {support : Array (FreeVariable σ)} {source base : Env M}
    (hSource : source.WellSorted []) (hBase : base.WellSorted []) :
    (overlay support source base).WellSorted [] := by
  constructor
  · intro index sort hLookup
    simp [Context.lookup?] at hLookup
  · intro sort id
    cases hMem : supportContainsCheck support { sort := sort, id := id }
    · simpa [overlay, hMem] using hBase.2 sort id
    · simpa [overlay, hMem] using hSource.2 sort id

/-- 在任意指定 bound 栈上选择一个类型正确的自由变量环境。 -/
noncomputable def canonicalOnBoundStack {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) (base : Env M) : Env M where
  boundVal := base.boundVal
  freeVal := fun sort _ => Classical.choose (M.sortNonempty sort)

/-- 固定 bound 栈规范环境在空上下文下类型正确。 -/
theorem canonicalOnBoundStack_wellSorted {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (base : Env M) :
    (canonicalOnBoundStack M base).WellSorted [] := by
  constructor
  · intro index sort hLookup
    simp [Context.lookup?] at hLookup
  · intro sort id
    exact Classical.choose_spec (M.sortNonempty sort)

/-- 固定 bound 栈规范环境确实保留输入的完整 bound 栈。 -/
theorem canonicalOnBoundStack_sameBoundStack {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (base : Env M) :
    SameBoundStack (canonicalOnBoundStack M base) base := by
  intro index
  rfl

/-- overlay 在覆盖支持上与 source 环境一致。 -/
theorem overlay_agreesOn_source {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure.{u, v, w, x} σ}
    {support : Array (FreeVariable σ)} {source base : Env M}
    (hBound : SameBoundStack base source) :
    EnvAgreesOn support (overlay support source base) source := by
  constructor
  · exact hBound
  · intro candidate hCandidate
    have hCheck := supportContainsCheck_true_of_contains hCandidate
    simp [overlay, hCheck]

/-- 覆盖支持与目标支持不交时，overlay 在目标支持上仍与 base 一致。 -/
theorem overlay_agreesOn_base_of_disjoint {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure.{u, v, w, x} σ}
    {overlaySupport support : Array (FreeVariable σ)}
    {source base : Env M}
    (hDisjoint : SupportDisjoint overlaySupport support) :
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

/-- 项解释只依赖 typed 自由变量支持和完整 bound 栈。 -/
theorem termEval_eq_of_envAgreesOn_aux {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ} :
    ∀ (term : Term σ) (left right : Env M),
      (∀ index, left.boundVal index = right.boundVal index) →
        (∀ candidate,
          SupportContains (termFreeSupport term) candidate →
            left.freeVal candidate.sort candidate.id =
              right.freeVal candidate.sort candidate.id) →
        Term.eval left term = Term.eval right term := by
  intro term
  refine Logic.HigherOrder.Term.rec
    (motive_1 := fun term =>
      ∀ (left right : Env M),
        (∀ index, left.boundVal index = right.boundVal index) →
          (∀ candidate,
            SupportContains (termFreeSupport term) candidate →
              left.freeVal candidate.sort candidate.id =
                right.freeVal candidate.sort candidate.id) →
          Term.eval left term = Term.eval right term)
    (motive_2 := fun terms =>
      ∀ (left right : Env M),
        (∀ index, left.boundVal index = right.boundVal index) →
          (∀ candidate,
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
        have hEq := hFree { sort := sort, id := id }
          (by simp [SupportContains, termFreeSupport])
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
        hFree candidate
          (supportContains_merge_left
            (right := termFreeSupport argument) hCandidate)),
      ihArgument left right hBound (fun candidate hCandidate =>
        hFree candidate
          (supportContains_merge_right
            (left := termFreeSupport function) hCandidate))]
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
        hFree candidate
          (supportContains_merge_left
            (right := termListFreeSupport tail) hCandidate)),
      ihTail left right hBound (fun candidate hCandidate =>
        hFree candidate
          (supportContains_merge_right
            (left := termFreeSupport head) hCandidate))]

/-- 项解释环境合同的常用参数顺序包装。 -/
theorem termEval_eq_of_envAgreesOn {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ} :
    ∀ (left right : Env M) (term : Term σ),
      (∀ index, left.boundVal index = right.boundVal index) →
        (∀ candidate,
          SupportContains (termFreeSupport term) candidate →
            left.freeVal candidate.sort candidate.id =
              right.freeVal candidate.sort candidate.id) →
        Term.eval left term = Term.eval right term :=
  fun left right term hBound hFree =>
    termEval_eq_of_envAgreesOn_aux term left right hBound hFree

/-- 项列表解释只依赖整个列表的 typed 自由变量支持。 -/
theorem termListEval_eq_of_envAgreesOn {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ} :
    ∀ (left right : Env M) (terms : List (Term σ)),
      SameBoundStack left right →
        (∀ candidate,
          SupportContains (termListFreeSupport terms) candidate →
            left.freeVal candidate.sort candidate.id =
              right.freeVal candidate.sort candidate.id) →
        terms.map (Term.eval left) = terms.map (Term.eval right)
  | left, right, [], _hBound, _hFree => rfl
  | left, right, head :: tail, hBound, hFree => by
      simp only [List.map_cons]
      rw [termEval_eq_of_envAgreesOn left right head hBound
          (fun candidate hCandidate =>
            hFree candidate
              (supportContains_merge_left
                (right := termListFreeSupport tail) hCandidate)),
        termListEval_eq_of_envAgreesOn left right tail hBound
          (fun candidate hCandidate =>
            hFree candidate
              (supportContains_merge_right
                (left := termFreeSupport head) hCandidate))]

/-- literal 支持折叠过程中保留已有支持成员。 -/
theorem foldlLiteralSupportContains {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] :
    ∀ (literals : List (Literal σ)) (support : Array (FreeVariable σ))
      (candidate : FreeVariable σ), SupportContains support candidate →
        SupportContains
          (literals.foldl
            (fun current literal =>
              mergeFreeSupport current (literalFreeSupport literal))
            support)
          candidate
  | [], support, candidate, hCandidate => hCandidate
  | head :: tail, support, candidate, hCandidate => by
      apply foldlLiteralSupportContains tail
        (mergeFreeSupport support (literalFreeSupport head)) candidate
      exact supportContains_merge_left hCandidate

/-- literal 列表成员的 typed 支持被折叠结果包含。 -/
theorem foldlLiteralSupportContains_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] :
    ∀ (literals : List (Literal σ)) (literal : Literal σ),
      literal ∈ literals → ∀ (candidate : FreeVariable σ),
        SupportContains (literalFreeSupport literal) candidate →
          ∀ support : Array (FreeVariable σ),
            SupportContains
              (literals.foldl
                (fun current item =>
                  mergeFreeSupport current (literalFreeSupport item))
                support)
              candidate
  | [], literal, hLiteral, candidate, hCandidate, support => by
      simp at hLiteral
  | head :: tail, literal, hLiteral, candidate, hCandidate, support => by
      rcases List.mem_cons.mp hLiteral with hHead | hTail
      · subst literal
        apply foldlLiteralSupportContains tail
          (mergeFreeSupport support (literalFreeSupport head)) candidate
        exact supportContains_merge_right hCandidate
      · exact foldlLiteralSupportContains_right tail literal hTail candidate
          hCandidate (mergeFreeSupport support (literalFreeSupport head))

/-- 字句中的任一 literal 支持都被字句总支持包含。 -/
theorem literalSupport_subset_clauseSupport {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {clause : Clause σ} {literal : Literal σ}
    (hLiteral : literal ∈ clause.literals.toList) :
    ∀ candidate, SupportContains (literalFreeSupport literal) candidate →
      SupportContains (clauseFreeSupport clause) candidate :=
  fun candidate hCandidate =>
    foldlLiteralSupportContains_right clause.literals.toList literal
    hLiteral candidate hCandidate #[]

/-- 原子满足性只依赖其 typed 自由变量支持和完整 bound 栈。 -/
theorem atomSatisfies_iff_of_envAgreesOn {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ}
    {left right : Env M} (atom : Atom σ)
    (hEnv : EnvAgreesOn (atomFreeSupport atom) left right) :
    atom.Satisfies left ↔ atom.Satisfies right := by
  cases atom with
  | rel symbol arguments =>
      have hArguments :=
        termListEval_eq_of_envAgreesOn left right arguments hEnv.1
          (fun candidate hCandidate => hEnv.2 candidate hCandidate)
      simp [Atom.Satisfies, hArguments]
  | equal sort leftTerm rightTerm =>
      have hLeft :=
        termEval_eq_of_envAgreesOn left right leftTerm hEnv.1
          (fun candidate hCandidate =>
            hEnv.2 candidate
              (supportContains_merge_left
                (right := termFreeSupport rightTerm) hCandidate))
      have hRight :=
        termEval_eq_of_envAgreesOn left right rightTerm hEnv.1
          (fun candidate hCandidate =>
            hEnv.2 candidate
              (supportContains_merge_right
                (left := termFreeSupport leftTerm) hCandidate))
      simp [Atom.Satisfies, hLeft, hRight]

/-- literal 满足性只依赖其 typed 自由变量支持和完整 bound 栈。 -/
theorem literalSatisfies_iff_of_envAgreesOn {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ}
    {left right : Env M} (literal : Literal σ)
    (hEnv : EnvAgreesOn (literalFreeSupport literal) left right) :
    literal.Satisfies left ↔ literal.Satisfies right := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · exact not_congr (atomSatisfies_iff_of_envAgreesOn atom hEnv)
      · exact atomSatisfies_iff_of_envAgreesOn atom hEnv

end Avatar

namespace Clause

/-- component 列表在 literal 层双向覆盖 source 字句。 -/
def Covers {σ : Signature.{u, v, w}} (source : Clause σ)
    (components : List (Clause σ)) : Prop :=
  (∀ literal, literal ∈ source.literals.toList →
    ∃ component, component ∈ components ∧
      literal ∈ component.literals.toList) ∧
  ∀ component, component ∈ components →
    ∀ literal, literal ∈ component.literals.toList →
      literal ∈ source.literals.toList

/-- component 列表的 typed 自由变量支持两两不交。 -/
def PairwiseSupportDisjoint {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] : List (Clause σ) → Prop
  | [] => True
  | clause :: rest =>
      (∀ other, other ∈ rest →
        Avatar.SupportDisjoint
          (Avatar.clauseFreeSupport clause)
          (Avatar.clauseFreeSupport other)) ∧
        PairwiseSupportDisjoint rest

/-- 一个 HO 字句在固定 bound 栈上的所有类型正确自由变量环境中成立。 -/
def ValidOnBoundStack {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ}
    (base : Env M) (clause : Clause σ) : Prop :=
  ∀ env, env.WellSorted [] → Avatar.SameBoundStack env base →
    clause.Satisfies env

/-- 字句满足性只依赖字句总 typed 支持和完整 bound 栈。 -/
theorem satisfies_iff_of_envAgreesOn {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ} {left right : Env M}
    (clause : Clause σ)
    (hEnv : Avatar.EnvAgreesOn (Avatar.clauseFreeSupport clause) left right) :
    clause.Satisfies left ↔ clause.Satisfies right := by
  constructor
  · rintro ⟨literal, hLiteral, hSat⟩
    refine ⟨literal, hLiteral, ?_⟩
    apply (Avatar.literalSatisfies_iff_of_envAgreesOn literal ?_).mp hSat
    constructor
    · exact hEnv.1
    · intro candidate hCandidate
      exact hEnv.2 candidate
        (Avatar.literalSupport_subset_clauseSupport
          (Array.mem_def.mp hLiteral) candidate hCandidate)
  · rintro ⟨literal, hLiteral, hSat⟩
    refine ⟨literal, hLiteral, ?_⟩
    apply (Avatar.literalSatisfies_iff_of_envAgreesOn literal ?_).mpr hSat
    constructor
    · exact hEnv.1
    · intro candidate hCandidate
      exact hEnv.2 candidate
        (Avatar.literalSupport_subset_clauseSupport
          (Array.mem_def.mp hLiteral) candidate hCandidate)

/-- `containsLiteral` 成功时恢复真实的文字成员。 -/
theorem containsLiteral_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {clause : Clause σ} {literal : Literal σ}
    (hCheck : containsLiteral clause literal = true) :
    ∃ found, found ∈ clause.literals.toList ∧ found = literal :=
  containsLiteralList_sound (by
    simpa [containsLiteral] using hCheck)

/-- 全文字覆盖检查解包为 `Covers` 合同。 -/
theorem coversCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {source : Clause σ}
    {components : List (Clause σ)}
    (hCheck : coversCheck source components = true) :
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

/-- 两两 typed 支持不交检查解包为 component decomposition 合同。 -/
theorem pairwiseSupportDisjoint_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {components : List (Clause σ)}
    (hCheck : Avatar.pairwiseSupportDisjoint components = true) :
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
            Avatar.supportsOverlap
                (Avatar.clauseFreeSupport head)
                (Avatar.clauseFreeSupport other) =
              false := by
          simpa using hAt
        exact Avatar.supportsOverlap_false_sound hNoOverlap
      · exact ih hRest

/-- literal 覆盖给出 source 与 component 析取语义等价。 -/
theorem satisfies_iff_exists_component_of_covers {σ : Signature.{u, v, w}}
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
      Array.mem_def.mpr (hCovers.2 component hComponent literal
        (Array.mem_def.mp hLiteral)), hSat⟩

private theorem exists_counterexample_of_not_valid
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure σ} {base : Env M} {clause : Clause σ}
    (hNotValid : ¬ ValidOnBoundStack base clause) :
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
theorem exists_common_counterexample {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ}
    (base : Env M) (components : List (Clause σ))
    (hDisjoint : PairwiseSupportDisjoint components)
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
      rcases exists_counterexample_of_not_valid
          (hNotValid head List.mem_cons_self) with
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
            Avatar.overlay_agreesOn_source
              (support := Avatar.clauseFreeSupport head) hBound
          exact hHeadFalse
            ((satisfies_iff_of_envAgreesOn head hAgree).mp hSat)
        · intro hSat
          have hAgree :=
            Avatar.overlay_agreesOn_base_of_disjoint
              (source := headEnv) (base := tailEnv)
              (hHeadDisjoint component hTail)
          exact hTailFalse component hTail
            ((satisfies_iff_of_envAgreesOn component hAgree).mp hSat)

/--
HO-AVATAR fixed-bound-stack component decomposition 主定理。

当 components 双向覆盖 source 且 typed 自由变量支持两两不交时，source 对固定
bound 栈上的所有类型正确自由变量环境有效，当且仅当某个 component 具有同一性质。
-/
theorem validOnBoundStack_iff_exists_component {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ}
    (base : Env M) (source : Clause σ) (components : List (Clause σ))
    (hCovers : Covers source components)
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

/-- selector/component 列表等长时，稳定配对不会丢失 selector。 -/
theorem selectors_ofLists {σ : Signature.{u, v, w}} :
    ∀ {selectors : List GuardLit} {components : List (Clause σ)},
      selectors.length = components.length →
        (ofLists selectors components).map AvatarSelectorComponent.selector =
          selectors
  | [], [], _hLength => rfl
  | [], _ :: _, hLength => by simp at hLength
  | _ :: _, [], hLength => by simp at hLength
  | selector :: selectors, component :: components, hLength => by
      simp only [List.length_cons, Nat.succ.injEq] at hLength
      simp [ofLists, selectors_ofLists hLength]

/-- selector/component 列表等长时，稳定配对不会丢失 component。 -/
theorem components_ofLists {σ : Signature.{u, v, w}} :
    ∀ {selectors : List GuardLit} {components : List (Clause σ)},
      selectors.length = components.length →
        (ofLists selectors components).map AvatarSelectorComponent.component =
          components
  | [], [], _hLength => rfl
  | [], _ :: _, hLength => by simp at hLength
  | _ :: _, [], hLength => by simp at hLength
  | selector :: selectors, component :: components, hLength => by
      simp only [List.length_cons, Nat.succ.injEq] at hLength
      simp [ofLists, components_ofLists hLength]

/-- 同槽位 selector/component 的稳定配对读取结果。 -/
theorem getElem?_ofLists {σ : Signature.{u, v, w}}
    {selectors : List GuardLit} {components : List (Clause σ)}
    {index : Nat} {selector : GuardLit} {component : Clause σ}
    (hSelector : selectors[index]? = some selector)
    (hComponent : components[index]? = some component) :
    (ofLists selectors components)[index]? =
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

/-- 一组 selector/component 登记项对应的命题 skeleton。 -/
def selectorClause {σ : Signature.{u, v, w}}
    (entries : List (AvatarSelectorComponent σ)) : PropResolution.Clause :=
  (entries.map AvatarSelectorComponent.selector).toArray

/-- 同一 selector 变量在 registry 中必须始终指向同一个 HO component。 -/
def Compatible {σ : Signature.{u, v, w}}
    (entries : List (AvatarSelectorComponent σ)) : Prop :=
  ∀ left, left ∈ entries → ∀ right, right ∈ entries →
    left.selector.var = right.selector.var → left.component = right.component

/-- 全局 selector/component 一致性检查的逻辑解包。 -/
theorem compatibleCheck_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {entries : List (AvatarSelectorComponent σ)}
    (hCheck : compatibleCheck entries = true) :
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
def valuation {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure σ} (base : Env M)
    (entries : List (AvatarSelectorComponent σ)) :
    PropResolution.Valuation :=
  fun selectorVar =>
    ∃ entry, entry ∈ entries ∧ entry.selector.var = selectorVar ∧
      Clause.ValidOnBoundStack base entry.component

/-- registry 中一条正 selector 的真值精确等价于其 component 的固定 bound 栈有效性。 -/
theorem holds_valuation_iff_component_valid {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ}
    (base : Env M) (entries : List (AvatarSelectorComponent σ))
    (hPositive : ∀ item, item ∈ entries → item.selector.positive = true)
    (hCompatible : Compatible entries) {entry : AvatarSelectorComponent σ}
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

/-- 局部 selector skeleton 在全局 registry valuation 下的精确语义。 -/
theorem selectorClause_satisfies_iff_exists_valid_in_registry
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure σ} (base : Env M)
    (registry entries : List (AvatarSelectorComponent σ))
    (hPositive :
      ∀ entry, entry ∈ registry → entry.selector.positive = true)
    (hCompatible : Compatible registry)
    (hSubset : ∀ entry, entry ∈ entries → entry ∈ registry) :
    PropResolution.Clause.Satisfies
        (valuation base registry) (selectorClause entries) ↔
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
    exact ⟨entry, hEntry,
      (holds_valuation_iff_component_valid
        base registry hPositive hCompatible hEntryRegistry).mp hSelector⟩
  · rintro ⟨entry, hEntry, hValid⟩
    have hEntryRegistry := hSubset entry hEntry
    refine ⟨entry.selector, ?_, ?_⟩
    · have hMapped :
          entry.selector ∈ entries.map AvatarSelectorComponent.selector :=
        List.mem_map.mpr ⟨entry, hEntry, rfl⟩
      simpa [selectorClause] using hMapped
    · exact
        (holds_valuation_iff_component_valid
          base registry hPositive hCompatible hEntryRegistry).mpr hValid

end AvatarSelectorComponent

namespace AvatarSplitPayload

/-- 单个 checked split 可机械恢复的 selector registry 局部合同。 -/
structure RegistryContract {σ : Signature.{u, v, w}}
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

/-- split checker 成功时，全部局部 registry 合同均由同一 checker 解包。 -/
theorem registryContract_of_check {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {parents : Array Nat}
    {payload : AvatarSplitPayload σ}
    (hCheck : payload.check parents = true) :
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

/-- 对齐合同把配对表的 selector skeleton 还原为 payload skeleton。 -/
theorem selectorClause_selectorComponents {σ : Signature.{u, v, w}}
    {payload : AvatarSplitPayload σ}
    (hAligned :
      payload.selectors.toList.length = payload.componentClauses.length) :
    AvatarSelectorComponent.selectorClause payload.selectorComponents =
      payload.selectors := by
  unfold selectorComponents AvatarSelectorComponent.selectorClause
  rw [AvatarSelectorComponent.selectors_ofLists hAligned]

/-- 对齐合同把配对表的 component 投影还原为 payload components。 -/
theorem components_selectorComponents {σ : Signature.{u, v, w}}
    {payload : AvatarSplitPayload σ}
    (hAligned :
      payload.selectors.toList.length = payload.componentClauses.length) :
    payload.selectorComponents.map AvatarSelectorComponent.component =
      payload.componentClauses :=
  AvatarSelectorComponent.components_ofLists hAligned

/-- 局部 registry 合同推出配对表中的 selector 全为正文字。 -/
theorem RegistryContract.selectorComponentsPositive
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
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

/-- partition/selector 同槽位读取可恢复对应的 registry entry。 -/
theorem selectorComponent_mem {σ : Signature.{u, v, w}}
    {payload : AvatarSplitPayload σ}
    {index : Nat} {indices : Array Nat} {selector : GuardLit}
    (hIndices : payload.partitions[index]? = some indices)
    (hSelector :
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

/-- 单个 split source 在全局 registry valuation 下等价于其 selector skeleton。 -/
theorem source_valid_iff_selectors_satisfy_in_registry
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    {M : Structure σ} (base : Env M) (payload : AvatarSplitPayload σ)
    (hContract : RegistryContract payload)
    (registry : List (AvatarSelectorComponent σ))
    (hPositive :
      ∀ entry, entry ∈ registry → entry.selector.positive = true)
    (hCompatible : AvatarSelectorComponent.Compatible registry)
    (hSubset :
      ∀ entry, entry ∈ payload.selectorComponents → entry ∈ registry) :
    Clause.ValidOnBoundStack base payload.source.clause ↔
      PropResolution.Clause.Satisfies
        (AvatarSelectorComponent.valuation base registry)
        payload.selectors := by
  have hComponents :=
    components_selectorComponents (payload := payload) hContract.aligned
  have hSelectors :=
    selectorClause_selectorComponents
      (payload := payload) hContract.aligned
  rw [← hSelectors]
  constructor
  · intro hSource
    rcases
        (Clause.validOnBoundStack_iff_exists_component
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
    exact
      (AvatarSelectorComponent.selectorClause_satisfies_iff_exists_valid_in_registry
          base registry payload.selectorComponents
          hPositive hCompatible hSubset).mpr
        ⟨entry, hEntry, hValid⟩
  · intro hSkeleton
    rcases
        (AvatarSelectorComponent.selectorClause_satisfies_iff_exists_valid_in_registry
            base registry payload.selectorComponents
            hPositive hCompatible hSubset).mp hSkeleton with
      ⟨entry, hEntry, hValid⟩
    apply
      (Clause.validOnBoundStack_iff_exists_component
        base payload.source.clause payload.componentClauses
        hContract.covers hContract.pairwiseDisjoint).mpr
    exact
      ⟨entry.component, by
        rw [← hComponents]
        exact List.mem_map.mpr ⟨entry, hEntry, rfl⟩, hValid⟩

/-- split checker 成功时，复算出的 components 双向覆盖 source。 -/
theorem covers_of_check {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {parents : Array Nat}
    {payload : AvatarSplitPayload σ}
    (hCheck : payload.check parents = true) :
    Clause.Covers payload.source.clause payload.componentClauses :=
  (registryContract_of_check hCheck).covers

/-- checked split 的 source 满足性等价于至少一个 component 的满足性。 -/
theorem source_satisfies_iff_exists_component_of_check
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {M : Structure σ} {env : Env M}
    {parents : Array Nat} {payload : AvatarSplitPayload σ}
    (hCheck : payload.check parents = true) :
    payload.source.clause.Satisfies env ↔
      ∃ component, component ∈ payload.componentClauses ∧
        component.Satisfies env :=
  Clause.satisfies_iff_exists_component_of_covers (covers_of_check hCheck)

end AvatarSplitPayload

namespace DAG

/-- registry 局部贡献中的任意 entry 必然来自一个 split payload。 -/
theorem avatarSelectorComponents_split {σ : Signature.{u, v, w}}
    {payload : Payload σ} {entry : AvatarSelectorComponent σ}
    (hEntry : entry ∈ avatarSelectorComponents payload) :
    ∃ split, payload = .avatarSplit split ∧
      entry ∈ split.selectorComponents := by
  cases payload <;> simp [avatarSelectorComponents] at hEntry ⊢
  exact hEntry

/-- 指定 split 中的 selector/component entry 一定属于整图 registry。 -/
theorem mem_avatarSelectorRegistry_of_split {σ : Signature.{u, v, w}}
    {dag : DAG σ} {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    {entry : AvatarSelectorComponent σ}
    (hNode : dag.node? splitId = some splitNode)
    (hPayload : splitNode.payload = .avatarSplit payload)
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

/-- checked DAG 自动解包任意 split 的局部 registry 合同。 -/
theorem avatarSplitRegistryContract {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedDAG (σ := σ))
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    (hNode : cert.dag.node? splitId = some splitNode)
    (hPayload : splitNode.payload = .avatarSplit payload) :
    AvatarSplitPayload.RegistryContract payload := by
  rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
  have hNodeAt : cert.dag.nodeAt splitId hIndex = splitNode := by
    simpa [DAG.nodeAt] using hGet
  have hNodeCheck := cert.nodeChecked splitId hIndex
  rw [hNodeAt] at hNodeCheck
  have hPayloadCheck : payload.check splitNode.parents = true := by
    simpa [Node.check, Payload.check, hPayload] using hNodeCheck
  exact AvatarSplitPayload.registryContract_of_check hPayloadCheck

/-- checked DAG 的全局 registry 中所有 selector 都是正文字。 -/
theorem avatarSelectorRegistry_positive {σ : Signature.{u, v, w}}
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
    simpa [DAG.nodeAt] using hGet
  have hNodeCheck := cert.nodeChecked index hIndex
  rw [hNodeAt] at hNodeCheck
  have hSplitCheck : split.check node.parents = true := by
    simpa [Node.check, Payload.check, hPayload] using hNodeCheck
  exact
    AvatarSplitPayload.RegistryContract.selectorComponentsPositive
      (AvatarSplitPayload.registryContract_of_check hSplitCheck)
      entry hEntryLocal

end CheckedDAG

/-- 全局 selector registry 对任一 component 槽位提供的 fixed-bound-stack 语义。 -/
def AvatarComponentSelectorSemantics {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ}
    (dag : DAG σ) (base : Env M)
    (valuation : PropResolution.Valuation) : Prop :=
  ∀ {splitId splitNode splitPayload componentIndex indices selector},
    dag.node? splitId = some splitNode →
      splitNode.payload = .avatarSplit splitPayload →
        splitPayload.partitions[componentIndex]? = some indices →
          Automation.AvatarSplit.selectorAt? splitPayload.selectors
              componentIndex =
            some selector →
            (selector.Holds valuation ↔
              Clause.ValidOnBoundStack base
                (Avatar.clauseAtIndices
                  splitPayload.source.clause indices))

/-- 全局 selector registry 对任一 split skeleton 提供的 fixed-bound-stack 语义。 -/
def AvatarSplitSelectorSemantics {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] {M : Structure σ}
    (dag : DAG σ) (base : Env M)
    (valuation : PropResolution.Valuation) : Prop :=
  ∀ {splitId splitNode splitPayload},
    dag.node? splitId = some splitNode →
      splitNode.payload = .avatarSplit splitPayload →
        (Clause.ValidOnBoundStack base splitPayload.source.clause ↔
          PropResolution.Clause.Satisfies valuation splitPayload.selectors)

namespace CheckedAvatarDAG

/-- checked HO-AVATAR DAG 自动诱导的 fixed-bound-stack selector valuation。 -/
def selectorValuation {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : Structure σ} (base : Env M) : PropResolution.Valuation :=
  AvatarSelectorComponent.valuation base cert.checked.dag.avatarSelectorRegistry

/-- checked registry 自动解包全局 selector/component 一致性。 -/
theorem avatarSelectorRegistry_compatible {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ)) :
    AvatarSelectorComponent.Compatible
      cert.checked.dag.avatarSelectorRegistry :=
  AvatarSelectorComponent.compatibleCheck_sound cert.registryChecked

/-- checked registry 自动给出所有 HO component selector 的精确语义。 -/
theorem componentSelectorSemantics {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : Structure σ} (base : Env M) :
    AvatarComponentSelectorSemantics cert.checked.dag base
      (cert.selectorValuation base) := by
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

/-- checked registry 自动给出所有 HO split selector skeleton 的精确语义。 -/
theorem splitSelectorSemantics {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : Structure σ} (base : Env M) :
    AvatarSplitSelectorSemantics cert.checked.dag base
      (cert.selectorValuation base) := by
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
def BoundStackGuardedInvariant {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {M : Structure σ}
    (base : Env M) (valuation : PropResolution.Valuation)
    (problem : Problem σ) (node : Node σ) : Prop :=
  ∃ conclusion, node.conclusion? problem = some conclusion ∧
    ∀ env : Env M, env.WellSorted [] → Avatar.SameBoundStack env base →
      GuardsHold valuation node.guards → conclusion.Satisfies env

/-- singleton selector guard 的精确语义给出 component 节点不变量。 -/
theorem boundStackGuardedInvariant_of_selector
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (base : Env M)
    (valuation : PropResolution.Valuation) (problem : Problem σ)
    (node : Node σ) (conclusion : Clause σ)
    (hConclusion : node.conclusion? problem = some conclusion)
    (selector : GuardLit)
    (hGuardEq : guardSetEq node.guards #[selector] = true)
    (hSemantic :
      selector.Holds valuation ↔
        Clause.ValidOnBoundStack base conclusion) :
    BoundStackGuardedInvariant base valuation problem node := by
  refine ⟨conclusion, hConclusion, ?_⟩
  intro env hEnv hBound hGuards
  have hSingleton : GuardsHold valuation #[selector] :=
    GuardsHold.of_guardSetEq hGuardEq hGuards
  have hSelectorMem :
      selector ∈ (canonicalGuards #[selector]).toList := by
    apply PropResolution.mem_canonicalClause_of_mem
    simp
  exact (hSemantic.mp (hSingleton selector hSelectorMem)) env hEnv hBound

end Node

namespace AvatarSplitPayload

/-- split payload checker 解包出 canonical source 父边。 -/
theorem source_mem_of_check {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {parents : Array Nat}
    {payload : AvatarSplitPayload σ}
    (hCheck : payload.check parents = true) :
    payload.source.id ∈ parents.toList := by
  simp only [AvatarSplitPayload.check, Bool.and_eq_true_iff] at hCheck
  rcases hCheck with
    ⟨⟨⟨⟨⟨⟨_hSize, hParent⟩, _hClause⟩, _hPartition⟩,
      _hSelectors⟩, _hDisjoint⟩, _hCovers⟩
  exact ParentClause.mem_toList_of_idIn hParent

end AvatarSplitPayload

private theorem guardLit_eq_of_beq_eq_true {left right : GuardLit}
    (hEq : (left == right) = true) : left = right := by
  cases left with
  | mk leftVar leftPositive =>
      cases right with
      | mk rightVar rightPositive =>
          change
            ((leftVar == rightVar) && (leftPositive == rightPositive)) =
              true at hEq
          simp only [Bool.and_eq_true_iff, beq_iff_eq] at hEq
          cases hEq.1
          cases hEq.2
          rfl

namespace DAG

/-- split descriptor 的整图检查解包。 -/
theorem avatarSplitNodeOk_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {node : Node σ}
    {payload : AvatarSplitPayload σ}
    (hOk : dag.avatarSplitNodeOk node payload = true) :
    node.unguarded = true ∧
      dag.parentSnapshotChecked payload.source = true ∧
        ∃ sourceNode initialIndex,
          dag.node? payload.source.id = some sourceNode ∧
            sourceNode.unguarded = true ∧
              sourceNode.payload = .source initialIndex := by
  unfold avatarSplitNodeOk at hOk
  split at hOk <;> simp_all
  split at hOk <;> simp_all

/-- component 整图检查解包出唯一 split 槽位和 singleton selector。 -/
theorem avatarComponentNodeOk_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ} {node : Node σ}
    {payload : AvatarComponentPayload σ}
    (hOk : dag.avatarComponentNodeOk node payload = true) :
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
                      guardSetEq node.guards #[selector] = true := by
  unfold avatarComponentNodeOk at hOk
  split at hOk <;> simp_all
  split at hOk <;> simp_all
  split at hOk <;> simp_all
  exact
    ⟨Clause.eq_sound _ _ hOk.2.2.1.1,
      guardLit_eq_of_beq_eq_true hOk.2.2.1.2⟩

/-- skeleton initial 整图检查解包出真实 split descriptor。 -/
theorem propAvatarSkeletonInitialLinkOk_sound
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {dag : DAG σ} {parents : Array Nat} {link : PropAvatarSkeletonLink}
    (hOk : dag.propAvatarSkeletonInitialLinkOk parents link = true) :
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

/-- fixed-bound-stack 父不变量与快照检查给出父字句满足性。 -/
theorem parentClauseSatisfiesOnBoundStack
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ))
    (base : Env M) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans
              (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (parent : ParentClause σ)
    (hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentSize : parent.id < cert.dag.nodes.size)
    (hSnapshotCheck : cert.dag.parentSnapshotChecked parent = true)
    (hParentGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt parent.id hParentSize).guards)
    (env : Env M) (hEnv : env.WellSorted [])
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

/-- split descriptor 复制 canonical source 的 fixed-bound-stack 不变量。 -/
theorem avatarSplitBoundStackGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ))
    (base : Env M) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans
              (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : AvatarSplitPayload σ)
    (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .avatarSplit payload) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have hNodeCheck := cert.nodeChecked index hIndex
  rw [Node.check, hPayload] at hNodeCheck
  have hSplitCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents = true := by
    simpa [Payload.check] using hNodeCheck
  have hSourceMem := AvatarSplitPayload.source_mem_of_check hSplitCheck
  have hSourceSize : payload.source.id < cert.dag.nodes.size :=
    Nat.lt_trans
      (cert.parentsBefore index hIndex payload.source.id hSourceMem) hIndex
  have hNodeOk :
      cert.dag.avatarSplitNodeOk
        (cert.dag.nodeAt index hIndex) payload = true := by
    have hGuards := cert.nodeGuardsChecked index hIndex
    simpa [DAG.localNodeGuardsOk, hPayload] using hGuards
  rcases DAG.avatarSplitNodeOk_sound hNodeOk with
    ⟨_hSplitUnguarded, hSnapshot, sourceNode, _initialIndex,
      hSourceLookup, hSourceUnguarded, _hSourcePayload⟩
  have hSourceNodeEq :
      sourceNode = cert.dag.nodeAt payload.source.id hSourceSize :=
    Option.some.inj
      (hSourceLookup.symm.trans
        (cert.dag.node?_eq_some_nodeAt hSourceSize))
  have hSourceGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt payload.source.id hSourceSize).guards :=
    Node.GuardsHold.of_isEmpty (by
      simpa [← hSourceNodeEq, Node.unguarded] using hSourceUnguarded)
  refine
    ⟨payload.source.clause,
      by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
  intro env hEnv hBound _hCurrentGuards
  exact cert.parentClauseSatisfiesOnBoundStack
    base valuation index hIndex hParents payload.source hSourceMem
    hSourceSize hSnapshot hSourceGuards env hEnv hBound

/-- component 节点消费对应 selector 槽位的 fixed-bound-stack 语义。 -/
theorem avatarComponentBoundStackGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ))
    (base : Env M) (valuation : PropResolution.Valuation)
    (hSelectorSemantics :
      AvatarComponentSelectorSemantics cert.dag base valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : AvatarComponentPayload σ)
    (hPayload :
      (cert.dag.nodeAt index hIndex).payload =
        .avatarComponent payload) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have hNodeOk :
      cert.dag.avatarComponentNodeOk
        (cert.dag.nodeAt index hIndex) payload = true := by
    have hGuards := cert.nodeGuardsChecked index hIndex
    simpa [DAG.localNodeGuardsOk, hPayload] using hGuards
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
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ))
    (base : Env M)
    (index : Nat) (hIndex : index < cert.checked.dag.nodes.size)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈
            (cert.checked.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base
          (cert.selectorValuation base) cert.checked.dag.problem
          (cert.checked.dag.nodeAt parent
            (Nat.lt_trans
              (cert.checked.parentsBefore index hIndex parent hParent)
              hIndex)))
    (payload : PropositionalClosurePayload σ)
    (initial : PropResolution.InitialClause)
    (link : PropAvatarSkeletonLink)
    (env : Env M)
    (hLinkCheck :
      link.check (cert.checked.dag.nodeAt index hIndex).parents
        payload.atomMap initial = true)
    (hDagOk :
      cert.checked.dag.propAvatarSkeletonInitialLinkOk
        (cert.checked.dag.nodeAt index hIndex).parents link = true) :
    PropResolution.Clause.Satisfies
      (PropLiteralLink.valuation
        (cert.selectorValuation base) payload.atomMap env)
      initial.clause := by
  unfold PropAvatarSkeletonLink.check at hLinkCheck
  rcases Bool.and_eq_true_iff.mp hLinkCheck with
    ⟨hLinkPrefix, hInitialEqBool⟩
  rcases Bool.and_eq_true_iff.mp hLinkPrefix with
    ⟨hParentContains, hOutside⟩
  have hInitialEq : initial.clause = link.skeleton :=
    PropResolution.clauseEq_eq.mp hInitialEqBool
  have hParentMem :
      link.parent ∈
        (cert.checked.dag.nodeAt index hIndex).parents.toList := by
    exact Array.mem_def.mp (by simpa using hParentContains)
  have hParentSize : link.parent < cert.checked.dag.nodes.size :=
    Nat.lt_trans
      (cert.checked.parentsBefore index hIndex link.parent hParentMem)
      hIndex
  rcases DAG.propAvatarSkeletonInitialLinkOk_sound hDagOk with
    ⟨parentNode, splitPayload, hParentLookup, hParentUnguarded,
      hParentPayload, hSkeletonEq⟩
  have hParentNodeEq :
      parentNode = cert.checked.dag.nodeAt link.parent hParentSize :=
    Option.some.inj
      (hParentLookup.symm.trans
        (cert.checked.dag.node?_eq_some_nodeAt hParentSize))
  have hParentPayload' :
      (cert.checked.dag.nodeAt link.parent hParentSize).payload =
        .avatarSplit splitPayload := by
    simpa [← hParentNodeEq] using hParentPayload
  have hParentGuards :
      Node.GuardsHold (cert.selectorValuation base)
        (cert.checked.dag.nodeAt link.parent hParentSize).guards :=
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
      PropResolution.Clause.Satisfies
        (cert.selectorValuation base) link.skeleton := by
    have hSelectors :=
      (cert.splitSelectorSemantics base
        hParentLookup hParentPayload).mp hSourceValid
    rw [hSkeletonEq]
    rcases hSelectors with ⟨literal, hLiteralMem, hLiteral⟩
    exact
      ⟨literal,
        PropResolution.mem_canonicalClause_of_mem hLiteralMem,
        hLiteral⟩
  rcases hSkeletonBase with ⟨literal, hLiteralMem, hLiteral⟩
  have hLiteralOutside :
      PropLiteralLink.outsideAtomMap payload.atomMap literal = true := by
    have hArrayMem : literal ∈ link.skeleton :=
      Array.mem_def.mpr hLiteralMem
    rcases Array.mem_iff_getElem.mp hArrayMem with
      ⟨literalSlot, hLiteralSlot, hLiteralGet⟩
    have hAt := (Array.all_eq_true.mp hOutside) literalSlot hLiteralSlot
    simpa [hLiteralGet] using hAt
  have hLiteralMixed :
      literal.Holds
        (PropLiteralLink.valuation
          (cert.selectorValuation base) payload.atomMap env) :=
    (PropLiteralLink.holds_valuation_iff_of_outsideAtomMap
      (base := cert.selectorValuation base) (env := env)
      hLiteralOutside).2 hLiteral
  exact PropResolution.Clause.satisfies_of_mem
    (by simpa only [hInitialEq] using hLiteralMem) hLiteralMixed

/-- checked registry 直接提供 split descriptor 的专用拓扑步骤。 -/
theorem avatarSplitBoundStackGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ))
    (base : Env M)
    (index : Nat) (hIndex : index < cert.checked.dag.nodes.size)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈
            (cert.checked.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base
          (cert.selectorValuation base) cert.checked.dag.problem
          (cert.checked.dag.nodeAt parent
            (Nat.lt_trans
              (cert.checked.parentsBefore index hIndex parent hParent)
              hIndex)))
    (payload : AvatarSplitPayload σ)
    (hPayload :
      (cert.checked.dag.nodeAt index hIndex).payload =
        .avatarSplit payload) :
    Node.BoundStackGuardedInvariant base
      (cert.selectorValuation base) cert.checked.dag.problem
      (cert.checked.dag.nodeAt index hIndex) :=
  cert.checked.avatarSplitBoundStackGuardedTopologicalStep
    base (cert.selectorValuation base) index hIndex hParents payload hPayload

/-- checked registry 直接提供 component 的专用拓扑步骤。 -/
theorem avatarComponentBoundStackGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ))
    (base : Env M)
    (index : Nat) (hIndex : index < cert.checked.dag.nodes.size)
    (payload : AvatarComponentPayload σ)
    (hPayload :
      (cert.checked.dag.nodeAt index hIndex).payload =
        .avatarComponent payload) :
    Node.BoundStackGuardedInvariant base
      (cert.selectorValuation base) cert.checked.dag.problem
      (cert.checked.dag.nodeAt index hIndex) :=
  cert.checked.avatarComponentBoundStackGuardedTopologicalStep
    base (cert.selectorValuation base)
    (cert.componentSelectorSemantics base)
    index hIndex payload hPayload

end CheckedAvatarDAG

/-! ## HO-AVATAR 专用整图支持边界 -/

namespace PropInitialJustification

/-- AVATAR 专用 residual soundness 允许消费 selector skeleton。 -/
def avatarSoundnessSupported {σ : Signature.{u, v, w}} :
    PropInitialJustification σ → Bool
  | .parentClause _ => true
  | .guardActivationClause _ => true
  | .propLearnedClause _ => true
  | .avatarSkeleton _ => true

end PropInitialJustification

namespace PropositionalClosurePayload

/-- AVATAR residual 的每个 initial 都必须具有专用语义回放。 -/
def avatarSoundnessSupported {σ : Signature.{u, v, w}}
    (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialJustifications.all
    PropInitialJustification.avatarSoundnessSupported

end PropositionalClosurePayload

namespace Payload

/--
HO-AVATAR fixed-bound-stack 整图允许的 payload。

这是独立于通用 `guardedSoundnessSupported` 的专用边界；新增 payload 时必须在本模块
提供对应拓扑证明后才能加入。
-/
def avatarSoundnessSupported {σ : Signature.{u, v, w}} : Payload σ → Bool
  | .source _ => true
  | .avatarSplit _ => true
  | .avatarComponent _ => true
  | .beta _ => true
  | .eta _ => true
  | .substitution _ => true
  | .standardizeApart _ => true
  | .resolution _ => true
  | .factoring _ => true
  | .equalityResolution _ => true
  | .booleanExtensionality _ => true
  | .demodulation _ => true
  | .positiveSuperposition _ => true
  | .negativeSuperposition _ => true
  | .extensionalParamodulation _ => true
  | .argumentCongruence _ => true
  | .functionExtensionality _ => true
  | .theoryConflict _ => true
  | .propositionalLearnedClause _ => true
  | .residualCdcl payload => payload.avatarSoundnessSupported

end Payload

namespace DAG

/-- 整张 HO-DAG 是否落在 AVATAR fixed-bound-stack soundness 片段。 -/
def avatarSoundnessSupported {σ : Signature.{u, v, w}} (dag : DAG σ) : Bool :=
  dag.nodes.all fun node => node.payload.avatarSoundnessSupported

/-- 整张 DAG 的 fixed-bound-stack guarded 不变量。 -/
def BoundStackGuardedInvariant {σ : Signature.{u, v, w}}
    [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {M : Structure σ}
    (dag : DAG σ) (base : Env M)
    (valuation : PropResolution.Valuation) : Prop :=
  ∀ index (hIndex : index < dag.nodes.size),
    Node.BoundStackGuardedInvariant base valuation dag.problem
      (dag.nodeAt index hIndex)

/-- 专用整图支持检查解包到任意节点。 -/
theorem avatarSoundnessSupported_of_eq_true
    {σ : Signature.{u, v, w}} {dag : DAG σ}
    (hSupported : dag.avatarSoundnessSupported = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      (dag.nodeAt index hIndex).payload.avatarSoundnessSupported = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hSupported
  simpa [avatarSoundnessSupported, nodeAt] using hAll index hIndex

end DAG

namespace CheckedDAG

/--
当前节点 guards 成立时，fixed-bound-stack 父不变量可回放任意 payload 父快照。
-/
theorem parentClauseSatisfiesOnBoundStackOfGuards
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ))
    (base : Env M) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hMerge :
      DAG.payloadMergesParentGuards
        (cert.dag.nodeAt index hIndex).payload = true)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans
              (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (hCurrentGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt index hIndex).guards)
    (parent : ParentClause σ)
    (hParent :
      parent ∈
        (cert.dag.nodeAt index hIndex).payload.parentClauses.toList)
    (env : Env M) (hEnv : env.WellSorted [])
    (hBound : Avatar.SameBoundStack env base) :
    parent.clause.Satisfies env := by
  have hParentMem :
      parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    Payload.parentIdsIn_of_check
      (cert.nodeChecked index hIndex) parent hParent
  have hParentSize : parent.id < cert.dag.nodes.size :=
    Nat.lt_trans
      (cert.parentsBefore index hIndex parent.id hParentMem) hIndex
  have hParentGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt parent.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex hMerge
      parent.id hParentMem hParentSize hCurrentGuards
  have hSnapshot :
      cert.dag.parentSnapshotChecked parent = true :=
    DAG.parentSnapshotChecked_of_eq_true cert.parentSnapshotsChecked
      index hIndex parent hParent
  exact cert.parentClauseSatisfiesOnBoundStack
    base valuation index hIndex hParents parent hParentMem hParentSize
    hSnapshot hParentGuards env hEnv hBound

/-- source 节点在 fixed-bound-stack 上直接消费问题有效性。 -/
theorem sourceBoundStackGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ))
    (base : Env M) (valuation : PropResolution.Valuation)
    (hProblem : cert.dag.problem.Valid M)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (initialIndex : Nat)
    (hSource :
      (cert.dag.nodeAt index hIndex).payload = .source initialIndex) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have hNodeCheck := cert.nodeChecked index hIndex
  rw [Node.check, hSource] at hNodeCheck
  cases hLookup :
      cert.dag.problem.initialClauses[initialIndex]? with
  | none =>
      simp [Payload.check, hLookup] at hNodeCheck
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
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (base : Env M) (valuation : PropResolution.Valuation)
    (hProblem : cert.dag.problem.Valid M)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans
              (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (hPayloadSupported :
      (cert.dag.nodeAt index hIndex).payload.soundnessSupported = true) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have hMergeOfParent :
      ∀ parent,
        parent ∈
            (cert.dag.nodeAt index hIndex).payload.parentClauses.toList →
          DAG.payloadMergesParentGuards
            (cert.dag.nodeAt index hIndex).payload = true := by
    intro parent hParent
    cases hPayload : (cert.dag.nodeAt index hIndex).payload <;>
      simp [hPayload, Payload.parentClauses, Payload.soundnessSupported,
        DAG.payloadMergesParentGuards] at hParent hPayloadSupported ⊢
  have hParentSat :
      ∀ parent,
        parent ∈
            (cert.dag.nodeAt index hIndex).payload.parentClauses.toList →
          ∀ env : Env M, env.WellSorted [] →
            Avatar.SameBoundStack env base →
              Node.GuardsHold valuation
                  (cert.dag.nodeAt index hIndex).guards →
                parent.clause.Satisfies env := by
    intro parent hParent env hEnv hBound hGuards
    exact cert.parentClauseSatisfiesOnBoundStackOfGuards
      base valuation index hIndex (hMergeOfParent parent hParent)
      hParents hGuards parent hParent env hEnv hBound
  cases hPayload : (cert.dag.nodeAt index hIndex).payload with
  | source initialIndex =>
      exact cert.sourceBoundStackGuardedTopologicalStep
        base valuation hProblem index hIndex initialIndex hPayload
  | avatarSplit payload =>
      simp [hPayload, Payload.soundnessSupported] at hPayloadSupported
  | avatarComponent payload =>
      simp [hPayload, Payload.soundnessSupported] at hPayloadSupported
  | beta payload =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hPayloadCheck : payload.check = true :=
        (Bool.and_eq_true_iff.mp hNodeCheck).2
      refine
        ⟨payload.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv _hBound _hGuards
      exact Beta.Payload.sound contract payload env hEnv hPayloadCheck
  | eta payload =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hPayloadCheck : payload.check = true :=
        (Bool.and_eq_true_iff.mp hNodeCheck).2
      refine
        ⟨payload.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv _hBound _hGuards
      exact Eta.Payload.sound contract payload env hEnv hPayloadCheck
  | substitution evidence =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hEvidenceCheck :
          evidence.check (cert.dag.nodeAt index hIndex).parents = true := by
        simpa [Payload.check] using hNodeCheck
      simp only [Substitution.Evidence.check, Bool.and_eq_true_iff]
        at hEvidenceCheck
      rcases hEvidenceCheck with
        ⟨⟨⟨_hParent, _hParentCheck⟩, hSubstitutionCheck⟩,
          _hConclusionCheck⟩
      have hAdmissible : evidence.substitution.Admissible :=
        TermSubstitution.check_sound hSubstitutionCheck
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      let targetEnv :=
        TermSubstitution.semanticEnv evidence.substitution env
      have hTargetEnv : targetEnv.WellSorted [] :=
        TermSubstitution.semanticEnv_wellSorted hAdmissible hEnv
      have hEnvMatches :=
        TermSubstitution.semanticEnv_matches
          (substitution := evidence.substitution) (sourceEnv := env)
      have hTargetBound :
          Avatar.SameBoundStack targetEnv base := by
        intro boundIndex
        exact (hEnvMatches.1 boundIndex).trans (hBound boundIndex)
      have hParent :=
        hParentSat evidence.parent
          (by simp [hPayload, Payload.parentClauses])
          targetEnv hTargetEnv hTargetBound hGuards
      exact
        (Clause.satisfies_applySubstitution_iff_of_envMatches
          hAdmissible hEnvMatches evidence.parent.clause).mpr hParent
  | standardizeApart evidence =>
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      let targetEnv :=
        FreeVarRenaming.semanticEnv evidence.offset env
      have hTargetEnv : targetEnv.WellSorted [] :=
        FreeVarRenaming.semanticEnv_wellSorted hEnv
      have hEnvMatches :=
        FreeVarRenaming.semanticEnv_matches
          (offset := evidence.offset) (sourceEnv := env)
      have hTargetBound :
          Avatar.SameBoundStack targetEnv base := by
        intro boundIndex
        exact (hEnvMatches.1 boundIndex).trans (hBound boundIndex)
      have hParent :=
        hParentSat evidence.parent
          (by simp [hPayload, Payload.parentClauses])
          targetEnv hTargetEnv hTargetBound hGuards
      exact
        (Clause.satisfies_renameFreeVars_iff_of_envMatches
          hEnvMatches evidence.parent.clause).mpr hParent
  | resolution evidence =>
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      exact Clause.satisfies_resolutionResult
        (hParentSat evidence.left
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
        (hParentSat evidence.right
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | factoring evidence =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hEvidenceCheck :
          evidence.check (cert.dag.nodeAt index hIndex).parents = true := by
        simpa [Payload.check] using hNodeCheck
      simp only [Factoring.Evidence.check, Bool.and_eq_true_iff]
        at hEvidenceCheck
      have hCovered :
          evidence.parent.clause.allLiteralsCovered evidence.conclusion =
            true :=
        hEvidenceCheck.1.2.2
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      exact Clause.satisfies_of_allLiteralsCovered hCovered
        (hParentSat evidence.parent
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | equalityResolution evidence =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hEvidenceCheck :
          evidence.check (cert.dag.nodeAt index hIndex).parents = true := by
        simpa [Payload.check] using hNodeCheck
      simp only [EqualityResolution.Evidence.check,
        Bool.and_eq_true_iff] at hEvidenceCheck
      have hTerm :
          StructuralEq.term evidence.left evidence.right = true :=
        hEvidenceCheck.1.2.1
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      exact Clause.satisfies_equalityResolutionResult hTerm
        (hParentSat evidence.parent
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | booleanExtensionality evidence =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hEvidenceCheck :
          evidence.check (cert.dag.nodeAt index hIndex).parents = true := by
        simpa [Payload.check] using hNodeCheck
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      apply Clause.satisfies_normalize
      exact Clause.satisfies_replaceLiteralAtEnd
        (evidence.selected_of_check hEvidenceCheck)
        ((evidence.satisfies_iff_replacement
          contract hEvidenceCheck env hEnv).mp)
        (hParentSat evidence.parent
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | demodulation evidence =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hEvidenceCheck :
          evidence.check .demodulation
            (cert.dag.nodeAt index hIndex).parents = true := by
        simpa [Payload.check] using hNodeCheck
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      exact evidence.sound contract hEvidenceCheck
        (hParentSat evidence.equality
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
        (hParentSat evidence.target
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | positiveSuperposition evidence =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hEvidenceCheck :
          evidence.check .positiveSuperposition
            (cert.dag.nodeAt index hIndex).parents = true := by
        simpa [Payload.check] using hNodeCheck
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      exact evidence.sound contract hEvidenceCheck
        (hParentSat evidence.equality
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
        (hParentSat evidence.target
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | negativeSuperposition evidence =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hEvidenceCheck :
          evidence.check .negativeSuperposition
            (cert.dag.nodeAt index hIndex).parents = true := by
        simpa [Payload.check] using hNodeCheck
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      exact evidence.sound contract hEvidenceCheck
        (hParentSat evidence.equality
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
        (hParentSat evidence.target
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | extensionalParamodulation evidence =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hEvidenceCheck :
          evidence.check .extensionalParamodulation
            (cert.dag.nodeAt index hIndex).parents = true := by
        simpa [Payload.check] using hNodeCheck
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      exact evidence.sound contract hEvidenceCheck
        (hParentSat evidence.equality
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
        (hParentSat evidence.target
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | argumentCongruence evidence =>
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      exact evidence.sound
        (hParentSat evidence.parent
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | functionExtensionality evidence =>
      have hNodeCheck := cert.nodeChecked index hIndex
      rw [Node.check, hPayload] at hNodeCheck
      have hEvidenceCheck :
          evidence.check (cert.dag.nodeAt index hIndex).parents = true := by
        simpa [Payload.check] using hNodeCheck
      refine
        ⟨evidence.conclusion,
          by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
      intro env hEnv hBound hGuards
      exact evidence.sound witnessContract hEnv hEvidenceCheck
        (hParentSat evidence.parent
          (by simp [hPayload, Payload.parentClauses])
          env hEnv hBound hGuards)
  | theoryConflict payload =>
      simp [hPayload, Payload.soundnessSupported] at hPayloadSupported
  | propositionalLearnedClause payload =>
      simp [hPayload, Payload.soundnessSupported] at hPayloadSupported
  | residualCdcl payload =>
      simp [hPayload, Payload.soundnessSupported] at hPayloadSupported

/-- theory conflict 节点在 fixed-bound-stack 上由空父字句推出矛盾。 -/
theorem theoryConflictBoundStackGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ))
    (base : Env M) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans
              (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : TheoryConflictPayload σ)
    (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have hCheck := cert.nodeChecked index hIndex
  rw [Node.check, hPayload] at hCheck
  have hConflictCheck :
      payload.conflict.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
        payload.conflict.clause.isEmpty = true := by
    simpa [Payload.check, TheoryConflictPayload.check] using
      Bool.and_eq_true_iff.mp hCheck
  have hParentMem :
      payload.conflict.id ∈
        (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hConflictCheck.1
  have hParentSize : payload.conflict.id < cert.dag.nodes.size :=
    Nat.lt_trans
      (cert.parentsBefore index hIndex payload.conflict.id hParentMem)
      hIndex
  have hSnapshot :
      cert.dag.parentSnapshotChecked payload.conflict = true :=
    DAG.parentSnapshotChecked_of_eq_true cert.parentSnapshotsChecked
      index hIndex payload.conflict
      (by
        simp [hPayload, Payload.parentClauses,
          TheoryConflictPayload.parentClauses])
  refine
    ⟨{ literals := #[] },
      by simp [Node.conclusion?, hPayload, Payload.conclusion?], ?_⟩
  intro env hEnv hBound hCurrentGuards
  have hParentGuards :
      Node.GuardsHold valuation
        (cert.dag.nodeAt payload.conflict.id hParentSize).guards :=
    cert.parentGuardsHold_of_localNodeGuardsOk index hIndex
      (by simp [hPayload, DAG.payloadMergesParentGuards])
      payload.conflict.id hParentMem hParentSize hCurrentGuards
  have hParentSat :=
    cert.parentClauseSatisfiesOnBoundStack
      base valuation index hIndex hParents payload.conflict hParentMem
      hParentSize hSnapshot hParentGuards env hEnv hBound
  exact False.elim
    (Clause.not_satisfies_of_isEmpty hConflictCheck.2 hParentSat)

/-- propositional learned-clause 节点在 fixed-bound-stack 上消费 theory conflict。 -/
theorem propositionalLearnedClauseBoundStackGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedDAG (σ := σ))
    (base : Env M) (valuation : PropResolution.Valuation)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base valuation cert.dag.problem
          (cert.dag.nodeAt parent
            (Nat.lt_trans
              (cert.parentsBefore index hIndex parent hParent) hIndex)))
    (payload : PropositionalLearnedClausePayload)
    (hPayload :
      (cert.dag.nodeAt index hIndex).payload =
        .propositionalLearnedClause payload) :
    Node.BoundStackGuardedInvariant base valuation cert.dag.problem
      (cert.dag.nodeAt index hIndex) := by
  have hCheck := cert.nodeChecked index hIndex
  rw [Node.check, hPayload] at hCheck
  have hParentIn :
      (cert.dag.nodeAt index hIndex).parents.contains payload.conflict =
        true := by
    simpa [Payload.check, PropositionalLearnedClausePayload.check] using
      hCheck
  have hParentMem :
      payload.conflict ∈
        (cert.dag.nodeAt index hIndex).parents.toList :=
    Array.mem_def.mp (by simpa using hParentIn)
  have hParentSize : payload.conflict < cert.dag.nodes.size :=
    Nat.lt_trans
      (cert.parentsBefore index hIndex payload.conflict hParentMem)
      hIndex
  have hGuardCheck := cert.nodeGuardsChecked index hIndex
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
      Node.GuardsHold valuation
        (cert.dag.nodeAt payload.conflict hParentSize).guards :=
    Node.GuardsHold.of_guardSetEq hGuardEq hCurrentGuards
  rcases hParents payload.conflict hParentMem with
    ⟨parentConclusion, hParentConclusion, hParentSat⟩
  have hParentEmpty : parentConclusion.isEmpty = true := by
    have hParentTheory :
        (cert.dag.nodeAt payload.conflict hParentSize).theoryConflict
          cert.dag.problem = true :=
      hTheory
    unfold Node.theoryConflict at hParentTheory
    rw [hParentConclusion] at hParentTheory
    exact (Bool.and_eq_true_iff.mp hParentTheory).2
  exact False.elim
    (Clause.not_satisfies_of_isEmpty hParentEmpty
      (hParentSat env hEnv hBound hParentGuards))

end CheckedDAG

namespace CheckedAvatarDAG

/-- residual CDCL 的 initial justification 槽位检查解包。 -/
private theorem avatarPropClosureJustificationCheckAt
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {parents : Array Nat} {payload : PropositionalClosurePayload σ}
    (hCheck : payload.justificationsCheck parents = true)
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
  have hAt :=
    (Array.all_eq_true.mp hAllBool) slot (by
      simpa [Array.size_mapIdx] using hSlot)
  have hJustGet :
      payload.initialJustifications[slot]? =
        some payload.initialJustifications[slot] :=
    Array.getElem?_eq_some_iff.mpr ⟨hJust, rfl⟩
  simpa [Array.getElem_mapIdx, hJustGet] using hAt

/-- AVATAR residual 支持检查解包到单个 initial justification。 -/
private theorem avatarPropClosureJustificationSupportedAt
    {σ : Signature.{u, v, w}}
    {payload : PropositionalClosurePayload σ}
    (hSupported : payload.avatarSoundnessSupported = true)
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
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ))
    (base : Env M)
    (index : Nat) (hIndex : index < cert.checked.dag.nodes.size)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈
            (cert.checked.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base
          (cert.selectorValuation base) cert.checked.dag.problem
          (cert.checked.dag.nodeAt parent
            (Nat.lt_trans
              (cert.checked.parentsBefore index hIndex parent hParent)
              hIndex)))
    (payload : PropositionalClosurePayload σ)
    (hPayload :
      (cert.checked.dag.nodeAt index hIndex).payload =
        .residualCdcl payload)
    (hPayloadSupported : payload.avatarSoundnessSupported = true) :
    Node.BoundStackGuardedInvariant base
      (cert.selectorValuation base) cert.checked.dag.problem
      (cert.checked.dag.nodeAt index hIndex) := by
  have hCheck := cert.checked.nodeChecked index hIndex
  rw [Node.check, hPayload] at hCheck
  have hResidualCheck :
      (!((cert.checked.dag.nodeAt index hIndex).parents.isEmpty) &&
        payload.check
          (cert.checked.dag.nodeAt index hIndex).parents) = true := by
    simpa [Payload.check] using hCheck
  have hClosureCheck :
      payload.check
        (cert.checked.dag.nodeAt index hIndex).parents = true :=
    (Bool.and_eq_true_iff.mp hResidualCheck).2
  have hCheckedUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof =
        true :=
    (Bool.and_eq_true_iff.mp hClosureCheck).1
  have hJustifications :
      payload.justificationsCheck
        (cert.checked.dag.nodeAt index hIndex).parents = true :=
    (Bool.and_eq_true_iff.mp hClosureCheck).2
  have hInitialLinks :=
    cert.checked.nodePropInitialLinksChecked index hIndex
  have hDagInitials :
      payload.initialJustifications.all
        (fun justification =>
          cert.checked.dag.propInitialJustificationDagOk
            (cert.checked.dag.nodeAt index hIndex).parents
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
  apply checkedCert.sound
    (valuation :=
      PropLiteralLink.valuation
        (cert.selectorValuation base) payload.atomMap env)
  intro initial hInitialMem
  have hInitialArray : initial ∈ payload.initialClauses :=
    Array.mem_def.mpr hInitialMem
  rcases Array.mem_iff_getElem.mp hInitialArray with
    ⟨slot, hSlot, hInitialGet⟩
  rcases avatarPropClosureJustificationCheckAt hJustifications hSlot with
    ⟨hJustSlot, hJustificationCheck⟩
  have hDagOk :=
    (Array.all_eq_true.mp hDagInitials) slot hJustSlot
  have _hJustificationSupported :=
    avatarPropClosureJustificationSupportedAt
      hPayloadSupported hJustSlot
  cases hJustification : payload.initialJustifications[slot] with
  | parentClause link =>
      have hLinkCheck :
          link.check
            (cert.checked.dag.nodeAt index hIndex).parents
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
          cert.checked.dag.propParentInitialLinkOk
            (cert.checked.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using
          hDagOk
      unfold DAG.propParentInitialLinkOk at hDagParent
      rcases Bool.and_eq_true_iff.mp hDagParent with
        ⟨hDagPrefix, hParentUnguardedCheck⟩
      rcases Bool.and_eq_true_iff.mp hDagPrefix with
        ⟨_hDagParentIn, hSnapshot⟩
      have hParentMem :
          link.parent.id ∈
            (cert.checked.dag.nodeAt index hIndex).parents.toList :=
        ParentClause.mem_toList_of_idIn hParentInBool
      have hParentSize :
          link.parent.id < cert.checked.dag.nodes.size :=
        Nat.lt_trans
          (cert.checked.parentsBefore
            index hIndex link.parent.id hParentMem)
          hIndex
      have hParentLookup :
          cert.checked.dag.node? link.parent.id =
            some
              (cert.checked.dag.nodeAt link.parent.id hParentSize) :=
        cert.checked.dag.node?_eq_some_nodeAt hParentSize
      rw [hParentLookup] at hParentUnguardedCheck
      have hParentGuards :
          Node.GuardsHold (cert.selectorValuation base)
            (cert.checked.dag.nodeAt
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
        PropParentClauseLink.encodedClause_satisfies_of_object
          (base := cert.selectorValuation base) (env := env)
          hLiteralChecks hObjectSat
  | guardActivationClause link =>
      have hLinkCheck :
          link.check
            (cert.checked.dag.nodeAt index hIndex).parents
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
          cert.checked.dag.propGuardActivationInitialLinkOk
            (cert.checked.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using
          hDagOk
      unfold DAG.propGuardActivationInitialLinkOk at hDagActivation
      rcases Bool.and_eq_true_iff.mp hDagActivation with
        ⟨hDagPrefix, hParentFields⟩
      rcases Bool.and_eq_true_iff.mp hDagPrefix with
        ⟨_hDagParentIn, hSnapshot⟩
      have hParentMem :
          link.parent.id ∈
            (cert.checked.dag.nodeAt index hIndex).parents.toList :=
        ParentClause.mem_toList_of_idIn hParentInBool
      have hParentSize :
          link.parent.id < cert.checked.dag.nodes.size :=
        Nat.lt_trans
          (cert.checked.parentsBefore
            index hIndex link.parent.id hParentMem)
          hIndex
      have hParentLookup :
          cert.checked.dag.node? link.parent.id =
            some
              (cert.checked.dag.nodeAt link.parent.id hParentSize) :=
        cert.checked.dag.node?_eq_some_nodeAt hParentSize
      rw [hParentLookup] at hParentFields
      rcases Bool.and_eq_true_iff.mp hParentFields with
        ⟨_hGuarded, hGuardEq⟩
      have hActivationSat :=
        PropGuardActivationLink.encodedClause_satisfies
          (base := cert.selectorValuation base) (env := env)
          hGuardChecks hLiteralChecks
          (fun hLinkGuards => by
            have hParentGuards :
                Node.GuardsHold (cert.selectorValuation base)
                  (cert.checked.dag.nodeAt
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
          link.check
            (cert.checked.dag.nodeAt index hIndex).parents
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
          link.clause = learnedClauseOfGuards link.guards :=
        PropResolution.clauseEq_eq.mp hLearnedEqBool
      have hDagLearned :
          cert.checked.dag.propLearnedInitialLinkOk
            (cert.checked.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using
          hDagOk
      unfold DAG.propLearnedInitialLinkOk at hDagLearned
      have hParentMem :
          link.parent ∈
            (cert.checked.dag.nodeAt index hIndex).parents.toList :=
        Array.mem_def.mp (by
          simpa using (Bool.and_eq_true_iff.mp hDagLearned).1)
      have hParentSize : link.parent < cert.checked.dag.nodes.size :=
        Nat.lt_trans
          (cert.checked.parentsBefore
            index hIndex link.parent hParentMem)
          hIndex
      have hParentLookup :
          cert.checked.dag.node? link.parent =
            some (cert.checked.dag.nodeAt link.parent hParentSize) :=
        cert.checked.dag.node?_eq_some_nodeAt hParentSize
      rw [hParentLookup] at hDagLearned
      rcases Bool.and_eq_true_iff.mp hDagLearned with
        ⟨_hParentIn, hParentPayloadCheck⟩
      cases hParentPayload :
          (cert.checked.dag.nodeAt link.parent hParentSize).payload with
      | propositionalLearnedClause learnedPayload =>
          simp [hParentPayload] at hParentPayloadCheck
          rcases hParentPayloadCheck with
            ⟨hGuardEq, _hClauseEq⟩
          by_cases hGuards :
              Node.GuardsHold
                (cert.selectorValuation base) link.guards
          · have hParentGuards :
                Node.GuardsHold (cert.selectorValuation base)
                  (cert.checked.dag.nodeAt
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
            exact False.elim
              (Clause.not_satisfies_of_isEmpty hParentEmpty
                (hParentSat env hEnv hBound hParentGuards))
          · simpa [hInitialEq] using
              PropLearnedClauseLink.satisfies_of_not_guards
                (base := cert.selectorValuation base) (env := env)
                hLearnedEq hOutside hGuards
      | source initialIndex =>
          simp [hParentPayload] at hParentPayloadCheck
      | avatarSplit splitPayload =>
          simp [hParentPayload] at hParentPayloadCheck
      | avatarComponent componentPayload =>
          simp [hParentPayload] at hParentPayloadCheck
      | beta betaPayload =>
          simp [hParentPayload] at hParentPayloadCheck
      | eta etaPayload =>
          simp [hParentPayload] at hParentPayloadCheck
      | substitution evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | standardizeApart evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | resolution evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | factoring evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | equalityResolution evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | booleanExtensionality evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | demodulation evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | positiveSuperposition evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | negativeSuperposition evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | extensionalParamodulation evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | argumentCongruence evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | functionExtensionality evidence =>
          simp [hParentPayload] at hParentPayloadCheck
      | theoryConflict conflictPayload =>
          simp [hParentPayload] at hParentPayloadCheck
      | residualCdcl closurePayload =>
          simp [hParentPayload] at hParentPayloadCheck
  | avatarSkeleton link =>
      have hLinkCheck :
          link.check
            (cert.checked.dag.nodeAt index hIndex).parents
            payload.atomMap initial = true := by
        simpa [PropInitialJustification.check, hJustification, hInitialGet]
          using hJustificationCheck
      have hDagSkeleton :
          cert.checked.dag.propAvatarSkeletonInitialLinkOk
            (cert.checked.dag.nodeAt index hIndex).parents link = true := by
        simpa [DAG.propInitialJustificationDagOk, hJustification] using
          hDagOk
      exact cert.avatarSkeletonInitialSatisfies
        base index hIndex hParents payload initial link env
        hLinkCheck hDagSkeleton

/-- HO-AVATAR fixed-bound-stack 支持片段的一步统一拓扑回放。 -/
theorem avatarBoundStackGuardedTopologicalStep
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (base : Env M)
    (hProblem : cert.checked.dag.problem.Valid M)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true)
    (index : Nat) (hIndex : index < cert.checked.dag.nodes.size)
    (hParents :
      ∀ parent
        (hParent :
          parent ∈
            (cert.checked.dag.nodeAt index hIndex).parents.toList),
        Node.BoundStackGuardedInvariant base
          (cert.selectorValuation base) cert.checked.dag.problem
          (cert.checked.dag.nodeAt parent
            (Nat.lt_trans
              (cert.checked.parentsBefore index hIndex parent hParent)
              hIndex))) :
    Node.BoundStackGuardedInvariant base
      (cert.selectorValuation base) cert.checked.dag.problem
      (cert.checked.dag.nodeAt index hIndex) := by
  have hNodeSupported :=
    DAG.avatarSoundnessSupported_of_eq_true hSupported index hIndex
  cases hPayload :
      (cert.checked.dag.nodeAt index hIndex).payload with
  | source initialIndex =>
      exact cert.checked.sourceBoundStackGuardedTopologicalStep
        base (cert.selectorValuation base) hProblem
        index hIndex initialIndex hPayload
  | avatarSplit payload =>
      exact cert.avatarSplitBoundStackGuardedTopologicalStep
        base index hIndex hParents payload hPayload
  | avatarComponent payload =>
      exact cert.avatarComponentBoundStackGuardedTopologicalStep
        base index hIndex payload hPayload
  | beta payload =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | eta payload =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | substitution evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | standardizeApart evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | resolution evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | factoring evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | equalityResolution evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | booleanExtensionality evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | demodulation evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | positiveSuperposition evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | negativeSuperposition evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | extensionalParamodulation evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | argumentCongruence evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | functionExtensionality evidence =>
      exact cert.checked.ordinaryBoundStackGuardedTopologicalStep
        contract witnessContract base (cert.selectorValuation base)
        hProblem index hIndex hParents
        (by simp [hPayload, Payload.soundnessSupported])
  | theoryConflict payload =>
      exact
        cert.checked.theoryConflictBoundStackGuardedTopologicalStep
          base (cert.selectorValuation base) index hIndex hParents
          payload hPayload
  | propositionalLearnedClause payload =>
      exact
        cert.checked.propositionalLearnedClauseBoundStackGuardedTopologicalStep
          base (cert.selectorValuation base) index hIndex hParents
          payload hPayload
  | residualCdcl payload =>
      have hPayloadSupported :
          payload.avatarSoundnessSupported = true := by
        simpa [hPayload, Payload.avatarSoundnessSupported] using
          hNodeSupported
      exact cert.residualCdclBoundStackGuardedTopologicalStep
        base index hIndex hParents payload hPayload hPayloadSupported

/-- checked HO-AVATAR DAG 的专用 fixed-bound-stack 整图 soundness。 -/
theorem boundStackGuardedInvariant
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (base : Env M)
    (hProblem : cert.checked.dag.problem.Valid M)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) :
    cert.checked.dag.BoundStackGuardedInvariant
      base (cert.selectorValuation base) :=
  cert.checked.topologicalInduction
    (P := fun _ _ node =>
      Node.BoundStackGuardedInvariant base
        (cert.selectorValuation base) cert.checked.dag.problem node)
    (fun index hIndex hParents =>
      cert.avatarBoundStackGuardedTopologicalStep
        contract witnessContract base hProblem hSupported
        index hIndex hParents)

/-- 专用整图归纳在 root 上的直接版本。 -/
theorem rootBoundStackGuardedInvariant
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (base : Env M)
    (hProblem : cert.checked.dag.problem.Valid M)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) :
    Node.BoundStackGuardedInvariant base
      (cert.selectorValuation base) cert.checked.dag.problem
      (cert.checked.dag.nodeAt
        cert.checked.dag.root cert.checked.rootExists) :=
  cert.checked.rootByTopologicalInduction
    (P := fun _ _ node =>
      Node.BoundStackGuardedInvariant base
        (cert.selectorValuation base) cert.checked.dag.problem node)
    (fun index hIndex hParents =>
      cert.avatarBoundStackGuardedTopologicalStep
        contract witnessContract base hProblem hSupported
        index hIndex hParents)

/--
HO-AVATAR residual CDCL 的专用空根矛盾。

root checker 保证结论为空且没有 guard；canonical selector valuation 下的整图
fixed-bound-stack 不变量因而否定当前模型中的问题有效性。
-/
theorem rootEmptyContradiction
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {M : Structure σ} (cert : CheckedAvatarDAG (σ := σ))
    (contract : Logic.HigherOrder.ExtensionalContract M)
    (witnessContract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (base : Env M) (hBase : base.WellSorted [])
    (hProblem : cert.checked.dag.problem.Valid M)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) :
    False := by
  have hRootInvariant :=
    cert.rootBoundStackGuardedInvariant
      contract witnessContract base hProblem hSupported
  rcases cert.checked.rootConclusion with
    ⟨rootConclusion, hRootConclusion, hRootEmpty⟩
  rcases hRootInvariant with
    ⟨invariantConclusion, hInvariantConclusion, hSatisfies⟩
  have hConclusionEq : invariantConclusion = rootConclusion :=
    Option.some.inj
      (hInvariantConclusion.symm.trans hRootConclusion)
  subst rootConclusion
  have hRootGuards :
      Node.GuardsHold (cert.selectorValuation base)
        (cert.checked.dag.nodeAt
          cert.checked.dag.root cert.checked.rootExists).guards :=
    Node.GuardsHold.of_isEmpty cert.checked.rootUnguarded
  exact Clause.not_satisfies_of_isEmpty hRootEmpty
    (hSatisfies base hBase (Avatar.SameBoundStack.refl base) hRootGuards)

end CheckedAvatarDAG

end HODAGCertificate
end Automation
end YesMetaZFC
