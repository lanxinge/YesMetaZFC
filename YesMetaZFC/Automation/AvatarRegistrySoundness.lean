import YesMetaZFC.Automation.AvatarSoundness

/-!
# AVATAR selector registry 的全局语义闭合

本模块在通用 `CheckedDAG` 之上增加一个 AVATAR 专用可信边界。checker 会复算每个
split 的 literal 覆盖、component 自由变量支持不交和 selector 正性，并检查整张图中
同一个 selector 变量始终指向同一个对象层 component。

通过这层边界后，AVATAR fixed-bound-stack soundness 所需的命题 valuation 与
component/split selector 语义合同都可从 DAG 自动构造，不再由调用者外部提供。
-/

namespace YesMetaZFC
namespace Automation

namespace PropResolution

private theorem mem_insertCanonicalLitList {candidate inserted : Lit} :
    ∀ {lits : List Lit},
      candidate ∈ insertCanonicalLitList lits inserted →
        candidate = inserted ∨ candidate ∈ lits
  | [], h => by
      simpa [insertCanonicalLitList] using h
  | current :: rest, h => by
      by_cases hEq : current = inserted
      · simp [insertCanonicalLitList, hEq] at h
        rcases h with hInserted | hRest
        · exact Or.inl hInserted
        · exact Or.inr (List.mem_cons_of_mem current hRest)
      · by_cases hLe : Lit.le inserted current
        · simp [insertCanonicalLitList, hEq, hLe] at h
          rcases h with hInserted | hCurrent | hRest
          · exact Or.inl hInserted
          · exact Or.inr (by simp [hCurrent])
          · exact Or.inr (by simp [hRest])
        · simp [insertCanonicalLitList, hEq, hLe] at h
          rcases h with hCurrent | hTail
          · exact Or.inr (by simp [hCurrent])
          · rcases mem_insertCanonicalLitList hTail with hInserted | hRest
            · exact Or.inl hInserted
            · exact Or.inr (by simp [hRest])

private theorem mem_of_mem_canonicalClauseList {candidate : Lit} :
    ∀ {lits : List Lit}, candidate ∈ canonicalClauseList lits → candidate ∈ lits
  | [], h => by simp [canonicalClauseList] at h
  | current :: rest, h => by
      rcases mem_insertCanonicalLitList h with hCurrent | hCanonicalRest
      · simp [hCurrent]
      · simp [mem_of_mem_canonicalClauseList hCanonicalRest]

namespace Clause

/-- 命题字句规范化保持且只保持原有文字，因此保持满足性。 -/
theorem satisfies_canonicalClause_iff (valuation : Valuation) (clause : Clause) :
    Satisfies valuation (canonicalClause clause) ↔ Satisfies valuation clause := by
  constructor
  · rintro ⟨literal, hMem, hHolds⟩
    exact
      ⟨literal,
        by
          simpa [canonicalClause] using
            mem_of_mem_canonicalClauseList hMem,
        hHolds⟩
  · rintro ⟨literal, hMem, hHolds⟩
    exact ⟨literal, mem_canonicalClause_of_mem hMem, hHolds⟩

end Clause
end PropResolution

namespace DAGCertificate

universe x

open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.Automation.LogicSoundness

namespace Clause

/-- 可计算地检查 components 是否在 literal 层双向覆盖 source。 -/
def coversCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (source : Clause σ) (components : List (Clause σ)) : Bool :=
  (source.literals.toList.all fun literal =>
    components.any fun component => component.containsLiteral literal) &&
  components.all fun component => component.allLiteralsCovered source

/-- literal 覆盖检查解包为语义分解所需的双向覆盖合同。 -/
theorem coversCheck_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {source : Clause σ} {components : List (Clause σ)}
    (hCheck : coversCheck source components = true) : Covers source components := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hForward, hBackward⟩
  constructor
  · intro literal hLiteral
    have hAny := List.all_eq_true.mp hForward literal hLiteral
    rcases List.any_eq_true.mp hAny with
      ⟨component, hComponent, hContains⟩
    rcases containsLiteralList_sound
        (by simpa [containsLiteral] using hContains) with
      ⟨found, hFound, hFoundEq⟩
    subst found
    exact ⟨component, hComponent, hFound⟩
  · intro component hComponent literal hLiteral
    have hCovered := List.all_eq_true.mp hBackward component hComponent
    rcases allLiteralsCovered_sound hCovered hLiteral with
      ⟨found, hFound, hFoundEq⟩
    simpa [hFoundEq] using hFound

/-- 两个有限自由变量支持是否不交。 -/
def supportsDisjointCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    (left right : Logic.FirstOrder.FreeVariable.Support σ) : Bool :=
  left.all fun fv => !right.contains fv

/-- component 列表的自由变量支持是否两两不交。 -/
def pairwiseSupportDisjointCheck {σ : Signature} [DecidableEq σ.SortSymbol] :
    List (Clause σ) → Bool
  | [] => true
  | head :: rest =>
      rest.all
        (fun other =>
          supportsDisjointCheck head.freeSupport other.freeSupport) &&
        pairwiseSupportDisjointCheck rest

/-- 有限支持不交检查的逻辑解包。 -/
theorem supportsDisjointCheck_sound {σ : Signature}
    [DecidableEq σ.SortSymbol]
    {left right : Logic.FirstOrder.FreeVariable.Support σ}
    (hCheck : supportsDisjointCheck left right = true) :
    Logic.FirstOrder.FreeVariable.Support.Disjoint left right := by
  intro fv hLeft hRight
  have hNotMem : ¬ fv ∈ right := by
    simpa [supportsDisjointCheck] using
      List.all_eq_true.mp hCheck fv hLeft
  exact hNotMem hRight

/-- 两两支持不交检查解包为 AVATAR component decomposition 合同。 -/
theorem pairwiseSupportDisjointCheck_sound {σ : Signature}
    [DecidableEq σ.SortSymbol] {components : List (Clause σ)}
    (hCheck : pairwiseSupportDisjointCheck components = true) :
    PairwiseSupportDisjoint components := by
  induction components with
  | nil =>
      trivial
  | cons head rest ih =>
      rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hRest⟩
      constructor
      · intro other hOther
        exact supportsDisjointCheck_sound
          (List.all_eq_true.mp hHead other hOther)
      · exact ih hRest

end Clause

namespace AvatarSelectorComponent

/-- 整个 registry 中同一 selector 变量是否始终指向同一个 component。 -/
def compatibleCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (entries : List (AvatarSelectorComponent σ)) : Bool :=
  entries.all fun left =>
    entries.all fun right =>
      if left.selector.var == right.selector.var then
        left.component.eq right.component
      else
        true

/-- 全局 selector/component 一致性检查解包。 -/
theorem compatibleCheck_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {entries : List (AvatarSelectorComponent σ)}
    (hCheck : compatibleCheck entries = true) : Compatible entries := by
  intro left hLeft right hRight hVariable
  have hLeftCheck := List.all_eq_true.mp hCheck left hLeft
  have hRightCheck := List.all_eq_true.mp hLeftCheck right hRight
  have hComponentCheck : left.component.eq right.component = true := by
    simpa [compatibleCheck, hVariable] using hRightCheck
  exact Clause.eq_sound _ _ hComponentCheck

/--
局部 selector skeleton 在全局 registry valuation 下的精确语义。

局部 entries 只需是 registry 的子列表；selector 的解释由全局正性和全局一致性唯一
确定。
-/
theorem selectorClause_satisfies_iff_exists_valid_in_registry
    {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M)
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
    exact
      ⟨entry, hEntry,
        (holds_valuation_iff_component_valid
          base registry hPositive hCompatible hEntryRegistry).mp hSelector⟩
  · rintro ⟨entry, hEntry, hValid⟩
    have hEntryRegistry := hSubset entry hEntry
    refine ⟨entry.selector, ?_, ?_⟩
    · have hMapped :
          entry.selector ∈
            entries.map AvatarSelectorComponent.selector :=
        List.mem_map.mpr ⟨entry, hEntry, rfl⟩
      simpa [selectorClause] using hMapped
    · exact
        (holds_valuation_iff_component_valid
          base registry hPositive hCompatible hEntryRegistry).mpr hValid

end AvatarSelectorComponent

namespace AvatarSplitPayload

/--
单个 split 可由 checker 独立复算出的 registry 合同。

selector 的跨 split 一致性是全图性质，因此不放在这里，而由全局 registry checker
统一提供。
-/
structure RegistryContract {σ : Signature}
    (payload : AvatarSplitPayload σ) : Prop where
  aligned :
    payload.selectors.toList.length = payload.componentClauses.length
  covers :
    Clause.Covers payload.source.clause payload.componentClauses
  pairwiseDisjoint :
    Clause.PairwiseSupportDisjoint payload.componentClauses
  selectorsPositive :
    ∀ selector, selector ∈ payload.selectors.toList →
      selector.positive = true

/-- 单个 split 的 AVATAR registry 可计算检查。 -/
def registryCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (payload : AvatarSplitPayload σ) : Bool :=
  payload.selectors.size == payload.componentClauses.length &&
    Clause.coversCheck payload.source.clause payload.componentClauses &&
      Clause.pairwiseSupportDisjointCheck payload.componentClauses &&
        payload.selectors.all fun selector => selector.positive

/-- 单 split registry 检查解包为局部分解合同。 -/
theorem registryCheck_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {payload : AvatarSplitPayload σ}
    (hCheck : registryCheck payload = true) : RegistryContract payload := by
  simp only [registryCheck, Bool.and_eq_true_iff] at hCheck
  rcases hCheck with
    ⟨⟨⟨hAligned, hCovers⟩, hDisjoint⟩, hPositive⟩
  exact {
    aligned := by simpa using hAligned
    covers := Clause.coversCheck_sound hCovers
    pairwiseDisjoint :=
      Clause.pairwiseSupportDisjointCheck_sound hDisjoint
    selectorsPositive := by
      intro selector hSelector
      have hArray : selector ∈ payload.selectors :=
        Array.mem_def.mpr hSelector
      rcases Array.mem_iff_getElem.mp hArray with
        ⟨index, hIndex, hGet⟩
      have hAt := Array.all_eq_true.mp hPositive index hIndex
      simpa [hGet] using hAt
  }

/-- 局部 registry 合同推出配对表中的 selector 全为正文字。 -/
theorem RegistryContract.selectorComponentsPositive {σ : Signature}
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
theorem selectorComponent_mem {σ : Signature}
    {payload : AvatarSplitPayload σ}
    {index : Nat} {indices : Array Nat} {selector : GuardLit}
    (hIndices : payload.partitions[index]? = some indices)
    (hSelector :
      AvatarSplit.selectorAt? payload.selectors index = some selector) :
    ⟨selector, Clause.atIndices payload.source.clause indices⟩ ∈
      payload.selectorComponents := by
  have hSelectorList :
      payload.selectors.toList[index]? = some selector := by
    simpa [AvatarSplit.selectorAt?] using hSelector
  have hComponentList :
      payload.componentClauses[index]? =
        some (Clause.atIndices payload.source.clause indices) := by
    have hPartitionList :
        payload.partitions.toList[index]? = some indices := by
      simpa using hIndices
    simp [componentClauses, hPartitionList]
  have hEntryGet :
      payload.selectorComponents[index]? =
        some ⟨selector, Clause.atIndices payload.source.clause indices⟩ :=
    AvatarSelectorComponent.getElem?_ofLists
      hSelectorList hComponentList
  rcases List.getElem?_eq_some_iff.mp hEntryGet with
    ⟨hIndex, hGet⟩
  rw [← hGet]
  exact List.getElem_mem hIndex

/-- 单 split source 在全局 registry valuation 下等价于其 selector skeleton。 -/
theorem source_valid_iff_selectors_satisfy_in_registry {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : SetLevel.StructureAt.{x} σ}
    (base : SetLevel.EnvAt.{x} M) (payload : AvatarSplitPayload σ)
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
      ⟨entry.component,
        by
          rw [← hComponents]
          exact List.mem_map.mpr ⟨entry, hEntry, rfl⟩,
        hValid⟩

end AvatarSplitPayload

namespace Payload

/-- 一个 payload 对全局 selector registry 的贡献。 -/
def avatarSelectorComponents {σ : Signature} :
    Payload σ → List (AvatarSelectorComponent σ)
  | .avatarSplit payload => payload.selectorComponents
  | _ => []

/-- 一个 payload 是否满足局部 AVATAR registry 检查。 -/
def avatarRegistryLocalCheck {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] : Payload σ → Bool
  | .avatarSplit payload => payload.registryCheck
  | _ => true

end Payload

namespace DAG

/-- 从整张 DAG 中按节点顺序收集所有 split selector/component 登记项。 -/
def avatarSelectorRegistry {σ : Signature} (dag : DAG σ) :
    List (AvatarSelectorComponent σ) :=
  dag.nodes.toList.flatMap fun node =>
    node.payload.avatarSelectorComponents

/-- 单个 DAG 节点的局部 AVATAR registry 检查。 -/
def nodeAvatarRegistryLocalCheck {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (node : Node σ) : Bool :=
  node.payload.avatarRegistryLocalCheck

/--
AVATAR selector registry 的整图可信边界。

左侧检查每个 split 的 decomposition 结构，右侧检查跨 split 的 selector/component
一致性。
-/
def avatarRegistryCheck {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (dag : DAG σ) : Bool :=
  dag.nodes.all nodeAvatarRegistryLocalCheck &&
    AvatarSelectorComponent.compatibleCheck dag.avatarSelectorRegistry

/--
逐节点局部证明与经等式审计的全局 registry 合成 AVATAR registry checker。
-/
theorem avatarRegistryCheck_eq_true_of_nodes_and_registry {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (dag : DAG σ)
    (registry : List (AvatarSelectorComponent σ))
    (checked : CheckedList nodeAvatarRegistryLocalCheck dag.nodes.toList)
    (hRegistry : dag.avatarSelectorRegistry = registry)
    (hCompatible : AvatarSelectorComponent.compatibleCheck registry = true) :
    dag.avatarRegistryCheck = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · rw [← Array.all_toList]
    exact checked.all_eq_true
  · rw [hRegistry]
    exact hCompatible

/-- DAG 自动诱导的 AVATAR selector valuation。 -/
def avatarSelectorValuation {σ : Signature} [DecidableEq σ.SortSymbol]
    {M : SetLevel.StructureAt.{x} σ} (dag : DAG σ) (base : SetLevel.EnvAt.{x} M) :
    PropResolution.Valuation :=
  AvatarSelectorComponent.valuation base dag.avatarSelectorRegistry

/-- 指定 split 中的 entry 一定属于整图 registry。 -/
theorem mem_avatarSelectorRegistry_of_split {σ : Signature}
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
  exact
    ⟨splitNode, hNodeMem,
      by
        simpa [Payload.avatarSelectorComponents, hPayload] using hEntry⟩

/-- 整图检查解包出指定 split 的局部 registry 检查。 -/
theorem avatarSplitRegistryCheck_of_eq_true {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hCheck : dag.avatarRegistryCheck = true)
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    (hNode : dag.node? splitId = some splitNode)
    (hPayload : splitNode.payload = .avatarSplit payload) :
    payload.registryCheck = true := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hNodes, _hCompatible⟩
  rcases getElem?_eq_some_iff.mp hNode with ⟨hIndex, hGet⟩
  have hAt := Array.all_eq_true.mp hNodes splitId hIndex
  simpa [hGet, hPayload, nodeAvatarRegistryLocalCheck,
    Payload.avatarRegistryLocalCheck] using hAt

/-- 整图检查解包出任意 split 的局部分解合同。 -/
theorem avatarSplitRegistryContract {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hCheck : dag.avatarRegistryCheck = true)
    {splitId : Nat} {splitNode : Node σ}
    {payload : AvatarSplitPayload σ}
    (hNode : dag.node? splitId = some splitNode)
    (hPayload : splitNode.payload = .avatarSplit payload) :
    AvatarSplitPayload.RegistryContract payload :=
  AvatarSplitPayload.registryCheck_sound
    (avatarSplitRegistryCheck_of_eq_true hCheck hNode hPayload)

/-- 整图检查保证 registry 中所有 selector 都是正文字。 -/
theorem avatarSelectorRegistry_positive {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hCheck : dag.avatarRegistryCheck = true) :
    ∀ entry, entry ∈ dag.avatarSelectorRegistry →
      entry.selector.positive = true := by
  intro entry hEntry
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hNodes, _hCompatible⟩
  rcases List.mem_flatMap.mp hEntry with
    ⟨node, hNodeMem, hPayloadEntry⟩
  have hNodeLocal : node.payload.avatarRegistryLocalCheck = true := by
    have hArray : node ∈ dag.nodes := Array.mem_def.mpr hNodeMem
    rcases Array.mem_iff_getElem.mp hArray with
      ⟨index, hIndex, hGet⟩
    have hAt := Array.all_eq_true.mp hNodes index hIndex
    simpa [hGet, nodeAvatarRegistryLocalCheck] using hAt
  cases hPayload : node.payload with
  | avatarSplit payload =>
      have hLocal : payload.registryCheck = true := by
        simpa [Payload.avatarRegistryLocalCheck, hPayload] using hNodeLocal
      have hEntryLocal : entry ∈ payload.selectorComponents := by
        simpa [Payload.avatarSelectorComponents, hPayload] using hPayloadEntry
      exact
        AvatarSplitPayload.RegistryContract.selectorComponentsPositive
          (AvatarSplitPayload.registryCheck_sound hLocal) entry hEntryLocal
  | source _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | avatarComponent _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | localRule _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | theoryConflict _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | propositionalLearnedClause _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry
  | residualCdcl _ =>
      simp [Payload.avatarSelectorComponents, hPayload] at hPayloadEntry

/-- 整图检查保证全局 selector/component registry 一致。 -/
theorem avatarSelectorRegistry_compatible {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] {dag : DAG σ}
    (hCheck : dag.avatarRegistryCheck = true) :
    AvatarSelectorComponent.Compatible dag.avatarSelectorRegistry :=
  AvatarSelectorComponent.compatibleCheck_sound
    (Bool.and_eq_true_iff.mp hCheck).2

end DAG

/-- 同时通过通用 DAG checker 与 AVATAR 全局 registry checker 的证书。 -/
structure CheckedAvatarDAG {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] where
  checked : CheckedDAG (σ := σ)
  registryChecked : checked.dag.avatarRegistryCheck = true

namespace CheckedAvatarDAG

/-- 从通用 checked DAG 继续运行 AVATAR registry checker。 -/
def mk? {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (checked : CheckedDAG (σ := σ)) :
    Option (CheckedAvatarDAG (σ := σ)) :=
  if h : checked.dag.avatarRegistryCheck = true then
    some { checked := checked, registryChecked := h }
  else
    none

/-- checked AVATAR DAG 自动诱导的 selector valuation。 -/
def selectorValuation {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedAvatarDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) :
    PropResolution.Valuation :=
  cert.checked.dag.avatarSelectorValuation base

/-- checked registry 自动给出 AVATAR component selector 的全局语义合同。 -/
theorem componentSelectorSemantics {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) :
    AvatarComponentSelectorSemantics cert.checked.dag base
      (cert.selectorValuation base) := by
  intro splitId splitNode splitPayload componentIndex indices selector
    hNode hPayload hIndices hSelector
  let entry : AvatarSelectorComponent σ :=
    ⟨selector, Clause.atIndices splitPayload.source.clause indices⟩
  have hEntryLocal : entry ∈ splitPayload.selectorComponents := by
    exact AvatarSplitPayload.selectorComponent_mem hIndices hSelector
  have hEntryGlobal :
      entry ∈ cert.checked.dag.avatarSelectorRegistry :=
    DAG.mem_avatarSelectorRegistry_of_split
      hNode hPayload hEntryLocal
  exact
    AvatarSelectorComponent.holds_valuation_iff_component_valid
      base cert.checked.dag.avatarSelectorRegistry
      (DAG.avatarSelectorRegistry_positive cert.registryChecked)
      (DAG.avatarSelectorRegistry_compatible cert.registryChecked)
      hEntryGlobal

/-- checked registry 自动给出 AVATAR split skeleton 的全局语义合同。 -/
theorem splitSelectorSemantics {σ : Signature}
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (cert : CheckedAvatarDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M) :
    AvatarSplitSelectorSemantics cert.checked.dag base
      (cert.selectorValuation base) := by
  intro splitId splitNode splitPayload hNode hPayload
  have hContract :=
    DAG.avatarSplitRegistryContract cert.registryChecked hNode hPayload
  have hSubset :
      ∀ entry, entry ∈ splitPayload.selectorComponents →
        entry ∈ cert.checked.dag.avatarSelectorRegistry := by
    intro entry hEntry
    exact DAG.mem_avatarSelectorRegistry_of_split
      hNode hPayload hEntry
  have hRaw :=
    AvatarSplitPayload.source_valid_iff_selectors_satisfy_in_registry
      base splitPayload hContract
      cert.checked.dag.avatarSelectorRegistry
      (DAG.avatarSelectorRegistry_positive cert.registryChecked)
      (DAG.avatarSelectorRegistry_compatible cert.registryChecked)
      hSubset
  exact hRaw.trans
    (PropResolution.Clause.satisfies_canonicalClause_iff
      (cert.selectorValuation base) splitPayload.selectors).symm

/--
AVATAR root contradiction 的自动 registry 版本。

调用者只需给出对象层 ClauseProblem.Valid 与 soundness-supported 检查；selector valuation
和 component/split 语义合同都由 checked registry 自动生成。
-/
theorem rootEmptyContradiction_of_avatarSoundnessSupported
    {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedAvatarDAG (σ := σ))
    {M : SetLevel.StructureAt.{x} σ} (base : SetLevel.EnvAt.{x} M)
    (hProblem : cert.checked.dag.problem.Valid base)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true) :
    False :=
  cert.checked.rootEmptyContradiction_of_avatarSoundnessSupported
    base (cert.selectorValuation base) hProblem
    (cert.componentSelectorSemantics base)
    (cert.splitSelectorSemantics base) hSupported

/--
显式 validity bridge 驱动的 AVATAR universe-polymorphic 语义结论。

该接口供整问题预处理主线消费：反模型经 preprocessing bridge 扩张为 DAG clause
problem 的模型后，checked AVATAR root 自动导出矛盾。
-/
theorem semanticallyEntails_of_avatarSoundnessSupported_of_valid
    {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedAvatarDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true)
    (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.checked.dag.problem.Valid targetEnv) :
    SetLevel.SemanticallyEntailsAt.{x} problem.theory problem.target := by
  intro M env hModels
  by_cases hTarget :
      Logic.FirstOrder.Formula.satisfies env problem.target
  · exact hTarget
  · rcases hValid env hModels hTarget with
      ⟨target, targetEnv, hClauseProblem⟩
    exact False.elim
      (cert.rootEmptyContradiction_of_avatarSoundnessSupported
        targetEnv hClauseProblem hSupported)

/-- checked AVATAR DAG 经 validity bridge 物化为同 universe 语义证书。 -/
def semanticCertificate_of_avatarSoundnessSupported_of_valid
    {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedAvatarDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true)
    (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.checked.dag.problem.Valid targetEnv) :
    SetLevel.SemanticCertificateAt.{x} problem.theory problem.target where
  entails :=
    cert.semanticallyEntails_of_avatarSoundnessSupported_of_valid
      problem hSupported hValid

/-- checked AVATAR DAG 接入 universe-polymorphic 后端成功协议。 -/
def backendSuccess_of_avatarSoundnessSupported_of_valid
    {σ : Signature} [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (cert : CheckedAvatarDAG (σ := σ)) (problem : DeepProblem σ)
    (hSupported : cert.checked.dag.avatarSoundnessSupported = true)
    (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.checked.dag.problem.Valid targetEnv) :
    SetLevel.BackendSuccessAt.{x} problem where
  backend := .dagReflection
  phase := .dagCheck
  cert :=
    cert.semanticCertificate_of_avatarSoundnessSupported_of_valid
      problem hSupported hValid
  audit? := some cert.checked.toComposite
  note := "DAG AVATAR soundness-supported fragment via checked preprocessing"

end CheckedAvatarDAG

end DAGCertificate
end Automation
end YesMetaZFC
