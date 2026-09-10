import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceBounds
import YesMetaZFC.Automation.ObjectTraceComposition

/-! # 任意源模型中的轨迹集合构造

用配对与并集公理合并内部轨迹，再证明幂集界和规则闭包。
整个构造保留模型内部集合，不将轨迹转换为宿主列表。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceTraceComposition
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceBounds
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ObjectTrace
set_option autoImplicit false
attribute [local implicit_reducible] PureProjectEmbedding.reduct _root_.YesMetaZFC.SetTheory.signature
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def Witness (step : FormulaTemplate.Binary) (root : 𝒩.Carrier .set) : Prop :=
  ∃ trace, mem 𝒩 trace (powerset 𝒩 (w 𝒩)) ∧ mem 𝒩 root trace ∧ Closed step trace

/-- 相同根值的轨迹对应只依赖自然数行上的局部对应。 -/
theorem witness_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (step : FormulaTemplate.Binary) (root : 𝒩.Carrier .set)
    (hStep : ∀ row, mem 𝒩 row (w 𝒩) → ∀ trace,
      step.body.satisfies (templateEnv (.cons row (.cons trace .nil)) : Env 𝒩 [] [.set,.set]) ↔
      step.body.satisfies (templateEnv (.cons row (.cons trace .nil)) :
        Env (PureSourceNumerals.canonical h𝒩) [] [.set,.set])) :
    Witness step root ↔ @Witness (PureSourceNumerals.canonical h𝒩) step root := by
  have h := trace_agrees h𝒩 step
    (templateEnv (.cons root .nil) : Env 𝒩 [] [.set])
    (templateEnv (.cons root .nil) : Env (PureSourceNumerals.canonical h𝒩) [] [.set])
    (.fvar .here) rfl (fun trace _ row _ hRow => hStep row hRow trace)
  simpa only [condition_satisfies] using! h

theorem union_exists (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (left right : 𝒩.Carrier .set) :
    ∃ joined, ∀ row, mem 𝒩 row joined ↔ mem 𝒩 row left ∨ mem 𝒩 row right := by
  obtain ⟨family, hFamily⟩ := PureModel.pair (PureZFCModels.reduct_models h𝒩) left right
  obtain ⟨joined, hJoined⟩ := PureModel.union (PureZFCModels.reduct_models h𝒩) family
  change ∀ element, mem 𝒩 element joined ↔ ∃ member, mem 𝒩 member family ∧ mem 𝒩 element member at hJoined
  refine ⟨joined, fun row => ?_⟩
  change mem 𝒩 row joined ↔ _
  rw [hJoined]
  constructor
  · rintro ⟨member, hMember, hRow⟩
    rcases (hFamily member).mp hMember with rfl | rfl
    · exact Or.inl hRow
    · exact Or.inr hRow
  · intro h
    rcases h with h | h
    · exact ⟨left, (hFamily left).mpr (Or.inl rfl), h⟩
    · exact ⟨right, (hFamily right).mpr (Or.inr rfl), h⟩

theorem insert_exists (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (row trace : 𝒩.Carrier .set) :
    ∃ extended, ∀ point, mem 𝒩 point extended ↔ point = row ∨ mem 𝒩 point trace := by
  obtain ⟨singleton, hSingleton⟩ := PureModel.pair (PureZFCModels.reduct_models h𝒩) row row
  change ∀ element, mem 𝒩 element singleton ↔ element = row ∨ element = row at hSingleton
  obtain ⟨extended, hExtended⟩ := union_exists h𝒩 singleton trace
  refine ⟨extended, fun point => ?_⟩
  rw [hExtended, hSingleton]
  exact ⟨fun h => h.elim (fun h => Or.inl (h.elim id id)) Or.inr,
    fun h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr⟩

/-- 合并两份有界闭轨迹，并保留两侧所有行。 -/
theorem merge (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (step : FormulaTemplate.Binary) (hMono : Monotone (𝒩 := 𝒩) step)
    {left right : 𝒩.Carrier .set}
    (hLeftBound : mem 𝒩 left (powerset 𝒩 (w 𝒩)))
    (hRightBound : mem 𝒩 right (powerset 𝒩 (w 𝒩)))
    (hLeft : Closed step left) (hRight : Closed step right) :
    ∃ joined, mem 𝒩 joined (powerset 𝒩 (w 𝒩)) ∧
      Included left joined ∧ Included right joined ∧ Closed step joined := by
  obtain ⟨joined, hJoined⟩ := union_exists h𝒩 left right
  refine ⟨joined, (power_spec h𝒩 _ _).mpr ?_,
    (fun row h => (hJoined row).mpr (Or.inl h)),
    (fun row h => (hJoined row).mpr (Or.inr h)),
    closed_union step hMono hJoined hLeft hRight⟩
  intro row hRow
  exact ((hJoined row).mp hRow).elim
    (trace_row_natural h𝒩 hLeftBound) (trace_row_natural h𝒩 hRightBound)

/-- 插入一行，保留自然数界、原轨迹和全部局部检查。 -/
theorem insert (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (step : FormulaTemplate.Binary) (hMono : Monotone (𝒩 := 𝒩) step)
    {trace row : 𝒩.Carrier .set}
    (hTraceBound : mem 𝒩 trace (powerset 𝒩 (w 𝒩)))
    (hNatural : mem 𝒩 row (w 𝒩)) (hClosed : Closed step trace)
    (hRow : step.body.satisfies (templateEnv (.cons row (.cons trace .nil)))) :
    ∃ extended, mem 𝒩 extended (powerset 𝒩 (w 𝒩)) ∧
      Included trace extended ∧ mem 𝒩 row extended ∧ Closed step extended := by
  obtain ⟨extended, hExtended⟩ := insert_exists h𝒩 row trace
  refine ⟨extended, (power_spec h𝒩 _ _).mpr ?_,
    (fun point h => (hExtended point).mpr (Or.inr h)),
    (hExtended row).mpr (Or.inl rfl), closed_insert step hMono hExtended hClosed hRow⟩
  intro point hp
  rcases (hExtended point).mp hp with rfl | h
  · exact hNatural
  · exact trace_row_natural h𝒩 hTraceBound h

/-- 收集固定语法参数列的轨迹；每份轨迹自身可以外部非有限。 -/
theorem collect (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (step : FormulaTemplate.Binary) (hMono : Monotone (𝒩 := 𝒩) step)
    (roots : List (𝒩.Carrier .set)) (hRoots : ∀ root ∈ roots, Witness step root) :
    ∃ trace, mem 𝒩 trace (powerset 𝒩 (w 𝒩)) ∧
      (∀ root ∈ roots, mem 𝒩 root trace) ∧ Closed step trace := by
  induction roots with
  | nil =>
    refine ⟨z 𝒩, (power_spec h𝒩 _ _).mpr ?_, ?_, ?_⟩
    · intro point hp
      exact False.elim (PureSourceNumerals.empty_spec h𝒩 point hp)
    · intro point hp
      cases hp
    · intro point hp
      exact False.elim (PureSourceNumerals.empty_spec h𝒩 point hp)
  | cons root roots ih =>
    obtain ⟨left, hLeft, hRoot, hClosed⟩ := hRoots root List.mem_cons_self
    obtain ⟨right, hRight, hRootsMem, hRightClosed⟩ := ih
      (fun point hp => hRoots point (List.mem_cons_of_mem root hp))
    obtain ⟨joined, hBound, hLeftSub, hRightSub, hJoined⟩ :=
      merge h𝒩 step hMono hLeft hRight hClosed hRightClosed
    refine ⟨joined, hBound, ?_, hJoined⟩
    intro point hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hLeftSub _ hRoot
    · exact hRightSub _ (hRootsMem point hp)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceTraceComposition
