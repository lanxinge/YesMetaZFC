import YesMetaZFC.Model.ZFC.Pure.PureSeparation
import YesMetaZFC.Model.ZFC.Pure.PureRelationDefinitions

/-! # 可定义单调集合算子的内部最小不动点

以所有闭合集合的共同成员定义最小闭合集合。分离给出这个集合及其一步像，
单调性再将闭合性提升为不动点方程；不使用模型外部的迭代或良基性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLeastFixedPoint
open PureModel
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ} {parameters : SortContext ℒ}

def Holds (body : Formula ℒ [] (setSort :: setSort :: parameters))
    (args : Values ℳ.Carrier parameters) (state element : Carrier ℳ) : Prop :=
  body.satisfies (templateEnv (.cons element (.cons state args)))

def Closed (body : Formula ℒ [] (setSort :: setSort :: parameters))
    (args : Values ℳ.Carrier parameters) (state : Carrier ℳ) : Prop :=
  ∀ element, Holds body args state element → membership ℳ element state

def closed (body : Formula ℒ [] (setSort :: setSort :: parameters)) :
    Formula ℒ [] (setSort :: parameters) :=
  (Formula.imp body (PureRelationDefinitions.mem (.fvar .here) (.fvar (.there .here)))).forallFreeTop setSort

private def skipElement : VariableRenaming (setSort :: parameters) (setSort :: setSort :: parameters) :=
  fun entry => match entry with
  | .here => .here
  | .there previous => .there (.there previous)

def member (body : Formula ℒ [] (setSort :: setSort :: parameters)) :
    Formula ℒ [] (setSort :: parameters) :=
  (Formula.imp ((closed body).renameFree skipElement)
    (PureRelationDefinitions.mem (.fvar (.there .here)) (.fvar .here))).forallFreeTop setSort

def graph (body : Formula ℒ [] (setSort :: setSort :: parameters)) :
    Formula ℒ [] (setSort :: parameters) := PureFunctionDefinitions.comprehension (member body)

theorem closed_correct (body : Formula ℒ [] (setSort :: setSort :: parameters))
    (args : Values ℳ.Carrier parameters) (state : Carrier ℳ) :
    (closed body).satisfies (templateEnv (.cons state args)) ↔ Closed body args state := by
  simp only [closed,Formula.satisfies_forallFreeTop,Formula.satisfies]
  apply forall_congr'
  intro element
  have hEnv : (templateEnv (.cons state args)).pushFree element = templateEnv (.cons element (.cons state args)) := by
    apply Env.ext
    · intro sort entry; cases entry
    · intro sort entry; cases entry <;> rfl
  rw [hEnv]
  rfl

theorem member_correct (body : Formula ℒ [] (setSort :: setSort :: parameters))
    (args : Values ℳ.Carrier parameters) (element : Carrier ℳ) :
    (member body).satisfies (templateEnv (.cons element args)) ↔
      ∀ state, Closed body args state → membership ℳ element state := by
  simp only [member,Formula.satisfies_forallFreeTop,Formula.satisfies]
  apply forall_congr'
  intro state
  have hRename := Formula.satisfies_rename ((templateEnv (.cons element args)).pushFree state)
    (Renaming.free skipElement) (closed body)
  have hEnv : ((templateEnv (.cons element args)).pushFree state).pullbackRenaming (Renaming.free skipElement) =
      templateEnv (.cons state args) := by
    apply Env.ext
    · intro sort entry; cases entry
    · intro sort entry; cases entry <;> rfl
  rw [hEnv] at hRename
  exact imp_congr (hRename.trans (closed_correct body args state)) Iff.rfl

theorem functional (hℳ : Theory.Models ℳ theory)
    (body : Formula ℒ [] (setSort :: setSort :: parameters)) (args : Values ℳ.Carrier parameters)
    (ambient : Carrier ℳ) (hBound : ∀ state element, Holds body args state element → membership ℳ element ambient) :
    ∃ output, (graph body).satisfies (templateEnv (.cons output args)) ∧
      ∀ other, (graph body).satisfies (templateEnv (.cons other args)) → other = output := by
  apply PureSeparation.bounded_functional hℳ (member body) args ambient
  intro element hElement
  exact (member_correct body args element).mp hElement ambient (hBound ambient)

/-- 最小闭合集合满足一步生成方程，且包含于每一个闭合集合。 -/
theorem fixed (hℳ : Theory.Models ℳ theory)
    (body : Formula ℒ [] (setSort :: setSort :: parameters)) (args : Values ℳ.Carrier parameters)
    (ambient : Carrier ℳ) (hBound : ∀ state element, Holds body args state element → membership ℳ element ambient)
    (hMono : ∀ first second, (∀ element, membership ℳ element first → membership ℳ element second) →
      ∀ element, Holds body args first element → Holds body args second element)
    {output : Carrier ℳ} (hOutput : (graph body).satisfies (templateEnv (.cons output args))) :
    (∀ element, membership ℳ element output ↔ Holds body args output element) ∧ Closed body args output := by
  have hMember (element : Carrier ℳ) :=
    ((PureFunctionDefinitions.comprehension_correct (member body) args output).mp hOutput element).trans
      (member_correct body args element)
  have hLeast (state : Carrier ℳ) (hState : Closed body args state) :
      ∀ element, membership ℳ element output → membership ℳ element state :=
    fun element hElement => (hMember element).mp hElement state hState
  have hClosed : Closed body args output := by
    intro element hElement
    apply (hMember element).mpr
    intro state hState
    exact hState element (hMono output state (hLeast state hState) element hElement)
  obtain ⟨step,hStep⟩ := PureSeparation.exists_subset hℳ body (.cons output args) ambient
  have hStepMember (element : Carrier ℳ) : membership ℳ element step ↔ Holds body args output element :=
    (hStep element).trans ⟨And.right,fun h => ⟨hBound output element h,h⟩⟩
  have hStepSubset : ∀ element, membership ℳ element step → membership ℳ element output :=
    fun element hElement => hClosed element ((hStepMember element).mp hElement)
  have hStepClosed : Closed body args step :=
    fun element hElement => (hStepMember element).mpr (hMono step output hStepSubset element hElement)
  exact ⟨fun element => ⟨fun hElement => (hStepMember element).mp (hLeast step hStepClosed element hElement),hClosed element⟩,hClosed⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureLeastFixedPoint
