import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureQuotation
import YesMetaZFC.Automation.ObjectHornSemantics

/-! # 纯数码公式在任意原 ZFC 模型中的唯一求值

只对外部有限数码归纳；内部对象域、自然数和参数赋值均不作标准性假设。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureQuotation
open Nonlogical.BasicSetTheory PureOpenTransfer
open _root_.YesMetaZFC.Automation
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature RelationalTranslation.Expansion.model
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

noncomputable def number_m (hℳ : Theory.Models ℳ PureModel.theory) (n : Nat) : PureModel.Carrier ℳ :=
  (numₘ(n) : SetTerm [] []).eval (Env.empty : Env (PureCompletedStage.expansion hℳ).model [] [])

theorem numeral_satisfies_m (hℳ : Theory.Models ℳ PureModel.theory)
    {bound free : SetContext} (n : Nat)
    (env : Env ℳ (pureContext_m (SetSort.set :: bound)) (pureContext_m free)) :
    (numeral_m (bound := bound) (free := free) n).satisfies env ↔
      env.boundVal .here = number_m hℳ n := by
  induction n generalizing bound with
  | zero =>
    exact (PureFinalBasic.empty_value hℳ (env.boundVal .here)).symm
  | succ n ih =>
    change (∃ y, (numeral_m (bound := SetSort.set :: bound) (free := free) n).satisfies (env.pushBound y) ∧
      ∀ z, PureModel.membership ℳ z (env.boundVal .here) ↔
        PureModel.membership ℳ z y ∨ z = y) ↔ _
    constructor
    · rintro ⟨y, hy, hs⟩
      have he : y = number_m hℳ n := (ih (env.pushBound y)).mp hy
      subst y
      apply PureModel.extensionality hℳ
      intro z
      exact (hs z).trans (PureFinalBasic.successor_value hℳ (number_m hℳ n) z).symm
    · intro h
      refine ⟨number_m hℳ n, (ih _).mpr rfl, ?_⟩
      rw [h]
      exact PureFinalBasic.successor_value hℳ (number_m hℳ n)

theorem specialize_satisfies_m (hℳ : Theory.Models ℳ PureModel.theory) {free : SetContext}
    (env : Env ℳ [] (pureContext_m free))
    (body : Formula ℒ (pureContext_m [SetSort.set]) (pureContext_m free)) (n : Nat) :
    (specialize_m body n).satisfies env ↔ body.satisfies (env.pushBound (number_m hℳ n)) := by
  change (∃ a, (numeral_m (bound := []) (free := free) n).satisfies (env.pushBound a) ∧
    body.satisfies (env.pushBound a)) ↔ _
  constructor
  · rintro ⟨a, ha, hb⟩
    have he : a = number_m hℳ n :=
      (numeral_satisfies_m hℳ (bound := []) (free := free) n (env.pushBound a)).mp ha
    simpa only [he] using hb
  · intro hb
    exact ⟨number_m hℳ n,
      (numeral_satisfies_m hℳ (bound := []) (free := free) n (env.pushBound _)).mpr rfl, hb⟩

/-- 纯候选在一个标准编码处的纯公式实例；任意尾部参数不变。 -/
def instance_m {free : SetContext}
    (P : OpenFormula ℒ (pureContext_m (SetSort.set :: free))) (n : Nat) :
    OpenFormula ℒ (pureContext_m free) := specialize_m P.abstractFreeTop n

theorem instance_satisfies_m (hℳ : Theory.Models ℳ PureModel.theory) {free : SetContext}
    (env : Env ℳ [] (pureContext_m free))
    (P : OpenFormula ℒ (pureContext_m (SetSort.set :: free))) (n : Nat) :
    (instance_m P n).satisfies env ↔ P.satisfies (env.pushFree (number_m hℳ n)) :=
  (specialize_satisfies_m hℳ env P.abstractFreeTop n).trans
    (Formula.satisfies_abstractFreeTop env (number_m hℳ n) P)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureQuotation
