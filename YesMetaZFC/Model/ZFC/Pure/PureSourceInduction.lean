import YesMetaZFC.Model.ZFC.Pure.PureSourceInfinity

/-! # 经最终纯解释传回的源模型内部归纳

性质必须由实际源公式给出，并在自然数参数上与规范重扩张逐值一致。
分离使用最终解释的纯翻译，不向原模型的任意外部谓词授予归纳。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInduction
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity
open _root_.YesMetaZFC.Automation.RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

/-- 最新公式的内部归纳；一致性前提随后由具体图的语义对应消去。 -/
theorem induction (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {parameters : SetContext} (body : SetOpenFormula (.set :: parameters))
    (args : Values 𝒩.Carrier parameters)
    (hAgreement : ∀ input, mem 𝒩 input (w 𝒩) →
      (body.satisfies (templateEnv (.cons input args) : Env 𝒩 [] (.set :: parameters)) ↔
        body.satisfies (templateEnv (.cons input args) : Env (canonical h𝒩) [] (.set :: parameters))))
    (hZero : body.satisfies (templateEnv (.cons (z 𝒩) args)))
    (hStep : ∀ input, mem 𝒩 input (w 𝒩) →
      body.satisfies (templateEnv (.cons input args)) →
        body.satisfies (templateEnv (.cons (suc 𝒩 input) args))) :
    ∀ input, mem 𝒩 input (w 𝒩) → body.satisfies (templateEnv (.cons input args)) := by
  let hPure := PureZFCModels.reduct_models h𝒩
  have hOmega : w 𝒩 = PureNaturalInduction.omega hPure :=
    (omega_agrees h𝒩).trans (omega_final hPure)
  have hEmpty : z 𝒩 = PureNaturalInduction.zero hPure :=
    (empty_agrees h𝒩).trans (zero_final hPure)
  have hSucc (input : 𝒩.Carrier .set) :
      suc 𝒩 input = PureNaturalInduction.succ hPure input :=
    (successor_agrees h𝒩 input).trans (succ_final hPure input)
  have hCorrect (input : 𝒩.Carrier .set) := openFormula_correct
    (PureCompletedStage.expansion hPure) (PureCompletedStage.realizes hPure) body (.cons input args)
  have hBase := (hCorrect _).mpr ((hAgreement _ (omega_closed h𝒩).1).mp hZero)
  rw [hEmpty] at hBase
  have hInduction := PureNaturalInduction.pure_induction hPure
    (openFormula PureCompletedStage.interpretation body)
    (mapValues PureCompletedStage.interpretation args) hBase (by
      intro input hInput hProperty
      have hNatural : mem 𝒩 input (w 𝒩) := hOmega.symm ▸ hInput
      have hNext := hStep input hNatural ((hAgreement input hNatural).mpr ((hCorrect input).mp hProperty))
      have hNextPure := (hCorrect _).mpr
        ((hAgreement _ ((omega_closed h𝒩).2 input hNatural)).mp hNext)
      rw [hSucc] at hNextPure
      exact hNextPure)
  intro input hInput
  exact (hAgreement input hInput).mpr ((hCorrect input).mp (hInduction input (hOmega ▸ hInput)))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInduction
