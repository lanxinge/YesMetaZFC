import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalBooleanReflection

/-! # 任意有限参数下的量词见证反射

数码见证经原存在公理构造存在证明；反例同样给出全称命题的否定证明。
见证取自整个内部 ω，不要求外部标准。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceFormulaConstruction
open ReducedProofCodeSemantics InternalNumeralProof ReducedProofLocalConstruction
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

/-- 已实例化的尾部参数保持不变，只引入顶部存在量词。 -/
theorem exists_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula (.set :: free)) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input named : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (hp : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) body)) :
    ProvableCode 𝒩 (formula 𝒩 values (body.existsFreeTop SetSort.set)) := by
  have he := numeralValues_prepend hv hi hn hg
  unfold ProvableCode at hp ⊢
  obtain ⟨proof, hp, hProof⟩ := hp
  exact ReducedProofLogicalConstruction.exists_introduction h𝒩
    (formula_natural h𝒩 (numeralValues_natural hv) body.abstractFreeTop) hn
    (formula_natural h𝒩 (numeralValues_natural he) body)
    ((syntax_satisfies _).mpr (numeral_wellFormed h𝒩 hv body.abstractFreeTop))
    ((syntax_satisfies _).mpr (PureSourceNumeralSyntax.graph_closedTerm h𝒩 hi hn hg))
    ((syntax_satisfies _).mpr (numeral_wellFormed h𝒩 he body))
    (numeral_point h𝒩 body hv hn) hp hProof

theorem exists_neg_forall_derives (body : SetOpenFormula (.set :: free)) :
    Derives intrinsic_zfc_theory [] (.imp ((Formula.neg body).existsFreeTop SetSort.set) (.neg (body.forallFreeTop SetSort.set))) := by
  apply source_complete
  intro 𝒩 _ env
  simp only [Formula.satisfies, Formula.satisfies_existsFreeTop, Formula.satisfies_forallFreeTop]
  intro h hn
  obtain ⟨input, hi⟩ := h
  exact hi (hn input)

theorem forall_counterexample (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula (.set :: free)) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {input named : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (hp : ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) (.neg body))) :
    ProvableCode 𝒩 (formula 𝒩 values (.neg (body.forallFreeTop SetSort.set))) :=
  reflection_rule h𝒩 values hv (exists_neg_forall_derives body) (exists_values h𝒩 (.neg body) values hv hi hn hg hp)

theorem exists_witness_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (body : SetOpenFormula (.set :: free)) {input : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩))
    (hBody : ∀ named, mem 𝒩 named (w 𝒩) → PureSourceNumeralSyntax.Graph 𝒩 input named →
      FormulaReflects (env.pushFree input) (ObjectCodeInstantiation.prepend named values) body)
    (ht : body.satisfies (env.pushFree input)) : ProvableCode 𝒩 (formula 𝒩 values (body.existsFreeTop SetSort.set)) := by
  obtain ⟨named, hn, hg⟩ := PureSourceNumeralSyntax.total h𝒩 hi
  exact exists_values h𝒩 body values hv hi hn hg ((hBody named hn hg).1 ht)

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
