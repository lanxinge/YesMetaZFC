import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralProof
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralParameters
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedDerivability

/-! # 已证定理的非标准数码实例

标准定理先经 D1 得到内部证明，再以实际全称特化公理实例化任意内部数码。
这是反射归纳的推导工具，不从任意公式真值断言其可证明性。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralProof
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceInstantiation PureSourceFormulaConstruction
open ReducedProofLocalConstruction ReducedProofCodeSemantics ReducedProofLogicalConstruction
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem of_derives (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) {sentence : SetSentence}
    (h : Derives intrinsic_zfc_theory [] sentence) :
    ∃ proof, mem 𝒩 proof (w 𝒩) ∧ CodeProof 𝒩 proof
      ((IntrinsicQuotation.quote sentence).eval (Env.empty : Env 𝒩 [] [])) := by
  obtain ⟨proof, hp, hProof⟩ := (ReducedProvability.provable_satisfies sentence).mp
    ((ReducedProvability.necessitation h).semantically_entails 𝒩 h𝒩)
  exact ⟨proof, hp, (codeProof_quotation _ _).mpr hProof⟩

/-- 尾部参数已经实例化时，仍可用原全称特化公理代入顶部数码。 -/
theorem forall_elimination (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (body : SetOpenFormula (.set :: free))
    {values : Nat → 𝒩.Carrier .set} (hValues : NumeralValues 𝒩 values)
    {input named : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (hProof : ProvableCode 𝒩 (formula 𝒩 values (body.forallFreeTop SetSort.set))) :
    ProvableCode 𝒩 (formula 𝒩 (ObjectCodeInstantiation.prepend named values) body) := by
  have hTarget := numeralValues_prepend hValues hi hn hg
  have hBody := formula_natural h𝒩 (numeralValues_natural hValues) body.abstractFreeTop
  have hInstance := formula_natural h𝒩 (numeralValues_natural hTarget) body
  have hAxiom := forall_axiom h𝒩 hBody hn hInstance
    ((syntax_satisfies _).mpr (numeral_wellFormed h𝒩 hValues body.abstractFreeTop))
    ((syntax_satisfies _).mpr (PureSourceNumeralSyntax.graph_closedTerm h𝒩 hi hn hg))
    (numeral_point h𝒩 body hValues hn)
  obtain ⟨proof, hp, hProof⟩ := hProof
  exact ⟨_, ReducedProofComposition.modus_ponens_code h𝒩
    (formula_natural h𝒩 (numeralValues_natural hValues) (body.forallFreeTop SetSort.set)) hInstance
    ((syntax_satisfies _).mpr (numeral_wellFormed h𝒩 hValues (body.forallFreeTop SetSort.set)))
    ((syntax_satisfies _).mpr (numeral_wellFormed h𝒩 hTarget body)) hp hAxiom.1 hProof hAxiom.2⟩

/-- 任意有限参数数目的源定理均可同时特化到不同的内部数码。 -/
theorem specialize_values (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (body : SetOpenFormula free) (hDerives : Derives intrinsic_zfc_theory [] body)
    {values : Nat → 𝒩.Carrier .set} (hValues : NumeralValues 𝒩 values) :
    ProvableCode 𝒩 (formula 𝒩 values body) := by
  induction free generalizing values with
  | nil =>
    have h := of_derives h𝒩 hDerives
    rw [← original_quote] at h
    have hCode := ObjectCodeInstantiation.formula_values_congr (node 𝒩) values (originalValues 𝒩) body
      (by intro i hi; cases hi)
    simpa only [PureSourceInstantiation.formula, hCode] using! h
  | cons sort free ih =>
    cases sort
    have hTail : NumeralValues 𝒩 (fun i => values (i + 1)) := fun i => hValues (i + 1)
    have hUniversal := ih (body.forallFreeTop SetSort.set) (Derives.forall_intro hDerives) hTail
    obtain ⟨input, hi, hg⟩ := (hValues 0).2
    have h := forall_elimination h𝒩 body hTail hi (hValues 0).1 hg hUniversal
    rw [ObjectCodeInstantiation.prepend_eta] at h
    exact h

/-- 调用者只须提供实际自由上下文中的槽位证书，无须约束其他位置。 -/
theorem specialize_finite (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (body : SetOpenFormula free) (hDerives : Derives intrinsic_zfc_theory [] body)
    {values : Nat → 𝒩.Carrier .set}
    (hValues : ∀ i, i < free.length → mem 𝒩 (values i) (w 𝒩) ∧
      ∃ input, mem 𝒩 input (w 𝒩) ∧ PureSourceNumeralSyntax.Graph 𝒩 input (values i)) :
    ProvableCode 𝒩 (formula 𝒩 values body) := by
  let extended i := if i < free.length then values i else numeral 𝒩 ObjectNumeralSyntax.zeroCode
  have hExtended : NumeralValues 𝒩 extended := by
    intro i
    by_cases hi : i < free.length
    · simpa only [extended, if_pos hi] using! hValues i hi
    · simpa only [extended, if_neg hi] using!
        And.intro (numeral_natural h𝒩 ObjectNumeralSyntax.zeroCode)
          ⟨z 𝒩, (omega_closed h𝒩).1, PureSourceNumeralSyntax.zero h𝒩⟩
  have h := specialize_values h𝒩 body hDerives hExtended
  have hCode := ObjectCodeInstantiation.formula_values_congr (node 𝒩) extended values body
    (by intro i hi; simp only [extended, if_pos hi])
  simpa only [PureSourceInstantiation.formula, hCode] using! h

/-- 单参数入口是统一有限参数特化的特例。 -/
theorem specialize (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (body : SetOpenFormula [.set]) (hDerives : Derives intrinsic_zfc_theory [] body)
    {input named : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named) :
    ∃ proof, mem 𝒩 proof (w 𝒩) ∧ CodeProof 𝒩 proof (formula 𝒩 (fun _ => named) body) :=
  specialize_values h𝒩 body hDerives (fun _ => ⟨hNamed, input, hInput, hGraph⟩)

/-- 任意有限参数环境下的内部 MP。 -/
theorem values_modus_ponens (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (left right : SetOpenFormula free)
    {values : Nat → 𝒩.Carrier .set} (hValues : NumeralValues 𝒩 values)
    (hLeft : ProvableCode 𝒩 (formula 𝒩 values left))
    (hImp : ProvableCode 𝒩 (formula 𝒩 values (.imp left right))) :
    ProvableCode 𝒩 (formula 𝒩 values right) := by
  obtain ⟨premise, hp, hPremise⟩ := hLeft
  obtain ⟨implication, hi, hImplication⟩ := hImp
  exact ⟨_, ReducedProofComposition.modus_ponens_code h𝒩
    (formula_natural h𝒩 (numeralValues_natural hValues) left) (formula_natural h𝒩 (numeralValues_natural hValues) right)
    ((syntax_satisfies _).mpr (numeral_wellFormed h𝒩 hValues left))
    ((syntax_satisfies _).mpr (numeral_wellFormed h𝒩 hValues right)) hp hi hPremise hImplication⟩

/-- 固定骨架实例的 MP；语法义务由数码图统一消去。 -/
theorem instance_modus_ponens (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (left right : SetOpenFormula [.set]) {input named : 𝒩.Carrier .set}
    (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (hLeft : ProvableCode 𝒩 (formula 𝒩 (fun _ => named) left))
    (hImp : ProvableCode 𝒩 (formula 𝒩 (fun _ => named) (.imp left right))) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) right) :=
  values_modus_ponens h𝒩 left right (fun _ => ⟨hNamed, input, hInput, hGraph⟩) hLeft hImp

/-- 以源逻辑定理装配两个数码实例的合取。 -/
theorem instance_conj_intro (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (left right : SetOpenFormula [.set]) {input named : 𝒩.Carrier .set}
    (hInput : mem 𝒩 input (w 𝒩)) (hNamed : mem 𝒩 named (w 𝒩))
    (hGraph : PureSourceNumeralSyntax.Graph 𝒩 input named)
    (hLeft : ProvableCode 𝒩 (formula 𝒩 (fun _ => named) left))
    (hRight : ProvableCode 𝒩 (formula 𝒩 (fun _ => named) right)) :
    ProvableCode 𝒩 (formula 𝒩 (fun _ => named) (.conj left right)) := by
  have hDerives : Derives intrinsic_zfc_theory [] (.imp left (.imp right (.conj left right))) :=
    Derives.imp_intro (Derives.imp_intro (Derives.conj_intro
      (Derives.assumption (by simp)) (Derives.assumption (List.mem_cons_self ..))))
  exact instance_modus_ponens h𝒩 right (.conj left right) hInput hNamed hGraph hRight
    (instance_modus_ponens h𝒩 left (.imp right (.conj left right)) hInput hNamed hGraph hLeft
      (specialize h𝒩 _ hDerives hInput hNamed hGraph))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralProof
