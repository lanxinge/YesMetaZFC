import YesMetaZFC.SetTheory.FunctionConstruction
import YesMetaZFC.SetTheory.ProductConstruction
import YesMetaZFC.SetTheory.Separation

/-!
# 函数集的模型内部构造

先构造 `source × target`，再从其幂集中分离出定义域恰为 `source` 且值落入 `target`
的单值关系。由此得到的集合恰好是全部模型内部函数图。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/--
沿定义域双射和值域双射输送一个函数图。

`domainMap` 正向从源定义域映到目标定义域，`baseMap` 正向从源值域映到目标值域。
-/
def IsFunctionTransport {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (domainMap baseMap targetDomain targetBase input output : ℳ.Domain) :
    Prop :=
  ℳ.IsSetFunctionFromTo 𝕀 output targetDomain targetBase ∧
    ∀ targetInput targetOutput,
      ℳ.PairMember 𝕀 targetInput targetOutput output ↔
        ℳ.mem targetInput targetDomain ∧
          ∃ sourceInput sourceOutput,
            ℳ.PairMember 𝕀 sourceInput targetInput domainMap ∧
              ℳ.PairMember 𝕀 sourceInput sourceOutput input ∧
                ℳ.PairMember 𝕀 sourceOutput targetOutput baseMap

/--
沿定义域单射扩张函数，并在单射像之外取固定默认值。
-/
def IsFunctionExtension {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (domainMap baseMap defaultValue targetDomain targetBase
      input output : ℳ.Domain) : Prop :=
  ℳ.IsSetFunctionFromTo 𝕀 output targetDomain targetBase ∧
    ∀ targetInput targetOutput,
      ℳ.PairMember 𝕀 targetInput targetOutput output ↔
        ℳ.mem targetInput targetDomain ∧
          ((∃ sourceInput sourceOutput,
              ℳ.PairMember 𝕀 sourceInput targetInput domainMap ∧
                ℳ.PairMember 𝕀 sourceInput sourceOutput input ∧
                  ℳ.PairMember 𝕀 sourceOutput targetOutput baseMap) ∨
            ((¬ ∃ sourceInput,
                ℳ.PairMember 𝕀 sourceInput targetInput domainMap) ∧
              targetOutput = defaultValue))

end Structure

namespace Definitional
namespace Project

namespace BinarySchema

/-- 给定输入函数后，输送函数在单个目标输入上的值关系。 -/
def transportedFunctionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 3 where
  body := .existsE <| .existsE <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 1) (.bound 3) (.bound 5)) <|
    .conj
      (Formula.orderedPairMem 𝒞
        (.bound 1) (.bound 0) (.bound 4))
      (Formula.orderedPairMem 𝒞
        (.bound 0) (.bound 2) (.bound 6))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

/-- 把一个函数图整体输送到目标定义域和值域。 -/
def functionTransportValue
    (𝒞 : OrderedPairConvention) : BinarySchema 4 where
  body := .conj
    (Formula.isFunctionFromTo 𝒞
      (.bound 0) (.bound 4) (.bound 5)) <|
    .forallE <| .forallE <|
      .iff
        (Formula.orderedPairMem 𝒞
          (.bound 1) (.bound 0) (.bound 2)) <|
        .conj (.mem (.bound 1) (.bound 6)) <|
          .existsE <| .existsE <|
            .conj
              (Formula.orderedPairMem 𝒞
                (.bound 1) (.bound 3) (.bound 6)) <|
            .conj
              (Formula.orderedPairMem 𝒞
                (.bound 1) (.bound 0) (.bound 5))
              (Formula.orderedPairMem 𝒞
                (.bound 0) (.bound 2) (.bound 7))
  freeClosed := by
    simp [Formula.isFunctionFromTo, Formula.isFunction,
      Formula.isRelation, Formula.isDomain,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]

/-- 定义域单射扩张后的单点值关系。 -/
def extendedFunctionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 4 where
  body := .disj
    (.existsE <| .existsE <|
      .conj
        (Formula.orderedPairMem 𝒞
          (.bound 1) (.bound 3) (.bound 5)) <|
      .conj
        (Formula.orderedPairMem 𝒞
          (.bound 1) (.bound 0) (.bound 4))
        (Formula.orderedPairMem 𝒞
          (.bound 0) (.bound 2) (.bound 6))) <|
    .conj
      (.neg <| .existsE <|
        Formula.orderedPairMem 𝒞
          (.bound 0) (.bound 2) (.bound 4))
      (Formula.extensionalEq (.bound 0) (.bound 5))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]

/-- 把一个函数整体扩张到更大的定义域。 -/
def functionExtensionValue
    (𝒞 : OrderedPairConvention) : BinarySchema 5 where
  body := .conj
    (Formula.isFunctionFromTo 𝒞
      (.bound 0) (.bound 5) (.bound 6)) <|
    .forallE <| .forallE <| .iff
      (Formula.orderedPairMem 𝒞
        (.bound 1) (.bound 0) (.bound 2)) <|
      .conj (.mem (.bound 1) (.bound 7)) <|
        .disj
          (.existsE <| .existsE <|
            .conj
              (Formula.orderedPairMem 𝒞
                (.bound 1) (.bound 3) (.bound 6)) <|
            .conj
              (Formula.orderedPairMem 𝒞
                (.bound 1) (.bound 0) (.bound 5))
              (Formula.orderedPairMem 𝒞
                (.bound 0) (.bound 2) (.bound 7))) <|
          .conj
            (.neg <| .existsE <|
              Formula.orderedPairMem 𝒞
                (.bound 0) (.bound 2) (.bound 5))
            (Formula.extensionalEq (.bound 0) (.bound 6))
  freeClosed := by
    simp [Formula.isFunctionFromTo, Formula.isFunction,
      Formula.isRelation, Formula.isDomain,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]

end BinarySchema

namespace Formula

/-- 单点输送值关系的纸面解释。 -/
theorem denote_transportedFunctionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 3) (input output : ℳ.Domain) :
    (BinarySchema.transportedFunctionValue 𝒞).denote env input output ↔
      ∃ sourceInput sourceOutput,
        ℳ.PairMember 𝕀 sourceInput input (env.bound 1) ∧
          ℳ.PairMember 𝕀 sourceInput sourceOutput (env.bound 0) ∧
            ℳ.PairMember 𝕀 sourceOutput output (env.bound 2) := by
  simp only [BinarySchema.transportedFunctionValue, BinarySchema.denote,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push]
  rfl

/-- 整体函数输送模式的纸面解释。 -/
theorem denote_functionTransportValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 4) (input output : ℳ.Domain) :
    (BinarySchema.functionTransportValue 𝒞).denote env input output ↔
      ℳ.IsFunctionTransport 𝕀
        (env.bound 0) (env.bound 1)
        (env.bound 2) (env.bound 3) input output := by
  simp only [BinarySchema.functionTransportValue, BinarySchema.denote,
    Structure.IsFunctionTransport, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_isFunctionFromTo_iff 𝕀 hExt,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push, Term.eval_bound_seven_push]
  rfl

/-- 单点扩张值关系的纸面解释。 -/
theorem denote_extendedFunctionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 4) (input output : ℳ.Domain) :
    (BinarySchema.extendedFunctionValue 𝒞).denote env input output ↔
      (∃ sourceInput sourceOutput,
          ℳ.PairMember 𝕀 sourceInput input (env.bound 1) ∧
            ℳ.PairMember 𝕀 sourceInput sourceOutput (env.bound 0) ∧
              ℳ.PairMember 𝕀 sourceOutput output (env.bound 2)) ∨
        ((¬ ∃ sourceInput,
            ℳ.PairMember 𝕀 sourceInput input (env.bound 1)) ∧
          output = env.bound 3) := by
  simp only [BinarySchema.extendedFunctionValue, BinarySchema.denote,
    Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    Formula.satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push]
  rfl

/-- 整体函数扩张模式的纸面解释。 -/
theorem denote_functionExtensionValue_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 5) (input output : ℳ.Domain) :
    (BinarySchema.functionExtensionValue 𝒞).denote env input output ↔
      ℳ.IsFunctionExtension 𝕀
        (env.bound 0) (env.bound 1) (env.bound 2)
        (env.bound 3) (env.bound 4) input output := by
  simp only [BinarySchema.functionExtensionValue, BinarySchema.denote,
    Structure.IsFunctionExtension, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_isFunctionFromTo_iff 𝕀 hExt,
    Formula.satisfies_orderedPairMem_iff 𝕀,
    Formula.satisfies_extensionalEq_iff_eq hExt,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push,
    Term.eval_bound_four_push, Term.eval_bound_five_push,
    Term.eval_bound_six_push, Term.eval_bound_seven_push]
  rfl

end Formula

namespace UnarySchema

/-- 固定源集和目标集后筛选集合编码函数图。 -/
def functionFromTo
    (𝒞 : OrderedPairConvention) : UnarySchema 2 where
  body := Formula.isFunctionFromTo 𝒞
    (.bound 0) (.bound 1) (.bound 2)
  freeClosed := by
    simp [Formula.isFunctionFromTo, Formula.isFunction,
      Formula.isRelation, Formula.isDomain,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.extensionalEq,
      Formula.FreeClosed, Term.newest]

end UnarySchema

namespace Formula

/-- 函数图筛选模式的纸面解释。 -/
theorem satisfies_functionFromTo_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 2) (function : ℳ.Domain) :
    satisfies (env.push function)
        (UnarySchema.functionFromTo 𝒞).body ↔
      ℳ.IsSetFunctionFromTo 𝕀 function
        (env.bound 0) (env.bound 1) := by
  simpa [UnarySchema.functionFromTo,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push] using
      satisfies_isFunctionFromTo_iff 𝕀 hExt
        (env.push function)
        (.bound 0) (.bound 1) (.bound 2)

end Formula

end Project
end Definitional

namespace ZF

/--
沿定义域和值域双射输送函数图，得到两个函数集之间的模型内部单射。
-/
theorem exists_functionSpaceTransportInjection
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sourceSpace targetSpace sourceDomain sourceBase
      targetDomain targetBase domainMap baseMap : ℳ.Domain}
    (hSourceSpace :
      ℳ.IsFunctionSpace 𝕀 sourceSpace sourceDomain sourceBase)
    (hTargetSpace :
      ℳ.IsFunctionSpace 𝕀 targetSpace targetDomain targetBase)
    (hDomainMap :
      ℳ.IsSetBijectionFromTo 𝕀
        domainMap sourceDomain targetDomain)
    (hBaseMap :
      ℳ.IsSetInjectionFromTo 𝕀
        baseMap sourceBase targetBase) :
    ∃ transport,
      ℳ.IsSetInjectionFromTo 𝕀 transport sourceSpace targetSpace := by
  let env : Env ℳ 4 := {
    bound := Fin.cases domainMap <|
      Fin.cases baseMap <|
        Fin.cases targetDomain <|
          Fin.cases targetBase Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setInjectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.functionTransportValue 𝒞) env
  · intro input hInput
    have hInputFunction := (hSourceSpace input).mp hInput
    let valueEnv : Env ℳ 3 := {
      bound := Fin.cases input <|
        Fin.cases domainMap <|
          Fin.cases baseMap Fin.elim0
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases exists_setFunctionFromTo_of_denote
        hZF 𝕀 (Definitional.Project.BinarySchema.transportedFunctionValue 𝒞)
        valueEnv
        (source := targetDomain) (target := targetBase)
        (by
          intro targetInput hTargetInput
          rcases hDomainMap.2 targetInput hTargetInput with
            ⟨sourceInput, hSourceInput, hDomainPair⟩
          rcases hInputFunction.2.2 sourceInput hSourceInput with
            ⟨sourceOutput, hSourceOutput, hInputPair⟩
          rcases hBaseMap.1.2.2 sourceOutput hSourceOutput with
            ⟨targetOutput, _, hBasePair⟩
          exact ⟨targetOutput,
            (Definitional.Project.Formula.denote_transportedFunctionValue_iff
              𝕀 valueEnv targetInput targetOutput).mpr
                ⟨sourceInput, sourceOutput,
                  hDomainPair, hInputPair, hBasePair⟩⟩)
        (by
          intro targetInput _ first second hFirst hSecond
          rw [Definitional.Project.Formula.denote_transportedFunctionValue_iff 𝕀]
            at hFirst hSecond
          rcases hFirst with
            ⟨firstInput, firstOutput,
              hFirstDomain, hFirstInput, hFirstBase⟩
          rcases hSecond with
            ⟨secondInput, secondOutput,
              hSecondDomain, hSecondInput, hSecondBase⟩
          have hInputEq :=
            hDomainMap.1.2 firstInput secondInput targetInput
              hFirstDomain hSecondDomain
          subst secondInput
          have hOutputEq :=
            hInputFunction.1.2 firstInput firstOutput secondOutput
              hFirstInput hSecondInput
          subst secondOutput
          exact hBaseMap.1.1.2 firstOutput first second
            hFirstBase hSecondBase)
        (by
          intro targetInput targetOutput _ hValue
          rw [Definitional.Project.Formula.denote_transportedFunctionValue_iff 𝕀]
            at hValue
          rcases hValue with
            ⟨_, sourceOutput, _, _, hBasePair⟩
          exact hBaseMap.1.output_mem_of_pairMember hBasePair) with
      ⟨output, hOutputFunction, hOutputPairs⟩
    refine ⟨output,
      (Definitional.Project.Formula.denote_functionTransportValue_iff
        𝕀 hZF.1 env input output).mpr ?_⟩
    refine ⟨hOutputFunction, fun targetInput targetOutput => ?_⟩
    rw [hOutputPairs targetInput targetOutput,
      Definitional.Project.Formula.denote_transportedFunctionValue_iff 𝕀]
    rfl
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_functionTransportValue_iff 𝕀 hZF.1]
      at hFirst hSecond
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hFirst.1.1.1 hSecond.1.1.1
    intro targetInput targetOutput
    rw [hFirst.2 targetInput targetOutput,
      hSecond.2 targetInput targetOutput]
  · intro input output _ hValue
    rw [Definitional.Project.Formula.denote_functionTransportValue_iff 𝕀 hZF.1]
      at hValue
    exact (hTargetSpace output).mpr hValue.1
  · intro first second output hFirstMem hSecondMem hFirst hSecond
    rw [Definitional.Project.Formula.denote_functionTransportValue_iff 𝕀 hZF.1]
      at hFirst hSecond
    have hFirstFunction := (hSourceSpace first).mp hFirstMem
    have hSecondFunction := (hSourceSpace second).mp hSecondMem
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hFirstFunction.1.1 hSecondFunction.1.1
    intro sourceInput sourceOutput
    constructor
    · intro hFirstPair
      have hSourceInput :=
        hFirstFunction.input_mem_of_pairMember hFirstPair
      have hSourceOutput :=
        hFirstFunction.output_mem_of_pairMember hFirstPair
      rcases hDomainMap.1.1.2.2 sourceInput hSourceInput with
        ⟨targetInput, hTargetInput, hDomainPair⟩
      rcases hBaseMap.1.2.2 sourceOutput hSourceOutput with
        ⟨targetOutput, _, hBasePair⟩
      have hOutputPair :
          ℳ.PairMember 𝕀 targetInput targetOutput output :=
        (hFirst.2 targetInput targetOutput).mpr
          ⟨hTargetInput, sourceInput, sourceOutput,
            hDomainPair, hFirstPair, hBasePair⟩
      rcases (hSecond.2 targetInput targetOutput).mp hOutputPair with
        ⟨_, secondInput, secondOutput,
          hSecondDomain, hSecondPair, hSecondBase⟩
      have hInputEq :=
        hDomainMap.1.2 sourceInput secondInput targetInput
          hDomainPair hSecondDomain
      have hOutputEq :=
        hBaseMap.2 sourceOutput secondOutput targetOutput
          hBasePair hSecondBase
      simpa [hInputEq, hOutputEq] using hSecondPair
    · intro hSecondPair
      have hSourceInput :=
        hSecondFunction.input_mem_of_pairMember hSecondPair
      have hSourceOutput :=
        hSecondFunction.output_mem_of_pairMember hSecondPair
      rcases hDomainMap.1.1.2.2 sourceInput hSourceInput with
        ⟨targetInput, hTargetInput, hDomainPair⟩
      rcases hBaseMap.1.2.2 sourceOutput hSourceOutput with
        ⟨targetOutput, _, hBasePair⟩
      have hOutputPair :
          ℳ.PairMember 𝕀 targetInput targetOutput output :=
        (hSecond.2 targetInput targetOutput).mpr
          ⟨hTargetInput, sourceInput, sourceOutput,
            hDomainPair, hSecondPair, hBasePair⟩
      rcases (hFirst.2 targetInput targetOutput).mp hOutputPair with
        ⟨_, firstInput, firstOutput,
          hFirstDomain, hFirstPair, hFirstBase⟩
      have hInputEq :=
        hDomainMap.1.2 sourceInput firstInput targetInput
          hDomainPair hFirstDomain
      have hOutputEq :=
        hBaseMap.2 sourceOutput firstOutput targetOutput
          hBasePair hFirstBase
      simpa [hInputEq, hOutputEq] using hFirstPair

/--
沿定义域单射扩张函数，并在单射像之外取固定值，得到函数集之间的模型内部单射。
-/
theorem exists_functionSpaceExtensionInjection
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {sourceSpace targetSpace sourceDomain sourceBase
      targetDomain targetBase domainMap baseMap defaultValue : ℳ.Domain}
    (hSourceSpace :
      ℳ.IsFunctionSpace 𝕀 sourceSpace sourceDomain sourceBase)
    (hTargetSpace :
      ℳ.IsFunctionSpace 𝕀 targetSpace targetDomain targetBase)
    (hDomainMap :
      ℳ.IsSetInjectionFromTo 𝕀
        domainMap sourceDomain targetDomain)
    (hBaseMap :
      ℳ.IsSetInjectionFromTo 𝕀
        baseMap sourceBase targetBase)
    (hDefault : ℳ.mem defaultValue targetBase) :
    ∃ extension,
      ℳ.IsSetInjectionFromTo 𝕀 extension sourceSpace targetSpace := by
  let env : Env ℳ 5 := {
    bound := Fin.cases domainMap <|
      Fin.cases baseMap <|
        Fin.cases defaultValue <|
          Fin.cases targetDomain <|
            Fin.cases targetBase Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  apply exists_setInjectionFromTo_of_denote
      hZF 𝕀 (Definitional.Project.BinarySchema.functionExtensionValue 𝒞) env
  · intro input hInput
    have hInputFunction := (hSourceSpace input).mp hInput
    let valueEnv : Env ℳ 4 := {
      bound := Fin.cases input <|
        Fin.cases domainMap <|
          Fin.cases baseMap <|
            Fin.cases defaultValue Fin.elim0
      free := fun _ => Classical.choice ℳ.nonempty
    }
    rcases exists_setFunctionFromTo_of_denote
        hZF 𝕀 (Definitional.Project.BinarySchema.extendedFunctionValue 𝒞)
        valueEnv
        (source := targetDomain) (target := targetBase)
        (by
          intro targetInput hTargetInput
          classical
          by_cases hImage :
              ∃ sourceInput,
                ℳ.PairMember 𝕀 sourceInput targetInput domainMap
          · rcases hImage with ⟨sourceInput, hDomainPair⟩
            have hSourceInput :=
              hDomainMap.1.input_mem_of_pairMember hDomainPair
            rcases hInputFunction.2.2 sourceInput hSourceInput with
              ⟨sourceOutput, hSourceOutput, hInputPair⟩
            rcases hBaseMap.1.2.2 sourceOutput hSourceOutput with
              ⟨targetOutput, _, hBasePair⟩
            exact ⟨targetOutput,
              (Definitional.Project.Formula.denote_extendedFunctionValue_iff
                𝕀 hZF.1 valueEnv targetInput targetOutput).mpr <|
                  Or.inl ⟨sourceInput, sourceOutput,
                    hDomainPair, hInputPair, hBasePair⟩⟩
          · exact ⟨defaultValue,
              (Definitional.Project.Formula.denote_extendedFunctionValue_iff
                𝕀 hZF.1 valueEnv targetInput defaultValue).mpr <|
                  Or.inr ⟨hImage, rfl⟩⟩)
        (by
          intro targetInput _ first second hFirst hSecond
          rw [Definitional.Project.Formula.denote_extendedFunctionValue_iff 𝕀 hZF.1]
            at hFirst hSecond
          rcases hFirst with hFirstImage | hFirstDefault
          · rcases hFirstImage with
              ⟨firstInput, firstOutput,
                hFirstDomain, hFirstFunction, hFirstBase⟩
            rcases hSecond with hSecondImage | hSecondDefault
            · rcases hSecondImage with
                ⟨secondInput, secondOutput,
                  hSecondDomain, hSecondFunction, hSecondBase⟩
              have hInputEq :=
                hDomainMap.2 firstInput secondInput targetInput
                  hFirstDomain hSecondDomain
              subst secondInput
              have hOutputEq :=
                hInputFunction.1.2 firstInput firstOutput secondOutput
                  hFirstFunction hSecondFunction
              subst secondOutput
              exact hBaseMap.1.1.2 firstOutput first second
                hFirstBase hSecondBase
            · exact False.elim <| hSecondDefault.1
                ⟨firstInput, hFirstDomain⟩
          · rcases hSecond with hSecondImage | hSecondDefault
            · rcases hSecondImage with
                ⟨secondInput, _, hSecondDomain, _, _⟩
              exact False.elim <| hFirstDefault.1
                ⟨secondInput, hSecondDomain⟩
            · exact hFirstDefault.2.trans hSecondDefault.2.symm)
        (by
          intro targetInput targetOutput _ hValue
          rw [Definitional.Project.Formula.denote_extendedFunctionValue_iff 𝕀 hZF.1]
            at hValue
          rcases hValue with hImage | hDefaultValue
          · rcases hImage with ⟨_, _, _, _, hBasePair⟩
            exact hBaseMap.1.output_mem_of_pairMember hBasePair
          · simpa [hDefaultValue.2] using hDefault) with
      ⟨output, hOutputFunction, hOutputPairs⟩
    refine ⟨output,
      (Definitional.Project.Formula.denote_functionExtensionValue_iff
        𝕀 hZF.1 env input output).mpr ?_⟩
    refine ⟨hOutputFunction, fun targetInput targetOutput => ?_⟩
    rw [hOutputPairs targetInput targetOutput,
      Definitional.Project.Formula.denote_extendedFunctionValue_iff 𝕀 hZF.1]
    rfl
  · intro input _ first second hFirst hSecond
    rw [Definitional.Project.Formula.denote_functionExtensionValue_iff 𝕀 hZF.1]
      at hFirst hSecond
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hFirst.1.1.1 hSecond.1.1.1
    intro targetInput targetOutput
    rw [hFirst.2 targetInput targetOutput,
      hSecond.2 targetInput targetOutput]
  · intro input output _ hValue
    rw [Definitional.Project.Formula.denote_functionExtensionValue_iff 𝕀 hZF.1]
      at hValue
    exact (hTargetSpace output).mpr hValue.1
  · intro first second output hFirstMem hSecondMem hFirst hSecond
    rw [Definitional.Project.Formula.denote_functionExtensionValue_iff 𝕀 hZF.1]
      at hFirst hSecond
    have hFirstFunction := (hSourceSpace first).mp hFirstMem
    have hSecondFunction := (hSourceSpace second).mp hSecondMem
    apply Structure.IsSetRelation.eq_of_pairMember_iff hZF.1
      hFirstFunction.1.1 hSecondFunction.1.1
    intro sourceInput sourceOutput
    constructor
    · intro hFirstPair
      have hSourceInput :=
        hFirstFunction.input_mem_of_pairMember hFirstPair
      have hSourceOutput :=
        hFirstFunction.output_mem_of_pairMember hFirstPair
      rcases hDomainMap.1.2.2 sourceInput hSourceInput with
        ⟨targetInput, _, hDomainPair⟩
      rcases hBaseMap.1.2.2 sourceOutput hSourceOutput with
        ⟨targetOutput, _, hBasePair⟩
      have hOutputPair :
          ℳ.PairMember 𝕀 targetInput targetOutput output :=
        (hFirst.2 targetInput targetOutput).mpr <|
          ⟨hDomainMap.1.output_mem_of_pairMember hDomainPair,
            Or.inl ⟨sourceInput, sourceOutput,
              hDomainPair, hFirstPair, hBasePair⟩⟩
      rcases (hSecond.2 targetInput targetOutput).mp hOutputPair with
        ⟨_, hSecondImage | hSecondDefault⟩
      · rcases hSecondImage with
          ⟨secondInput, secondOutput,
            hSecondDomain, hSecondPair, hSecondBase⟩
        have hInputEq :=
          hDomainMap.2 sourceInput secondInput targetInput
            hDomainPair hSecondDomain
        have hOutputEq :=
          hBaseMap.2 sourceOutput secondOutput targetOutput
            hBasePair hSecondBase
        simpa [hInputEq, hOutputEq] using hSecondPair
      · exact False.elim <| hSecondDefault.1
          ⟨sourceInput, hDomainPair⟩
    · intro hSecondPair
      have hSourceInput :=
        hSecondFunction.input_mem_of_pairMember hSecondPair
      have hSourceOutput :=
        hSecondFunction.output_mem_of_pairMember hSecondPair
      rcases hDomainMap.1.2.2 sourceInput hSourceInput with
        ⟨targetInput, _, hDomainPair⟩
      rcases hBaseMap.1.2.2 sourceOutput hSourceOutput with
        ⟨targetOutput, _, hBasePair⟩
      have hOutputPair :
          ℳ.PairMember 𝕀 targetInput targetOutput output :=
        (hSecond.2 targetInput targetOutput).mpr <|
          ⟨hDomainMap.1.output_mem_of_pairMember hDomainPair,
            Or.inl ⟨sourceInput, sourceOutput,
              hDomainPair, hSecondPair, hBasePair⟩⟩
      rcases (hFirst.2 targetInput targetOutput).mp hOutputPair with
        ⟨_, hFirstImage | hFirstDefault⟩
      · rcases hFirstImage with
          ⟨firstInput, firstOutput,
            hFirstDomain, hFirstPair, hFirstBase⟩
        have hInputEq :=
          hDomainMap.2 sourceInput firstInput targetInput
            hDomainPair hFirstDomain
        have hOutputEq :=
          hBaseMap.2 sourceOutput firstOutput targetOutput
            hBasePair hFirstBase
        simpa [hInputEq, hOutputEq] using hFirstPair
      · exact False.elim <| hFirstDefault.1
          ⟨sourceInput, hDomainPair⟩

/-- ZF 模型中任意源集和目标集都有相应的函数集。 -/
theorem exists_functionSpace
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (source target : ℳ.Domain) :
    ∃ space, ℳ.IsFunctionSpace 𝕀 space source target := by
  rcases exists_cartesianProduct hZF 𝕀 source target with
    ⟨product, hProduct⟩
  rcases exists_powerSet hZF product with
    ⟨power, hPower⟩
  let env : Env ℳ 2 := {
    bound := Fin.cases source <| Fin.cases target Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (Definitional.Project.UnarySchema.functionFromTo 𝒞) env power with
    ⟨space, hSpace⟩
  refine ⟨space, fun function => ?_⟩
  rw [hSpace function,
    Definitional.Project.Formula.satisfies_functionFromTo_iff
      𝕀 hZF.1 env function]
  constructor
  · exact fun h => h.2
  · intro hFunction
    refine ⟨(hPower function).mpr ?_, hFunction⟩
    intro pair hPair
    rcases hFunction.1.1 pair hPair with
      ⟨input, output, hCode⟩
    apply (hProduct pair).mpr
    exact ⟨input,
      hFunction.input_mem_of_pairMember
        ⟨pair, hCode, hPair⟩,
      output,
      hFunction.output_mem_of_pairMember
        ⟨pair, hCode, hPair⟩,
      hCode⟩

end ZF

end SetTheory
end YesMetaZFC
