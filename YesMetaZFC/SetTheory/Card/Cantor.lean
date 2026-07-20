import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.SetTheory.Replacement
import YesMetaZFC.SetTheory.SetConstruction

/-!
# Cantor 定理

本文件在模型内部构造对角集与单元素函数图，证明任意集合的基数严格小于其幂集的
基数。函数、函数图和幂集见证都由 ZF 模型中的集合给出。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace ZF

/-- 从给定函数图中分离 Cantor 对角集的模式。 -/
private def cantorDiagonalSchema
    (𝒞 : Definitional.Project.OrderedPairConvention) :
    Definitional.Project.UnarySchema 1 where
  body := .neg <| .existsE <| .conj
    (Definitional.Project.Formula.orderedPairMem
      𝒞 (.bound 1) (.bound 0) (.bound 2))
    (.mem (.bound 1) (.bound 0))
  freeClosed := by
    simp [Definitional.Project.Formula.orderedPairMem,
      Definitional.Formula.FreeClosed, Definitional.Term.newest]

/-- 生成 `x ↦ ⟨x, {x}⟩` 函数图成员的模式。 -/
private def singletonGraphSchema
    (𝒞 : Definitional.Project.OrderedPairConvention) :
    Definitional.Project.BinarySchema 0 where
  body := .existsE <| .conj
    (Definitional.Project.Formula.isSingleton (.bound 0) (.bound 2))
    (𝒞.code (.bound 1) (.bound 2) (.bound 0))
  freeClosed := by
    simp [Definitional.Project.Formula.isSingleton,
      Definitional.Project.Formula.isUnorderedPair,
      Definitional.Project.Formula.extensionalEq,
      Definitional.Formula.FreeClosed, Definitional.Term.newest]

/-- 对角模式恰好表达 `x ∉ f(x)`。 -/
private theorem satisfies_cantorDiagonalSchema_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 1) (value : ℳ.Domain) :
    Definitional.Project.Formula.satisfies (env.push value)
        (cantorDiagonalSchema 𝒞).body ↔
      ¬ ∃ output,
          ℳ.PairMember 𝕀 value output (env.bound 0) ∧
          ℳ.mem value output := by
  simp only [cantorDiagonalSchema,
    Definitional.Project.Formula.satisfies_neg_iff,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Project.Formula.satisfies_orderedPairMem_iff 𝕀,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Project.Term.eval_bound_zero_push,
    Definitional.Project.Term.eval_bound_one_push,
    Definitional.Project.Term.eval_bound_two_push]
  rfl

/-- 单元素函数图模式恰好生成编码对 `⟨x, {x}⟩`。 -/
private theorem denote_singletonGraphSchema_iff
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (hExt : Extensional ℳ)
    (env : Env ℳ 0) (input pair : ℳ.Domain) :
    (singletonGraphSchema 𝒞).denote env input pair ↔
      ∃ singleton,
        ℳ.IsSingletonOf singleton input ∧
          𝕀.Codes pair input singleton := by
  simp only [singletonGraphSchema,
    Definitional.Project.BinarySchema.denote,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_conj_iff,
    Definitional.Project.Formula.satisfies_isSingleton_iff hExt,
    𝕀.satisfies_code_iff,
    Definitional.Project.Term.eval_bound_zero_push,
    Definitional.Project.Term.eval_bound_one_push,
    Definitional.Project.Term.eval_bound_two_push]

/--
不存在从一个集合到其幂集的模型内部满射。

证明使用分离公理构造 `D = {x ∈ X | x ∉ f(x)}`，再令满射原像为 `d`，从
`d ∈ D ↔ d ∉ D` 得到矛盾。
-/
theorem not_surjectiveOnto_powerSet
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {function source power : ℳ.Domain}
    (hFunction :
      ℳ.IsSetFunctionFromTo 𝕀 function source power)
    (hPower : ℳ.IsPowerSetOf power source) :
    ¬ ℳ.IsSetSurjectiveOnto 𝕀 function source power := by
  let env : Env ℳ 1 := {
    bound := fun _ => function
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (cantorDiagonalSchema 𝒞) env source with
    ⟨diagonal, hDiagonalMembers⟩
  have hDiagonal (value : ℳ.Domain) :
      ℳ.mem value diagonal ↔
        ℳ.mem value source ∧
          ¬ ∃ output,
            ℳ.PairMember 𝕀 value output function ∧
              ℳ.mem value output := by
    rw [hDiagonalMembers value,
      satisfies_cantorDiagonalSchema_iff 𝕀 env value]
  have hDiagonalPower : ℳ.mem diagonal power :=
    (hPower diagonal).mpr fun value hValue =>
      (hDiagonal value).mp hValue |>.1
  intro hSurjective
  rcases hSurjective diagonal hDiagonalPower with
    ⟨input, hInput, hInputDiagonal⟩
  by_cases hMember : ℳ.mem input diagonal
  · exact
      (hDiagonal input).mp hMember |>.2
        ⟨diagonal, hInputDiagonal, hMember⟩
  · apply hMember
    apply (hDiagonal input).mpr
    refine ⟨hInput, ?_⟩
    rintro ⟨output, hInputOutput, hMemberOutput⟩
    have hOutputEq :=
      hFunction.1.2 input output diagonal
        hInputOutput hInputDiagonal
    subst output
    exact hMember hMemberOutput

/-- 单元素映射 `x ↦ {x}` 给出从任意集合到其幂集的模型内部单射。 -/
theorem exists_singletonInjectionToPowerSet
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source power : ℳ.Domain}
    (hPower : ℳ.IsPowerSetOf power source) :
    ∃ function,
      ℳ.IsSetInjectionFromTo 𝕀 function source power := by
  let env : Env ℳ 0 := {
    bound := Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hTotal : ∀ input, ℳ.mem input source →
      ∃ pair,
        (singletonGraphSchema 𝒞).denote
          env input pair := by
    intro input _
    rcases KP.exists_singleton (modelsKP hZF) input with
      ⟨singleton, hSingleton⟩
    rcases 𝕀.total input singleton with
      ⟨pair, hPair⟩
    refine ⟨pair, ?_⟩
    apply
      (denote_singletonGraphSchema_iff
        𝕀 hZF.1 env input pair).mpr
    exact ⟨singleton, hSingleton, hPair⟩
  have hUnique : ∀ input, ℳ.mem input source →
      ∀ first second,
        (singletonGraphSchema 𝒞).denote
            env input first →
          (singletonGraphSchema 𝒞).denote
            env input second →
          first = second := by
    intro input _ first second hFirst hSecond
    rcases
        (denote_singletonGraphSchema_iff
          𝕀 hZF.1 env input first).mp hFirst with
      ⟨firstSingleton, hFirstSingleton, hFirstCode⟩
    rcases
        (denote_singletonGraphSchema_iff
          𝕀 hZF.1 env input second).mp hSecond with
      ⟨secondSingleton, hSecondSingleton, hSecondCode⟩
    have hSingletonEq :=
      Structure.IsSingletonOf.eq hZF.1
        hFirstSingleton hSecondSingleton
    subst secondSingleton
    exact 𝕀.unique hFirstCode hSecondCode
  rcases exists_functionalImageOn hZF
      (singletonGraphSchema 𝒞)
      env source hTotal hUnique with
    ⟨function, hFunctionMembers⟩
  have hPairMember (input output : ℳ.Domain) :
      ℳ.PairMember 𝕀 input output function ↔
        ℳ.mem input source ∧
          ℳ.IsSingletonOf output input := by
    constructor
    · rintro ⟨pair, hPairCode, hPairMem⟩
      rcases (hFunctionMembers pair).mp hPairMem with
        ⟨sourceInput, hSourceInput, hGraph⟩
      rcases
          (denote_singletonGraphSchema_iff
            𝕀 hZF.1 env sourceInput pair).mp hGraph with
        ⟨singleton, hSingleton, hGraphCode⟩
      rcases 𝕀.injective hPairCode hGraphCode with
        ⟨hInputEq, hOutputEq⟩
      subst sourceInput
      subst singleton
      exact ⟨hSourceInput, hSingleton⟩
    · rintro ⟨hInput, hSingleton⟩
      rcases 𝕀.total input output with
        ⟨pair, hPairCode⟩
      refine ⟨pair, hPairCode, (hFunctionMembers pair).mpr ?_⟩
      refine ⟨input, hInput, ?_⟩
      apply
        (denote_singletonGraphSchema_iff
          𝕀 hZF.1 env input pair).mpr
      exact ⟨output, hSingleton, hPairCode⟩
  have hRelation : ℳ.IsSetRelation 𝕀 function := by
    intro pair hPair
    rcases (hFunctionMembers pair).mp hPair with
      ⟨input, _, hGraph⟩
    rcases
        (denote_singletonGraphSchema_iff
          𝕀 hZF.1 env input pair).mp hGraph with
      ⟨output, _, hCode⟩
    exact ⟨input, output, hCode⟩
  have hSetFunction : ℳ.IsSetFunction 𝕀 function := by
    refine ⟨hRelation, ?_⟩
    intro input first second hFirst hSecond
    exact
      Structure.IsSingletonOf.eq hZF.1
        ((hPairMember input first).mp hFirst).2
        ((hPairMember input second).mp hSecond).2
  have hDomain : ℳ.IsDomainOf 𝕀 source function := by
    intro input
    constructor
    · intro hInput
      rcases KP.exists_singleton (modelsKP hZF) input with
        ⟨singleton, hSingleton⟩
      exact
        ⟨singleton, (hPairMember input singleton).mpr
          ⟨hInput, hSingleton⟩⟩
    · rintro ⟨output, hOutput⟩
      exact ((hPairMember input output).mp hOutput).1
  have hIntoPower :
      ∀ input, ℳ.mem input source →
        ∃ output, ℳ.mem output power ∧
          ℳ.PairMember 𝕀 input output function := by
    intro input hInput
    rcases KP.exists_singleton (modelsKP hZF) input with
      ⟨singleton, hSingleton⟩
    have hSingletonPower : ℳ.mem singleton power := by
      apply (hPower singleton).mpr
      intro member hMember
      rw [hSingleton member] at hMember
      simpa [hMember] using hInput
    exact
      ⟨singleton, hSingletonPower,
        (hPairMember input singleton).mpr
          ⟨hInput, hSingleton⟩⟩
  have hInjective : ℳ.IsSetInjective 𝕀 function := by
    intro first second output hFirst hSecond
    have hFirstSingleton :=
      ((hPairMember first output).mp hFirst).2
    have hSecondSingleton :=
      ((hPairMember second output).mp hSecond).2
    exact (hSecondSingleton first).mp <|
      (hFirstSingleton first).mpr rfl
  exact
    ⟨function,
      ⟨⟨hSetFunction, hDomain, hIntoPower⟩,
        hInjective⟩⟩

/-- Cantor 定理：任意集合的基数严格小于其幂集的基数。 -/
theorem cardinalLess_powerSet
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source power : ℳ.Domain}
    (hPower : ℳ.IsPowerSetOf power source) :
    ℳ.CardinalLess 𝕀 source power := by
  constructor
  · exact exists_singletonInjectionToPowerSet
      hZF 𝕀 hPower
  · rintro ⟨function, hBijection⟩
    exact
      not_surjectiveOnto_powerSet hZF 𝕀
        hBijection.1.1 hPower hBijection.2

/-- 每个集合都有一个基数严格更大的幂集见证。 -/
theorem exists_powerSet_cardinalLess
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (source : ℳ.Domain) :
    ∃ power,
      ℳ.IsPowerSetOf power source ∧
        ℳ.CardinalLess 𝕀 source power := by
  rcases exists_powerSet hZF source with
    ⟨power, hPower⟩
  exact
    ⟨power, hPower,
      cardinalLess_powerSet hZF 𝕀 hPower⟩

end ZF

end SetTheory
end YesMetaZFC
