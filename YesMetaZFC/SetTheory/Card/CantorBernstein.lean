import YesMetaZFC.SetTheory.Card.Basic
import YesMetaZFC.SetTheory.Replacement
import YesMetaZFC.SetTheory.Separation
import YesMetaZFC.SetTheory.SetConstruction

/-!
# Cantor--Bernstein 定理

本文件从两个模型内部集合编码单射构造双射。证明先在源集中分离出包含所有没有
逆向原像的元素、并在 `reverse ∘ forward` 下封闭的最小子集；随后在该子集上使用
正向单射，在其补集上使用逆向单射的逆关系，并通过 Replacement 生成模型内部函数图。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Structure

/-- Cantor--Bernstein 构造中对 `reverse ∘ forward` 封闭的候选集合。 -/
def IsCantorBernsteinClosed {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (forward reverse source target closed : ℳ.Domain) : Prop :=
  (∀ input, ℳ.mem input source →
    (¬ ∃ output, ℳ.mem output target ∧
      ℳ.PairMember 𝕀 output input reverse) →
    ℳ.mem input closed) ∧
  ∀ input middle output,
    ℳ.mem input closed →
    ℳ.PairMember 𝕀 input middle forward →
    ℳ.PairMember 𝕀 middle output reverse →
    ℳ.mem output closed

/-- Cantor--Bernstein 分片函数在一个输入输出对上的纸面关系。 -/
def IsCantorBernsteinValue {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (forward reverse closed input output : ℳ.Domain) : Prop :=
  (ℳ.mem input closed ∧
    ℳ.PairMember 𝕀 input output forward) ∨
  (¬ ℳ.mem input closed ∧
    ℳ.PairMember 𝕀 output input reverse)

end Structure

namespace Definitional
namespace Project
namespace Formula

/-- Cantor--Bernstein 闭集谓词的对象语言公式。 -/
def isCantorBernsteinClosed (𝒞 : OrderedPairConvention)
    {depth : Nat}
    (forward reverse source target closed : Term depth) :
    Formula 1 depth :=
  .conj
    (Formula.forallMem source <|
      .imp
        (.neg <| Formula.existsMem target.weaken <|
          orderedPairMem 𝒞 Term.newest (.bound 1)
            reverse.weaken.weaken)
        (.mem Term.newest closed.weaken)) <|
    Formula.forallMem closed <|
      .forallE <| .forallE <|
        .imp
          (.conj
            (orderedPairMem 𝒞 (.bound 2) (.bound 1)
              forward.weaken.weaken.weaken)
            (orderedPairMem 𝒞 (.bound 1) (.bound 0)
              reverse.weaken.weaken.weaken))
          (.mem (.bound 0) closed.weaken.weaken.weaken)

theorem satisfies_isCantorBernsteinClosed_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {depth : Nat} (env : Env ℳ depth)
    (forward reverse source target closed : Term depth) :
    satisfies env
        (isCantorBernsteinClosed 𝒞
          forward reverse source target closed) ↔
      ℳ.IsCantorBernsteinClosed 𝕀
        (forward.eval env) (reverse.eval env)
        (source.eval env) (target.eval env) (closed.eval env) := by
  simp only [isCantorBernsteinClosed,
    Structure.IsCantorBernsteinClosed,
    satisfies_conj_iff, satisfies_forallMem_iff,
    satisfies_imp_iff, satisfies_neg_iff,
    satisfies_existsMem_iff, satisfies_orderedPairMem_iff 𝕀,
    satisfies_mem_iff, satisfies_forall_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨hBase, hClosed⟩
    refine ⟨hBase, ?_⟩
    intro input middle output hInput hForward hReverse
    exact hClosed input hInput middle output ⟨hForward, hReverse⟩
  · rintro ⟨hBase, hClosed⟩
    refine ⟨hBase, ?_⟩
    intro input hInput middle output hPairs
    exact hClosed input middle output hInput hPairs.1 hPairs.2

end Formula

namespace UnarySchema

/-- 从源集分离出最小 Cantor--Bernstein 闭集的模式。 -/
def cantorBernsteinClosure
    (𝒞 : OrderedPairConvention) : UnarySchema 4 where
  body := .forallE <|
    .imp
      (Formula.isCantorBernsteinClosed 𝒞
        (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 0))
      (.mem (.bound 1) (.bound 0))
  freeClosed := by
    simp [Formula.isCantorBernsteinClosed,
      Formula.orderedPairMem, Formula.forallMem,
      Formula.existsMem, Formula.FreeClosed, Term.newest]

end UnarySchema

namespace BinarySchema

/-- 生成 Cantor--Bernstein 分片函数图成员的模式。 -/
def cantorBernsteinGraph
    (𝒞 : OrderedPairConvention) : BinarySchema 3 where
  body := .existsE <| .conj
    (.disj
      (.conj
        (.mem (.bound 2) (.bound 5))
        (Formula.orderedPairMem 𝒞
          (.bound 2) (.bound 0) (.bound 3)))
      (.conj
        (.neg (.mem (.bound 2) (.bound 5)))
        (Formula.orderedPairMem 𝒞
          (.bound 0) (.bound 2) (.bound 4))))
    (𝒞.code (.bound 1) (.bound 2) (.bound 0))
  freeClosed := by
    simp [Formula.orderedPairMem, Formula.FreeClosed,
      Term.newest]

end BinarySchema

namespace Formula

theorem satisfies_cantorBernsteinClosure_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 4) (value : ℳ.Domain) :
    satisfies (env.push value)
        (UnarySchema.cantorBernsteinClosure 𝒞).body ↔
      ∀ closed,
        ℳ.IsCantorBernsteinClosed 𝕀
          (env.bound 0) (env.bound 1)
          (env.bound 2) (env.bound 3) closed →
        ℳ.mem value closed := by
  simp only [UnarySchema.cantorBernsteinClosure,
    satisfies_forall_iff, satisfies_imp_iff, satisfies_mem_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]
  have hSemantic (closed : ℳ.Domain) :
      satisfies ((env.push value).push closed)
          (isCantorBernsteinClosed 𝒞
            (.bound 2) (.bound 3) (.bound 4)
            (.bound 5) (.bound 0)) ↔
        ℳ.IsCantorBernsteinClosed 𝕀
          (env.bound 0) (env.bound 1)
          (env.bound 2) (env.bound 3) closed := by
    simpa using
      (satisfies_isCantorBernsteinClosed_iff 𝕀
        ((env.push value).push closed)
        (.bound 2) (.bound 3) (.bound 4)
        (.bound 5) (.bound 0))
  constructor
  · intro h closed hClosed
    have hMember := h closed ((hSemantic closed).mpr hClosed)
    simpa using hMember
  · intro h closed hClosed
    have hMember := h closed <| (hSemantic closed).mp hClosed
    simpa using hMember

theorem denote_cantorBernsteinGraph_iff
    {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    (env : Env ℳ 3) (input pair : ℳ.Domain) :
    (BinarySchema.cantorBernsteinGraph 𝒞).denote
        env input pair ↔
      ∃ output,
        ℳ.IsCantorBernsteinValue 𝕀
          (env.bound 0) (env.bound 1) (env.bound 2)
          input output ∧
        𝕀.Codes pair input output := by
  simp only [BinarySchema.cantorBernsteinGraph,
    BinarySchema.denote, Structure.IsCantorBernsteinValue,
    satisfies_exists_iff, satisfies_conj_iff, satisfies_disj_iff,
    satisfies_mem_iff, satisfies_neg_iff,
    satisfies_orderedPairMem_iff 𝕀, 𝕀.satisfies_code_iff,
    Term.eval_bound_zero_push, Term.eval_bound_one_push,
    Term.eval_bound_two_push, Term.eval_bound_three_push]
  rfl

end Formula
end Project
end Definitional

namespace ZF

private theorem input_mem_of_pairMember
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {function source target input output : ℳ.Domain}
    (hFunction :
      ℳ.IsSetFunctionFromTo 𝕀 function source target)
    (hPair : ℳ.PairMember 𝕀 input output function) :
    ℳ.mem input source :=
  (hFunction.2.1 input).mpr ⟨output, hPair⟩

private theorem output_mem_of_pairMember
    {ℳ : Structure.{u}}
    {𝒞 : Definitional.Project.OrderedPairConvention}
    {𝕀 : 𝒞.Interpretation ℳ}
    {function source target input output : ℳ.Domain}
    (hFunction :
      ℳ.IsSetFunctionFromTo 𝕀 function source target)
    (hPair : ℳ.PairMember 𝕀 input output function) :
    ℳ.mem output target := by
  have hInput := input_mem_of_pairMember hFunction hPair
  rcases hFunction.2.2 input hInput with
    ⟨selected, hSelectedTarget, hSelectedPair⟩
  have hOutputEq :=
    hFunction.1.2 input output selected hPair hSelectedPair
  simpa [hOutputEq] using hSelectedTarget

/--
Cantor--Bernstein 的具体单射形式：若存在给定的双向模型内部单射，则两集合等势。
-/
theorem equinumerous_of_injections
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {source target forward reverse : ℳ.Domain}
    (hForward :
      ℳ.IsSetInjectionFromTo 𝕀 forward source target)
    (hReverse :
      ℳ.IsSetInjectionFromTo 𝕀 reverse target source) :
    ℳ.Equinumerous 𝕀 source target := by
  have hForwardFunction := hForward.1
  have hForwardInjective := hForward.2
  have hReverseFunction := hReverse.1
  have hReverseInjective := hReverse.2

  -- 分离所有 Cantor--Bernstein 闭集的交，得到源集中的最小闭集。
  let closureEnv : Env ℳ 4 := {
    bound :=
      Fin.cases forward <|
        Fin.cases reverse <|
          Fin.cases source <|
            Fin.cases target Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  rcases exists_separation hZF
      (Definitional.Project.UnarySchema.cantorBernsteinClosure 𝒞)
      closureEnv source with
    ⟨closed, hClosedMembers⟩
  have hClosedSemantic (input : ℳ.Domain) :
      ℳ.mem input closed ↔
        ℳ.mem input source ∧
          ∀ candidate,
            ℳ.IsCantorBernsteinClosed 𝕀
              forward reverse source target candidate →
            ℳ.mem input candidate := by
    rw [hClosedMembers input,
      Definitional.Project.Formula.satisfies_cantorBernsteinClosure_iff
        𝕀 closureEnv input]
    rfl
  have hClosedIs :
      ℳ.IsCantorBernsteinClosed 𝕀
        forward reverse source target closed := by
    constructor
    · intro input hInput hNoReverse
      apply (hClosedSemantic input).mpr
      refine ⟨hInput, ?_⟩
      intro candidate hCandidate
      exact hCandidate.1 input hInput hNoReverse
    · intro input middle output hInput hForwardPair hReversePair
      have hOutputSource :=
        output_mem_of_pairMember hReverseFunction hReversePair
      apply (hClosedSemantic output).mpr
      refine ⟨hOutputSource, ?_⟩
      intro candidate hCandidate
      exact
        hCandidate.2 input middle output
          (((hClosedSemantic input).mp hInput).2
            candidate hCandidate)
          hForwardPair hReversePair
  have hClosedSubset :
      ∀ input, ℳ.mem input closed → ℳ.mem input source :=
    fun input hInput => ((hClosedSemantic input).mp hInput).1
  have hClosedMinimal :
      ∀ candidate,
        ℳ.IsCantorBernsteinClosed 𝕀
          forward reverse source target candidate →
        ∀ input, ℳ.mem input closed → ℳ.mem input candidate :=
    fun candidate hCandidate input hInput =>
      ((hClosedSemantic input).mp hInput).2 candidate hCandidate

  -- 若 `reverse(output) ∈ closed`，则 `output` 已来自 `forward(closed)`。
  -- 否则从最小闭集中删去该点仍得到闭集，与最小性矛盾。
  have hForwardPreimage_of_reverse_mem
      (output : ℳ.Domain) (hOutput : ℳ.mem output target)
      (input : ℳ.Domain)
      (hReversePair : ℳ.PairMember 𝕀 output input reverse)
      (hInputClosed : ℳ.mem input closed) :
      ∃ predecessor,
        ℳ.mem predecessor closed ∧
          ℳ.PairMember 𝕀 predecessor output forward := by
    classical
    by_cases hExists :
        ∃ predecessor,
          ℳ.mem predecessor closed ∧
            ℳ.PairMember 𝕀 predecessor output forward
    · exact hExists
    · exfalso
      rcases KP.exists_singleton (modelsKP hZF) input with
        ⟨singleton, hSingleton⟩
      rcases KP.exists_difference
          (modelsKP hZF) singleton closed with
        ⟨reduced, hReduced⟩
      have hReducedClosed :
          ℳ.IsCantorBernsteinClosed 𝕀
            forward reverse source target reduced := by
        constructor
        · intro current hCurrent hNoReverse
          apply (hReduced current).mpr
          refine ⟨hClosedIs.1 current hCurrent hNoReverse, ?_⟩
          intro hCurrentSingleton
          have hCurrentEq :=
            (hSingleton current).mp hCurrentSingleton
          subst current
          exact hNoReverse ⟨output, hOutput, hReversePair⟩
        · intro current middle next hCurrent hForwardPair hNext
          have hCurrentClosed := ((hReduced current).mp hCurrent).1
          apply (hReduced next).mpr
          refine
            ⟨hClosedIs.2 current middle next
                hCurrentClosed hForwardPair hNext, ?_⟩
          intro hNextSingleton
          have hNextEq := (hSingleton next).mp hNextSingleton
          have hMiddleEq :=
            hReverseInjective middle output input
              (by simpa [hNextEq] using hNext)
              hReversePair
          subst middle
          exact hExists
            ⟨current, hCurrentClosed, hForwardPair⟩
      have hInputReduced :=
        hClosedMinimal reduced hReducedClosed input hInputClosed
      exact ((hReduced input).mp hInputReduced).2 <|
        (hSingleton input).mpr rfl

  -- 在闭集上使用正向单射，在补集上使用逆向单射的逆关系。
  let graphEnv : Env ℳ 3 := {
    bound :=
      Fin.cases forward <|
        Fin.cases reverse <|
          Fin.cases closed Fin.elim0
    free := fun _ => Classical.choice ℳ.nonempty
  }
  have hValueTotal :
      ∀ input, ℳ.mem input source →
        ∃ output,
          ℳ.IsCantorBernsteinValue 𝕀
            forward reverse closed input output := by
    intro input hInput
    by_cases hInputClosed : ℳ.mem input closed
    · rcases hForwardFunction.2.2 input hInput with
        ⟨output, _, hForwardPair⟩
      exact ⟨output, Or.inl ⟨hInputClosed, hForwardPair⟩⟩
    · have hReversePreimage :
          ∃ output, ℳ.mem output target ∧
            ℳ.PairMember 𝕀 output input reverse := by
        classical
        by_cases hExists :
            ∃ output, ℳ.mem output target ∧
              ℳ.PairMember 𝕀 output input reverse
        · exact hExists
        · exact False.elim <| hInputClosed <|
            hClosedIs.1 input hInput hExists
      rcases hReversePreimage with
        ⟨output, _, hReversePair⟩
      exact
        ⟨output, Or.inr ⟨hInputClosed, hReversePair⟩⟩
  have hValueUnique :
      ∀ input first second,
        ℳ.IsCantorBernsteinValue 𝕀
            forward reverse closed input first →
          ℳ.IsCantorBernsteinValue 𝕀
            forward reverse closed input second →
          first = second := by
    intro input first second hFirst hSecond
    rcases hFirst with
        ⟨hInputClosed, hFirstPair⟩ |
        ⟨hInputNotClosed, hFirstPair⟩
    · rcases hSecond with
          ⟨_, hSecondPair⟩ |
          ⟨hInputNotClosed, _⟩
      · exact
          hForwardFunction.1.2 input first second
            hFirstPair hSecondPair
      · exact False.elim <| hInputNotClosed hInputClosed
    · rcases hSecond with
          ⟨hInputClosed, _⟩ |
          ⟨_, hSecondPair⟩
      · exact False.elim <| hInputNotClosed hInputClosed
      · exact hReverseInjective first second input
          hFirstPair hSecondPair
  have hGraphTotal :
      ∀ input, ℳ.mem input source →
        ∃ pair,
          (Definitional.Project.BinarySchema.cantorBernsteinGraph 𝒞).denote
            graphEnv input pair := by
    intro input hInput
    rcases hValueTotal input hInput with
      ⟨output, hValue⟩
    rcases 𝕀.total input output with
      ⟨pair, hCode⟩
    refine ⟨pair, ?_⟩
    apply
      (Definitional.Project.Formula.denote_cantorBernsteinGraph_iff
        𝕀 graphEnv input pair).mpr
    exact ⟨output, hValue, hCode⟩
  have hGraphUnique :
      ∀ input, ℳ.mem input source →
        ∀ first second,
          (Definitional.Project.BinarySchema.cantorBernsteinGraph 𝒞).denote
              graphEnv input first →
            (Definitional.Project.BinarySchema.cantorBernsteinGraph 𝒞).denote
              graphEnv input second →
            first = second := by
    intro input _ first second hFirst hSecond
    rcases
        (Definitional.Project.Formula.denote_cantorBernsteinGraph_iff
          𝕀 graphEnv input first).mp hFirst with
      ⟨firstOutput, hFirstValue, hFirstCode⟩
    rcases
        (Definitional.Project.Formula.denote_cantorBernsteinGraph_iff
          𝕀 graphEnv input second).mp hSecond with
      ⟨secondOutput, hSecondValue, hSecondCode⟩
    have hOutputEq :=
      hValueUnique input firstOutput secondOutput
        hFirstValue hSecondValue
    subst secondOutput
    exact 𝕀.unique hFirstCode hSecondCode

  -- Replacement 把分片值关系收集为模型内部函数图。
  rcases exists_functionalImageOn hZF
      (Definitional.Project.BinarySchema.cantorBernsteinGraph 𝒞)
      graphEnv source hGraphTotal hGraphUnique with
    ⟨bijection, hBijectionMembers⟩
  have hPairMember (input output : ℳ.Domain) :
      ℳ.PairMember 𝕀 input output bijection ↔
        ℳ.mem input source ∧
          ℳ.IsCantorBernsteinValue 𝕀
            forward reverse closed input output := by
    constructor
    · rintro ⟨pair, hPairCode, hPairMem⟩
      rcases (hBijectionMembers pair).mp hPairMem with
        ⟨sourceInput, hSourceInput, hGraph⟩
      rcases
          (Definitional.Project.Formula.denote_cantorBernsteinGraph_iff
            𝕀 graphEnv sourceInput pair).mp hGraph with
        ⟨graphOutput, hValue, hGraphCode⟩
      rcases 𝕀.injective hPairCode hGraphCode with
        ⟨hInputEq, hOutputEq⟩
      subst sourceInput
      subst graphOutput
      exact ⟨hSourceInput, hValue⟩
    · rintro ⟨hInput, hValue⟩
      rcases 𝕀.total input output with
        ⟨pair, hPairCode⟩
      refine ⟨pair, hPairCode, (hBijectionMembers pair).mpr ?_⟩
      refine ⟨input, hInput, ?_⟩
      apply
        (Definitional.Project.Formula.denote_cantorBernsteinGraph_iff
          𝕀 graphEnv input pair).mpr
      exact ⟨output, hValue, hPairCode⟩

  -- 逐项验证函数图、定义域、值域、单射性与满射性。
  have hRelation : ℳ.IsSetRelation 𝕀 bijection := by
    intro pair hPair
    rcases (hBijectionMembers pair).mp hPair with
      ⟨input, _, hGraph⟩
    rcases
        (Definitional.Project.Formula.denote_cantorBernsteinGraph_iff
          𝕀 graphEnv input pair).mp hGraph with
      ⟨output, _, hCode⟩
    exact ⟨input, output, hCode⟩
  have hSetFunction : ℳ.IsSetFunction 𝕀 bijection := by
    refine ⟨hRelation, ?_⟩
    intro input first second hFirst hSecond
    exact
      hValueUnique input first second
        ((hPairMember input first).mp hFirst).2
        ((hPairMember input second).mp hSecond).2
  have hDomain : ℳ.IsDomainOf 𝕀 source bijection := by
    intro input
    constructor
    · intro hInput
      rcases hValueTotal input hInput with
        ⟨output, hValue⟩
      exact
        ⟨output, (hPairMember input output).mpr
          ⟨hInput, hValue⟩⟩
    · rintro ⟨output, hOutput⟩
      exact ((hPairMember input output).mp hOutput).1
  have hIntoTarget :
      ∀ input, ℳ.mem input source →
        ∃ output, ℳ.mem output target ∧
          ℳ.PairMember 𝕀 input output bijection := by
    intro input hInput
    rcases hValueTotal input hInput with
      ⟨output, hValue⟩
    have hOutput : ℳ.mem output target := by
      rcases hValue with
          ⟨_, hForwardPair⟩ |
          ⟨_, hReversePair⟩
      · exact output_mem_of_pairMember
          hForwardFunction hForwardPair
      · exact input_mem_of_pairMember
          hReverseFunction hReversePair
    exact
      ⟨output, hOutput,
        (hPairMember input output).mpr
          ⟨hInput, hValue⟩⟩
  have hInjective : ℳ.IsSetInjective 𝕀 bijection := by
    intro first second output hFirst hSecond
    have hFirstValue := ((hPairMember first output).mp hFirst).2
    have hSecondValue := ((hPairMember second output).mp hSecond).2
    rcases hFirstValue with
        ⟨hFirstClosed, hFirstPair⟩ |
        ⟨hFirstNotClosed, hFirstPair⟩
    · rcases hSecondValue with
          ⟨_, hSecondPair⟩ |
          ⟨hSecondNotClosed, hSecondPair⟩
      · exact hForwardInjective first second output
          hFirstPair hSecondPair
      · exact False.elim <| hSecondNotClosed <|
          hClosedIs.2 first output second
            hFirstClosed hFirstPair hSecondPair
    · rcases hSecondValue with
          ⟨hSecondClosed, hSecondPair⟩ |
          ⟨_, hSecondPair⟩
      · exact False.elim <| hFirstNotClosed <|
          hClosedIs.2 second output first
            hSecondClosed hSecondPair hFirstPair
      · exact hReverseFunction.1.2 output first second
          hFirstPair hSecondPair
  have hSurjective :
      ℳ.IsSetSurjectiveOnto 𝕀 bijection source target := by
    intro output hOutput
    by_cases hForwardImage :
        ∃ input, ℳ.mem input closed ∧
          ℳ.PairMember 𝕀 input output forward
    · rcases hForwardImage with
        ⟨input, hInputClosed, hForwardPair⟩
      have hInput := hClosedSubset input hInputClosed
      exact
        ⟨input, hInput,
          (hPairMember input output).mpr
            ⟨hInput, Or.inl
              ⟨hInputClosed, hForwardPair⟩⟩⟩
    · rcases hReverseFunction.2.2 output hOutput with
        ⟨input, hInput, hReversePair⟩
      have hInputNotClosed : ¬ ℳ.mem input closed := by
        intro hInputClosed
        exact hForwardImage <|
          hForwardPreimage_of_reverse_mem
            output hOutput input hReversePair hInputClosed
      exact
        ⟨input, hInput,
          (hPairMember input output).mpr
            ⟨hInput, Or.inr
              ⟨hInputNotClosed, hReversePair⟩⟩⟩
  exact
    ⟨bijection,
      ⟨⟨⟨hSetFunction, hDomain, hIntoTarget⟩,
          hInjective⟩,
        hSurjective⟩⟩

/-- Cantor--Bernstein 定理：双向基数不大于推出等势。 -/
theorem equinumerous_of_cardinalLessOrEqual
    {ℳ : Structure.{u}} (hZF : ℳ.Models SetTheory.ZF)
    {𝒞 : Definitional.Project.OrderedPairConvention}
    (𝕀 : 𝒞.Interpretation ℳ)
    {left right : ℳ.Domain}
    (hLeft : ℳ.CardinalLessOrEqual 𝕀 left right)
    (hRight : ℳ.CardinalLessOrEqual 𝕀 right left) :
    ℳ.Equinumerous 𝕀 left right := by
  rcases hLeft with ⟨forward, hForward⟩
  rcases hRight with ⟨reverse, hReverse⟩
  exact equinumerous_of_injections
    hZF 𝕀 hForward hReverse

end ZF

end SetTheory
end YesMetaZFC
