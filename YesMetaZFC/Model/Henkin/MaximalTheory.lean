import YesMetaZFC.Model.Henkin.Construction
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution

/-!
# 内在 Henkin 完成理论的演绎闭包

本模块把 `Henkin.Result` 的有限一致性与逐闭句决定性组合成最大一致理论接口。公式、
项、排序和作用域均由索引语法保证，因此这里不再出现 `Admissible`、自由变量编号或
close/open 新鲜性旁证。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin
namespace Result

open HenkinSignature

universe u v w

variable {σ : Signature.{u, v, w}}
variable [DecidableEq σ.SortSymbol]
variable {T : Theory (HSignature σ)} {background : Background T}

/-! ## 最大一致闭包 -/

omit [DecidableEq σ.SortSymbol] in
/-- 完成候选不可能同时包含闭句及其否定。 -/
theorem not_both (result : Result background)
    {sentence : Sentence (HSignature σ)}
    (hSentence : result.candidate sentence)
    (hNegated : result.candidate (.neg sentence)) : False := by
  have hConsistent :
      Derives.Consistent T [sentence, .neg sentence] :=
    result.wf.wf_consistent _ (by
      intro target hTarget
      rcases List.mem_cons.mp hTarget with rfl | hTarget
      · exact hSentence
      · have hEqual : target = .neg sentence := by
          simpa using hTarget
        subst target
        exact hNegated)
  apply hConsistent
  exact Derives.neg_elim
    (Derives.assumption (formula := sentence) List.mem_cons_self)
    (Derives.assumption (formula := .neg sentence)
      (List.mem_cons_of_mem sentence List.mem_cons_self))

omit [DecidableEq σ.SortSymbol] in
/-- 完成候选对背景理论上的有限闭句推导封闭。 -/
theorem contains_of_derives (result : Result background)
    {Γ : Context (HSignature σ) []}
    {sentence : Sentence (HSignature σ)}
    (hDerives : Derives T Γ sentence)
    (hΓ : ∀ target, target ∈ Γ → result.candidate target) :
    result.candidate sentence := by
  rcases result.decides sentence with hSentence | hNegated
  · exact hSentence
  · have hConsistent :
        Derives.Consistent T (.neg sentence :: Γ) :=
      result.wf.wf_consistent _ (by
        intro target hTarget
        rcases List.mem_cons.mp hTarget with rfl | hTarget
        · exact hNegated
        · exact hΓ target hTarget)
    exact False.elim <| hConsistent <| Derives.neg_elim
      (hDerives.context_weaken (fun target hTarget =>
        List.mem_cons_of_mem (.neg sentence) hTarget))
      (Derives.assumption (formula := .neg sentence)
        List.mem_cons_self)

omit [DecidableEq σ.SortSymbol] in
/-- 背景理论中的每条闭句都进入完成候选。 -/
theorem contains_background (result : Result background)
    {sentence : Sentence (HSignature σ)}
    (hSentence : T sentence) : result.candidate sentence :=
  result.contains_of_derives (Γ := [])
    (Derives.theory_axiom hSentence) (by
      intro target hTarget
      cases hTarget)

omit [DecidableEq σ.SortSymbol] in
/-- 真闭句属于完成候选。 -/
theorem contains_truth (result : Result background) :
    result.candidate (.truth : Sentence (HSignature σ)) :=
  result.contains_of_derives (Γ := []) Derives.truth_intro (by
    intro target hTarget
    cases hTarget)

omit [DecidableEq σ.SortSymbol] in
/-- 假闭句不属于完成候选。 -/
theorem not_contains_falsum (result : Result background) :
    ¬ result.candidate (.falsum : Sentence (HSignature σ)) := by
  intro hFalsum
  have hConsistent :
      Derives.Consistent T [(.falsum : Sentence (HSignature σ))] :=
    result.wf.wf_consistent _ (by
      intro target hTarget
      have hEqual : target = (.falsum : Sentence (HSignature σ)) := by
        simpa using hTarget
      subst target
      exact hFalsum)
  exact hConsistent
    (Derives.assumption (formula :=
      (.falsum : Sentence (HSignature σ))) List.mem_cons_self)

omit [DecidableEq σ.SortSymbol] in
/-- 最大一致候选中的否定成员关系就是元层否定。 -/
theorem neg_mem_iff (result : Result background)
    {sentence : Sentence (HSignature σ)} :
    result.candidate (.neg sentence) ↔
      ¬ result.candidate sentence := by
  constructor
  · intro hNegated hSentence
    exact result.not_both hSentence hNegated
  · intro hNotSentence
    rcases result.decides sentence with hSentence | hNegated
    · exact False.elim (hNotSentence hSentence)
    · exact hNegated

/-! ## 命题连接词 -/

omit [DecidableEq σ.SortSymbol] in
/-- 合取的候选成员关系逐分量分解。 -/
theorem conj_mem_iff (result : Result background)
    {left right : Sentence (HSignature σ)} :
    result.candidate (.conj left right) ↔
      result.candidate left ∧ result.candidate right := by
  constructor
  · intro hConjunction
    constructor
    · exact result.contains_of_derives
        (Γ := [Formula.conj left right])
        (Derives.conj_elim_left
          (Derives.assumption (formula := .conj left right)
            List.mem_cons_self)) (by
          intro target hTarget
          have hEqual : target = .conj left right := by
            simpa using hTarget
          subst target
          exact hConjunction)
    · exact result.contains_of_derives
        (Γ := [Formula.conj left right])
        (Derives.conj_elim_right
          (Derives.assumption (formula := .conj left right)
            List.mem_cons_self)) (by
          intro target hTarget
          have hEqual : target = .conj left right := by
            simpa using hTarget
          subst target
          exact hConjunction)
  · rintro ⟨hLeft, hRight⟩
    exact result.contains_of_derives (Γ := [left, right])
      (Derives.conj_intro
        (Derives.assumption (formula := left) List.mem_cons_self)
        (Derives.assumption (formula := right)
          (List.mem_cons_of_mem left List.mem_cons_self))) (by
        intro target hTarget
        rcases List.mem_cons.mp hTarget with rfl | hTarget
        · exact hLeft
        · have hEqual : target = right := by
            simpa using hTarget
          subst target
          exact hRight)

omit [DecidableEq σ.SortSymbol] in
/-- 析取的候选成员关系分解为元层析取。 -/
theorem disj_mem_iff (result : Result background)
    {left right : Sentence (HSignature σ)} :
    result.candidate (.disj left right) ↔
      result.candidate left ∨ result.candidate right := by
  constructor
  · intro hDisjunction
    by_cases hLeft : result.candidate left
    · exact Or.inl hLeft
    · right
      by_cases hRight : result.candidate right
      · exact hRight
      · have hNegLeft : result.candidate (.neg left) :=
          result.neg_mem_iff.mpr hLeft
        have hNegRight : result.candidate (.neg right) :=
          result.neg_mem_iff.mpr hRight
        have hConsistent : Derives.Consistent T
            [.disj left right, .neg left, .neg right] :=
          result.wf.wf_consistent _ (by
            intro target hTarget
            rcases List.mem_cons.mp hTarget with rfl | hTarget
            · exact hDisjunction
            · rcases List.mem_cons.mp hTarget with rfl | hTarget
              · exact hNegLeft
              · have hEqual : target = .neg right := by
                  simpa using hTarget
                subst target
                exact hNegRight)
        exfalso
        apply hConsistent
        exact Derives.disj_elim
          (Derives.assumption (formula := .disj left right)
            List.mem_cons_self)
          (Derives.neg_elim
            (Derives.assumption (formula := left) List.mem_cons_self)
            (Derives.assumption (formula := .neg left) (by simp)))
          (Derives.neg_elim
            (Derives.assumption (formula := right) List.mem_cons_self)
            (Derives.assumption (formula := .neg right) (by simp)))
  · rintro (hLeft | hRight)
    · exact result.contains_of_derives (Γ := [left])
        (Derives.disj_intro_left
          (Derives.assumption (formula := left) List.mem_cons_self)) (by
          intro target hTarget
          have hEqual : target = left := by simpa using hTarget
          subst target
          exact hLeft)
    · exact result.contains_of_derives (Γ := [right])
        (Derives.disj_intro_right
          (Derives.assumption (formula := right) List.mem_cons_self)) (by
          intro target hTarget
          have hEqual : target = right := by simpa using hTarget
          subst target
          exact hRight)

omit [DecidableEq σ.SortSymbol] in
/-- 蕴含的候选成员关系就是候选成员间的元层函数。 -/
theorem imp_mem_iff (result : Result background)
    {left right : Sentence (HSignature σ)} :
    result.candidate (.imp left right) ↔
      (result.candidate left → result.candidate right) := by
  constructor
  · intro hImplication hLeft
    exact result.contains_of_derives
      (Γ := [Formula.imp left right, left])
      (Derives.imp_elim
        (Derives.assumption (formula := .imp left right)
          List.mem_cons_self)
        (Derives.assumption (formula := left)
          (List.mem_cons_of_mem (Formula.imp left right)
            List.mem_cons_self))) (by
        intro target hTarget
        rcases List.mem_cons.mp hTarget with rfl | hTarget
        · exact hImplication
        · have hEqual : target = left := by simpa using hTarget
          subst target
          exact hLeft)
  · intro hSemantic
    rcases result.decides left with hLeft | hNegLeft
    · have hRight := hSemantic hLeft
      exact result.contains_of_derives (Γ := [right])
        (Derives.imp_intro
          (Derives.assumption (formula := right) (by simp))) (by
          intro target hTarget
          have hEqual : target = right := by simpa using hTarget
          subst target
          exact hRight)
    · exact result.contains_of_derives (Γ := [Formula.neg left])
        (Derives.imp_intro
          (Derives.falsum_elim
            (Derives.neg_elim
              (Derives.assumption (formula := left) List.mem_cons_self)
              (Derives.assumption (formula := .neg left) (by simp))))) (by
          intro target hTarget
          have hEqual : target = .neg left := by simpa using hTarget
          subst target
          exact hNegLeft)

omit [DecidableEq σ.SortSymbol] in
/-- 双条件的候选成员关系就是两侧成员关系的元层等价。 -/
theorem iff_mem_iff (result : Result background)
    {left right : Sentence (HSignature σ)} :
    result.candidate (.iff left right) ↔
      (result.candidate left ↔ result.candidate right) := by
  constructor
  · intro hIff
    constructor
    · intro hLeft
      exact result.contains_of_derives
        (Γ := [Formula.iff left right, left])
        (Derives.iff_elim_left
          (Derives.assumption (formula := .iff left right)
            List.mem_cons_self)
          (Derives.assumption (formula := left)
            (List.mem_cons_of_mem (Formula.iff left right)
              List.mem_cons_self))) (by
          intro target hTarget
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hIff
          · have hEqual : target = left := by simpa using hTarget
            subst target
            exact hLeft)
    · intro hRight
      exact result.contains_of_derives
        (Γ := [Formula.iff left right, right])
        (Derives.iff_elim_right
          (Derives.assumption (formula := .iff left right)
            List.mem_cons_self)
          (Derives.assumption (formula := right)
            (List.mem_cons_of_mem (Formula.iff left right)
              List.mem_cons_self))) (by
          intro target hTarget
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hIff
          · have hEqual : target = right := by simpa using hTarget
            subst target
            exact hRight)
  · intro hSemantic
    rcases result.decides left with hLeft | hNegLeft
    · have hRight := hSemantic.mp hLeft
      exact result.contains_of_derives (Γ := [left, right])
        (Derives.iff_intro
          (Derives.assumption (formula := right) (by simp))
          (Derives.assumption (formula := left) (by simp))) (by
          intro target hTarget
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hLeft
          · have hEqual : target = right := by simpa using hTarget
            subst target
            exact hRight)
    · have hNotRight : ¬ result.candidate right := by
        intro hRight
        exact result.not_both (hSemantic.mpr hRight) hNegLeft
      have hNegRight : result.candidate (.neg right) :=
        result.neg_mem_iff.mpr hNotRight
      exact result.contains_of_derives
        (Γ := [Formula.neg left, Formula.neg right])
        (Derives.iff_intro
          (Derives.falsum_elim
            (Derives.neg_elim
              (Derives.assumption (formula := left) List.mem_cons_self)
              (Derives.assumption (formula := .neg left) (by simp))))
          (Derives.falsum_elim
            (Derives.neg_elim
              (Derives.assumption (formula := right) List.mem_cons_self)
              (Derives.assumption (formula := .neg right) (by simp))))) (by
          intro target hTarget
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hNegLeft
          · have hEqual : target = .neg right := by simpa using hTarget
            subst target
            exact hNegRight)

/-! ## 等词闭包 -/

omit [DecidableEq σ.SortSymbol] in
/-- 任意内在类型正确的闭项与自身的等词属于完成候选。 -/
theorem equal_mem_refl (result : Result background)
    {sort : σ.SortSymbol}
    (term : OpenTerm (HSignature σ) [] sort) :
    result.candidate (.equal term term) :=
  result.contains_of_derives (Γ := []) (Derives.eq_refl term) (by
    intro target hTarget
    cases hTarget)

omit [DecidableEq σ.SortSymbol] in
/-- 完成候选对核心 Leibniz 等词替换规则封闭。 -/
theorem substitute_mem_of_equal_mem (result : Result background)
    {sort : σ.SortSymbol}
    {left right : OpenTerm (HSignature σ) [] sort}
    {body : Formula (HSignature σ) [sort] []}
    (hEquality : result.candidate (.equal left right))
    (hSource : result.candidate (body.instantiateTop left)) :
    result.candidate (body.instantiateTop right) :=
  result.contains_of_derives
    (Γ := [Formula.equal left right, body.instantiateTop left])
    (Derives.eq_subst
      (Derives.assumption (formula := .equal left right)
        List.mem_cons_self)
      (Derives.assumption (formula := body.instantiateTop left)
        (List.mem_cons_of_mem (Formula.equal left right)
          List.mem_cons_self))) (by
      intro target hTarget
      rcases List.mem_cons.mp hTarget with rfl | hTarget
      · exact hEquality
      · have hEqual : target = body.instantiateTop left := by
          simpa using hTarget
        subst target
        exact hSource)

omit [DecidableEq σ.SortSymbol] in
/-- 完成候选中的等词成员关系具有对称性。 -/
theorem equal_mem_symm (result : Result background)
    {sort : σ.SortSymbol}
    {left right : OpenTerm (HSignature σ) [] sort}
    (hEquality : result.candidate (.equal left right)) :
    result.candidate (.equal right left) :=
  result.contains_of_derives (Γ := [Formula.equal left right])
    (Derives.eq_symm
      (Derives.assumption (formula := .equal left right)
        List.mem_cons_self)) (by
      intro target hTarget
      have hEqual : target = .equal left right := by
        simpa using hTarget
      subst target
      exact hEquality)

omit [DecidableEq σ.SortSymbol] in
/-- 完成候选中的等词成员关系具有传递性。 -/
theorem equal_mem_trans (result : Result background)
    {sort : σ.SortSymbol}
    {left middle right : OpenTerm (HSignature σ) [] sort}
    (hLeftMiddle : result.candidate (.equal left middle))
    (hMiddleRight : result.candidate (.equal middle right)) :
    result.candidate (.equal left right) :=
  result.contains_of_derives
    (Γ := [Formula.equal left middle, Formula.equal middle right])
    (Derives.eq_trans
      (Derives.assumption (formula := .equal left middle)
        List.mem_cons_self)
      (Derives.assumption (formula := .equal middle right)
        (List.mem_cons_of_mem (Formula.equal left middle)
          List.mem_cons_self))) (by
      intro target hTarget
      rcases List.mem_cons.mp hTarget with rfl | hTarget
      · exact hLeftMiddle
      · have hEqual : target = .equal middle right := by
          simpa using hTarget
        subst target
        exact hMiddleRight)

/-! ## 量词闭包 -/

omit [DecidableEq σ.SortSymbol] in
/-- 全称式的否定推出否定体的存在式。 -/
theorem neg_forall_mem_imp_exists_neg_mem
    (result : Result background)
    {sort : σ.SortSymbol}
    {body : Formula (HSignature σ) [sort] []}
    (hNegForall : result.candidate (.neg (.forallE sort body))) :
    result.candidate (.existsE sort (.neg body)) := by
  let opened : OpenFormula (HSignature σ) [sort] :=
    Formula.openBoundTop (σ := HSignature σ) sort body
  let universal : Sentence (HSignature σ) := .forallE sort body
  let counterexample : Sentence (HSignature σ) :=
    .existsE sort (.neg body)
  have hDerives : Derives T [.neg universal] counterexample := by
    apply Derives.by_contradiction
    have hOpened : Derives T
        (FreshVariable.extendContext (σ := HSignature σ) sort
          [.neg counterexample, .neg universal]) opened := by
      apply Derives.by_contradiction
      have hNegOpened : Derives T
          (.neg opened ::
            FreshVariable.extendContext (σ := HSignature σ) sort
              [.neg counterexample, .neg universal])
          (.neg opened) :=
        Derives.assumption (formula := .neg opened) List.mem_cons_self
      have hCounterexample : Derives T
          (.neg opened ::
            FreshVariable.extendContext (σ := HSignature σ) sort
              [.neg counterexample, .neg universal])
          (Formula.weakenFree (σ := HSignature σ) sort
            counterexample) := by
        have hOpenedAbstract :
            (Formula.neg opened).abstractFreeTop =
              Formula.neg body := by
          change Formula.neg opened.abstractFreeTop = Formula.neg body
          simp [opened]
        simpa only [Formula.existsFreeTop, hOpenedAbstract,
          counterexample] using
          (Derives.exists_intro_newest hNegOpened)
      have hNegCounterexample : Derives T
          (.neg opened ::
            FreshVariable.extendContext (σ := HSignature σ) sort
              [.neg counterexample, .neg universal])
          (Formula.weakenFree (σ := HSignature σ) sort
            (Formula.neg counterexample)) :=
        Derives.assumption
          (formula := Formula.weakenFree (σ := HSignature σ) sort
            (Formula.neg counterexample)) (by
            simp [FreshVariable.extendContext])
      exact Derives.neg_elim hCounterexample hNegCounterexample
    have hUniversal : Derives T
        [.neg counterexample, .neg universal] universal := by
      simpa [opened, universal] using Derives.forall_intro hOpened
    exact Derives.neg_elim hUniversal
      (Derives.assumption (formula := Formula.neg universal)
        (List.mem_cons_of_mem (Formula.neg counterexample)
          List.mem_cons_self))
  exact result.contains_of_derives (Γ := [Formula.neg universal])
    hDerives (by
    intro target hTarget
    have hEqual : target = Formula.neg universal := by
      simpa using hTarget
    subst target
    simpa [universal] using hNegForall)

omit [DecidableEq σ.SortSymbol] in
/-- 存在量词属于候选，当且仅当某个内在类型正确的闭项实例属于候选。 -/
theorem exists_mem_iff (result : Result background)
    {sort : σ.SortSymbol}
    {body : Formula (HSignature σ) [sort] []} :
    result.candidate (.existsE sort body) ↔
      ∃ term : OpenTerm (HSignature σ) [] sort,
        result.candidate (body.instantiateTop term) := by
  constructor
  · intro hExists
    rcases result.witnessed sort body hExists with
      ⟨index, hWitness⟩
    exact ⟨witnessTerm (σ := σ) sort index, hWitness⟩
  · rintro ⟨term, hInstance⟩
    exact result.contains_of_derives
      (Γ := [body.instantiateTop term])
      (Derives.exists_intro term
        (Derives.assumption (formula := body.instantiateTop term)
          List.mem_cons_self)) (by
        intro target hTarget
        have hEqual : target = body.instantiateTop term := by
          simpa using hTarget
        subst target
        exact hInstance)

omit [DecidableEq σ.SortSymbol] in
/-- 全称量词属于候选，当且仅当每个内在类型正确的闭项实例都属于候选。 -/
theorem forall_mem_iff (result : Result background)
    {sort : σ.SortSymbol}
    {body : Formula (HSignature σ) [sort] []} :
    result.candidate (.forallE sort body) ↔
      ∀ term : OpenTerm (HSignature σ) [] sort,
        result.candidate (body.instantiateTop term) := by
  constructor
  · intro hForall term
    exact result.contains_of_derives
      (Γ := [Formula.forallE sort body])
      (Derives.forall_elim term
        (Derives.assumption (formula :=
          (Formula.forallE sort body : Sentence (HSignature σ)))
          List.mem_cons_self)) (by
        intro target hTarget
        have hEqual : target =
            (Formula.forallE sort body : Sentence (HSignature σ)) := by
          simpa using hTarget
        subst target
        exact hForall)
  · intro hInstances
    rcases result.decides
        (Formula.forallE sort body : Sentence (HSignature σ)) with
      hForall | hNegForall
    · exact hForall
    · have hExistsNeg :
          result.candidate (.existsE sort (.neg body)) :=
        result.neg_forall_mem_imp_exists_neg_mem hNegForall
      rcases result.witnessed sort (.neg body) hExistsNeg with
        ⟨index, hNegInstance⟩
      let term : OpenTerm (HSignature σ) [] sort :=
        witnessTerm (σ := σ) sort index
      have hInstance := hInstances term
      have hNegInstance :
          result.candidate (.neg (body.instantiateTop term)) := by
        simpa [term] using hNegInstance
      exact False.elim (result.not_both hInstance hNegInstance)

end Result
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
