import YesMetaZFC.Model.Henkin.ProofTheory
import YesMetaZFC.Model.Henkin.Transport

/-!
# 内在闭句上的 Henkin 完成

本模块只使用索引语法中的闭句、标准 Hilbert 推导和显式 Henkin 常量。旧实现中的
`Admissible`、raw 公式、自然数自由变量新鲜性与 close/open 桥接全部删除。

新见证编号由有限语法树的绝对结构上界直接给出。见证一致性证明把新常量消去为
规范 fresh 变量，再调用标准 `exists_elim`；没有良构、作用域或编号避让义务。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin

open HenkinSignature

universe u v w

variable {σ : Signature.{u, v, w}}
variable [DecidableEq σ.SortSymbol]

/-! ## 见证自由背景 -/

/--
Henkin 构造的背景理论。理论成员已经由 `Theory` 保证为闭句；额外只要求一致性以及
不含 Henkin 见证常量。
-/
structure Background (T : Theory (HSignature σ)) : Prop where
  consistent : Derives.Consistent T (free := []) []
  avoidsWitness :
    ∀ {sentence : Sentence (HSignature σ)}, T sentence →
      ∀ sort index, ¬ Formula.usesWitness sort index sentence

namespace Background

omit [DecidableEq σ.SortSymbol] in
/-- 背景理论避开任意指定见证，直接供推导消去器消费。 -/
theorem avoids {T : Theory (HSignature σ)}
    (background : Background T)
    (sort : σ.SortSymbol) (index : Nat)
    {sentence : Sentence (HSignature σ)} (hSentence : T sentence) :
    ¬ Formula.usesWitness sort index sentence :=
  background.avoidsWitness hSentence sort index

end Background

/-! ## 有限上下文的绝对见证上界 -/

namespace Context

/-- 有限闭句上下文中全部 Henkin 见证编号的严格上界。 -/
def witnessBound : Context (HSignature σ) [] → Nat
  | [] => 0
  | sentence :: rest =>
      Nat.max (Formula.witnessBound sentence) (witnessBound rest)

omit [DecidableEq σ.SortSymbol] in
/-- 上下文成员的公式上界不超过整个上下文上界。 -/
theorem formula_witnessBound_le
    {Γ : Context (HSignature σ) []}
    {sentence : Sentence (HSignature σ)}
    (hSentence : sentence ∈ Γ) :
    Formula.witnessBound sentence ≤ witnessBound Γ := by
  induction Γ with
  | nil =>
      cases hSentence
  | cons head rest ih =>
      rcases List.mem_cons.mp hSentence with rfl | hRest
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hRest) (Nat.le_max_right _ _)

/-- 针对一个焦点公式与当前有限上下文计算下一枚全局新见证编号。 -/
def freshWitnessIndex
    (focus : Sentence (HSignature σ))
    (Γ : Context (HSignature σ) []) : Nat :=
  Nat.max (Formula.witnessBound focus) (witnessBound Γ)

omit [DecidableEq σ.SortSymbol] in
/-- 焦点公式不含其计算出的新见证编号。 -/
theorem focus_avoids_freshWitnessIndex
    (focus : Sentence (HSignature σ))
    (Γ : Context (HSignature σ) [])
    (sort : σ.SortSymbol) :
    ¬ Formula.usesWitness sort (freshWitnessIndex focus Γ) focus :=
  Formula.not_usesWitness_of_witnessBound_le
    sort (freshWitnessIndex focus Γ) focus (Nat.le_max_left _ _)

omit [DecidableEq σ.SortSymbol] in
/-- 当前上下文的每个成员都不含计算出的新见证编号。 -/
theorem member_avoids_freshWitnessIndex
    (focus : Sentence (HSignature σ))
    (Γ : Context (HSignature σ) [])
    (sort : σ.SortSymbol)
    {sentence : Sentence (HSignature σ)}
    (hSentence : sentence ∈ Γ) :
    ¬ Formula.usesWitness sort (freshWitnessIndex focus Γ) sentence :=
  Formula.not_usesWitness_of_witnessBound_le
    sort (freshWitnessIndex focus Γ) sentence
    (Nat.le_trans (formula_witnessBound_le hSentence)
      (Nat.le_max_right _ _))

end Context

/-! ## 新见证实例的一致性 -/

/--
若一个存在闭句已在一致上下文中，且指定见证常量不出现在背景、上下文和量词体中，
则加入该见证实例仍保持一致。
-/
theorem consistent_witness_instance
    {T : Theory (HSignature σ)}
    (background : Background T)
    {Γ : Context (HSignature σ) []}
    (hConsistent : Derives.Consistent T Γ)
    {sort : σ.SortSymbol} {index : Nat}
    {body : Formula (HSignature σ) [sort] []}
    (hContextAvoids :
      ∀ sentence, sentence ∈ Γ →
        ¬ Formula.usesWitness sort index sentence)
    (hBodyAvoids : ¬ Formula.usesWitness sort index body)
    (hExists : (Formula.existsE sort body : Sentence (HSignature σ)) ∈ Γ) :
    Derives.Consistent T
      (body.instantiateTop (witnessTerm (σ := σ) sort index) :: Γ) := by
  intro hFalse
  have hTransported :=
    Derives.eliminatePersistentWitness (σ := σ) sort index
      (fun hTheory => background.avoids sort index hTheory) hFalse
  have hContext :
      (body.instantiateTop (witnessTerm (σ := σ) sort index) :: Γ).map
          (Formula.eliminatePersistentWitness (σ := σ) sort index) =
        Formula.openBoundTop (σ := HSignature σ) sort body ::
          FreshVariable.extendContext (σ := HSignature σ) sort Γ := by
    change
      Formula.eliminatePersistentWitness (σ := σ) sort index
          (body.instantiateTop (witnessTerm (σ := σ) sort index)) ::
          Γ.map (Formula.eliminatePersistentWitness (σ := σ) sort index) =
        Formula.openBoundTop (σ := HSignature σ) sort body ::
          FreshVariable.extendContext (σ := HSignature σ) sort Γ
    rw [Formula.eliminatePersistentWitness_witnessInstance
        (σ := σ) sort index body hBodyAvoids,
      _root_.YesMetaZFC.Logic.FirstOrder.Context.eliminatePersistentWitness_sentences
        (σ := σ) sort index Γ hContextAvoids]
  rw [hContext] at hTransported
  have hCase :
      Derives T
        (Formula.openBoundTop (σ := HSignature σ) sort body ::
          FreshVariable.extendContext (σ := HSignature σ) sort Γ)
        (Formula.weakenFree (σ := HSignature σ) sort
          (Formula.falsum : Sentence (HSignature σ))) := by
    simpa using hTransported
  have hExistential :
      Derives T Γ
        (Formula.existsFreeTop (σ := HSignature σ) sort
          (Formula.openBoundTop (σ := HSignature σ) sort body)) := by
    simpa using (Derives.assumption_of_mem (T := T) hExists)
  apply hConsistent
  exact Derives.exists_elim hExistential hCase

/--
有限上下文中的存在闭句总有一个由绝对结构上界计算出的新见证实例，并保持一致。
-/
theorem consistent_fresh_witness_instance
    {T : Theory (HSignature σ)}
    (background : Background T)
    {Γ : Context (HSignature σ) []}
    (hConsistent : Derives.Consistent T Γ)
    {sort : σ.SortSymbol}
    {body : Formula (HSignature σ) [sort] []}
    (hExists : (Formula.existsE sort body : Sentence (HSignature σ)) ∈ Γ) :
    let index := Context.freshWitnessIndex
      (Formula.existsE sort body : Sentence (HSignature σ)) Γ
    Derives.Consistent T
      (body.instantiateTop (witnessTerm (σ := σ) sort index) :: Γ) := by
  let existential : Sentence (HSignature σ) := Formula.existsE sort body
  let index := Context.freshWitnessIndex existential Γ
  have hFocusAvoids :
      ¬ Formula.usesWitness sort index existential :=
    Context.focus_avoids_freshWitnessIndex existential Γ sort
  have hBodyAvoids : ¬ Formula.usesWitness sort index body := by
    simpa [existential, Formula.usesWitness] using hFocusAvoids
  exact consistent_witness_instance background hConsistent
    (fun sentence hSentence =>
      Context.member_avoids_freshWitnessIndex existential Γ sort hSentence)
    hBodyAvoids hExists

/-! ## 内在闭句调度与有限阶段 -/

/--
Henkin 构造的公平闭句调度。闭句的良构性已经由类型保证；公平性只要求每条闭句在任意
阶段之后仍会再次出现。
-/
structure Schedule (σ : Signature.{u, v, w}) where
  sentence : Nat → Sentence (HSignature σ)
  cofinal :
    ∀ target : Sentence (HSignature σ),
      ∀ start, ∃ index, start ≤ index ∧ sentence index = target

/-- Henkin 构造的有限闭句阶段。 -/
structure Stage {T : Theory (HSignature σ)} (background : Background T) where
  sentences : List (Sentence (HSignature σ))
  consistent : Derives.Consistent T sentences

namespace Stage

/-- 任意一致的有限闭句上下文都可直接作为构造种子。 -/
def seed {T : Theory (HSignature σ)}
    (background : Background T)
    (sentences : List (Sentence (HSignature σ)))
    (hConsistent : Derives.Consistent T sentences) :
    Stage background :=
  ⟨sentences, hConsistent⟩

/-- 空上下文是默认初始阶段。 -/
def initial {T : Theory (HSignature σ)}
    (background : Background T) : Stage background :=
  seed background [] background.consistent

/-- 若闭句不可推出，则其否定给出一致反例种子。 -/
def refutation_seed {T : Theory (HSignature σ)}
    (background : Background T)
    (sentence : Sentence (HSignature σ))
    (hNotDerives : ¬ Derives T [] sentence) :
    Stage background :=
  seed background [.neg sentence] (by
    intro hFalse
    exact hNotDerives (Derives.by_contradiction hFalse))

omit [DecidableEq σ.SortSymbol] in
/-- 有限阶段诱导的闭句理论携带 Lindenbaum 所需的有限一致性。 -/
theorem wf {T : Theory (HSignature σ)} {background : Background T}
    (stage : Stage background) :
    Derives.WF_Candidate T (Theory.ofList stage.sentences) :=
  ⟨Derives.FinitelyConsistent.ofList_iff.mpr stage.consistent⟩

/-- 把理论插入证书搬回列表头插入表示。 -/
def of_insert {T : Theory (HSignature σ)}
    {background : Background T}
    (current : Stage background)
    {sentence : Sentence (HSignature σ)}
    (hCandidate : Derives.WF_Candidate T
      (Theory.insert sentence (Theory.ofList current.sentences))) :
    Stage background :=
  seed background (sentence :: current.sentences) (by
    apply Derives.FinitelyConsistent.ofList_iff.mp
    simpa using hCandidate.wf_consistent)

end Stage

/-! ## 单步 Lindenbaum/Henkin 扩张 -/

/-- 一个阶段对指定闭句完成一次保持一致的决定，并在需要时加入见证。 -/
structure Extension {T : Theory (HSignature σ)}
    {background : Background T}
    (current : Stage background)
    (sentence : Sentence (HSignature σ)) where
  next : Stage background
  subset :
    ∀ target, target ∈ current.sentences → target ∈ next.sentences
  decision :
    sentence ∈ next.sentences ∨ .neg sentence ∈ next.sentences
  witness :
    ∀ sort (body : Formula (HSignature σ) [sort] []),
      sentence = .existsE sort body →
        sentence ∈ current.sentences →
          ∃ index,
            body.instantiateTop (witnessTerm (σ := σ) sort index) ∈
              next.sentences

namespace Extension

omit [DecidableEq σ.SortSymbol] in
/-- 若负分支保持有限一致，则当前阶段尚未包含被否定的闭句。 -/
theorem not_mem_of_negative
    {T : Theory (HSignature σ)}
    {background : Background T}
    (current : Stage background)
    {sentence : Sentence (HSignature σ)}
    (hNegative : Derives.WF_Candidate T
      (Theory.insert (.neg sentence) (Theory.ofList current.sentences))) :
    sentence ∉ current.sentences := by
  intro hSentence
  have hConsistent :
      Derives.Consistent T [sentence, .neg sentence] :=
    hNegative.wf_consistent _ (by
      intro target hTarget
      rcases List.mem_cons.mp hTarget with rfl | hTarget
      · exact Or.inr hSentence
      · have hNegated : target = .neg sentence := by
          simpa using hTarget
        subst target
        exact Or.inl rfl)
  apply hConsistent
  exact Derives.neg_elim
    (Derives.assumption (formula := sentence) List.mem_cons_self)
    (Derives.assumption (formula := .neg sentence)
      (List.mem_cons_of_mem sentence List.mem_cons_self))

/-- 正分支不是存在式时，只需保留 Lindenbaum 插入结果。 -/
private def positive_without_witness
    {T : Theory (HSignature σ)}
    {background : Background T}
    (current : Stage background)
    {sentence : Sentence (HSignature σ)}
    (hPositive : Derives.WF_Candidate T
      (Theory.insert sentence (Theory.ofList current.sentences)))
    (hNotExists :
      ∀ sort (body : Formula (HSignature σ) [sort] []),
        sentence ≠ .existsE sort body) :
    Extension current sentence :=
  let next := Stage.of_insert current hPositive
  {
    next := next
    subset := by
      intro target hTarget
      exact List.mem_cons_of_mem sentence hTarget
    decision := Or.inl List.mem_cons_self
    witness := by
      intro sort body hShape _
      exact False.elim (hNotExists sort body hShape)
  }

/-- 每条闭句都能完成一次保持一致的 Lindenbaum/Henkin 扩张。 -/
theorem nonempty
    {T : Theory (HSignature σ)}
    {background : Background T}
    (current : Stage background)
    (sentence : Sentence (HSignature σ)) :
    Nonempty (Extension current sentence) := by
  classical
  rcases current.wf.wf_extend_or_neg sentence with hPositive | hNegative
  · cases sentence with
    | falsum =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort body hShape
          cases hShape)⟩
    | truth =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort body hShape
          cases hShape)⟩
    | rel relation arguments =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort body hShape
          cases hShape)⟩
    | equal left right =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort body hShape
          cases hShape)⟩
    | neg body =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort quantifiedBody hShape
          cases hShape)⟩
    | conj left right =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort body hShape
          cases hShape)⟩
    | disj left right =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort body hShape
          cases hShape)⟩
    | imp left right =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort body hShape
          cases hShape)⟩
    | iff left right =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort body hShape
          cases hShape)⟩
    | forallE quantifiedSort body =>
        exact ⟨positive_without_witness current hPositive (by
          intro sort quantifiedBody hShape
          cases hShape)⟩
    | existsE sort body =>
        let existential : Sentence (HSignature σ) := .existsE sort body
        let positive : Stage background :=
          Stage.of_insert current hPositive
        let index :=
          Context.freshWitnessIndex existential positive.sentences
        let witness : Sentence (HSignature σ) :=
          body.instantiateTop (witnessTerm (σ := σ) sort index)
        have hExists : existential ∈ positive.sentences := by
          exact List.mem_cons_self
        have hWitnessConsistent :
            Derives.Consistent T (witness :: positive.sentences) := by
          simpa [index, witness] using
            (consistent_fresh_witness_instance background
              positive.consistent hExists)
        let next : Stage background :=
          Stage.seed background (witness :: positive.sentences)
            hWitnessConsistent
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            exact List.mem_cons_of_mem witness
              (List.mem_cons_of_mem existential hTarget)
          decision := Or.inl (List.mem_cons_of_mem witness
            List.mem_cons_self)
          witness := by
            intro witnessSort witnessBody hShape _
            cases hShape
            exact ⟨index, List.mem_cons_self⟩
        }⟩
  · let next := Stage.of_insert current hNegative
    have hNotCurrent : sentence ∉ current.sentences :=
      not_mem_of_negative current hNegative
    exact ⟨{
      next := next
      subset := by
        intro target hTarget
        exact List.mem_cons_of_mem (.neg sentence) hTarget
      decision := Or.inr List.mem_cons_self
      witness := by
        intro sort body _ hCurrent
        exact False.elim (hNotCurrent hCurrent)
    }⟩

/-- 经典选择固定一个扩张；全部可信性质仍来自 `nonempty` 的证明。 -/
noncomputable def choose
    {T : Theory (HSignature σ)}
    {background : Background T}
    (current : Stage background)
    (sentence : Sentence (HSignature σ)) :
    Extension current sentence :=
  Classical.choice (nonempty current sentence)

end Extension

/-! ## 公平迭代与极限候选 -/

/-- 候选理论决定每条闭句或其否定。 -/
def Decides (candidate : Theory (HSignature σ)) : Prop :=
  ∀ sentence, candidate sentence ∨ candidate (.neg sentence)

/-- 候选理论中的每个存在闭句都有一枚 Henkin 常量见证。 -/
def Witnessed (candidate : Theory (HSignature σ)) : Prop :=
  ∀ sort (body : Formula (HSignature σ) [sort] []),
    candidate (.existsE sort body) →
      ∃ index,
        candidate (body.instantiateTop
          (witnessTerm (σ := σ) sort index))

/-- Henkin 完成的公开 proof-carrying 结果。 -/
structure Result {T : Theory (HSignature σ)}
    (background : Background T) where
  candidate : Theory (HSignature σ)
  wf : Derives.WF_Candidate T candidate
  decides : Decides candidate
  witnessed : Witnessed candidate

namespace Construction

noncomputable section

/-- 按公平调度递归生成有限闭句阶段。 -/
def stage {T : Theory (HSignature σ)}
    {background : Background T}
    (initial : Stage background)
    (schedule : Schedule σ) : Nat → Stage background
  | 0 => initial
  | index + 1 =>
      (Extension.choose (stage initial schedule index)
        (schedule.sentence index)).next

@[simp]
theorem stage_zero {T : Theory (HSignature σ)}
    {background : Background T}
    (initial : Stage background) (schedule : Schedule σ) :
    stage initial schedule 0 = initial :=
  rfl

@[simp]
theorem stage_succ {T : Theory (HSignature σ)}
    {background : Background T}
    (initial : Stage background) (schedule : Schedule σ)
    (index : Nat) :
    stage initial schedule (index + 1) =
      (Extension.choose (stage initial schedule index)
        (schedule.sentence index)).next :=
  rfl

/-- 每个阶段的闭句都保留到下一阶段。 -/
theorem subset_succ {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ}
    (index : Nat) {sentence : Sentence (HSignature σ)}
    (hSentence : sentence ∈ (stage initial schedule index).sentences) :
    sentence ∈ (stage initial schedule (index + 1)).sentences :=
  (Extension.choose (stage initial schedule index)
    (schedule.sentence index)).subset sentence hSentence

/-- 阶段闭句沿自然数序单调保留。 -/
theorem subset_of_le {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ}
    {small large : Nat} (hLe : small ≤ large)
    {sentence : Sentence (HSignature σ)}
    (hSentence : sentence ∈ (stage initial schedule small).sentences) :
    sentence ∈ (stage initial schedule large).sentences := by
  induction hLe with
  | refl => exact hSentence
  | step hPrevious ih => exact subset_succ _ ih

/-- 第 `index` 步决定调度到的闭句。 -/
theorem decision_at {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ}
    (index : Nat) :
    schedule.sentence index ∈
        (stage initial schedule (index + 1)).sentences ∨
      .neg (schedule.sentence index) ∈
        (stage initial schedule (index + 1)).sentences :=
  (Extension.choose (stage initial schedule index)
    (schedule.sentence index)).decision

/-- 已在当前阶段出现的存在闭句在该调度步骤后获得见证。 -/
theorem witness_at {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ}
    (index : Nat) {sort : σ.SortSymbol}
    {body : Formula (HSignature σ) [sort] []}
    (hShape : schedule.sentence index = .existsE sort body)
    (hMember : schedule.sentence index ∈
      (stage initial schedule index).sentences) :
    ∃ witnessIndex,
      body.instantiateTop
          (witnessTerm (σ := σ) sort witnessIndex) ∈
        (stage initial schedule (index + 1)).sentences :=
  (Extension.choose (stage initial schedule index)
    (schedule.sentence index)).witness sort body hShape hMember

/-- 极限候选是全部有限阶段的并。 -/
def candidate {T : Theory (HSignature σ)}
    {background : Background T}
    (initial : Stage background) (schedule : Schedule σ) :
    Theory (HSignature σ) :=
  fun sentence =>
    ∃ index, sentence ∈ (stage initial schedule index).sentences

/-- 任意阶段成员进入极限候选。 -/
theorem candidate_of_stage {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ}
    {index : Nat} {sentence : Sentence (HSignature σ)}
    (hSentence : sentence ∈ (stage initial schedule index).sentences) :
    candidate initial schedule sentence :=
  ⟨index, hSentence⟩

/-- 初始种子中的每个闭句都保留到极限候选。 -/
theorem candidate_of_initial {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ}
    {sentence : Sentence (HSignature σ)}
    (hSentence : sentence ∈ initial.sentences) :
    candidate initial schedule sentence :=
  candidate_of_stage (index := 0) (by simpa using hSentence)

/-- 极限候选中的有限上下文总能同时落入某个有限阶段。 -/
theorem context_in_stage {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ}
    (Γ : Context (HSignature σ) [])
    (hΓ : ∀ sentence, sentence ∈ Γ →
      candidate initial schedule sentence) :
    ∃ index,
      ∀ sentence, sentence ∈ Γ →
        sentence ∈ (stage initial schedule index).sentences := by
  induction Γ with
  | nil =>
      exact ⟨0, by
        intro sentence hSentence
        cases hSentence⟩
  | cons head tail ih =>
      rcases hΓ head List.mem_cons_self with ⟨headIndex, hHead⟩
      have hTail :
          ∀ sentence, sentence ∈ tail →
            candidate initial schedule sentence := by
        intro sentence hSentence
        exact hΓ sentence (List.mem_cons_of_mem head hSentence)
      rcases ih hTail with ⟨tailIndex, hTailAt⟩
      refine ⟨Nat.max headIndex tailIndex, ?_⟩
      intro sentence hSentence
      rcases List.mem_cons.mp hSentence with rfl | hSentence
      · exact subset_of_le (Nat.le_max_left _ _) hHead
      · exact subset_of_le (Nat.le_max_right _ _)
          (hTailAt sentence hSentence)

/-- 极限候选相对背景理论保持有限一致。 -/
theorem candidate_finitelyConsistent
    {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ} :
    Derives.FinitelyConsistent T (candidate initial schedule) := by
  intro Γ hΓ
  rcases context_in_stage Γ hΓ with ⟨index, hAtStage⟩
  exact Derives.Consistent.mono
    (stage initial schedule index).consistent hAtStage

/-- 公平调度保证极限候选决定每条闭句。 -/
theorem candidate_decides
    {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ} :
    Decides (candidate initial schedule) := by
  intro sentence
  rcases schedule.cofinal sentence 0 with
    ⟨index, _, hScheduled⟩
  rcases decision_at (initial := initial) (schedule := schedule) index with
    hPositive | hNegative
  · left
    exact candidate_of_stage (index := index + 1) (by
      simpa [hScheduled] using hPositive)
  · right
    exact candidate_of_stage (index := index + 1) (by
      simpa [hScheduled] using hNegative)

/-- 公平调度保证极限候选中的每个存在闭句最终获得见证。 -/
theorem candidate_witnessed
    {T : Theory (HSignature σ)}
    {background : Background T}
    {initial : Stage background} {schedule : Schedule σ} :
    Witnessed (candidate initial schedule) := by
  intro sort body hExists
  rcases hExists with ⟨memberIndex, hMember⟩
  rcases schedule.cofinal (.existsE sort body) memberIndex with
    ⟨index, hMemberIndex, hScheduled⟩
  have hAtIndex :
      schedule.sentence index ∈
        (stage initial schedule index).sentences := by
    rw [hScheduled]
    exact subset_of_le hMemberIndex hMember
  rcases witness_at (initial := initial) (schedule := schedule)
      index hScheduled hAtIndex with
    ⟨witnessIndex, hWitness⟩
  exact ⟨witnessIndex, candidate_of_stage hWitness⟩

/-- 公平调度生成完整 Henkin 候选。 -/
def result {T : Theory (HSignature σ)}
    {background : Background T}
    (initial : Stage background) (schedule : Schedule σ) :
    Result background where
  candidate := candidate initial schedule
  wf := ⟨candidate_finitelyConsistent⟩
  decides := candidate_decides
  witnessed := candidate_witnessed

end

end Construction

end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
