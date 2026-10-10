import YesMetaZFC.Logic.FirstOrder.Context.Basic
import YesMetaZFC.Logic.FirstOrder.Derivation.Core

/-!
# 局部上下文到 Hilbert 核的结构化编译

局部上下文不扩张可信演绎核。一个判断 `Γ ⊢ φ` 被定义为：把 Γ 中的假设按列表
顺序折叠成蕴含后，所得开放公式具有标准 Hilbert 证书。

列表头表示最近加入的假设，因此
`discharge (ψ :: Γ) φ = discharge Γ (ψ → φ)`。演绎定理由此成为定义等式；结构
弱化、cut 与上下文 modus ponens 则由三个 Hilbert 蕴含公理统一推出。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

namespace Context

/-- 把有限局部上下文规范编译为右侧结论前的蕴含链。 -/
def discharge {σ : Signature.{u, v, w}} {free : SortContext σ} :
    Context σ free → OpenFormula σ free → OpenFormula σ free
  | [], conclusion => conclusion
  | assumption :: rest, conclusion =>
      discharge rest (.imp assumption conclusion)

end Context

/-- 从局部上下文可推导，定义为其规范蕴含闭包在 Hilbert 核中可证。 -/
def Derives {σ : Signature.{u, v, w}}
    (T : Theory σ) {free : SortContext σ}
    (Γ : Context σ free) (formula : OpenFormula σ free) : Prop :=
  Provable T (Context.discharge Γ formula)

namespace Provable

/-- 自蕴含基础公理。 -/
theorem self_implication {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    (formula : OpenFormula σ free) :
    Provable T (.imp formula formula) := by
  have hFirst : Provable T
      (.imp formula (.imp (.imp formula formula) formula)) :=
    logical_axiom
      (.weakening formula (.imp formula formula))
  have hSecond : Provable T
      (.imp formula (.imp formula formula)) :=
    logical_axiom (.self_implication formula)
  have hDistribution : Provable T
      (.imp (.imp formula (.imp (.imp formula formula) formula))
        (.imp (.imp formula (.imp formula formula))
          (.imp formula formula))) :=
    logical_axiom
      (.implication_distribution formula (.imp formula formula) formula)
  exact modus_ponens hSecond (modus_ponens hFirst hDistribution)

/-- 已证公式可加入一个无关前件。 -/
theorem weakening {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {formula : OpenFormula σ free} (extra : OpenFormula σ free)
    (hFormula : Provable T formula) :
    Provable T (.imp extra formula) :=
  modus_ponens hFormula
    (logical_axiom (.weakening formula extra))

/-- 蕴含可逐点提升到同一个前件之下。 -/
theorem imp_mono {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {antecedent consequent : OpenFormula σ free}
    (guard : OpenFormula σ free)
    (hImplication : Provable T (.imp antecedent consequent)) :
    Provable T
      (.imp (.imp guard antecedent) (.imp guard consequent)) := by
  have hLifted : Provable T (.imp guard (.imp antecedent consequent)) :=
    hImplication.weakening guard
  exact modus_ponens hLifted
    (logical_axiom
      (.implication_distribution guard antecedent consequent))

end Provable

namespace Context

/-- 已证蕴含可穿过整个局部上下文。 -/
theorem consequence {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    (Γ : Context σ free)
    {antecedent consequent : OpenFormula σ free}
    (hImplication : Provable T (.imp antecedent consequent)) :
    Provable T (.imp (discharge Γ antecedent) (discharge Γ consequent)) := by
  induction Γ generalizing antecedent consequent with
  | nil =>
      simpa [discharge] using hImplication
  | cons head rest ih =>
      simpa [discharge] using ih (Provable.imp_mono head hImplication)

/-- 全局 Hilbert 定理可提升到任意局部上下文。 -/
theorem lift {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    (Γ : Context σ free) {formula : OpenFormula σ free}
    (hFormula : Provable T formula) :
    Provable T (discharge Γ formula) := by
  induction Γ generalizing formula with
  | nil =>
      simpa [discharge] using hFormula
  | cons head rest ih =>
      simpa [discharge] using ih (Provable.weakening head hFormula)

end Context

namespace Derives

/-- Hilbert 核中的证明可用于任意局部上下文。 -/
theorem of_provable {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hFormula : Provable T formula) :
    Derives T Γ formula :=
  Context.lift Γ hFormula

/-- 逻辑公理可用于任意局部上下文。 -/
theorem logical_axiom {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hAxiom : HilbertBaseAxiom σ formula) :
    Derives T Γ formula :=
  of_provable (Provable.logical_axiom hAxiom)

/-- 闭理论公理可用于任意 free 上下文与局部上下文。 -/
theorem theory_axiom {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {sentence : Sentence σ}
    (hTheory : T sentence) :
    Derives T Γ (Formula.fromSentence sentence) :=
  of_provable (Provable.theory_axiom hTheory)

/-- 局部上下文成员可直接使用。 -/
theorem assumption_of_mem {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hMem : formula ∈ Γ) :
    Derives T Γ formula := by
  induction Γ with
  | nil =>
      cases hMem
  | cons head rest ih =>
      -- 直接消去成员构造子，不经库中的命题等式转换。
      cases hMem with
      | head => exact Context.lift rest (Provable.self_implication formula)
      | tail _ hRest =>
        have hTail : Provable T (Context.discharge rest formula) :=
          ih hRest
        have hWeakening :
            Provable T (.imp formula (.imp head formula)) :=
          Provable.logical_axiom
            (.weakening formula head)
        exact Provable.modus_ponens hTail
          (Context.consequence rest hWeakening)

/-- info: 'YesMetaZFC.Logic.FirstOrder.Derives.assumption_of_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms assumption_of_mem

/-- 上下文编码下的 modus ponens。 -/
theorem modus_ponens {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {antecedent consequent : OpenFormula σ free}
    (hAntecedent : Derives T Γ antecedent)
    (hImplication : Derives T Γ (.imp antecedent consequent)) :
    Derives T Γ consequent := by
  induction Γ generalizing antecedent consequent with
  | nil =>
      exact Provable.modus_ponens hAntecedent hImplication
  | cons assumption rest ih =>
      have hDistribution : Derives T rest
          (.imp (.imp assumption (.imp antecedent consequent))
            (.imp (.imp assumption antecedent)
              (.imp assumption consequent))) :=
        of_provable
          (Provable.logical_axiom
            (.implication_distribution assumption antecedent consequent))
      have hStep : Derives T rest
          (.imp (.imp assumption antecedent)
            (.imp assumption consequent)) :=
        ih hImplication hDistribution
      exact ih hAntecedent hStep

/-- 演绎定理是上下文编码的定义等式。 -/
theorem deduction {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {antecedent consequent : OpenFormula σ free}
    (hBody : Derives T (antecedent :: Γ) consequent) :
    Derives T Γ (.imp antecedent consequent) :=
  hBody

/-- 演绎定理的双向形式。 -/
theorem deduction_iff {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {antecedent consequent : OpenFormula σ free} :
    Derives T (antecedent :: Γ) consequent ↔
      Derives T Γ (.imp antecedent consequent) :=
  Iff.rfl

/-- 单个 cut 由演绎定理与上下文 modus ponens 给出。 -/
theorem cut {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {middle conclusion : OpenFormula σ free}
    (hMiddle : Derives T Γ middle)
    (hConclusion : Derives T (middle :: Γ) conclusion) :
    Derives T Γ conclusion :=
  modus_ponens hMiddle (deduction hConclusion)

/-- 局部上下文沿成员包含关系弱化。 -/
theorem context_weaken {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ Δ : Context σ free} {formula : OpenFormula σ free}
    (hSubset : ∀ candidate, candidate ∈ Γ → candidate ∈ Δ)
    (hDerives : Derives T Γ formula) :
    Derives T Δ formula := by
  induction Γ generalizing formula with
  | nil =>
      exact of_provable hDerives
  | cons assumption rest ih =>
      change Derives T rest (.imp assumption formula) at hDerives
      have hTail : Derives T Δ (.imp assumption formula) :=
        ih (fun candidate hMem =>
          hSubset candidate (List.mem_cons_of_mem assumption hMem)) hDerives
      exact modus_ponens
        (assumption_of_mem (hSubset assumption List.mem_cons_self))
        hTail

/-- 在上下文头部加入一个假设。 -/
theorem context_weaken_cons {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {assumption formula : OpenFormula σ free}
    (hDerives : Derives T Γ formula) :
    Derives T (assumption :: Γ) formula :=
  context_weaken (fun _ hMem =>
    List.mem_cons_of_mem assumption hMem) hDerives

/-- 在上下文右侧加入任意有限列表。 -/
theorem context_weaken_append {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ Δ : Context σ free} {formula : OpenFormula σ free}
    (hDerives : Derives T Γ formula) :
    Derives T (Γ ++ Δ) formula :=
  context_weaken (fun _ hMem =>
    List.mem_append.mpr (Or.inl hMem)) hDerives

/-- 在上下文左侧加入任意有限前缀。 -/
theorem context_weaken_prefix {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {initial Γ : Context σ free} {formula : OpenFormula σ free}
    (hDerives : Derives T Γ formula) :
    Derives T (initial ++ Γ) formula :=
  context_weaken (fun _ hMem =>
    List.mem_append.mpr (Or.inr hMem)) hDerives

/-- 交换最前面的两个局部假设。 -/
theorem exchange {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {left right formula : OpenFormula σ free}
    (hDerives : Derives T (left :: right :: Γ) formula) :
    Derives T (right :: left :: Γ) formula :=
  context_weaken (by
    intro candidate hMem
    rcases List.mem_cons.mp hMem with rfl | hMem
    · exact List.mem_cons_of_mem right List.mem_cons_self
    · rcases List.mem_cons.mp hMem with rfl | hTail
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem right
          (List.mem_cons_of_mem left hTail)) hDerives

/-- 收缩重复的最前假设。 -/
theorem contraction {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free}
    {assumption formula : OpenFormula σ free}
    (hDerives : Derives T (assumption :: assumption :: Γ) formula) :
    Derives T (assumption :: Γ) formula :=
  context_weaken (by
    intro candidate hMem
    rcases List.mem_cons.mp hMem with rfl | hMem
    · exact List.mem_cons_self
    · rcases List.mem_cons.mp hMem with rfl | hTail
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem assumption hTail) hDerives

/-- 沿理论包含关系搬运局部推导。 -/
theorem theory_weaken {σ : Signature.{u, v, w}}
    {T U : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hTheory : Theory.Extends U T)
    (hDerives : Derives T Γ formula) :
    Derives U Γ formula :=
  Provable.theory_weakening hTheory hDerives

/-- 同时扩大理论与局部上下文。 -/
theorem monotone {σ : Signature.{u, v, w}}
    {T U : Theory σ} {free : SortContext σ}
    {Γ Δ : Context σ free} {formula : OpenFormula σ free}
    (hTheory : Theory.Extends U T)
    (hContext : ∀ candidate, candidate ∈ Γ → candidate ∈ Δ)
    (hDerives : Derives T Γ formula) :
    Derives U Δ formula :=
  context_weaken hContext (theory_weaken hTheory hDerives)

/-- 空理论、空上下文中的逻辑定理可用于任意理论和上下文。 -/
theorem of_empty {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hDerives : Derives (Theory.empty : Theory σ) [] formula) :
    Derives T Γ formula :=
  context_weaken (by simp)
    (theory_weaken (fun hTheory => False.elim hTheory) hDerives)

/-- 有限多个已证明前提可一次性从结论证明中消去。 -/
theorem multi_cut {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ premises : Context σ free}
    {conclusion : OpenFormula σ free}
    (hPremises : ∀ formula, formula ∈ premises → Derives T Γ formula)
    (hConclusion : Derives T (premises ++ Γ) conclusion) :
    Derives T Γ conclusion := by
  induction premises generalizing Γ with
  | nil =>
      simpa using hConclusion
  | cons head tail ih =>
      have hHead : Derives T Γ head :=
        hPremises head List.mem_cons_self
      have hHeadInTail : Derives T (tail ++ Γ) head :=
        hHead.context_weaken (fun candidate hMem =>
          List.mem_append.mpr (Or.inr hMem))
      have hAfterHead : Derives T (tail ++ Γ) conclusion := by
        apply hHeadInTail.cut
        simpa [List.cons_append] using hConclusion
      apply ih
      · intro formula hFormula
        exact hPremises formula
          (List.mem_cons_of_mem head hFormula)
      · exact hAfterHead

/-- 把一组前提证明接到带独立右上下文的结论证明前。 -/
theorem multi_cut_append {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {left right premises : Context σ free}
    {conclusion : OpenFormula σ free}
    (hPremises : ∀ formula, formula ∈ premises → Derives T left formula)
    (hConclusion : Derives T (premises ++ right) conclusion) :
    Derives T (left ++ right) conclusion := by
  apply multi_cut (Γ := left ++ right) (premises := premises)
  · intro formula hFormula
    exact (hPremises formula hFormula).context_weaken_append
  · apply hConclusion.context_weaken
    intro formula hFormula
    rcases List.mem_append.mp hFormula with hPremise | hRight
    · exact List.mem_append.mpr (Or.inl hPremise)
    · exact List.mem_append.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hRight)))

/-- 单个中间公式的左右上下文拼接。 -/
theorem cut_append {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {left right : Context σ free}
    {middle conclusion : OpenFormula σ free}
    (hMiddle : Derives T left middle)
    (hConclusion : Derives T (middle :: right) conclusion) :
    Derives T (left ++ right) conclusion := by
  apply cut (middle := middle) (Γ := left ++ right)
  · exact hMiddle.context_weaken_append
  · apply hConclusion.context_weaken
    intro formula hFormula
    rcases List.mem_cons.mp hFormula with rfl | hRight
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem middle
        (List.mem_append.mpr (Or.inr hRight))

/-- 左理论中的证明可嵌入理论并。 -/
theorem theory_union_left {σ : Signature.{u, v, w}}
    {left right : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hDerives : Derives left Γ formula) :
    Derives (Theory.union left right) Γ formula :=
  hDerives.theory_weaken (fun hTheory => Or.inl hTheory)

/-- 右理论中的证明可嵌入理论并。 -/
theorem theory_union_right {σ : Signature.{u, v, w}}
    {left right : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hDerives : Derives right Γ formula) :
    Derives (Theory.union left right) Γ formula :=
  hDerives.theory_weaken (fun hTheory => Or.inr hTheory)

end Derives
end FirstOrder
end Logic
end YesMetaZFC
