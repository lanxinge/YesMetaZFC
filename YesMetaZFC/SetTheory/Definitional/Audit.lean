import YesMetaZFC.SetTheory.Definitional.Theory
import YesMetaZFC.SetTheory.Definitional.Audit.Pure

/-!
# 带定义原子核的旧核审计

本模块是新核唯一接触旧纯 `∈` 公式 AST 的位置。它提供完全展开、语义等价和旧语言
片段上的双向保守性；日常定理与自动化不应导入本模块。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Audit

universe u v

namespace Term

/-- 把旧核项嵌入新核。 -/
def embed {depth : Nat} : Pure.Term depth → Definitional.Term depth
  | .bound entry => .bound entry
  | .free id => .free id

/-- 把新核项翻译到旧核。 -/
def expand {depth : Nat} : Definitional.Term depth → Pure.Term depth
  | .bound entry => .bound entry
  | .free id => .free id

@[simp] theorem expand_embed {depth : Nat} (term : Pure.Term depth) :
    expand (embed term) = term := by
  cases term <;> rfl

@[simp] theorem freeSupport_embed {depth : Nat} (term : Pure.Term depth) :
    (embed term).freeSupport = term.freeSupport := by
  cases term <;> rfl

@[simp] theorem freeSupport_expand {depth : Nat}
    (term : Definitional.Term depth) :
    (expand term).freeSupport = term.freeSupport := by
  cases term <;> rfl

@[simp] theorem eval_expand {ℳ : SetTheory.Structure.{v}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) (term : Definitional.Term depth) :
    Pure.Term.eval env (expand term) =
      Definitional.Term.eval env term := by
  cases term <;> rfl

end Term

namespace Formula

/-- 旧纯隶属公式嵌入新核。 -/
def embed {σ : AtomSignature.{u}} {availableStage depth : Nat} :
    Pure.Formula depth → Definitional.Formula σ availableStage depth
  | .falsum => .falsum
  | .truth => .truth
  | .mem left right => .mem (Term.embed left) (Term.embed right)
  | .neg formula => .neg (embed formula)
  | .conj left right => .conj (embed left) (embed right)
  | .disj left right => .disj (embed left) (embed right)
  | .imp left right => .imp (embed left) (embed right)
  | .iff left right => .iff (embed left) (embed right)
  | .forallE body => .forallE (embed body)
  | .existsE body => .existsE (embed body)

/-- 将定义原子递归消去到旧纯隶属核。 -/
def expand {σ : AtomSignature.{u}} (definitions : Definitions σ) :
    {availableStage depth : Nat} →
      Definitional.Formula σ availableStage depth →
        Pure.Formula depth
  | _, _, .falsum => .falsum
  | _, _, .truth => .truth
  | _, _, .mem left right => .mem (Term.expand left) (Term.expand right)
  | _, _, .atom symbol _ arguments =>
      (expand definitions (definitions.body symbol)).bind fun entry =>
        Term.expand (arguments entry)
  | _, _, .neg formula => .neg (expand definitions formula)
  | _, _, .conj left right =>
      .conj (expand definitions left) (expand definitions right)
  | _, _, .disj left right =>
      .disj (expand definitions left) (expand definitions right)
  | _, _, .imp left right =>
      .imp (expand definitions left) (expand definitions right)
  | _, _, .iff left right =>
      .iff (expand definitions left) (expand definitions right)
  | _, _, .forallE body => .forallE (expand definitions body)
  | _, _, .existsE body => .existsE (expand definitions body)
termination_by availableStage _depth formula =>
  (availableStage, sizeOf formula)

/-- 纯核公式嵌入后再展开，严格回到原公式。 -/
@[simp] theorem expand_embed {σ : AtomSignature.{u}}
    (definitions : Definitions σ) {availableStage depth : Nat}
    (formula : Pure.Formula depth) :
    expand definitions (embed (availableStage := availableStage) formula) =
      formula := by
  induction formula with
  | falsum =>
      simp [embed, expand]
  | truth =>
      simp [embed, expand]
  | mem =>
      simp [embed, expand]
  | neg formula ih =>
      simp [embed, expand, ih]
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp [embed, expand, ihLeft, ihRight]
  | forallE body ih
  | existsE body ih =>
      simp [embed, expand, ih]

/-- 旧核自由闭合公式嵌入后在新核中仍自由闭合。 -/
theorem freeClosed_embed {σ : AtomSignature.{u}}
    {availableStage depth : Nat} (formula : Pure.Formula depth)
    (hClosed : formula.FreeClosed) :
    Definitional.Formula.FreeClosed
      (embed (σ := σ) (availableStage := availableStage) formula) := by
  induction formula with
  | falsum =>
      simp [embed, Definitional.Formula.FreeClosed]
  | truth =>
      simp [embed, Definitional.Formula.FreeClosed]
  | mem left right =>
      simpa [Pure.Formula.FreeClosed,
        Pure.Formula.freeSupport, embed,
        Definitional.Formula.FreeClosed] using hClosed
  | neg formula ih =>
      simpa [embed, Definitional.Formula.FreeClosed] using ih hClosed
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      have hParts :
          left.FreeClosed ∧ right.FreeClosed := by
        simpa [Pure.Formula.FreeClosed,
          Pure.Formula.freeSupport] using hClosed
      simpa [embed, Definitional.Formula.FreeClosed] using
        And.intro (ihLeft hParts.1) (ihRight hParts.2)
  | forallE body ih
  | existsE body ih =>
      simpa [embed, Definitional.Formula.FreeClosed] using ih hClosed

/-- 自由闭合的新核公式展开后仍是旧核的自由闭合公式。 -/
theorem expand_freeClosed {σ : AtomSignature.{u}}
    (definitions : Definitions σ) :
    {availableStage depth : Nat} →
      (formula : Definitional.Formula σ availableStage depth) →
      Definitional.Formula.FreeClosed formula →
        Pure.Formula.FreeClosed (expand definitions formula)
  | _, _, .falsum, _ => by
      simp [expand, Pure.Formula.FreeClosed,
        Pure.Formula.freeSupport]
  | _, _, .truth, _ => by
      simp [expand, Pure.Formula.FreeClosed,
        Pure.Formula.freeSupport]
  | _, _, .mem left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simp [expand, Pure.Formula.FreeClosed,
        Pure.Formula.freeSupport, hClosed]
  | _, _, .atom symbol _ arguments, hClosed => by
      simp only [Definitional.Formula.FreeClosed,
        TermVector.FreeClosed] at hClosed
      rw [expand]
      change
        ((expand definitions (definitions.body symbol)).bind
            fun entry => Term.expand (arguments entry)).freeSupport = []
      rw [Pure.Formula.freeSupport_bind_of_closed]
      · exact
          expand_freeClosed definitions (definitions.body symbol)
            (definitions.bodyFreeClosed symbol)
      · intro entry
        simpa using hClosed entry
  | _, _, .neg formula, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simpa [expand, Pure.Formula.FreeClosed,
        Pure.Formula.freeSupport] using
        expand_freeClosed definitions formula hClosed
  | _, _, .conj left right, hClosed
  | _, _, .disj left right, hClosed
  | _, _, .imp left right, hClosed
  | _, _, .iff left right, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      rcases hClosed with ⟨hLeft, hRight⟩
      simpa [expand, Pure.Formula.FreeClosed,
        Pure.Formula.freeSupport] using
        And.intro
          (expand_freeClosed definitions left hLeft)
          (expand_freeClosed definitions right hRight)
  | _, _, .forallE body, hClosed
  | _, _, .existsE body, hClosed => by
      simp only [Definitional.Formula.FreeClosed] at hClosed
      simpa [expand, Pure.Formula.FreeClosed,
        Pure.Formula.freeSupport] using
        expand_freeClosed definitions body hClosed
termination_by availableStage _depth formula _hClosed =>
  (availableStage, sizeOf formula)

end Formula

namespace Sentence

/-- 把旧核句子嵌入新核。 -/
def embed {σ : AtomSignature.{u}} (sentence : Pure.Sentence) :
    Definitional.Sentence σ where
  formula :=
    Formula.embed (σ := σ) (availableStage := σ.maxStage)
      sentence.formula
  freeClosed :=
    Formula.freeClosed_embed sentence.formula sentence.freeClosed

/-- 把新核句子完全展开到旧纯隶属核。 -/
def expand {σ : AtomSignature.{u}} (definitions : Definitions σ)
    (sentence : Definitional.Sentence σ) : Pure.Sentence where
  formula := Formula.expand definitions sentence.formula
  freeClosed :=
    Formula.expand_freeClosed definitions sentence.formula
      sentence.freeClosed

/-- 旧核句子嵌入后再展开，严格回到原句子。 -/
@[simp] theorem expand_embed {σ : AtomSignature.{u}}
    (definitions : Definitions σ) (sentence : Pure.Sentence) :
    expand definitions (embed (σ := σ) sentence) = sentence := by
  cases sentence
  simp [expand, embed]

end Sentence

namespace Theory

/-- 新核理论完全展开后在旧核中的像。 -/
def expand {σ : AtomSignature.{u}} (definitions : Definitions σ)
    (theory : Definitional.Theory σ) : Pure.Theory :=
  fun candidate =>
    ∃ sentence, theory sentence ∧ Sentence.expand definitions sentence = candidate

/-- 旧核理论沿完全展开逆像提升到新核。 -/
def lift {σ : AtomSignature.{u}} (definitions : Definitions σ)
    (theory : Pure.Theory) : Definitional.Theory σ :=
  fun sentence => theory (Sentence.expand definitions sentence)

/-- 提升旧核理论后再展开，严格回到原理论。 -/
theorem expand_lift {σ : AtomSignature.{u}} (definitions : Definitions σ)
    (theory : Pure.Theory) :
    expand definitions (lift definitions theory) = theory := by
  funext candidate
  apply propext
  constructor
  · rintro ⟨sentence, hTheory, rfl⟩
    exact hTheory
  · intro hTheory
    refine ⟨Sentence.embed (σ := σ) candidate, ?_, ?_⟩
    · simpa [lift] using hTheory
    · exact Sentence.expand_embed definitions candidate

end Theory

namespace Semantics

/-- 旧核 substitution 环境与新核原子参数环境一致。 -/
private theorem substitute_arguments {σ : AtomSignature.{u}}
    {ℳ : SetTheory.Structure.{v}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) {symbol : σ.Symbol}
    (arguments : TermVector (σ.arity symbol) depth) :
    Pure.Env.substitute env (fun entry => Term.expand (arguments entry)) =
      Definitional.Semantics.atomEnv env arguments := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext entry
    simp [Pure.Env.substitute, Definitional.Semantics.atomEnv,
      TermVector.eval]
  · rfl

/-- 新核原生语义与完全展开到旧核后的语义一致。 -/
theorem satisfies_expand {σ : AtomSignature.{u}} (kernel : Kernel.{u, v} σ)
    {ℳ : SetTheory.Structure.{v}} (hExtensional : Extensional ℳ) :
    {availableStage depth : Nat} →
      (env : SetTheory.Env ℳ depth) →
      (formula : Definitional.Formula σ availableStage depth) →
      Definitional.Semantics.satisfies kernel.interpretation env formula ↔
        Pure.Formula.satisfies env
          (Formula.expand kernel.definitions formula)
  | _, _, env, .falsum => by
      simp [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies]
  | _, _, env, .truth => by
      simp [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies]
  | _, _, env, .mem left right => by
      simp [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies]
  | _, _, env, .atom symbol _ arguments => by
      rw [Formula.expand, Pure.Formula.satisfies_bind,
        substitute_arguments]
      simp only [Definitional.Semantics.satisfies]
      have hAtom :=
        kernel.atom_iff symbol hExtensional (arguments.eval env) env.free
      exact hAtom.trans
        (satisfies_expand kernel hExtensional
          (Definitional.Semantics.atomEnv env arguments)
          (kernel.definitions.body symbol))
  | _, _, env, .neg formula => by
      simpa [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies] using
        not_congr (satisfies_expand kernel hExtensional env formula)
  | _, _, env, .conj left right => by
      simpa [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies] using
        and_congr
          (satisfies_expand kernel hExtensional env left)
          (satisfies_expand kernel hExtensional env right)
  | _, _, env, .disj left right => by
      simpa [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies] using
        or_congr
          (satisfies_expand kernel hExtensional env left)
          (satisfies_expand kernel hExtensional env right)
  | _, _, env, .imp left right => by
      simpa [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies] using
        imp_congr
          (satisfies_expand kernel hExtensional env left)
          (satisfies_expand kernel hExtensional env right)
  | _, _, env, .iff left right => by
      simpa [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies] using
        iff_congr
          (satisfies_expand kernel hExtensional env left)
          (satisfies_expand kernel hExtensional env right)
  | _, _, env, .forallE body => by
      simp only [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies]
      exact forall_congr' fun value =>
        satisfies_expand kernel hExtensional (env.push value) body
  | _, _, env, .existsE body => by
      simp only [Definitional.Semantics.satisfies, Formula.expand,
        Pure.Formula.satisfies]
      exact exists_congr fun value =>
        satisfies_expand kernel hExtensional (env.push value) body
termination_by availableStage _depth _env formula =>
  (availableStage, sizeOf formula)

/-- 旧核公式嵌入新核后在外延结构中保持原有语义。 -/
theorem satisfies_embed {σ : AtomSignature.{u}}
    (kernel : Kernel.{u, v} σ) {ℳ : SetTheory.Structure.{v}}
    (hExtensional : Extensional ℳ)
    {availableStage depth : Nat} (env : SetTheory.Env ℳ depth)
    (formula : Pure.Formula depth) :
    Definitional.Semantics.satisfies kernel.interpretation env
        (Formula.embed (σ := σ) (availableStage := availableStage) formula) ↔
      Pure.Formula.satisfies env formula := by
  rw [satisfies_expand kernel hExtensional, Formula.expand_embed]

end Semantics

namespace Structure

/-- 新核句子与其旧核完全展开具有相同满足关系。 -/
theorem satisfiesSentence_expand {σ : AtomSignature.{u}}
    (kernel : Kernel.{u, v} σ) (ℳ : SetTheory.Structure.{v})
    (hExtensional : Extensional ℳ)
    (sentence : Definitional.Sentence σ) :
    Definitional.Structure.SatisfiesSentence kernel ℳ sentence ↔
      Pure.Structure.SatisfiesSentence ℳ
        (Sentence.expand kernel.definitions sentence) := by
  apply forall_congr'
  intro free
  exact Semantics.satisfies_expand kernel hExtensional _ sentence.formula

/-- 新核理论模型恰好是其旧核完全展开理论的模型。 -/
theorem models_expand {σ : AtomSignature.{u}} (kernel : Kernel.{u, v} σ)
    (ℳ : SetTheory.Structure.{v}) (theory : Definitional.Theory σ) :
    Definitional.Structure.Models kernel ℳ theory ↔
      Pure.Structure.Models ℳ
        (Theory.expand kernel.definitions theory) := by
  constructor
  · rintro ⟨hExtensional, hModels⟩
    refine ⟨hExtensional, ?_⟩
    intro candidate hCandidate
    rcases hCandidate with ⟨sentence, hSentence, rfl⟩
    exact
      (satisfiesSentence_expand kernel ℳ hExtensional sentence).mp
        (hModels sentence hSentence)
  · rintro ⟨hExtensional, hModels⟩
    refine ⟨hExtensional, ?_⟩
    intro sentence hSentence
    apply (satisfiesSentence_expand kernel ℳ hExtensional sentence).mpr
    exact hModels (Sentence.expand kernel.definitions sentence)
      ⟨sentence, hSentence, rfl⟩

end Structure

/-- 新核蕴涵与完全展开后的旧核蕴涵等价。 -/
theorem semanticallyEntails_expand {σ : AtomSignature.{u}}
    (kernel : Kernel.{u, v} σ) (theory : Definitional.Theory σ)
    (target : Definitional.Sentence σ) :
    Definitional.SemanticallyEntails kernel theory target ↔
      Pure.SemanticallyEntails.{v}
        (Theory.expand kernel.definitions theory)
        (Sentence.expand kernel.definitions target) := by
  constructor
  · intro hEntails ℳ hModels
    apply (Structure.satisfiesSentence_expand kernel ℳ hModels.1 target).mp
    exact hEntails ℳ
      ((Structure.models_expand kernel ℳ theory).mpr hModels)
  · intro hEntails ℳ hModels
    apply (Structure.satisfiesSentence_expand kernel ℳ hModels.1 target).mpr
    exact hEntails ℳ
      ((Structure.models_expand kernel ℳ theory).mp hModels)

/-- 在旧纯语言片段上，新核是旧核的双向保守扩张。 -/
theorem conservative_on_pure_fragment {σ : AtomSignature.{u}}
    (kernel : Kernel.{u, v} σ) (theory : Pure.Theory)
    (target : Pure.Sentence) :
    Definitional.SemanticallyEntails kernel
        (Theory.lift kernel.definitions theory)
        (Sentence.embed (σ := σ) target) ↔
      Pure.SemanticallyEntails.{v} theory target := by
  rw [semanticallyEntails_expand, Theory.expand_lift]
  simp

end Audit
end Definitional
end SetTheory
end YesMetaZFC
