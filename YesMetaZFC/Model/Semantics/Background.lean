import YesMetaZFC.Model.Semantics.Substitution
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-! # 相对模型性与原 Hilbert 核的可靠性

背景给出上下文操作及成立判断，模型另给函数与关系解释，模型性由公式解释逐公理计算。
规则证书独立于解释数据：量词、等同或非空性的解释变化后，不能自动继承它。
这里给出原生语义与背景理论可证性两份完整证书，不假定背景有外部模型。
-/

namespace YesMetaZFC.Model
open Logic Logic.FirstOrder
universe u v w x y

-- 打包不改变两个解释字段各自的 universe。
set_option linter.checkUnivs false in
/-- 背景中“谓词在该上下文成立”的观察。它不是外部 Tarski 真值的别名。 -/
structure Sem_background (σ : Signature.{u, v, w}) where
  context : Sem_context.{u, v, w, x, y} σ
  valid : ∀ {f}, context.Pr [] f → Prop

/-- 同一背景上的不同结构分别提供自己的符号解释。 -/
structure Sem_model {σ : Signature.{u, v, w}}
    (𝒱 : Sem_background.{u, v, w, x, y} σ) where
  app : ∀ {b f} (a : σ.FuncSymbol),
    Values (𝒱.context.Tm b f) (σ.funcDomain a) → 𝒱.context.Tm b f (σ.funcCodomain a)
  rel : ∀ {b f} (r : σ.RelSymbol),
    Values (𝒱.context.Tm b f) (σ.relDomain r) → 𝒱.context.Pr b f

namespace Sem_model
variable {σ : Signature.{u, v, w}} {𝒱 : Sem_background.{u, v, w, x, y} σ}
  (ℳ : Sem_model 𝒱)

/-- 把背景操作与当前模型的符号解释装配给唯一的公式求值器。 -/
abbrev algebra : Sem_algebra.{u, v, w, x, y} σ where
  toSem_context := 𝒱.context
  app := ℳ.app
  rel := ℳ.rel

/-- 默认使用当前标准 AST；内部语法视角另由 `Syntax_view` 接入。 -/
def holds {f} (φ : OpenFormula σ f) : Prop := 𝒱.valid (ℳ.algebra.fm φ)

/-- 背景相对于标准理论所认可的模型性。 -/
def models (T : Theory σ) : Prop := ∀ φ, T φ → ℳ.holds φ

/-- 有限假设由原核的蕴含闭包解释；不添加另一套推导。 -/
def entails {f} (Γ : Context σ f) (φ : OpenFormula σ f) : Prop :=
  ℳ.holds (Context.discharge Γ φ)

end Sem_model

/-- 原核六条规则的逐规则证书。它是可选能力，不是所有背景的默认假设。 -/
structure Sem_rules {σ : Signature.{u, v, w}}
    {𝒱 : Sem_background.{u, v, w, x, y} σ} (ℳ : Sem_model 𝒱) : Prop where
  axiom_valid : ∀ {f} {φ : OpenFormula σ f}, HilbertBaseAxiom σ φ → ℳ.holds φ
  sentence_lift : ∀ {f} {φ : Sentence σ}, ℳ.holds φ → ℳ.holds (φ.fromSentence (free := f))
  mp : ∀ {f} {φ ψ : OpenFormula σ f}, ℳ.holds φ → ℳ.holds (.imp φ ψ) → ℳ.holds ψ
  generalize : ∀ {f s} {φ : OpenFormula σ (s :: f)},
    ℳ.holds φ → ℳ.holds (φ.forallFreeTop s)
  strengthen : ∀ {f s} {φ : OpenFormula σ f},
    ℳ.holds (φ.weakenFree s) → ℳ.holds φ
  substitute : ∀ {f f'} (θ : VariableSubstitution σ f [] f') {φ : OpenFormula σ f},
    ℳ.holds φ → ℳ.holds (φ.substituteFree θ)

namespace Sem_rules
variable {σ : Signature.{u, v, w}} {𝒱 : Sem_background.{u, v, w, x, y} σ}
  {ℳ : Sem_model 𝒱}

/-- 对原始证明树归纳的相对可靠性；没有内部证明码反射。 -/
theorem proof_sound (R : Sem_rules ℳ) {T : Theory σ} (hT : ℳ.models T)
    {f} {φ : OpenFormula σ f} (d : HilbertDerivation T f φ) : ℳ.holds φ := by
  induction d with
  | logical_axiom h => exact R.axiom_valid h
  | theory_axiom h => exact R.sentence_lift (hT _ h)
  | modus_ponens _ _ h k => exact R.mp h k
  | forall_generalization _ h => exact R.generalize h
  | free_strengthening _ h => exact R.strengthen h
  | free_substitution θ _ h => exact R.substitute θ h

/-- 公共 `Derives` 的相对语义出口，保留任意有限局部上下文。 -/
theorem derives_sound (R : Sem_rules ℳ) {T : Theory σ} (hT : ℳ.models T)
    {f} {Γ : Context σ f} {φ : OpenFormula σ f} (h : Derives T Γ φ) :
    ℳ.entails Γ φ := by
  rcases h with ⟨d⟩
  exact R.proof_sound hT d

/-- 背景不认可矛盾且认可理论公理，就排除该理论的外部标准矛盾证明。 -/
theorem consistent_of_models (R : Sem_rules ℳ)
    (h₀ : ¬ ℳ.holds (.falsum : Sentence σ)) {T : Theory σ} (hT : ℳ.models T) :
    Derives.Consistent T ([] : Context σ []) :=
  fun h => h₀ (R.derives_sound hT h)

end Sem_rules

namespace Native
variable {σ : Signature.{u, v, w}} (ℳ : Structure.{u, v, w, x} σ)

/-- 原生背景保持原结构的载体 universe。 -/
abbrev background : Sem_background.{u, v, w, max u x, max u x} σ where
  context := (algebra ℳ).toSem_context
  valid p := ∀ ρ, p ρ

/-- 原结构的函数、关系在默认背景中的实际解释。 -/
abbrev model : Sem_model (background ℳ) where
  app := (algebra ℳ).app
  rel := (algebra ℳ).rel

theorem holds_iff {f} (φ : OpenFormula σ f) :
    (model ℳ).holds φ ↔ ∀ ρ : Env ℳ [] f, Formula.satisfies ρ φ :=
  ⟨fun h ρ => (fm_eq ℳ φ ρ).mp (h ρ), fun h ρ => (fm_eq ℳ φ ρ).mpr (h ρ)⟩

/-- 默认模型性精确恢复原 `Theory.Models`，没有增加任何模型条件。 -/
theorem models_iff (T : Theory σ) : (model ℳ).models T ↔ Theory.Models ℳ T := by
  constructor
  · intro h φ hφ
    exact (holds_iff ℳ φ).mp (h φ hφ) Env.empty
  · intro h φ hφ
    apply (holds_iff ℳ φ).mpr
    intro ρ
    rw [Env.empty_unique ρ]
    exact h φ hφ

/-- 原生六规则证书；非空性只在删除未使用的自由变量时使用。 -/
theorem rules : Sem_rules (model ℳ) where
  axiom_valid h := (holds_iff ℳ _).mpr (fun ρ => h.sound ρ)
  sentence_lift h := by
    apply (holds_iff ℳ _).mpr
    intro ρ
    exact (Formula.satisfies_fromSentence ρ _).mpr ((holds_iff ℳ _).mp h Env.empty)
  mp h k := by
    apply (holds_iff ℳ _).mpr
    intro ρ
    exact (holds_iff ℳ _).mp k ρ ((holds_iff ℳ _).mp h ρ)
  generalize h := by
    apply (holds_iff ℳ _).mpr
    intro ρ
    apply (Formula.satisfies_forallFreeTop ρ _).mpr
    intro a
    exact (holds_iff ℳ _).mp h (ρ.pushFree a)
  strengthen {f} {s} {φ} h := by
    apply (holds_iff ℳ _).mpr
    intro ρ
    obtain ⟨a⟩ := ℳ.nonempty s
    exact (Formula.satisfies_weakenFree ρ a _).mp ((holds_iff ℳ _).mp h (ρ.pushFree a))
  substitute {f} {f'} θ {φ} h := by
    apply (holds_iff ℳ _).mpr
    intro ρ
    apply (Formula.satisfies_substituteFree ρ θ _).mpr
    exact (holds_iff ℳ _).mp h (ρ.pullback (Substitution.free_map θ))

/-- 原生一致性接口不使用完备性、枚举、quotation 或额外选择实例。 -/
theorem consistent {T : Theory σ} (hT : Theory.Models ℳ T) :
    Derives.Consistent T ([] : Context σ []) :=
  (rules ℳ).consistent_of_models
    (fun h => (holds_iff ℳ _).mp h Env.empty) ((models_iff ℳ T).mpr hT)

end Native

namespace Ast
variable {σ : Signature.{u, v, w}}

/-- 理论内部的标准语法视角：成立表示背景理论可证，而非存在外部模型。 -/
abbrev background (U : Theory σ) :
    Sem_background.{u, v, w, max u v w, max u v w} σ where
  context := (algebra σ).toSem_context
  valid φ := Provable U φ

/-- 默认语法模型逐字解释原符号；同一背景也允许其他已核验的符号解释。 -/
abbrev model (U : Theory σ) : Sem_model (background U) where
  app := (algebra σ).app
  rel := (algebra σ).rel

theorem holds_iff (U : Theory σ) {f} (φ : OpenFormula σ f) :
    (model U).holds φ ↔ Provable U φ := by
  change Provable U ((algebra σ).fm φ) ↔ Provable U φ
  rw [fm_eq]

/-- 纯句法背景的六规则证书由原核构造子给出。 -/
theorem rules (U : Theory σ) : Sem_rules (model U) where
  axiom_valid h := (holds_iff U _).mpr (Provable.logical_axiom h)
  sentence_lift {f} {φ} h := by
    apply (holds_iff U _).mpr
    have k := (holds_iff U φ).mp h
    cases f with
    | nil => exact k
    | cons s f =>
        simpa [Formula.fromSentence, Formula.renameFree, Renaming.emptyFree] using
          Provable.free_renaming (VariableRenaming.empty : VariableRenaming [] (s :: f)) k
  mp h k := (holds_iff U _).mpr (Provable.modus_ponens
    ((holds_iff U _).mp h) ((holds_iff U _).mp k))
  generalize h := (holds_iff U _).mpr (Provable.forall_generalization ((holds_iff U _).mp h))
  strengthen h := (holds_iff U _).mpr (Provable.free_strengthening ((holds_iff U _).mp h))
  substitute {f} {f'} θ {φ} h :=
    (holds_iff U _).mpr (Provable.free_substitution θ ((holds_iff U _).mp h))

/-- 任意背景理论都认可自己的公理；这里没有一致性或模型存在性前提。 -/
theorem models_self (U : Theory σ) : (model U).models U := by
  intro φ h
  exact (holds_iff U φ).mpr (Provable.theory_axiom (free := []) h)

/-- 内部标准推导可以在背景理论中逐规则回放，但不被反射为外部模型真值。 -/
theorem derives_transfer {U T : Theory σ} (hT : (model U).models T)
    {f} {Γ : Context σ f} {φ : OpenFormula σ f} (h : Derives T Γ φ) : Derives U Γ φ :=
  (holds_iff U _).mp ((rules U).derives_sound hT h)

end Ast
end YesMetaZFC.Model
