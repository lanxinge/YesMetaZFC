import YesMetaZFC.Model.Semantics.Background

/-! # 可选的内部语法与证明码视角

内部码可有标准像以外的对象。接口只要求标准嵌入及其代入作用，不提供总解码器、
外部良基性或“内部证明可还原为标准证明”的字段。默认实例就是当前 AST 与原证明树。
此能力独立于语义背景，并不要求每个模型都拥有内部语法或证明编码。
-/

namespace YesMetaZFC.Model
open Logic Logic.FirstOrder
universe u v w x y z x' y'

variable {σ : Signature.{u, v, w}}

-- 代码族沿用其背景所选择的两个 universe，不强制编码为自然数。
set_option linter.checkUnivs false in
/-- 一个实际语法呈现。注入性只约束标准像，不声称它覆盖所有内部码。 -/
structure Syntax_view (σ : Signature.{u, v, w}) where
  code : Sem_algebra.{u, v, w, x, y} σ
  substitution : Sem_substitution code
  action : Sem_action substitution
  tm_injective : ∀ {b f s}, Function.Injective (code.tm (b := b) (f := f) (s := s))
  fm_injective : ∀ {b f}, Function.Injective (code.fm (b := b) (f := f))

namespace Ast

/-- 所有语言都可使用默认 AST，不需要可数签名或自然数 quotation。 -/
def syntax_view (σ : Signature.{u, v, w}) :
    Syntax_view.{u, v, w, max u v w, max u v w} σ where
  code := algebra σ
  substitution := substitution σ
  action := action σ
  tm_injective := by intro b f s t t' h; simpa only [tm_eq] using h
  fm_injective := by intro b f φ ψ h; simpa only [fm_eq] using h

end Ast

namespace Sem_map
variable {A : Sem_algebra.{u, v, w, x, y} σ}
  {𝒱 : Sem_background.{u, v, w, x', y'} σ}
  (ℳ : Sem_model 𝒱) (I : Sem_map A ℳ.algebra)

/-- 沿给定语法解释检查标准理论公理；不量化尚未给出语义的非标准证明码。 -/
def models (T : Theory σ) : Prop := ∀ φ, T φ → 𝒱.valid (I.fm (A.fm φ))

/-- 标准像上的模型性由完整公式解释交换决定，不需要所有内部码的反射。 -/
theorem models_iff (T : Theory σ) : I.models ℳ T ↔ ℳ.models T := by
  unfold models Sem_model.models Sem_model.holds
  simp only [I.fm_eval]

end Sem_map

/-- 证明码接口只承诺标准证明的前向表示，检查关系可包含非标准证明。 -/
structure Proof_view (C : Sem_algebra.{u, v, w, x, y} σ) (T : Theory σ) where
  Code : SortContext σ → Type z
  checks : ∀ {f}, Code f → C.Pr [] f → Prop
  quote : ∀ {f φ}, HilbertDerivation T f φ → Code f
  quote_checks : ∀ {f φ} (d : HilbertDerivation T f φ), checks (quote d) (C.fm φ)

namespace Proof_view
variable {C : Sem_algebra.{u, v, w, x, y} σ} {T : Theory σ}
  (P : Proof_view.{u, v, w, x, y, z} C T)

/-- 给出一个被接受的码的外部存在性；不冒充背景量词所表达的内部存在判断。 -/
def has_proof {f} (φ : C.Pr [] f) : Prop := ∃ p, P.checks p φ

/-- 标准推导总能进入其已核验的内部表示。没有反向解码步骤。 -/
theorem standard_provable {f} {φ : OpenFormula σ f} (h : Provable T φ) :
    P.has_proof (C.fm φ) := by
  rcases h with ⟨d⟩
  exact ⟨P.quote d, P.quote_checks d⟩

/-- 无内部矛盾码足以排除标准矛盾证明；反方向不由接口提供。 -/
theorem standard_consistent (h : ¬ P.has_proof (C.bot (b := []) (f := []))) :
    Derives.Consistent T ([] : Context σ []) :=
  fun d => h (P.standard_provable d)

end Proof_view

namespace Ast

/-- 默认代码是带结论的实际 Hilbert 证明树，不引入另一套验证器。 -/
def proofs (T : Theory σ) :
    Proof_view.{u, v, w, max u v w, max u v w, max u v w} (algebra σ) T where
  Code f := Σ φ : OpenFormula σ f, HilbertDerivation T f φ
  checks p φ := p.1 = φ
  quote d := ⟨_, d⟩
  quote_checks _ := (fm_eq _).symm

/-- 只有默认 AST 证明树实例具有这个已证明的反向读取定理。 -/
theorem has_proof_iff (T : Theory σ) {f} (φ : OpenFormula σ f) :
    (proofs T).has_proof ((algebra σ).fm φ) ↔ Provable T φ := by
  constructor
  · rintro ⟨⟨ψ, d⟩, h⟩
    change ψ = (algebra σ).fm φ at h
    rw [fm_eq] at h
    exact ⟨d.castFormula h⟩
  · exact (proofs T).standard_provable

/-- 默认码的可靠性消费原生模型的实际公理证据。此结论不推广到任意内部码视角。 -/
theorem proof_sound (ℳ : Structure.{u, v, w, z} σ) {T : Theory σ}
    (hT : Theory.Models ℳ T) {f} {φ : OpenFormula σ f}
    (h : (proofs T).has_proof ((algebra σ).fm φ)) (ρ : Env ℳ [] f) :
    Formula.satisfies ρ φ :=
  ((has_proof_iff T φ).mp h).sound hT ρ

end Ast
end YesMetaZFC.Model
