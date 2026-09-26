import YesMetaZFC.Automation.FirstOrderDerives
import YesMetaZFC.Model.Boolean.Completion
import YesMetaZFC.Model.Boolean.Filter

/-! # 林登鲍姆布尔代数

对任意签名、理论、自由变量上下文和局部假设，按原 `Derives` 的可证等价取商。
运算直接由 `Quotient.liftOn₂` 下降，不选代表元，也不以语义等价替代可证等价。
这里处理原 AST；非标准模型内部的公式码与内部证明码不自动等于此宿主商。
-/

namespace YesMetaZFC.Logic.FirstOrder.Lindenbaum
open Model.Boolean
universe u v w
variable {σ : Signature.{u,v,w}} (T : Theory σ) {Δ : SortContext σ} (Γ : Context σ Δ)

def setoid_m : Setoid (OpenFormula σ Δ) where
  r φ ψ := Derives T Γ (.iff φ ψ)
  iseqv := ⟨fun _ => by derive_prop, fun _ => by derive_prop,
    fun _ _ => by derive_prop⟩

abbrev Algebra_m := Quotient (setoid_m T Γ)

def class_m (φ : OpenFormula σ Δ) : Algebra_m T Γ := Quotient.mk _ φ

theorem eq_iff_m (φ ψ : OpenFormula σ Δ) :
    class_m T Γ φ = class_m T Γ ψ ↔ Derives T Γ (.iff φ ψ) :=
  ⟨Quotient.exact, fun h => Quotient.sound (s := setoid_m T Γ) h⟩

def le_m (a b : Algebra_m T Γ) : Prop :=
  Quotient.liftOn₂ a b (fun φ ψ => Derives T Γ (.imp φ ψ)) (by
    intro φ ψ χ θ h k
    apply propext
    change Derives T Γ (.iff φ χ) at h
    change Derives T Γ (.iff ψ θ) at k
    constructor <;> intro h₁ <;> derive_prop)

def meet_m (a b : Algebra_m T Γ) : Algebra_m T Γ :=
  Quotient.liftOn₂ a b (fun φ ψ => class_m T Γ (.conj φ ψ)) (by
    intro φ ψ χ θ h k
    apply Quotient.sound
    change Derives T Γ (.iff φ χ) at h
    change Derives T Γ (.iff ψ θ) at k
    change Derives T Γ (.iff (.conj φ ψ) (.conj χ θ))
    derive_prop)

def imp_m (a b : Algebra_m T Γ) : Algebra_m T Γ :=
  Quotient.liftOn₂ a b (fun φ ψ => class_m T Γ (.imp φ ψ)) (by
    intro φ ψ χ θ h k
    apply Quotient.sound
    change Derives T Γ (.iff φ χ) at h
    change Derives T Γ (.iff ψ θ) at k
    change Derives T Γ (.iff (.imp φ ψ) (.imp χ θ))
    derive_prop)

/-- 原经典推导核的实际布尔代数，不要求理论一致。 -/
def algebra_m : BA_alg (Algebra_m T Γ) where
  le := le_m T Γ
  bot := class_m T Γ .falsum
  meet := meet_m T Γ
  imp := imp_m T Γ
  le_refl a := Quotient.inductionOn a (fun φ => by
    change Derives T Γ (.imp φ φ)
    derive_prop)
  le_trans := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro φ ψ χ h k
    change Derives T Γ (.imp φ ψ) at h
    change Derives T Γ (.imp ψ χ) at k
    change Derives T Γ (.imp φ χ)
    derive_prop
  le_antisymm := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ h k
    apply Quotient.sound
    change Derives T Γ (.imp φ ψ) at h
    change Derives T Γ (.imp ψ φ) at k
    change Derives T Γ (.iff φ ψ)
    derive_prop
  bot_le a := Quotient.inductionOn a (fun φ => by
    change Derives T Γ (.imp .falsum φ)
    derive_prop)
  le_meet_iff a b c := Quotient.inductionOn₃ a b c (fun φ ψ χ => by
    change Derives T Γ (.imp φ (.conj ψ χ)) ↔
      Derives T Γ (.imp φ ψ) ∧ Derives T Γ (.imp φ χ)
    constructor
    · intro h; exact ⟨by derive_prop, by derive_prop⟩
    · rintro ⟨h, k⟩; derive_prop)
  le_imp_iff a b c := Quotient.inductionOn₃ a b c (fun φ ψ χ => by
    change Derives T Γ (.imp φ (.imp ψ χ)) ↔ Derives T Γ (.imp (.conj φ ψ) χ)
    constructor <;> intro h <;> derive_prop)
  double_neg a := Quotient.inductionOn a (fun φ => by
    apply Quotient.sound
    change Derives T Γ (.iff (.imp (.imp φ .falsum) .falsum) φ)
    derive_prop)

theorem class_top_m (φ : OpenFormula σ Δ) :
    class_m T Γ φ = (algebra_m T Γ).top ↔ Derives T Γ φ := by
  change class_m T Γ φ = class_m T Γ (.imp .falsum .falsum) ↔ _
  rw [eq_iff_m]
  constructor <;> intro h <;> derive_prop

theorem class_neg_m (φ : OpenFormula σ Δ) :
    class_m T Γ (.neg φ) = (algebra_m T Γ).neg (class_m T Γ φ) := by
  apply Quotient.sound
  change Derives T Γ (.iff (.neg φ) (.imp φ .falsum))
  derive_prop

theorem class_disj_m (φ ψ : OpenFormula σ Δ) :
    class_m T Γ (.disj φ ψ) = (algebra_m T Γ).join (class_m T Γ φ) (class_m T Γ ψ) := by
  apply Quotient.sound
  change Derives T Γ (.iff (.disj φ ψ)
    (.imp (.conj (.imp φ .falsum) (.imp ψ .falsum)) .falsum))
  derive_prop

theorem nontrivial_iff_m :
    (algebra_m T Γ).bot ≠ (algebra_m T Γ).top ↔ ¬ Derives T Γ .falsum := by
  exact not_congr (class_top_m T Γ .falsum)

/-- 完备化直接消费可证等价商，不借用逻辑完备性或超滤扩张。 -/
def completion_m : CB_alg (BA_alg.Cut_l (algebra_m T Γ)) := BA_alg.Cut_l.algebra_l

/-- 扩张理论的可证公式在原林登鲍姆代数中给出滤子。 -/
def theory_filter_m (U : Theory σ) (h : Theory.Extends U T) : Filter_l (algebra_m T Γ) where
  mem a := Quotient.liftOn a (fun φ => Derives U Γ φ) (by
    intro φ ψ k
    have k₁ := Derives.theory_weaken h (show Derives T Γ (.iff φ ψ) from k)
    apply propext
    exact ⟨fun hp => Derives.iff_elim_left k₁ hp, fun hp => Derives.iff_elim_right k₁ hp⟩)
  top_mem := by
    change Derives U Γ (.imp .falsum .falsum)
    derive_prop
  upward := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ hp hq
    have h₁ := Derives.theory_weaken h (show Derives T Γ (.imp φ ψ) from hq)
    exact Derives.imp_elim h₁ hp
  meet_mem := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro φ ψ hp hq
    exact Derives.conj_intro hp hq

theorem theory_filter_proper_m (U : Theory σ) (h : Theory.Extends U T) :
    (theory_filter_m T Γ U h).Proper_l ↔ ¬ Derives U Γ .falsum := Iff.rfl

/-- 超滤性精确对应扩张理论的一致性和逐公式完备性。 -/
theorem theory_filter_maximal_m (U : Theory σ) (h : Theory.Extends U T) :
    (theory_filter_m T Γ U h).Maximal_l ↔ ¬ Derives U Γ .falsum ∧
      ∀ φ : OpenFormula σ Δ, Derives U Γ φ ∨ Derives U Γ (.neg φ) := by
  rw [Filter_l.maximal_iff_l, theory_filter_proper_m]
  apply and_congr_right
  intro _
  constructor
  · intro k φ
    have h₁ := k (class_m T Γ φ)
    rw [← class_neg_m T Γ φ] at h₁
    exact h₁
  · intro k a
    refine Quotient.inductionOn a ?_
    intro φ
    change (theory_filter_m T Γ U h).mem (class_m T Γ φ) ∨
      (theory_filter_m T Γ U h).mem ((algebra_m T Γ).neg (class_m T Γ φ))
    rw [← class_neg_m T Γ φ]
    exact k φ

end YesMetaZFC.Logic.FirstOrder.Lindenbaum
