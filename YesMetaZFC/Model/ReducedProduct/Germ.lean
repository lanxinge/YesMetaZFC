import YesMetaZFC.SetTheory.Filter.Logic

/-! # 滤子模下的依赖截面商

商的映射和谓词直接下降，不抽取代表元。函数空间和商保持 `max` 指定的原层；
一阶超幂入口会约束指标层级，使此 `max` 不提升模型载体。
-/

namespace YesMetaZFC.Model
open SetTheory
universe u v w x
variable {I : Type u} (U : Filter I) {A : I → Type v}

def germSetoid_l (A : I → Type v) : Setoid ((i : I) → A i) where
  r a b := U.sets (fun i => a i = b i)
  iseqv := ⟨fun _ => U.upward U.univ_mem (fun _ _ => rfl),
    fun h => U.upward h (fun _ hi => hi.symm),
    fun h k => U.upward (U.inter_mem h k) (fun _ hi => hi.1.trans hi.2)⟩

def Germ_l (A : I → Type v) : Type (max u v) := Quotient (germSetoid_l U A)

namespace Germ_l

def class_l (a : (i : I) → A i) : Germ_l U A := Quotient.mk _ a

theorem class_eq_l (a b : (i : I) → A i) :
    class_l U a = class_l U b ↔ U.sets (fun i => a i = b i) :=
  ⟨Quotient.exact, fun h => Quotient.sound (s := germSetoid_l U A) h⟩

theorem induction_l {P : Germ_l U A → Prop} (q : Germ_l U A)
    (h : ∀ a, P (class_l U a)) : P q := Quotient.inductionOn q h

/-- 仅在 Prop 中消去商；不提供抽取代表元的数据函数。 -/
theorem exists_rep_l (q : Germ_l U A) : ∃ a, class_l U a = q :=
  induction_l U (P := fun q => ∃ a, class_l U a = q) q (fun a => ⟨a, rfl⟩)

def map_l {B : I → Type w} (f : (i : I) → A i → B i) (q : Germ_l U A) : Germ_l U B :=
  Quotient.liftOn q (fun a => class_l U (fun i => f i (a i)))
    (fun _ _ h => Quotient.sound (U.upward h (fun i hi => congrArg (f i) hi)))

def map₂_l {B : I → Type w} {C : I → Type x}
    (f : (i : I) → A i → B i → C i) (q : Germ_l U A) (r : Germ_l U B) : Germ_l U C :=
  Quotient.liftOn₂ q r (fun a b => class_l U (fun i => f i (a i) (b i)))
    (fun _ _ _ _ h k => Quotient.sound
      (U.upward (U.inter_mem h k) (fun i hi => by
        dsimp at hi ⊢
        rw [hi.1, hi.2])))

def pred_l (P : (i : I) → A i → Prop) (q : Germ_l U A) : Prop :=
  Quotient.liftOn q (fun a => U.sets (fun i => P i (a i))) (fun _ _ h =>
    propext (U.congr_l (U.upward h (fun i hi => congrArg (P i) hi ▸ Iff.rfl))))

@[simp] theorem map_class_l {B : I → Type w} (f : (i : I) → A i → B i)
    (a : (i : I) → A i) : map_l U f (class_l U a) = class_l U (fun i => f i (a i)) := rfl

@[simp] theorem map₂_class_l {B : I → Type w} {C : I → Type x}
    (f : (i : I) → A i → B i → C i) (a : (i : I) → A i) (b : (i : I) → B i) :
    map₂_l U f (class_l U a) (class_l U b) = class_l U (fun i => f i (a i) (b i)) := rfl

@[simp] theorem pred_class_l (P : (i : I) → A i → Prop) (a : (i : I) → A i) :
    pred_l U P (class_l U a) ↔ U.sets (fun i => P i (a i)) := Iff.rfl

end Germ_l
end YesMetaZFC.Model
