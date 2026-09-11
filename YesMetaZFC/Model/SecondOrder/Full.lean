import YesMetaZFC.Model.Semantics.Predicates

/-! # Full 二阶语义的同层实例

关系对象是载体上的谓词本身，没有选择、商化或载体提升。
原有 Full 满足关系与这个实际 Henkin 结构逐公式相同。
-/

namespace YesMetaZFC.Logic.SecondOrder.Full
open FirstOrder
universe u v w i x
variable {σ : Signature.{u, v, w}}

/-- 同一模型上全部有限元谓词形成的规范二阶结构。 -/
abbrev structure_of (ℳ : FirstOrder.Structure.{u, v, w, x} σ) :
    Henkin.Structure.{u, v, w, x, max u x} σ where
  base := ℳ
  relDomain := Relation ℳ
  relInterp _ p := p

/-- 规范结构实际覆盖原生背景的全部谓词。 -/
theorem predicate_full (ℳ : FirstOrder.Structure.{u, v, w, x} σ) :
    (Model.Native.predicate_domain (structure_of ℳ)).Full :=
  (Model.Native.predicate_full_iff _).mpr (fun _ p => ⟨p, fun _ => Iff.rfl⟩)

/-- Full 环境在规范 Henkin 结构中的逐字段实现。 -/
def Env.to_henkin {ℳ : FirstOrder.Structure.{u, v, w, x} σ}
    {b f : ObjContext.{u, v, w, i} σ} {r t : RelContext.{u, v, w, i} σ}
    (ρ : Env ℳ b f r t) : Henkin.Env (structure_of ℳ) b f r t where
  firstOrder := ρ.firstOrder
  boundRel := ρ.boundRel
  freeRel := ρ.freeRel

/-- 对象量词与关系量词都使用同一环境扩展，因而整个二阶公式保持真值。 -/
theorem satisfies_iff {ℳ : FirstOrder.Structure.{u, v, w, x} σ}
    {b f : ObjContext.{u, v, w, i} σ} {r t : RelContext.{u, v, w, i} σ}
    (φ : SecondOrder.Formula σ b f r t) (ρ : Env ℳ b f r t) :
    Henkin.Formula.satisfies ρ.to_henkin φ ↔ Formula.satisfies ρ φ := by
  induction φ with
  | falsum | truth | rel | equal | relBound | relFree => rfl
  | neg φ h => exact not_congr (h _)
  | conj φ ψ h k => exact and_congr (h _) (k _)
  | disj φ ψ h k => exact or_congr (h _) (k _)
  | imp φ ψ h k => exact imp_congr (h _) (k _)
  | iff φ ψ h k => exact iff_congr (h _) (k _)
  | forallObj s φ h =>
      exact ⟨fun hp a => (h (ρ.pushObj s a)).mp (hp a),
        fun hp a => (h (ρ.pushObj s a)).mpr (hp a)⟩
  | existsObj s φ h =>
      exact ⟨fun ⟨a, hp⟩ => ⟨a, (h (ρ.pushObj s a)).mp hp⟩,
        fun ⟨a, hp⟩ => ⟨a, (h (ρ.pushObj s a)).mpr hp⟩⟩
  | forallRel ss φ h =>
      exact ⟨fun hp p => (h (ρ.pushRel ss p)).mp (hp p),
        fun hp p => (h (ρ.pushRel ss p)).mpr (hp p)⟩
  | existsRel ss φ h =>
      exact ⟨fun ⟨p, hp⟩ => ⟨p, (h (ρ.pushRel ss p)).mp hp⟩,
        fun ⟨p, hp⟩ => ⟨p, (h (ρ.pushRel ss p)).mpr hp⟩⟩

end YesMetaZFC.Logic.SecondOrder.Full
