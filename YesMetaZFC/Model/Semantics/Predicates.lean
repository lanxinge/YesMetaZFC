import YesMetaZFC.Model.Semantics.SyntaxView
import YesMetaZFC.Model.FirstOrder.Valuation
import YesMetaZFC.Model.SecondOrder

/-! # 可选谓词域与相对封闭性

关系对象和它所表示的上下文谓词分开给出。`Full` 只相对于所选语义代数的谓词域，
不把内部公式域等同于外部幂集，也不把封闭性放入基础结构的必填字段。
-/

namespace YesMetaZFC.Model
open Logic Logic.FirstOrder
universe u v w x y z

variable {σ : Signature.{u, v, w}}

/-- 在固定背景中可量化的关系对象及其谓词解释。 -/
structure Predicate_domain (A : Sem_algebra.{u, v, w, x, y} σ) where
  Rel : SortContext σ → Type z
  denote : ∀ {ss}, Rel ss → A.Pr [] ss

namespace Predicate_domain
variable {A : Sem_algebra.{u, v, w, x, y} σ}

/-- 指定背景的全部谓词都在关系域中有代表。 -/
def Full (D : Predicate_domain.{u, v, w, x, y, z} A) : Prop :=
  ∀ {ss}, Function.Surjective (D.denote (ss := ss))

/-- 对标准公式解释像封闭；该定义本身不声称覆盖全部背景谓词。 -/
def Formula_closed (D : Predicate_domain.{u, v, w, x, y, z} A) : Prop :=
  ∀ {ss} (φ : Formula σ [] ss), ∃ r, D.denote r = A.fm φ

theorem formula_closed_of_full {D : Predicate_domain.{u, v, w, x, y, z} A}
    (h : D.Full) : D.Formula_closed := fun φ => h (A.fm φ)

/-- 规范关系域直接使用所选背景的谓词对象，保持该谓词域的 universe。 -/
def canonical (A : Sem_algebra.{u, v, w, x, y} σ) :
    Predicate_domain.{u, v, w, x, y, y} A where
  Rel ss := A.Pr [] ss
  denote := id

theorem canonical_full (A : Sem_algebra.{u, v, w, x, y} σ) : (canonical A).Full :=
  fun p => ⟨p, rfl⟩

end Predicate_domain

namespace Native
open Automation.RelationalTranslation Automation.ModelClosure

/-- 既有 Henkin 关系域直接接入背景谓词接口。 -/
def predicate_domain (H : SecondOrder.Henkin.Structure.{u, v, w, x, z} σ) :
    Predicate_domain.{u, v, w, max u x, max u x, z} (algebra H.base) where
  Rel := H.relDomain
  denote r ρ := H.relInterp _ r (valuesOfAssignment ρ.freeVal)

/-- 原生相对满性精确表示“覆盖所有外部类型正确谓词”，没有假定关系对象外延性。 -/
theorem predicate_full_iff (H : SecondOrder.Henkin.Structure.{u, v, w, x, z} σ) :
    (predicate_domain H).Full ↔
      ∀ ss (p : Values H.base.Carrier ss → Prop),
        ∃ r, ∀ a, H.relInterp ss r a ↔ p a := by
  constructor
  · intro h ss p
    obtain ⟨r, hr⟩ := h (fun ρ => p (valuesOfAssignment ρ.freeVal))
    refine ⟨r, fun a => ?_⟩
    have k := congrArg (fun q => q (templateEnv a)) hr
    simpa only [predicate_domain, templateEnv, values_assignment] using Iff.of_eq k
  · intro h ss p
    obtain ⟨r, hr⟩ := h ss (fun a => p (templateEnv a))
    refine ⟨r, ?_⟩
    funext ρ
    apply propext
    simpa only [predicate_domain, template_of_env] using hr (valuesOfAssignment ρ.freeVal)

end Native
end YesMetaZFC.Model
