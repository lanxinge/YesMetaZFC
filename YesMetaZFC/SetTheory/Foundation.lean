import YesMetaZFC.SetTheory.SetConstruction

/-!
# 基础公理的语义推论

本文件集中整理 Foundation 的普通 Lean 语义接口，并导出无自隶属与不存在全集等常用
推论。具体序数或自然数模块不再重复展开对象语言公理。
-/

namespace YesMetaZFC
namespace SetTheory

universe u

namespace Axioms

/-- 基础公理的项目核语义。 -/
theorem satisfies_foundation_iff {ℳ : Structure.{u}}
    (free : FreeVarId → ℳ.Domain) :
    Definitional.Project.Formula.satisfies
        ({ bound := Fin.elim0, free := free } : Env ℳ 0)
        foundation.formula ↔
      ∀ set, (∃ value, ℳ.mem value set) →
        ∃ minimal, ℳ.mem minimal set ∧
          ∀ value, ℳ.mem value set → ¬ ℳ.mem value minimal := by
  unfold foundation
  dsimp only [Definitional.Project.Sentence.ofFormula]
  simp only [
    Definitional.Project.Formula.satisfies_forall_iff,
    Definitional.Project.Formula.satisfies_imp_iff,
    Definitional.Project.Formula.satisfies_exists_iff,
    Definitional.Project.Formula.satisfies_existsMem_iff,
    Definitional.Project.Formula.satisfies_forallMem_iff,
    Definitional.Project.Formula.satisfies_neg_iff,
    Definitional.Project.Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

end Axioms

namespace KP

/-- 每个非空集合都具有一个与该集合不交的成员。 -/
theorem exists_mem_minimal {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) {set : ℳ.Domain}
    (hNonempty : ∃ value, ℳ.mem value set) :
    ∃ minimal, ℳ.mem minimal set ∧
      ∀ value, ℳ.mem value set → ¬ ℳ.mem value minimal := by
  let free : FreeVarId → ℳ.Domain := fun _ =>
    Classical.choice ℳ.nonempty
  have hFoundation :=
    hKP.2 Axioms.foundation Axiom.foundation free
  exact
    (Axioms.satisfies_foundation_iff free).mp hFoundation
      set hNonempty

/-- Foundation 排除集合的自隶属。 -/
theorem mem_irrefl {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) (set : ℳ.Domain) :
    ¬ ℳ.mem set set := by
  intro hSelf
  rcases exists_singleton hKP set with
    ⟨singleton, hSingleton⟩
  have hNonempty : ∃ value, ℳ.mem value singleton :=
    ⟨set, (hSingleton set).mpr rfl⟩
  rcases exists_mem_minimal hKP hNonempty with
    ⟨minimal, hMinimal, hDisjoint⟩
  have hMinimalEq : minimal = set :=
    (hSingleton minimal).mp hMinimal
  subst minimal
  exact hDisjoint set
    ((hSingleton set).mpr rfl) hSelf

/-- Foundation 排除包含所有对象的全集。 -/
theorem no_universalSet {ℳ : Structure.{u}}
    (hKP : ℳ.Models SetTheory.KP) :
    ¬ ∃ universal, ∀ value, ℳ.mem value universal := by
  rintro ⟨universal, hUniversal⟩
  exact mem_irrefl hKP universal
    (hUniversal universal)

end KP

end SetTheory
end YesMetaZFC
