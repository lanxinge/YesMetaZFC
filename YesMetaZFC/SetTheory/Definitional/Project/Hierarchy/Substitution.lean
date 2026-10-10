import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Syntax

/-! # 有界公式的替换闭性 -/

namespace YesMetaZFC.SetTheory.Definitional.Project

namespace Formula.IsDelta0

/-- 项替换保持有界公式；它只改变变量，不引入新的量词。 -/
theorem bind_l {n m} {φ : Formula 1 n} (h : φ.IsDelta0) (e : Fin n → Term m) :
    Formula.IsDelta0 (φ.bind e) := by
  induction h generalizing m with
  | falsum => exact .falsum
  | truth => exact .truth
  | mem s t => exact .mem _ _
  | atom r hr ts => exact .atom _ _ _
  | neg h ih => exact .neg (ih e)
  | conj h g ih jh => exact .conj (ih e) (jh e)
  | disj h g ih jh => exact .disj (ih e) (jh e)
  | imp h g ih jh => exact .imp (ih e) (jh e)
  | iff h g ih jh => exact .iff (ih e) (jh e)
  | forallMem t h ih =>
      have ht : t.weaken.bind (Term.liftSubstitution e) = (t.bind e).weaken := by cases t <;> rfl
      simpa only [Formula.forallMem, Definitional.Formula.bind, ht] using!
        (IsDelta0.forallMem (t.bind e) (ih (Term.liftSubstitution e)))
  | existsMem t h ih =>
      have ht : t.weaken.bind (Term.liftSubstitution e) = (t.bind e).weaken := by cases t <;> rfl
      simpa only [Formula.existsMem, Definitional.Formula.bind, ht] using!
        (IsDelta0.existsMem (t.bind e) (ih (Term.liftSubstitution e)))

theorem rename_l {n m} {φ : Formula 1 n} (h : φ.IsDelta0) (e : Fin n → Fin m) :
    Formula.IsDelta0 (φ.rename e) := h.bind_l (fun i => .bound (e i))

end Formula.IsDelta0

end YesMetaZFC.SetTheory.Definitional.Project
