import YesMetaZFC.SetTheory.Definitional.Project

/-! # 自由闭合原公式只依赖绑定赋值 -/

namespace YesMetaZFC.SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

theorem term_closed_env_l {n} (t : Term n) (ht : t.freeSupport = []) {ρ η : Env M n}
    (he : ρ.bound = η.bound) : t.eval ρ = t.eval η := by
  cases t with
  | bound i => exact congrFun he i
  | free i => cases ht

theorem Formula.closed_env_l {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) {ρ η : Env M n}
    (he : ρ.bound = η.bound) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  induction φ <;> simp only [Definitional.Formula.FreeClosed] at hφ
  case falsum => simp only [Formula.satisfies_falsum_iff]
  case truth => simp only [Formula.satisfies_truth_iff]
  case mem x y => simp only [Formula.satisfies_mem_iff, term_closed_env_l x hφ.1 he, term_closed_env_l y hφ.2 he]
  case atom s _ a =>
    have ha : a.eval ρ = a.eval η := funext fun i => term_closed_env_l (a.get i) (hφ i) he
    cases s <;> simp only [Formula.satisfies, Definitional.Semantics.satisfies, Semantics.interpretation, ha]
  case neg φ ih => simpa only [Formula.satisfies_neg_iff] using not_congr (ih hφ he)
  case conj φ ψ ih jh => simpa only [Formula.satisfies_conj_iff] using and_congr (ih hφ.1 he) (jh hφ.2 he)
  case disj φ ψ ih jh => simpa only [Formula.satisfies_disj_iff] using or_congr (ih hφ.1 he) (jh hφ.2 he)
  case imp φ ψ ih jh => simpa only [Formula.satisfies_imp_iff] using imp_congr (ih hφ.1 he) (jh hφ.2 he)
  case iff φ ψ ih jh => simpa only [Formula.satisfies_iff_iff] using iff_congr (ih hφ.1 he) (jh hφ.2 he)
  case forallE φ ih =>
    simp only [Formula.satisfies_forall_iff]
    exact forall_congr' fun x => ih hφ (funext (Fin.cases rfl (congrFun he)))
  case existsE φ ih =>
    simp only [Formula.satisfies_exists_iff]
    exact exists_congr fun x => ih hφ (funext (Fin.cases rfl (congrFun he)))

end YesMetaZFC.SetTheory.Definitional.Project
