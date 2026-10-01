import YesMetaZFC.Model.SetTheory.Internal.Prefix

/-! # 原 Project AST 的原子消去

目标仍是同一个生产 AST 的第 0 层，只把外延等同与子集展开为原定义正文。
语义对应对任意结构成立，不给编码模型额外添加外延性假设。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u

def source_core_l : {a n : Nat} → Formula a n → Formula 0 n
  | _, _, .falsum => .falsum
  | _, _, .truth => .truth
  | _, _, .mem s t => .mem s t
  | _, _, .atom r _ ts => (definitions.body r).bind (fun i => ts i)
  | _, _, .neg φ => .neg (source_core_l φ)
  | _, _, .conj φ ψ => .conj (source_core_l φ) (source_core_l ψ)
  | _, _, .disj φ ψ => .disj (source_core_l φ) (source_core_l ψ)
  | _, _, .imp φ ψ => .imp (source_core_l φ) (source_core_l ψ)
  | _, _, .iff φ ψ => .iff (source_core_l φ) (source_core_l ψ)
  | _, _, .forallE φ => .forallE (source_core_l φ)
  | _, _, .existsE φ => .existsE (source_core_l φ)

theorem source_core_closed_l {a n} (φ : Formula a n) (hφ : φ.FreeClosed) :
    (source_core_l φ).FreeClosed := by
  induction φ <;> simp only [source_core_l, Definitional.Formula.FreeClosed] at hφ ⊢
  case mem s t => exact hφ
  case atom r _ ts =>
    change ∀ i, (ts i).freeSupport = [] at hφ
    exact (Definitional.Formula.freeClosed_bind_iff_of_closed _ hφ _).mpr (definitions.bodyFreeClosed r)
  case neg φ ih => exact ih hφ
  case conj φ ψ ih jh | disj φ ψ ih jh | imp φ ψ ih jh | iff φ ψ ih jh =>
    exact ⟨ih hφ.1, jh hφ.2⟩
  case forallE φ ih | existsE φ ih => exact ih hφ

theorem source_core_sat_l {M : Structure.{u}} {a n} (φ : Formula a n) (ρ : Env M n) :
    Definitional.Semantics.satisfies Semantics.interpretation ρ (source_core_l φ) ↔
      Definitional.Semantics.satisfies Semantics.interpretation ρ φ := by
  induction φ <;> simp only [source_core_l, Definitional.Semantics.satisfies]
  case atom r _ ts =>
    rw [Definitional.Semantics.satisfies_bind]
    cases r <;> simp [definitions, Semantics.interpretation,
      Definitional.Semantics.satisfies, Definitional.Env.substitute, Definitional.Term.eval, Env.push] <;> rfl
  case neg φ ih => exact not_congr (ih ρ)
  case conj φ ψ ih jh => exact and_congr (ih ρ) (jh ρ)
  case disj φ ψ ih jh => exact or_congr (ih ρ) (jh ρ)
  case imp φ ψ ih jh => exact imp_congr (ih ρ) (jh ρ)
  case iff φ ψ ih jh => exact iff_congr (ih ρ) (jh ρ)
  case forallE φ ih => exact forall_congr' (fun x => ih (ρ.push x))
  case existsE φ ih => exact exists_congr (fun x => ih (ρ.push x))

end YesMetaZFC.SetTheory.Internal
