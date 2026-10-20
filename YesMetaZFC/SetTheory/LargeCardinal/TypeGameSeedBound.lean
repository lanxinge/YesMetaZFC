import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRenewalSyntax

/-! # 原回答证书已经给出首个临界点的下界

只读取所属短扩展器公式中的 ω∈κ，不为读取这一事实另作一次树后继，
也不把该模型内部的超幂证书整体坍塌到背景。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem tg_image_omega_l {d} (ρ : Env M d) (ω κ δ l n U D u τ Q w b z r q h : Term d)
    (σ : Fin 7 → Term d) (valid : Formula.satisfies ρ (tg_image_m ω κ δ l n U D u τ Q w b z r q h σ)) :
    M.mem (ω.eval ρ) (κ.eval ρ) := by
  simp only [tg_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', core, _⟩ := valid
  simp only [ti_image_m, Formula.satisfies_conj_iff] at core
  have loc := (Formula.satisfies_conj_iff ..).mp core.2.2.2.2.2.1 |>.1
  simp only [ex_local_m, Formula.satisfies_conj_iff] at loc
  have short := loc.2.2.2.2
  change Formula.satisfies _ (.conj _ _) at short
  have pre := (Formula.satisfies_conj_iff ..).mp short |>.1
  change Formula.satisfies _ (.conj _ (.conj _ (.conj _ _))) at pre
  have bound := ((Formula.satisfies_conj_iff ..).mp
    ((Formula.satisfies_conj_iff ..).mp ((Formula.satisfies_conj_iff ..).mp pre).2).2).1
  have bound := (Formula.satisfies_mem_iff ..).mp bound
  cases ω <;> cases κ <;> simpa [Definitional.Term.bind, fin_cases, Fin.cases, Fin.induction,
    Fin.induction.go, Fin.succ, Definitional.Term.weaken, Definitional.Term.rename, Definitional.Term.eval, Env.push] using bound

theorem tg_successor_omega_l (ρ : Env M 38) (valid : Formula.satisfies ρ tg_successor0_m) :
    M.mem (ρ.bound 0) (ρ.bound 5) := by
  simp only [tg_successor0_m, tg_successor_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨τ, C, V, Q, w, η, Z, a, H, f₀, f₁, f₂, f₃, q₀, q₁, q₂, valid⟩ := valid
  simp only [tg_round_m, Formula.satisfies_conj_iff] at valid
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, image⟩ := valid
  exact tg_image_omega_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ image

end YesMetaZFC.SetTheory.LargeCardinal
