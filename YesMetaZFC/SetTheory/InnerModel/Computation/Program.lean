import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Graph

/-! # 集合程序及独立求值语义

程序有 n 个集合寄存器。局部绑定压栈；有界循环对源集合的每个成员求值，
形成模型内部的结果族，再取并。程序中没有公式求值或可定义性预言机。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

inductive Cp_code : Nat → Type where
  | var {n} : Fin n → Cp_code n
  | zero {n} : Cp_code n
  | op {n} : Rd_sym → Cp_code n → Cp_code n → Cp_code n → Cp_code n
  | let1 {n} : Cp_code n → Cp_code (n + 1) → Cp_code n
  | bunion {n} : Cp_code n → Cp_code (n + 1) → Cp_code n

def Cp_eval_d : {n : Nat} → Cp_code n → Env M n → M.Domain → Prop
  | _, .var i, ρ, y => y = ρ.bound i
  | _, .zero, _, y => ∀ t, ¬ M.mem t y
  | _, .op k p q r, ρ, y => ∃ a b c,
      Cp_eval_d p ρ a ∧ Cp_eval_d q ρ b ∧ Cp_eval_d r ρ c ∧ Rd_fun_d k a b c y
  | _, .let1 p q, ρ, y => ∃ a, Cp_eval_d p ρ a ∧ Cp_eval_d q (ρ.push a) y
  | _, .bunion p q, ρ, y => ∃ X R, Cp_eval_d p ρ X ∧
      (∀ z, M.mem z X → ∃ v, Cp_eval_d q (ρ.push z) v) ∧
      (∀ v, M.mem v R ↔ ∃ z, M.mem z X ∧ Cp_eval_d q (ρ.push z) v) ∧ M.IsUnionOf y R

theorem cp_eval_unique_l (hE : Extensional M) {n} (p : Cp_code n) (ρ : Env M n)
    {y z : M.Domain} (hy : Cp_eval_d p ρ y) (hz : Cp_eval_d p ρ z) : y = z := by
  induction p generalizing y z with
  | var i => exact hy.trans hz.symm
  | zero => exact hE.eq_of_same_members y z (fun t => iff_of_false (hy t) (hz t))
  | op k p q r ih jh kh =>
    obtain ⟨a, b, c, ha, hb, hc, hy⟩ := hy
    obtain ⟨a', b', c', ha', hb', hc', hz⟩ := hz
    have he := ih ρ ha ha'; subst a'
    have he := jh ρ hb hb'; subst b'
    have he := kh ρ hc hc'; subst c'
    exact rd_fun_unique_l hE hy hz
  | let1 p q ih jh =>
    obtain ⟨a, ha, hy⟩ := hy
    obtain ⟨b, hb, hz⟩ := hz
    have he := ih ρ ha hb; subst b
    exact jh (ρ.push a) hy hz
  | bunion p q ih _ =>
    obtain ⟨X, R, hx, _, hr, hy⟩ := hy
    obtain ⟨X', R', hx', _, hr', hz⟩ := hz
    have he := ih ρ hx hx'; subst X'
    have he := hE.eq_of_same_members R R' (fun t => (hr t).trans (hr' t).symm); subst R'
    exact hE.eq_of_same_members y z (fun t => (hy t).trans (hz t).symm)

/-- 计算证书的所有中间对象都在同一个内部集合界中。 -/
def Cp_cert_d : {n : Nat} → Cp_code n → Env M n → M.Domain → M.Domain → Prop
  | _, .var i, ρ, y, _ => y = ρ.bound i
  | _, .zero, _, y, _ => ∀ t, ¬ M.mem t y
  | _, .op k p q r, ρ, y, T => ∃ a, M.mem a T ∧ ∃ b, M.mem b T ∧ ∃ c, M.mem c T ∧
      Cp_cert_d p ρ a T ∧ Cp_cert_d q ρ b T ∧ Cp_cert_d r ρ c T ∧ Rd_fun_d k a b c y
  | _, .let1 p q, ρ, y, T => ∃ a, M.mem a T ∧ Cp_cert_d p ρ a T ∧ Cp_cert_d q (ρ.push a) y T
  | _, .bunion p q, ρ, y, T => ∃ X, M.mem X T ∧ ∃ R, M.mem R T ∧ Cp_cert_d p ρ X T ∧
      (∀ z, M.mem z X → ∃ v, M.mem v R ∧ Cp_cert_d q (ρ.push z) v T) ∧
      (∀ v, M.mem v R → ∃ z, M.mem z X ∧ Cp_cert_d q (ρ.push z) v T) ∧ M.IsUnionOf y R

theorem cp_cert_sound_l (hE : Extensional M) {n} (p : Cp_code n) (ρ : Env M n)
    {y T : M.Domain} (h : Cp_cert_d p ρ y T) : Cp_eval_d p ρ y := by
  induction p generalizing y with
  | var i => exact h
  | zero => exact h
  | op k p q r ih jh kh =>
    obtain ⟨a, _, b, _, c, _, ha, hb, hc, hy⟩ := h
    exact ⟨a, b, c, ih ρ ha, jh ρ hb, kh ρ hc, hy⟩
  | let1 p q ih jh =>
    obtain ⟨a, _, ha, hy⟩ := h
    exact ⟨a, ih ρ ha, jh (ρ.push a) hy⟩
  | bunion p q ih jh =>
    obtain ⟨X, _, R, _, hx, ht, hr, hy⟩ := h
    refine ⟨X, R, ih ρ hx, fun z hz => (ht z hz).imp (fun v hv => jh (ρ.push z) hv.2), fun v => ?_, hy⟩
    refine ⟨fun hv => (hr v hv).imp (fun z hz => ⟨hz.1, jh (ρ.push z) hz.2⟩), fun ⟨z, hz, hv⟩ => ?_⟩
    obtain ⟨w, hwR, hw⟩ := ht z hz
    exact cp_eval_unique_l hE q (ρ.push z) (jh (ρ.push z) hw) hv ▸ hwR

theorem cp_cert_mono_l {n} (p : Cp_code n) (ρ : Env M n) {y T U : M.Domain}
    (htu : M.MemberSubset T U) (h : Cp_cert_d p ρ y T) : Cp_cert_d p ρ y U := by
  induction p generalizing y with
  | var i => exact h
  | zero => exact h
  | op k p q r ih jh kh =>
    obtain ⟨a, haT, b, hbT, c, hcT, ha, hb, hc, hy⟩ := h
    exact ⟨a, htu a haT, b, htu b hbT, c, htu c hcT, ih ρ ha, jh ρ hb, kh ρ hc, hy⟩
  | let1 p q ih jh =>
    obtain ⟨a, haT, ha, hy⟩ := h
    exact ⟨a, htu a haT, ih ρ ha, jh (ρ.push a) hy⟩
  | bunion p q ih jh =>
    obtain ⟨X, hXT, R, hRT, hx, ht, hr, hy⟩ := h
    exact ⟨X, htu X hXT, R, htu R hRT, ih ρ hx,
      fun z hz => (ht z hz).imp (fun v hv => ⟨hv.1, jh (ρ.push z) hv.2⟩),
      fun v hv => (hr v hv).imp (fun z hz => ⟨hz.1, jh (ρ.push z) hz.2⟩), hy⟩

end YesMetaZFC.SetTheory.InnerModel
