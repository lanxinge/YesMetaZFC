import YesMetaZFC.SetTheory.InnerModel.Computation.Boolean

/-! # 基础运算、局部绑定及有界循环的求值法则 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def cp_basic_l (k : Rd_sym) : Cp_code 3 := .op k (.var 0) (.var 1) (.var 2)

theorem cp_basic_iff_l (hE : Extensional M) (k : Rd_sym) (ρ : Env M 3) (y : M.Domain) :
    Cp_eval_d (cp_basic_l k) ρ y ↔ Rd_fun_d k (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) y :=
  cp_op_iff_l hE (show Cp_eval_d (.var 0) ρ (ρ.bound 0) from rfl)
    (show Cp_eval_d (.var 1) ρ (ρ.bound 1) from rfl) (show Cp_eval_d (.var 2) ρ (ρ.bound 2) from rfl) k y

theorem cp_let_iff_l (hE : Extensional M) {n} {p : Cp_code n} (q : Cp_code (n + 1)) {ρ : Env M n}
    {a : M.Domain} (hp : Cp_eval_d p ρ a) (y : M.Domain) :
    Cp_eval_d (.let1 p q) ρ y ↔ Cp_eval_d q (ρ.push a) y :=
  ⟨fun ⟨_, hb, hy⟩ => cp_eval_unique_l hE p ρ hb hp ▸ hy, fun hy => ⟨a, hp, hy⟩⟩

theorem cp_bunion_iff_l (hKP : M.Models KP) {n} {p : Cp_code n} (q : Cp_code (n + 1)) {ρ : Env M n}
    {X : M.Domain} (hp : Cp_eval_d p ρ X) (y : M.Domain) :
    Cp_eval_d (.bunion p q) ρ y ↔
      ∀ t, M.mem t y ↔ ∃ z, M.mem z X ∧ ∃ v, Cp_eval_d q (ρ.push z) v ∧ M.mem t v := by
  have sound {v} (hv : Cp_eval_d (.bunion p q) ρ v) t :
      M.mem t v ↔ ∃ z, M.mem z X ∧ ∃ w, Cp_eval_d q (ρ.push z) w ∧ M.mem t w := by
    obtain ⟨X', R, hx, _, hr, hv⟩ := hv
    have he := cp_eval_unique_l hKP.1 p ρ hx hp; subst X'
    rw [hv t]
    exact ⟨fun ⟨w, hw, ht⟩ => ((hr w).mp hw).elim (fun z hz => ⟨z, hz.1, w, hz.2, ht⟩),
      fun ⟨z, hz, w, hw, ht⟩ => ⟨w, (hr w).mpr ⟨z, hz, hw⟩, ht⟩⟩
  refine ⟨fun hy t => sound hy t, fun hy => ?_⟩
  obtain ⟨v, hv⟩ := cp_eval_total_l hKP (.bunion p q) ρ
  exact hKP.1.eq_of_same_members v y (fun t => (sound hv t).trans (hy t).symm) ▸ hv

theorem cp_bunion_member_l (hKP : M.Models KP) {n} {p : Cp_code n} (q : Cp_code (n + 1)) {ρ : Env M n}
    {X : M.Domain} (hp : Cp_eval_d p ρ X) (t : M.Domain) :
    (∃ y, Cp_eval_d (.bunion p q) ρ y ∧ M.mem t y) ↔
      ∃ z, M.mem z X ∧ ∃ v, Cp_eval_d q (ρ.push z) v ∧ M.mem t v := by
  refine ⟨fun ⟨y, hy, ht⟩ => ((cp_bunion_iff_l hKP q hp y).mp hy t).mp ht, fun ht => ?_⟩
  obtain ⟨y, hy⟩ := cp_eval_total_l hKP (.bunion p q) ρ
  exact ⟨y, hy, ((cp_bunion_iff_l hKP q hp y).mp hy t).mpr ht⟩

theorem cp_opair_iff_l (hKP : M.Models KP) {n} {p q : Cp_code n} {ρ : Env M n} {a b : M.Domain}
    (hp : Cp_eval_d p ρ a) (hq : Cp_eval_d q ρ b) (y : M.Domain) :
    Cp_eval_d (.op .opair p q .zero) ρ y ↔ KPair_d M y a b := by
  obtain ⟨e, he⟩ := KP.exists_empty hKP
  rw [cp_op_iff_l hKP.1 hp hq (show Cp_eval_d .zero ρ e from he)]
  refine ⟨fun hy => ?_, rd_opair_value_l hKP.1⟩
  obtain ⟨v, hv⟩ := (kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)).total a b
  exact rd_fun_unique_l hKP.1 (rd_opair_value_l hKP.1 hv) hy ▸ hv

end YesMetaZFC.SetTheory.InnerModel
