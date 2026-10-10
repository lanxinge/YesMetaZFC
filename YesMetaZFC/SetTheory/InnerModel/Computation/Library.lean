import YesMetaZFC.SetTheory.InnerModel.Computation.DSL
import YesMetaZFC.SetTheory.InnerModel.Computation.Laws

/-! # 经验证的集合 DSL 程序

交集展示局部绑定，笛卡尔积展示嵌套集合循环及跨层变量引用。
两者均直接证明成员规格，因此可继续交给统一的程序—公式编译器。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def cp_intersection_l : Cp_code 2 := setfn! (x, y) {
  set d = x - y;
  return x - d;
}

theorem cp_intersection_sat_l (hKP : M.Models KP) (ρ : Env M 2) (y : M.Domain) :
    Cp_eval_d cp_intersection_l ρ y ↔ ∀ t, M.mem t y ↔ M.mem t (ρ.bound 0) ∧ M.mem t (ρ.bound 1) := by
  obtain ⟨D, hd⟩ := cp_eval_total_l hKP (cp_diff_l (.var 0) (.var 1)) ρ
  have hD := (cp_diff_iff_l hKP (show Cp_eval_d (.var 0) ρ (ρ.bound 0) from rfl)
    (show Cp_eval_d (.var 1) ρ (ρ.bound 1) from rfl) D).mp hd
  change Cp_eval_d (.let1 (cp_diff_l (.var 0) (.var 1)) (cp_diff_l (.var 1) (.var 0))) ρ y ↔ _
  rw [cp_let_iff_l hKP.1 _ hd, cp_diff_iff_l hKP
    (show Cp_eval_d (.var 1) (ρ.push D) (ρ.bound 0) from rfl) (show Cp_eval_d (.var 0) (ρ.push D) D from rfl)]
  apply forall_congr'; intro t
  rw [hD t]
  exact iff_congr Iff.rfl ⟨fun ⟨hx, hn⟩ => ⟨hx, Classical.byContradiction (fun hy => hn ⟨hx, hy⟩)⟩,
    fun ⟨hx, hy⟩ => ⟨hx, fun hn => hn.2 hy⟩⟩

def cp_product_l : Cp_code 2 := setfn! (x, y) {
  return union_for (a : x) {
    return union_for (b : y) {
      set p = opair(a, b);
      return pair(p, p);
    };
  };
}

theorem cp_product_sat_l (hKP : M.Models KP) (ρ : Env M 2) (y : M.Domain) :
    Cp_eval_d cp_product_l ρ y ↔
      ∀ t, M.mem t y ↔ ∃ a, M.mem a (ρ.bound 0) ∧ ∃ b, M.mem b (ρ.bound 1) ∧ KPair_d M t a b := by
  let q : Cp_code 4 := .let1 (.op .opair (.var 1) (.var 0) .zero) (cp_pair_l (.var 0) (.var 0))
  have emit a b t : (∃ v, Cp_eval_d q ((ρ.push a).push b) v ∧ M.mem t v) ↔ KPair_d M t a b := by
    let η := (ρ.push a).push b
    obtain ⟨c, hc⟩ := (kpair_interpretation_l M hKP.1 (KP.exists_pair hKP)).total a b
    have ho := (cp_opair_iff_l hKP (show Cp_eval_d (.var 1) η a from rfl)
      (show Cp_eval_d (.var 0) η b from rfl) c).mpr hc
    have he v : Cp_eval_d q η v ↔ Pair_d M v c c :=
      (cp_let_iff_l hKP.1 _ ho v).trans (cp_pair_iff_l hKP
        (show Cp_eval_d (.var 0) (η.push c) c from rfl) (show Cp_eval_d (.var 0) (η.push c) c from rfl) v)
    constructor
    · rintro ⟨v, hv, ht⟩
      have ht : t = c := (((he v).mp hv t).mp ht).elim id id
      exact ht.symm ▸ hc
    · intro ht
      obtain ⟨v, hv⟩ := KP.exists_pair hKP c c
      exact ⟨v, (he v).mpr hv, (hv t).mpr (Or.inl (kpair_unique_l M hKP.1 ht hc))⟩
  change Cp_eval_d (.bunion (.var 0) (.bunion (.var 2) q)) ρ y ↔ _
  rw [cp_bunion_iff_l hKP _ (show Cp_eval_d (.var 0) ρ (ρ.bound 0) from rfl)]
  apply forall_congr'; intro t
  apply iff_congr Iff.rfl
  apply exists_congr; intro a
  apply and_congr_right; intro _
  rw [cp_bunion_member_l hKP q (show Cp_eval_d (.var 2) (ρ.push a) (ρ.bound 1) from rfl)]
  simp only [emit]

end YesMetaZFC.SetTheory.InnerModel
