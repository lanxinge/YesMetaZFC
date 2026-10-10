import YesMetaZFC.SetTheory.InnerModel.Computation.Laws

/-! # 由实际判定程序筛选集合 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def cp_filter_l {n} (p : Cp_code n) (q : Cp_code (n + 1)) : Cp_code n :=
  .bunion p (.bunion q (cp_pair_l (.var 1) (.var 1)))

theorem cp_filter_iff_l (hKP : M.Models KP) {n} {p : Cp_code n} {q : Cp_code (n + 1)} {ρ : Env M n}
    {X : M.Domain} {P : M.Domain → Prop} (hp : Cp_eval_d p ρ X)
    (hq : ∀ z, M.mem z X → Cp_decides_d q (ρ.push z) (P z)) (y : M.Domain) :
    Cp_eval_d (cp_filter_l p q) ρ y ↔ ∀ t, M.mem t y ↔ M.mem t X ∧ P t := by
  have emit z (hz : M.mem z X) t :
      (∃ v, Cp_eval_d (.bunion q (cp_pair_l (.var 1) (.var 1))) (ρ.push z) v ∧ M.mem t v) ↔ P z ∧ t = z := by
    obtain ⟨B, hB⟩ := cp_eval_total_l hKP q (ρ.push z)
    rw [cp_bunion_member_l hKP _ hB]
    have hs a v := cp_pair_iff_l hKP
      (show Cp_eval_d (.var 1) ((ρ.push z).push a) z from rfl)
      (show Cp_eval_d (.var 1) ((ρ.push z).push a) z from rfl) v
    constructor
    · rintro ⟨a, ha, v, hv, ht⟩
      exact ⟨((hq z hz B hB a).mp ha).2, (((hs a v).mp hv t).mp ht).elim id id⟩
    · rintro ⟨hzP, ht⟩
      obtain ⟨e, he⟩ := KP.exists_empty hKP
      obtain ⟨v, hv⟩ := KP.exists_pair hKP z z
      exact ⟨e, (hq z hz B hB e).mpr ⟨he, hzP⟩, v, (hs e v).mpr hv, (hv t).mpr (Or.inl ht)⟩
  rw [cp_filter_l, cp_bunion_iff_l hKP _ hp]
  apply forall_congr'; intro t
  apply iff_congr Iff.rfl
  constructor
  · rintro ⟨z, hz, h⟩
    obtain ⟨hp, he⟩ := (emit z hz t).mp h
    exact he.symm ▸ ⟨hz, hp⟩
  · rintro ⟨ht, hp⟩
    exact ⟨t, ht, (emit t ht t).mpr ⟨hp, rfl⟩⟩

end YesMetaZFC.SetTheory.InnerModel
