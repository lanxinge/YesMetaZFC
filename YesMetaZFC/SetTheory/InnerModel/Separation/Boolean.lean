import YesMetaZFC.SetTheory.InnerModel.Separation.Tuple

/-! # 真值表的命题联结与量词运算 -/

namespace YesMetaZFC.SetTheory.InnerModel
universe u
variable {M : Structure.{u}}

theorem Rt_table_d.congr_l {U R : M.Domain} {n} {P Q : Rt_env U n → Prop}
    (h : Rt_table_d U P R) (he : ∀ e, P e ↔ Q e) : Rt_table_d U Q R :=
  fun p => (h p).trans (exists_congr fun e => and_congr_right fun _ => he e)

theorem rt_or_l (hKP : M.Models KP) {C U R S : M.Domain} {n} {P Q : Rt_env U n → Prop}
    (hC : Rd_closed_d C) (hRC : M.mem R C) (hSC : M.mem S C)
    (hR : Rt_table_d U P R) (hS : Rt_table_d U Q S) :
    ∃ T, M.mem T C ∧ Rt_table_d U (fun e => P e ∨ Q e) T := by
  obtain ⟨D, hDC, hD⟩ := hC.exists_l hKP .pair hRC hSC hRC
  obtain ⟨T, hTC, hT⟩ := hC.exists_l hKP .union hDC hDC hDC
  refine ⟨T, hTC, fun p => (hT p).trans ?_⟩
  constructor
  · rintro ⟨V, hv, hp⟩
    rcases (hD V).mp hv with rfl | rfl
    · exact ((hR p).mp hp).imp fun _ h => ⟨h.1, Or.inl h.2⟩
    · exact ((hS p).mp hp).imp fun _ h => ⟨h.1, Or.inr h.2⟩
  · rintro ⟨e, he, hp | hq⟩
    · exact ⟨R, (hD R).mpr (Or.inl rfl), (hR p).mpr ⟨e, he, hp⟩⟩
    · exact ⟨S, (hD S).mpr (Or.inr rfl), (hS p).mpr ⟨e, he, hq⟩⟩

theorem rt_imp_l (hKP : M.Models KP) {C U R S : M.Domain} {n} {P Q : Rt_env U n → Prop}
    (hC : Rd_closed_d C) (hU : M.mem U C) (hRC : M.mem R C) (hSC : M.mem S C)
    (hR : Rt_table_d U P R) (hS : Rt_table_d U Q S) :
    ∃ T, M.mem T C ∧ Rt_table_d U (fun e => P e → Q e) T := by
  obtain ⟨D, hDC, hD⟩ := rt_neg_l hKP hC hU hRC hR
  obtain ⟨T, hTC, hT⟩ := rt_or_l hKP hC hDC hSC hD hS
  classical
  refine ⟨T, hTC, hT.congr_l fun e => ⟨fun h hp => h.elim (fun hn => (hn hp).elim) id, fun h => ?_⟩⟩
  by_cases hp : P e
  · exact Or.inr (h hp)
  · exact Or.inl hp

theorem rt_iff_l (hKP : M.Models KP) {C U R S : M.Domain} {n} {P Q : Rt_env U n → Prop}
    (hC : Rd_closed_d C) (hU : M.mem U C) (hRC : M.mem R C) (hSC : M.mem S C)
    (hR : Rt_table_d U P R) (hS : Rt_table_d U Q S) :
    ∃ T, M.mem T C ∧ Rt_table_d U (fun e => P e ↔ Q e) T := by
  obtain ⟨A, hAC, hA⟩ := rt_imp_l hKP hC hU hRC hSC hR hS
  obtain ⟨B, hBC, hB⟩ := rt_imp_l hKP hC hU hSC hRC hS hR
  obtain ⟨T, hTC, hT⟩ := rt_and_l hKP hC hAC hBC hA hB
  exact ⟨T, hTC, hT.congr_l fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩⟩

theorem rt_forall_l (hKP : M.Models KP) {C U R : M.Domain} {n} {P : Rt_env U (n + 1) → Prop}
    (hC : Rd_closed_d C) (hU : M.mem U C) (hRC : M.mem R C) (hR : Rt_table_d U P R) :
    ∃ S, M.mem S C ∧ Rt_table_d U (fun e => ∀ x, P (Fin.cases x e)) S := by
  obtain ⟨A, hAC, hA⟩ := rt_neg_l hKP hC hU hRC hR
  obtain ⟨B, hBC, hB⟩ := rt_exists_l hKP hC hAC hA
  obtain ⟨S, hSC, hS⟩ := rt_neg_l hKP hC hU hBC hB
  exact ⟨S, hSC, hS.congr_l fun _ =>
    ⟨fun hn x => Classical.byContradiction (fun hx => hn ⟨x, hx⟩), fun h ⟨x, hn⟩ => hn (h x)⟩⟩

end YesMetaZFC.SetTheory.InnerModel
