import YesMetaZFC.Model.Forcing.Internal.Forcing.Truth
import YesMetaZFC.Model.Forcing.Internal.Check.Model

/-! # 规范名称在泛型商中的忠实性

对地模型对象使用实际公式的内部成员归纳。等号力迫的双向匹配给出原对象的
相同成员，故规范名称嵌入在非标准及外部非良基模型上仍为单射。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 两个基点下的规范名称在共同加强处相等；证书是共享闭支撑内的实际双模拟。 -/
theorem check_force_bases_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    {b c x s t p} (hb : M.mem b B) (hc : M.mem c B)
    (hs : Check_d M b x s) (ht : Check_d M c x t) (hp : M.mem p B)
    (hpb : Entry_d M p b R) (hpc : Entry_d M p c R) : Eq_force_d M B R z p s t := by
  obtain ⟨S, hsS, htS, hS⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) (check_name_l M (check_range_l M hZF) hb hs)
      (check_name_l M (check_range_l M hZF) hc ht)
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push c
  let φ : BinarySchema 6 := {
    body := .existsE (.conj (check_m (.bound 5) .newest (.bound 2))
      (.conj (check_m (.bound 4) .newest (.bound 1))
        (.conj (entry_m (.bound 3) (.bound 5) (.bound 7)) (entry_m (.bound 3) (.bound 4) (.bound 7))))) }
  obtain ⟨F, hF⟩ := rel_separation_l hZF φ ρ B S
  have he p s t : Rel_d M F p s t ↔ M.mem p B ∧ M.mem s S ∧ M.mem t S ∧
      ∃ x, Check_d M b x s ∧ Check_d M c x t ∧ Entry_d M p b R ∧ Entry_d M p c R := by
    simpa only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      check_sat_l M hZF.1, entry_sat_l M hZF.1] using! hF p s t
  refine ⟨hp, F, ?_, (he p s t).mpr ⟨hp, hsS, htS, x, hs, ht, hpb, hpc⟩⟩
  intro p s t hf
  obtain ⟨hp, hsS, htS, x, hs, ht, hpb, hpc⟩ := (he p s t).mp hf
  constructor
  · intro a d had q hq _
    obtain ⟨_, y, hy, ha⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) hs a d).mp had
    obtain ⟨a', ha'⟩ := check_child_l M ht hy
    have ha't := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) ht a' c).mpr ⟨rfl, y, hy, ha'⟩
    have hqb := O.trans q p b hq.1 hp hb hq.2.2 hpb
    have hqc := O.trans q p c hq.1 hp hc hq.2.2 hpc
    exact ⟨q, a', c, below_refl_l O hq.1 hq.2.1, ha't, hqc, (he q a a').mpr
      ⟨hq.1, (supp_entry_l M hS hsS had).1, (supp_entry_l M hS htS ha't).1, y, ha, ha', hqb, hqc⟩⟩
  · intro a d had q hq _
    obtain ⟨_, y, hy, ha⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) ht a d).mp had
    obtain ⟨a', ha'⟩ := check_child_l M hs hy
    have ha's := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) hs a' b).mpr ⟨rfl, y, hy, ha'⟩
    have hqb := O.trans q p b hq.1 hp hb hq.2.2 hpb
    have hqc := O.trans q p c hq.1 hp hc hq.2.2 hpc
    exact ⟨q, a', b, below_refl_l O hq.1 hq.2.1, ha's, hqb, (he q a' a).mpr
      ⟨hq.1, (supp_entry_l M hS hsS ha's).1, (supp_entry_l M hS htS had).1, y, ha', ha, hqb, hqc⟩⟩

theorem check_force_reflect_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    {b p x y s t} (hb : M.mem b B) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : Below_d M B R z p b) (he : Eq_force_d M B R z p s t) : x = y := by
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b
  let φ : UnarySchema 4 := {
    body := .forallE (.forallE (.forallE (.forallE (.imp
      (.conj (check_m (.bound 5) (.bound 4) (.bound 2))
        (.conj (check_m (.bound 5) (.bound 3) (.bound 1))
          (.conj (below_m (.bound 8) (.bound 7) (.bound 6) .newest (.bound 5))
            (eq_force_m (.bound 8) (.bound 7) (.bound 6) .newest (.bound 2) (.bound 1)))))
      (Formula.extensionalEq (.bound 4) (.bound 3)))))) }
  have hφ a : φ.denote ρ a ↔ ∀ c s t p,
      Check_d M b a s ∧ Check_d M b c t ∧ Below_d M B R z p b ∧ Eq_force_d M B R z p s t → a = c := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, check_sat_l M hZF.1, below_sat_l M hZF.1, eq_force_sat_l M hZF.1,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have hall := check_ind_l M hZF φ ρ (fun a ih => (hφ a).mpr (by
    rintro c s t p ⟨hs, ht, hp, he⟩
    have hsN := check_name_l M (check_range_l M hZF) hb hs
    have htN := check_name_l M (check_range_l M hZF) hb ht
    obtain ⟨_, hl, hr⟩ := (eq_force_unfold_l M hZF hsN htN).mp he
    apply hZF.1.eq_of_same_members a c
    intro d
    constructor
    · intro hda
      obtain ⟨v, hv⟩ := check_child_l M hs hda
      have hd := (check_entry_l M hZF.1 (check_ind_l M hZF)
        (KP.exists_pair (ZF.modelsKP hZF)) hs v b).mpr ⟨rfl, d, hda, hv⟩
      obtain ⟨r, w, e, hpr, hw, _, hvw⟩ := hl v b hd p (below_refl_l O hp.1 hp.2.1) hp.2.2
      obtain ⟨_, f, hfc, hfw⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
        (KP.exists_pair (ZF.modelsKP hZF)) ht w e).mp hw
      have hef := (hφ d).mp (ih d hda) f v w r ⟨hv, hfw, below_trans_l O hb hpr hp, hvw⟩
      exact hef.symm ▸ hfc
    · intro hdc
      obtain ⟨v, hv⟩ := check_child_l M ht hdc
      have hd := (check_entry_l M hZF.1 (check_ind_l M hZF)
        (KP.exists_pair (ZF.modelsKP hZF)) ht v b).mpr ⟨rfl, d, hdc, hv⟩
      obtain ⟨r, w, e, hpr, hw, _, hwv⟩ := hr v b hd p (below_refl_l O hp.1 hp.2.1) hp.2.2
      obtain ⟨_, f, hfa, hfw⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
        (KP.exists_pair (ZF.modelsKP hZF)) hs w e).mp hw
      have hef := (hφ f).mp (ih f hfa) d w v r ⟨hfw, hv, below_trans_l O hb hpr hp, hwv⟩
      exact hef ▸ hfa))
  exact (hφ x).mp (hall x) y s t p ⟨hs, ht, hp, he⟩

end YesMetaZFC.Model.Forcing.Internal
