import YesMetaZFC.Model.Forcing.Stage.NameMap.Construction

/-! # 名称搬运与规范名称相容 -/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} {F : M.Domain}

/-- 单个标签的确定像就足以搬运 check 递归；不需要条件序或全图双射。 -/
theorem nmap_check_l (hZF : M.Models ZF) {b c : M.Domain}
    (hf : ∀ d, Entry_d M b d F ↔ d = c) {x s t}
    (hs : Check_d M b x s) (ht : Check_d M c x t) : Nmap_d M F s t := by
  let ρ : Env M 3 := ((⟨fun _ => F, fun _ => F⟩ : Env M 1).push b).push c
  let φ : UnarySchema 3 := {
    body := .forallE (.forallE (.imp
      (.conj (check_m (.bound 4) (.bound 2) (.bound 1)) (check_m (.bound 3) (.bound 2) .newest))
      (nmap_m (.bound 5) (.bound 1) .newest))) }
  have hφ x : φ.denote ρ x ↔ ∀ s t, Check_d M b x s ∧ Check_d M c x t → Nmap_d M F s t := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, check_sat_l M hZF.1, nmap_sat_l M hZF.1]
    rfl
  let hI : Mem_ind_d M := check_ind_l M hZF
  let hP := KP.exists_pair (ZF.modelsKP hZF)
  have hall := hI φ ρ (fun x ih => (hφ x).mpr (by
    rintro s t ⟨hs, ht⟩
    obtain ⟨v, hv⟩ := nmap_exists_l M hZF F s
    have he : v = t := hZF.1.eq_of_same_members v t (fun w => by
      constructor
      · intro hw
        obtain ⟨a, d, a', d', had, haa, hdd, hw⟩ := (nmap_mem_l M hZF.1 hI hv w).mp hw
        obtain ⟨rfl, y, hy, hya⟩ := (check_entry_l M hZF.1 hI hP hs a d).mp had
        obtain ⟨u, hu⟩ := check_child_l M ht hy
        have hau := (hφ y).mp (ih y hy) a u ⟨hya, hu⟩
        have ha := nmap_unique_l M hZF.1 hI F a a' u haa hau
        exact (check_mem_l M hZF.1 hI ht w).mpr ⟨y, u, hy, hu, ha ▸ (hf d').mp hdd ▸ hw⟩
      · intro hw
        obtain ⟨y, a', hy, hya', hw⟩ := (check_mem_l M hZF.1 hI ht w).mp hw
        obtain ⟨a, hya⟩ := check_child_l M hs hy
        exact (nmap_mem_l M hZF.1 hI hv w).mpr ⟨a, b, a', c,
          (check_entry_l M hZF.1 hI hP hs a b).mpr ⟨rfl, y, hy, hya⟩,
          (hφ y).mp (ih y hy) a a' ⟨hya, hya'⟩, (hf c).mpr rfl, hw⟩)
    exact he ▸ hv))
  exact (hφ x).mp (hall x) s t ⟨hs, ht⟩

end YesMetaZFC.Model.Forcing.Internal
