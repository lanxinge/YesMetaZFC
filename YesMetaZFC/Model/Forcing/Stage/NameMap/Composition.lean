import YesMetaZFC.Model.Forcing.Stage.NameMap.Construction

/-! # 名称搬运与标签关系复合

先搬运两次与沿复合标签关系搬运给出同一个模型对象。证明在实际原公式上作
内部条目归纳；输出是递归图证书，未引入全局名称选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {F G H : M.Domain}

theorem nmap_comp_l (hZF : M.Models ZF)
    (hH : ∀ b c, Entry_d M b c H ↔ ∃ a, Entry_d M b a F ∧ Entry_d M a c G)
    {x s t} (hs : Nmap_d M F x s) (ht : Nmap_d M G s t) : Nmap_d M H x t := by
  let ρ : Env M 3 := ((⟨fun _ => F, fun _ => F⟩ : Env M 1).push G).push H
  let φ : UnarySchema 3 := {
    body := .forallE (.forallE (.imp
      (.conj (nmap_m (.bound 5) (.bound 2) (.bound 1)) (nmap_m (.bound 4) (.bound 1) .newest))
      (nmap_m (.bound 3) (.bound 2) .newest))) }
  have hφ x : φ.denote ρ x ↔ ∀ s t, Nmap_d M F x s ∧ Nmap_d M G s t → Nmap_d M H x t := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, nmap_sat_l M hZF.1]
    rfl
  let hI : Mem_ind_d M := check_ind_l M hZF
  let hP := KP.exists_pair (ZF.modelsKP hZF)
  have hall := entry_ind_l hI φ ρ (fun x ih => (hφ x).mpr (by
    rintro s t ⟨hs, ht⟩
    obtain ⟨u, hu⟩ := nmap_exists_l M hZF H x
    have he : t = u := hZF.1.eq_of_same_members t u (fun v => by
      constructor
      · intro hv
        obtain ⟨a, c, d, e, hac, had, hce, hv⟩ := (nmap_mem_l M hZF.1 hI ht v).mp hv
        obtain ⟨r, b, hrb, hra, hbc⟩ := (nmap_entry_l M hZF.1 hI hP hs a c).mp hac
        have hrd := (hφ r).mp (ih r b hrb) a d ⟨hra, had⟩
        exact (nmap_mem_l M hZF.1 hI hu v).mpr ⟨r, b, d, e, hrb, hrd, (hH b e).mpr ⟨c, hbc, hce⟩, hv⟩
      · intro hv
        obtain ⟨r, b, d, e, hrb, hrd, hbe, hv⟩ := (nmap_mem_l M hZF.1 hI hu v).mp hv
        obtain ⟨c, hbc, hce⟩ := (hH b e).mp hbe
        obtain ⟨a, hra⟩ := nmap_exists_l M hZF F r
        obtain ⟨w, haw⟩ := nmap_exists_l M hZF G a
        have hrw := (hφ r).mp (ih r b hrb) a w ⟨hra, haw⟩
        have hw := nmap_unique_l M hZF.1 hI H r d w hrd hrw
        exact (nmap_mem_l M hZF.1 hI ht v).mpr
          ⟨a, c, w, e, (nmap_entry_l M hZF.1 hI hP hs a c).mpr ⟨r, b, hrb, hra, hbc⟩,
            haw, hce, hw ▸ hv⟩)
    exact he.symm ▸ hu))
  exact (hφ x).mp (hall x) s t ⟨hs, ht⟩

end YesMetaZFC.Model.Forcing.Internal
