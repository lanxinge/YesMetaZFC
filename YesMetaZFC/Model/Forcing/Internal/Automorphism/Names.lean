import YesMetaZFC.Model.Forcing.Internal.Automorphism.Basic

/-! # 自同构在内部名称上的严格作用

直接使用已有 Nmap 递归图：每个 (σ,p) 变成 (πσ,πp)。全标签恒等图严格固定名称，
逆图给出真正的逆作用。check 名称的基条件也随之移动；基条件固定时名称本身固定。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z F G : M.Domain}

/-- 逆作用恢复原名称对象，结论强于被迫相等。 -/
theorem aut_nmap_inverse_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    (hg : ∀ p q, Entry_d M p q G ↔ Entry_d M q p F)
    {x s} (hx : Name_d M B x) (hs : Nmap_d M F x s) : Nmap_d M G s x := by
  obtain ⟨H, _, hH⟩ := aut_id_l hZF B R z
  have hc p q : Entry_d M p q H ↔ ∃ a, Entry_d M p a F ∧ Entry_d M a q G := by
    rw [hH]
    constructor
    · rintro ⟨hp, rfl⟩
      obtain ⟨a, ha⟩ := h.total q hp
      exact ⟨a, ha, (hg a q).mpr ha⟩
    · rintro ⟨a, hpa, haq⟩
      exact ⟨(h.domain p a hpa).1, h.injective q p a ((hg a q).mp haq) hpa⟩
  obtain ⟨t, ht⟩ := nmap_exists_l M hZF G s
  have he := nmap_unique_l M hZF.1 (check_ind_l M hZF) H x t x
    (nmap_comp_l hZF hc hs ht) (nmap_identity_l hZF hH hx)
  exact he ▸ ht

theorem aut_nmap_injective_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {x y t} (hx : Name_d M B x) (hy : Name_d M B y)
    (ht : Nmap_d M F x t) (hu : Nmap_d M F y t) : x = y := by
  obtain ⟨G, _, hg⟩ := aut_inverse_l hZF h
  exact nmap_unique_l M hZF.1 (check_ind_l M hZF) G t x y
    (aut_nmap_inverse_l hZF h hg hx ht) (aut_nmap_inverse_l hZF h hg hy hu)

/-- 所有内部名称都有原像；量词搬运不要求选择一个全局名称函数。 -/
theorem aut_nmap_onto_l (hZF : M.Models ZF) (h : Aut_d M B R z F)
    {t} (ht : Name_d M B t) : ∃ x, Name_d M B x ∧ Nmap_d M F x t := by
  obtain ⟨G, k, hg⟩ := aut_inverse_l hZF h
  obtain ⟨x, hx⟩ := nmap_exists_l M hZF G t
  exact ⟨x, nmap_name_l M hZF (fun p q hpq => (k.domain p q hpq).2) hx,
    aut_nmap_inverse_l hZF k (fun p q => (hg q p).symm) ht hx⟩

/-- 实际复合自同构的名称作用恰好是两次作用。 -/
theorem aut_nmap_comp_l (hZF : M.Models ZF) (h : Aut_d M B R z F) (k : Aut_d M B R z G) :
    ∃ H, Aut_d M B R z H ∧
      (∀ p r, Entry_d M p r H ↔ ∃ q, Entry_d M p q F ∧ Entry_d M q r G) ∧
      ∀ x t, Nmap_d M H x t ↔ ∃ s, Nmap_d M F x s ∧ Nmap_d M G s t := by
  obtain ⟨H, hH, he⟩ := aut_comp_l hZF h k
  refine ⟨H, hH, he, fun x t => ⟨?_, ?_⟩⟩
  · intro ht
    obtain ⟨s, hs⟩ := nmap_exists_l M hZF F x
    obtain ⟨a, ha⟩ := nmap_exists_l M hZF G s
    have he := nmap_unique_l M hZF.1 (check_ind_l M hZF) H x a t (nmap_comp_l hZF he hs ha) ht
    exact ⟨s, hs, he ▸ ha⟩
  · rintro ⟨s, hs, ht⟩
    exact nmap_comp_l hZF he hs ht

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

theorem aut_check_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {b c x s t}
    (hbc : Entry_d M b c F) (hs : Check_d M b x s) (ht : Check_d M c x t) : Nmap_d M F s t :=
  nmap_check_l hZF (fun d => ⟨fun hd => h.functional b d c hd hbc, fun he => he ▸ hbc⟩) hs ht

/-- 固定基条件时，全部地模型对象的 check 名称逐对象固定。 -/
theorem aut_check_fixed_l (hZF : M.Models ZF) (h : Aut_d M B R z F) {b x t}
    (hb : Entry_d M b b F) (ht : Check_d M b x t) : Nmap_d M F t t :=
  aut_check_l hZF h hb ht ht

end YesMetaZFC.Model.Forcing.Internal
