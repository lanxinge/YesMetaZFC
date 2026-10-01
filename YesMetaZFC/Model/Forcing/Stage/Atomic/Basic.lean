import YesMetaZFC.Model.Forcing.Stage.Atomic.Pull

/-! # 阶段名称搬运的完整原子对应

隶属力迫由加权条目及等号的稠密匹配得到。等号和隶属的肯定、否定均在阶段像
上精确对应；这里只处理原子，不把一般阶段嵌入误认为全部公式的初等嵌入。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}} {P R z Q S w F : M.Domain}
variable (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w) (hZF : M.Models ZF)
variable (h : Reg_embed_d M P R z Q S w F)
include O L hZF h

theorem nmap_mem_push_l {x y s t p q} (hx : Name_d M P x) (hy : Name_d M P y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F)
    (hm : Mem_force_d M P R z p x y) : Mem_force_d M Q S w q s t := by
  have name {a b} (hab : Nmap_d M F a b) : Name_d M Q b :=
    nmap_name_l M hZF (fun c d hcd => (h.domain c d hcd).2.2.1) hab
  refine ⟨(h.domain p q hpq).2.2.1, fun r hr => ?_⟩
  obtain ⟨p₀, hp₀, hred⟩ := reg_reduce_below_l O L h hr.1 hr.2.1 hpq hr.2.2
  obtain ⟨p₁, a, b, hp₁, hab, hp₁b, he⟩ := hm.2 p₀ hp₀
  obtain ⟨a', haa⟩ := nmap_exists_l M hZF F a
  have hb := (name_entry_l M hy hab).2
  have hbz : b ≠ z := fun hz => hp₁.2.1 (O.zero p₁ hp₁.1 (hz ▸ hp₁b))
  obtain ⟨b', hbb⟩ := h.total b hb hbz
  obtain ⟨q₁, hp₁q⟩ := h.total p₁ hp₁.1 hp₁.2.1
  obtain ⟨v, hv, hvq⟩ := hred p₁ q₁ hp₁q hp₁.2.2
  have ha'b := (nmap_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht a' b').mpr
    ⟨a, b, hab, haa, hbb⟩
  have hvb := L.trans v q₁ b' hv.1 (h.domain p₁ q₁ hp₁q).2.2.1 (h.domain b b' hbb).2.2.1
    hvq ((h.order p₁ b q₁ b' hp₁q hbb).mpr hp₁b)
  have he' := nmap_eq_push_l O L hZF h hx (name_entry_l M hy hab).1 hs haa hp₁q he
  exact ⟨v, a', b', hv, ha'b, hvb, eq_force_lower_l L hZF (name hs) (name haa) q₁ v
    (h.domain p₁ q₁ hp₁q).2.2.1 ⟨hv.1, hv.2.1, hvq⟩ he'⟩

theorem nmap_mem_pull_l {x y s t p q} (hx : Name_d M P x) (hy : Name_d M P y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hp : M.mem p P)
    (hr : Red_d M R Q S w F q p) (hm : Mem_force_d M Q S w q s t) : Mem_force_d M P R z p x y := by
  refine ⟨hp, fun r hrp => ?_⟩
  obtain ⟨v, hrv⟩ := h.total r hrp.1 hrp.2.1
  obtain ⟨a, ha, hav⟩ := hr r v hrv hrp.2.2
  obtain ⟨b, c, d, hb, hcd, hbd, he⟩ := hm.2 a ha
  obtain ⟨c₀, d₀, hc₀d, hc₀c, hd₀d⟩ :=
    (nmap_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht c d).mp hcd
  have hbv := L.trans b a v hb.1 ha.1 (h.domain r v hrv).2.2.1 hb.2.2 hav
  obtain ⟨p₀, hp₀, hred₀⟩ := reg_reduce_below_l O L h hb.1 hb.2.1 hrv hbv
  obtain ⟨p₁, hp₁, hp₁d, hred₁⟩ := red_refine_l O L h hb.1 hp₀.1 hp₀.2.1 hred₀ hd₀d hbd
  exact ⟨p₁, c₀, d₀, below_trans_l O hrp.1 hp₁ hp₀, hc₀d, hp₁d,
    nmap_eq_pull_l O L hZF h hx (name_entry_l M hy hc₀d).1 hs hc₀c hp₁.1 hred₁ he⟩

theorem nmap_mem_force_l {x y s t p q} (hx : Name_d M P x) (hy : Name_d M P y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F) :
    Mem_force_d M P R z p x y ↔ Mem_force_d M Q S w q s t :=
  ⟨nmap_mem_push_l O L hZF h hx hy hs ht hpq,
    nmap_mem_pull_l O L hZF h hx hy hs ht (h.domain p q hpq).1 (red_image_l L h hpq)⟩

omit hZF in
private theorem neg_transfer_l {A D : M.Domain → Prop}
    (up : ∀ p q, Entry_d M p q F → A p → D q)
    (down : ∀ p q, M.mem p P → Red_d M R Q S w F q p → D q → A p)
    {p q} (hpq : Entry_d M p q F) : Neg_d M P R z A p ↔ Neg_d M Q S w D q := by
  constructor
  · intro hn v hv hd
    obtain ⟨r, hr, hred⟩ := reg_reduce_below_l O L h hv.1 hv.2.1 hpq hv.2.2
    exact hn r hr (down r v hr.1 hred hd)
  · intro hn r hr ha
    obtain ⟨v, hrv⟩ := h.total r hr.1 hr.2.1
    have hv := (h.domain r v hrv).2.2
    exact hn v ⟨hv.1, hv.2, (h.order r p v q hrv hpq).mpr hr.2.2⟩ (up r v hrv ha)

theorem nmap_neg_eq_l {x y s t p q} (hx : Name_d M P x) (hy : Name_d M P y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F) :
    Neg_d M P R z (fun r => Eq_force_d M P R z r x y) p ↔
      Neg_d M Q S w (fun r => Eq_force_d M Q S w r s t) q :=
  neg_transfer_l O L h (fun _ _ => nmap_eq_push_l O L hZF h hx hy hs ht)
    (fun _ _ => nmap_eq_pull_l O L hZF h hx hy hs ht) hpq

theorem nmap_neg_mem_l {x y s t p q} (hx : Name_d M P x) (hy : Name_d M P y)
    (hs : Nmap_d M F x s) (ht : Nmap_d M F y t) (hpq : Entry_d M p q F) :
    Neg_d M P R z (fun r => Mem_force_d M P R z r x y) p ↔
      Neg_d M Q S w (fun r => Mem_force_d M Q S w r s t) q :=
  neg_transfer_l O L h (fun _ _ => nmap_mem_push_l O L hZF h hx hy hs ht)
    (fun _ _ => nmap_mem_pull_l O L hZF h hx hy hs ht) hpq

end YesMetaZFC.Model.Forcing.Internal
