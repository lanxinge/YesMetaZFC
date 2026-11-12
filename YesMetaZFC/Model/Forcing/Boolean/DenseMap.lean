import YesMetaZFC.Model.Forcing.CCC.Basic

/-! # 内部稠密映射及指定源条件以下的提升

映射是原模型内集合图；只在非零条件上全定义。单调性、不相容性反射与像稠密
自动给出指定源条件以下的稠密提升，不要求偏序预先分离。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : Structure.{u}}

structure Dmap_d (P R z Q S w F : M.Domain) : Prop where
  total : ∀ p, M.mem p P → p ≠ z → ∃ x, Entry_d M p x F
  domain : ∀ p x, Entry_d M p x F → (M.mem p P ∧ p ≠ z) ∧ M.mem x Q ∧ x ≠ w
  functional : ∀ p x y, Entry_d M p x F → Entry_d M p y F → x = y
  mono : ∀ p q x y, Entry_d M p x F → Entry_d M q y F → Entry_d M p q R → Entry_d M x y S
  compat : ∀ p q x y, Entry_d M p x F → Entry_d M q y F → Cmp_d M Q S w x y → Cmp_d M P R z p q
  dense : ∀ x, M.mem x Q → x ≠ w → ∃ p y, Entry_d M p y F ∧ Entry_d M y x S

/-- 保持并反映序且像稠密的实际图自动反映相容性。 -/
theorem dmap_of_order_l {P R z Q S w F : M.Domain} (L : Cond_order_d M Q S w)
    (total : ∀ p, M.mem p P → p ≠ z → ∃ x, Entry_d M p x F)
    (domain : ∀ p x, Entry_d M p x F → (M.mem p P ∧ p ≠ z) ∧ M.mem x Q ∧ x ≠ w)
    (functional : ∀ p x y, Entry_d M p x F → Entry_d M p y F → x = y)
    (order : ∀ p q x y, Entry_d M p x F → Entry_d M q y F → (Entry_d M x y S ↔ Entry_d M p q R))
    (dense : ∀ x, M.mem x Q → x ≠ w → ∃ p y, Entry_d M p y F ∧ Entry_d M y x S) :
    Dmap_d P R z Q S w F := by
  refine ⟨total,domain,functional,(fun p q x y px qy => (order p q x y px qy).mpr),?_,dense⟩
  intro p q x y px qy cmp
  obtain ⟨r,hr,ry⟩ := cmp
  obtain ⟨s,t,st,tr⟩ := dense r hr.1 hr.2.1
  have hs := domain s t st
  exact ⟨s,⟨hs.1.1,hs.1.2,(order s p t x st px).mp
    (L.trans t r x hs.2.1 hr.1 (domain p x px).2.1 tr hr.2.2)⟩,
    (order s q t y st qy).mp (L.trans t r y hs.2.1 hr.1 (domain q y qy).2.1 tr ry)⟩

theorem Dmap_d.lower_l {P R z Q S w F p x q : M.Domain} (h : Dmap_d P R z Q S w F)
    (L : Cond_order_d M Q S w) (px : Entry_d M p x F) (qx : Below_d M Q S w q x) :
    ∃ s y, Below_d M P R z s p ∧ Entry_d M s y F ∧ Below_d M Q S w y q := by
  obtain ⟨r,v,rv,vq⟩ := h.dense q qx.1 qx.2.1
  have hv := (h.domain r v rv).2
  have vx := L.trans v q x hv.1 qx.1 (h.domain p x px).2.1 vq qx.2.2
  obtain ⟨s,sr,sp⟩ := h.compat r p v x rv px ⟨v,below_refl_l L hv.1 hv.2,vx⟩
  obtain ⟨y,sy⟩ := h.total s sr.1 sr.2.1
  have hy := (h.domain s y sy).2
  exact ⟨s,y,⟨sr.1,sr.2.1,sp⟩,sy,hy.1,hy.2,
    L.trans y v q hy.1 hv.1 qx.1 (h.mono s r y v sy rv sr.2.2) vq⟩

end YesMetaZFC.Model.Forcing.Internal
