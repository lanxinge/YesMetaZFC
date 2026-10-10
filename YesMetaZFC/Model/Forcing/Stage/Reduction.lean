import YesMetaZFC.Model.Forcing.Stage.Embedding

/-! # 完全嵌入的约减公式与受限加强

约减本身是实际原公式。若目标条件位于某个阶段像以下，可以把约减同时加强到
对应源条件以下；重复使用即可同时满足任意有限组源界。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def red_m {n} (R Q S w F x p : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp (.conj (entry_m (.bound 1) .newest F.weaken.weaken)
    (entry_m (.bound 1) p.weaken.weaken R.weaken.weaken))
    (cmp_m Q.weaken.weaken S.weaken.weaken w.weaken.weaken x.weaken.weaken .newest)))
derive_free_closed red_m

theorem red_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (ρ : Env M n) (R Q S w F x p : Term n) :
    Formula.satisfies ρ (red_m R Q S w F x p) ↔
      Red_d M (R.eval ρ) (Q.eval ρ) (S.eval ρ) (w.eval ρ) (F.eval ρ) (x.eval ρ) (p.eval ρ) := by
  simp only [red_m, Red_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, entry_sat_l M hE, cmp_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  exact forall_congr' fun q => forall_congr' fun y =>
    ⟨fun h hq hy => h ⟨hq, hy⟩, fun h ⟨hq, hy⟩ => h hq hy⟩

variable {M : SetTheory.Structure.{u}} {P R z Q S w F : M.Domain}

theorem red_lower_l (O : Cond_order_d M P R z) (h : Reg_embed_d M P R z Q S w F)
    {x p q} (hp : M.mem p P) (hq : Below_d M P R z q p) (hr : Red_d M R Q S w F x p) :
    Red_d M R Q S w F x q :=
  fun r y hry hrq => hr r y hry (O.trans r q p (h.domain r y hry).1 hq.1 hp hrq hq.2.2)

theorem red_image_l (L : Cond_order_d M Q S w) (h : Reg_embed_d M P R z Q S w F)
    {p x} (hx : Entry_d M p x F) : Red_d M R Q S w F x p := by
  intro q y hy hqp
  have hyQ := (h.domain q y hy).2.2
  exact ⟨y, ⟨hyQ.1, hyQ.2, (h.order q p y x hy hx).mpr hqp⟩, L.refl y hyQ.1⟩

/-- 目标条件位于另一阶段像以下时，源约减可与该源界共同加强。 -/
theorem red_refine_l (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    (h : Reg_embed_d M P R z Q S w F) {x p q y}
    (hx : M.mem x Q) (hp : M.mem p P) (hpz : p ≠ z) (hr : Red_d M R Q S w F x p)
    (hy : Entry_d M q y F) (hxy : Entry_d M x y S) :
    ∃ r, Below_d M P R z r p ∧ Entry_d M r q R ∧ Red_d M R Q S w F x r := by
  obtain ⟨v, hpv⟩ := h.total p hp hpz
  obtain ⟨a, hax, hav⟩ := hr p v hpv (O.refl p hp)
  have hay := L.trans a x y hax.1 hx (h.domain q y hy).2.2.1 hax.2.2 hxy
  obtain ⟨r, hrp, hrq⟩ := (h.compat p q v y hpv hy).mp ⟨a, ⟨hax.1, hax.2.1, hav⟩, hay⟩
  exact ⟨r, hrp, hrq, red_lower_l O h hp hrp hr⟩

/-- 每个阶段像以下的正目标条件，都有位于对应源条件以下的实际约减。 -/
theorem reg_reduce_below_l (O : Cond_order_d M P R z) (L : Cond_order_d M Q S w)
    (h : Reg_embed_d M P R z Q S w F) {x p y}
    (hx : M.mem x Q) (hxw : x ≠ w) (hy : Entry_d M p y F) (hxy : Entry_d M x y S) :
    ∃ r, Below_d M P R z r p ∧ Red_d M R Q S w F x r := by
  obtain ⟨q, hq, hqz, hr⟩ := h.reduction x hx hxw
  obtain ⟨r, hrq, hrp, hred⟩ := red_refine_l O L h hx hq hqz hr hy hxy
  exact ⟨r, ⟨hrq.1, hrq.2.1, hrp⟩, hred⟩

end YesMetaZFC.Model.Forcing.Internal
