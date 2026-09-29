import YesMetaZFC.Model.Forcing.InternalConditions
import YesMetaZFC.Model.Forcing.Generic

/-! # 可数地模型上的实际泛型滤子

枚举模型对象，对每个集合安排“遇到它或进入其不可达区”的全局稠密要求。
共同加强排除接受条件以下稠密集的不可达分支，得到完整的模型泛型性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem enumerated_setlike_l (e : Nat → M.Domain) (he : Function.Surjective e) : Setlike_d.{u,0} M := by
  intro a
  refine ⟨{n : Nat // M.mem (e n) a}, fun n => e n.1, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := he x
    exact ⟨⟨n, hx⟩, rfl⟩
  · rintro ⟨n, rfl⟩
    exact n.2

theorem internal_generic_l (O : Cond_order_d M B R z) (e : Nat → M.Domain) (he : Function.Surjective e)
    {p} (hp : M.mem p B) (hn : p ≠ z) : ∃ U, Generic_d M B R z U ∧ U p := by
  classical
  let P := {q : M.Domain // M.mem q B ∧ q ≠ z}
  let Q : PO_pre P := {
    le := fun q r => Entry_d M q.1 r.1 R
    le_refl := fun q => O.refl q.1 q.2.1
    le_trans := fun {q r s} hqr hrs => O.trans q.1 r.1 s.1 q.2.1 r.2.1 s.2.1 hqr hrs }
  let D (n : Nat) (q : P) := M.mem q.1 (e n) ∨ Neg_d M B R z (fun r => M.mem r (e n)) q.1
  have hd n : Q.Dense_l (D n) := by
    intro q
    by_cases h : ∃ r, Below_d M B R z r q.1 ∧ M.mem r (e n)
    · obtain ⟨r, hr, hD⟩ := h
      exact ⟨⟨r, hr.1, hr.2.1⟩, hr.2.2, Or.inl hD⟩
    · exact ⟨q, Q.le_refl q, Or.inr (fun r hr hD => h ⟨r, hr, hD⟩)⟩
  obtain ⟨G, hGp, hG⟩ := generic_countable_l Q D hd (⟨p, hp, hn⟩ : P)
  let U q := ∃ r : P, G.mem r ∧ r.1 = q
  have hproper q (hq : U q) : M.mem q B ∧ q ≠ z := by
    obtain ⟨r, _, rfl⟩ := hq
    exact r.2
  refine ⟨U, ⟨hproper, ?_, ?_, ?_, ?_⟩, ⟨⟨p, hp, hn⟩, hGp, rfl⟩⟩
  · obtain ⟨q, hq⟩ := G.inhabited
    exact ⟨q.1, q, hq, rfl⟩
  · rintro q r ⟨s, hs, rfl⟩ hr hsr
    have hrz : r ≠ z := fun heq => s.2.2 (O.zero s.1 s.2.1 (heq ▸ hsr))
    exact ⟨⟨r, hr, hrz⟩, G.upward hs hsr, rfl⟩
  · rintro q r ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    obtain ⟨v, hv, hvs, hvt⟩ := G.directed hs ht
    exact ⟨v.1, ⟨v, hv, rfl⟩, hvs, hvt⟩
  · rintro q ⟨s, hs, rfl⟩ A hA
    obtain ⟨n, rfl⟩ := he A
    obtain ⟨t, ht, hD⟩ := hG n
    rcases hD with hD | hD
    · exact ⟨t.1, ⟨t, ht, rfl⟩, hD⟩
    · obtain ⟨r, _, hrs, hrt⟩ := G.directed hs ht
      obtain ⟨v, hv, hve⟩ := hA r.1 ⟨r.2.1, r.2.2, hrs⟩
      exact False.elim (hD v ⟨hv.1, hv.2.1, O.trans v r.1 t.1 hv.1 r.2.1 t.2.1 hv.2.2 hrt⟩ hve)

end YesMetaZFC.Model.Forcing.Internal
