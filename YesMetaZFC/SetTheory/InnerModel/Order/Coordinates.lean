import YesMetaZFC.SetTheory.InnerModel.Order.Selection

/-! # 模型内三元组的唯一性与有界坐标投影 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem pc_triple_inj_l {p a b c x y z : M.Domain} (h : Rd_triple_d p a b c) (g : Rd_triple_d p x y z) :
    a = x ∧ b = y ∧ c = z := by
  obtain ⟨q, hq, hp⟩ := h
  obtain ⟨r, hr, hg⟩ := g
  obtain ⟨ha, he⟩ := kpair_injective_l M hp hg; subst r
  exact ⟨ha, kpair_injective_l M hq hr⟩

theorem pn_triple_unique_l (hE : Extensional M) {v w a h c : M.Domain}
    (hv : Rd_triple_d v a h c) (hw : Rd_triple_d w a h c) : v = w := by
  obtain ⟨p, hp, hv⟩ := hv
  obtain ⟨q, hq, hw⟩ := hw
  have he := kpair_unique_l M hE hp hq; subst q
  exact kpair_unique_l M hE hv hw

def Pn_proj_d (i : Fin 3) (T v x : M.Domain) : Prop := ∃ a, M.mem a T ∧ ∃ h, M.mem h T ∧ ∃ c, M.mem c T ∧
  Rd_triple_d v a h c ∧ x = Fin.cases a (Fin.cases h (fun _ => c)) i

def pn_proj_s (i : Fin 3) : Delta0BinarySchema 1 where
  body := Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
    .conj (rd_triple0_m (.bound 4) (.bound 2) (.bound 1) .newest)
      (Formula.extensionalEq (.bound 3) (Fin.cases (.bound 2) (Fin.cases (.bound 1) (fun _ => .newest)) i))
  freeClosed := by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] <;> rfl
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_triple0_delta_l ..) (.atom _ _ _))))

theorem pn_proj_sat_l (hE : Extensional M) (i : Fin 3) (ρ : Env M 1) (v x : M.Domain) :
    (pn_proj_s i).toBinarySchema.denote ρ v x ↔ Pn_proj_d i (ρ.bound 0) v x := by
  simp only [BinarySchema.denote, pn_proj_s, Pn_proj_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, rd_triple0_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rfl

theorem pn_proj_value_l (i : Fin 3) {T v x a h c : M.Domain} (hv : Rd_triple_d v a h c) (hx : Pn_proj_d i T v x) :
    x = Fin.cases a (Fin.cases h (fun _ => c)) i := by
  obtain ⟨a', _, h', _, c', _, hv', hx⟩ := hx
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hv' hv
  exact hx

theorem pn_proj_unique_l (i : Fin 3) {T v x y : M.Domain} (hx : Pn_proj_d i T v x) (hy : Pn_proj_d i T v y) : x = y := by
  obtain ⟨a, _, h, _, c, _, hv, hx⟩ := hx
  exact hx.trans (pn_proj_value_l i hv hy).symm

theorem Pn_proj_d.bound_l {U p x : M.Domain} {i} (h : Pn_proj_d i U p x) : M.mem x U := by
  obtain ⟨a, ha, b, hb, c, hc, _, rfl⟩ := h
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

theorem pn_fields_l {T v a h c : M.Domain} (ht : M.TransitiveSet T) (hv : M.mem v T)
    (hn : Rd_triple_d v a h c) (i : Fin 3) : Pn_proj_d i T v (Fin.cases a (Fin.cases h (fun _ => c)) i) := by
  obtain ⟨p, hp, hq⟩ := hn
  have hb := po_pair_bound_l ht hv hq
  have hc := po_pair_bound_l ht hb.2 hp
  exact ⟨a, hb.1, h, hc.1, c, hc.2, ⟨p, hp, hq⟩, rfl⟩

end YesMetaZFC.SetTheory.InnerModel
