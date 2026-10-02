import YesMetaZFC.SetTheory.InnerModel.Order.OperatorWitness
import YesMetaZFC.SetTheory.InnerModel.Order.JoinOrder
import YesMetaZFC.SetTheory.InnerModel.Recursion.LocalExtend

/-! # 后继历史对递归算子见证的有限更新

值域、后继像和两个坐标像各追加一个对象。端延拓保证新坐标并恰为新状态，
旧状态的全部计算见证继续使用原传递界。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem rp_image_insert_l (hE : Extensional M) {i : Bool} {Y D Y' D' p v : M.Domain}
    (h : Rp_image_d i Y D) (hy : ∀ q, M.mem q Y' ↔ M.mem q Y ∨ q = p)
    (hd : ∀ x, M.mem x D' ↔ M.mem x D ∨ x = v) (hp : Rp_proj_d i p v) : Rp_image_d i Y' D' := by
  intro x; rw [hd x, h x]
  constructor
  · rintro (⟨q, hq, hx⟩ | he)
    · exact ⟨q, (hy q).mpr (Or.inl hq), hx⟩
    · exact ⟨p, (hy p).mpr (Or.inr rfl), he.symm ▸ hp⟩
  · rintro ⟨q, hq, hx⟩
    rcases (hy q).mp hq with hq | he
    · exact Or.inl ⟨q, hq, hx⟩
    · subst q; exact Or.inr (rp_proj_unique_l hE hx hp)

theorem rd_union_insert_l {D D' U V : M.Domain} (h : Rd_fun_d .union D D D U)
    (hd : ∀ x, M.mem x D' ↔ M.mem x D ∨ x = V) (hu : M.MemberSubset U V) : Rd_fun_d .union D' D' D' V := by
  intro x
  exact ⟨fun hx => ⟨V, (hd V).mpr (Or.inr rfl), hx⟩, fun ⟨A, ha, hx⟩ =>
    ((hd A).mp ha).elim (fun ha => hu x ((h x).mpr ⟨A, ha, hx⟩)) (fun he => he ▸ hx)⟩

theorem rw_op_insert_in_l (hKP : M.Models KP) {C T F G r a p q U R V S : M.Domain}
    (hC : Rd_closed_d C) (hc : M.TransitiveSet C) (hTC : M.mem T C) (ht : M.TransitiveSet T)
    (ρ : Env M 0) (h : Rw_parts_d ρ T F p) (hp : KPair_d M p U R) (hq : KPair_d M q V S)
    (hu : M.TransitiveSet U) (ho : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hb : Rw_bound_d U R)
    (hs : Rw_successor_d U R V S) (hr : KPair_d M r a p)
    (hg : ∀ z, M.mem z G ↔ M.mem z F ∨ z = r) : Si_cert_d C rw_op_s ρ G q := by
  obtain ⟨X, Y, D, E, U', R', hX, hY, hD, hE, hU, hR, hx, hd, he, hDU, hER, hp', hw⟩ := h
  obtain ⟨hUeq, hReq⟩ := kpair_injective_l M hp' hp
  subst U'; subst R'
  have inT x hx : ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ M.mem x B := ⟨T, hTC, ht, hx⟩
  have hpe := rd_fun_enclosed_l hKP hC (inT U hU) (inT R hR) (inT U hU) (rd_opair_value_l hKP.1 hp)
  have hstep : Rw_state_d p q := (rw_state_pair_l hKP.1 hp hq).mpr hs
  obtain ⟨W, hWC, hwt, hqW, hwq⟩ := rw_state_in_l hKP hC hc (hc T hTC U hU) hu hp (inT R hR) hstep ρ
  have coords := po_pair_bound_l hwt hqW hq
  have inW x hx : ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ M.mem x B := ⟨W, hWC, hwt, hx⟩
  have memC x (hx : ∃ B, M.mem B C ∧ M.TransitiveSet B ∧ M.mem x B) : M.mem x C :=
    hx.elim fun B h => hc B h.1 x h.2.2
  obtain ⟨X', _, hx'⟩ := rd_insert_closed_l hKP hC (hc T hTC X hX) (memC p hpe)
  obtain ⟨Y', _, hy'⟩ := rd_insert_closed_l hKP hC (hc T hTC Y hY) (hc W hWC q hqW)
  obtain ⟨D', _, hd'⟩ := rd_insert_closed_l hKP hC (hc T hTC D hD) (hc W hWC V coords.1)
  obtain ⟨E', _, he'⟩ := rd_insert_closed_l hKP hC (hc T hTC E hE) (hc W hWC S coords.2)
  have hXe := rd_insert_enclosed_l hKP hC (inT X hX) hpe hx'
  have hYe := rd_insert_enclosed_l hKP hC (inT Y hY) (inW q hqW) hy'
  have hDe := rd_insert_enclosed_l hKP hC (inT D hD) (inW V coords.1) hd'
  have hEe := rd_insert_enclosed_l hKP hC (inT E hE) (inW S coords.2) he'
  obtain ⟨B, hBC, hbt, tb, hL⟩ := rd_finite_enclosed_l hKP hC hTC ht [X', Y', D', E', V, S, W] (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h
    · exact h ▸ hXe
    · exact h ▸ hYe
    · exact h ▸ hDe
    · exact h ▸ hEe
    · exact h ▸ inW V coords.1
    · exact h ▸ inW S coords.2
    · exact h ▸ rd_transitive_enclosed_l hKP hC hWC hwt)
  have hend := (rw_successor_correct_l hKP ho hs).2.2
  apply rw_op_in_l hKP hC hBC hbt ρ
  refine ⟨X', Y', D', E', V, S, hL X' (by simp), hL Y' (by simp), hL D' (by simp), hL E' (by simp),
    hL V (by simp), hL S (by simp), ?_,
    rp_image_insert_l hKP.1 hd hy' hd' ((rp_proj_pair_l hKP.1 hq false).mpr rfl),
    rp_image_insert_l hKP.1 he hy' he' ((rp_proj_pair_l hKP.1 hq true).mpr rfl),
    rd_union_insert_l hDU hd' hend.1, rd_union_insert_l hER he' (hend.relation_subset_l hKP.1 hb), hq, ?_⟩
  · intro z; apply (hx' z).trans
    constructor
    · rintro (hz | hz)
      · obtain ⟨b, h⟩ := (hx z).mp hz
        exact ⟨b, (rd_entry_insert_l hg hr b z).mpr (Or.inl h)⟩
      · subst z; exact ⟨a, (rd_entry_insert_l hg hr a p).mpr (Or.inr ⟨rfl, rfl⟩)⟩
    · rintro ⟨b, h⟩
      exact ((rd_entry_insert_l hg hr b z).mp h).elim (fun h => Or.inl ((hx z).mpr ⟨b, h⟩)) (fun h => Or.inr h.2)
  · obtain ⟨old, back⟩ := (rw_state_s.image_matrix_l ρ X Y T).mp hw
    apply (rw_state_s.image_matrix_l ρ X' Y' B).mpr
    constructor
    · intro x hxX
      rcases (hx' x).mp hxX with hxX | hxp
      · obtain ⟨y, hyY, w, hwT, hw⟩ := old x hxX
        exact ⟨y, (hy' y).mpr (Or.inl hyY), w, tb w hwT, hw⟩
      · subst x; exact ⟨q, (hy' q).mpr (Or.inr rfl), W, hL W (by simp), hwq⟩
    · intro y hyY
      rcases (hy' y).mp hyY with hyY | hyq
      · obtain ⟨x, hxX, w, hwT, hw⟩ := back y hyY
        exact ⟨x, (hx' x).mpr (Or.inl hxX), w, tb w hwT, hw⟩
      · subst y; exact ⟨p, (hx' p).mpr (Or.inr rfl), W, hL W (by simp), hwq⟩

end YesMetaZFC.SetTheory.InnerModel
