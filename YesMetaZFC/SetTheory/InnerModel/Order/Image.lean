import YesMetaZFC.SetTheory.InnerModel.Order.Function
import YesMetaZFC.SetTheory.InnerModel.Order.Relation

/-! # 将参数字典良序推送到每个 rud 运算的像 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rw_cmp_d (k : Rd_sym) (U R P x y : M.Domain) : Prop := ∃ p, M.mem p P ∧ ∃ q, M.mem q P ∧
  Rw_min_d k U R P p x ∧ Rw_min_d k U R P q y ∧ Rw_lex_d U R p q
def rw_cmp_s (k : Rd_sym) : Delta0BinarySchema 3 where
  body := Formula.existsMem (.bound 4) (Formula.existsMem (.bound 5)
    (.conj (rw_min_m k (.bound 4) (.bound 5) (.bound 6) (.bound 1) (.bound 3))
      (.conj (rw_min_m k (.bound 4) (.bound 5) (.bound 6) .newest (.bound 2))
        (rw_lex_m (.bound 4) (.bound 5) (.bound 1) .newest))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.conj (rw_min_delta_l ..) (.conj (rw_min_delta_l ..) (rw_lex_delta_l ..))))
theorem rw_cmp_sat_l (hKP : M.Models KP) (k : Rd_sym) (ρ : Env M 3) (x y : M.Domain) :
    (rw_cmp_s k).toBinarySchema.denote ρ x y ↔ Rw_cmp_d k (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) x y := by
  simp only [BinarySchema.denote, rw_cmp_s, Rw_cmp_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, rw_min_sat_l hKP, rw_lex_formula_l hKP.1]; rfl

theorem rw_cmp_irrefl_l (hKP : M.Models KP) {k U R P x}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_domain_d U P) : ¬ Rw_cmp_d k U R P x x := by
  rintro ⟨p, _, q, _, hx, hy, h⟩
  have he := rw_min_unique_l hKP hr hp hx hy; subst q
  exact rw_lex_irrefl_l hKP hr h
theorem rw_cmp_trans_l (hKP : M.Models KP) {k U R P x y z}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_domain_d U P)
    (h : Rw_cmp_d k U R P x y) (g : Rw_cmp_d k U R P y z) : Rw_cmp_d k U R P x z := by
  obtain ⟨p, hpP, q, _, hx, hy, h⟩ := h
  obtain ⟨q', _, r, hrP, hy', hz, g⟩ := g
  have he := rw_min_unique_l hKP hr hp hy hy'; subst q'
  exact ⟨p, hpP, r, hrP, hx, hz, rw_lex_trans_l hKP hr h g⟩

theorem rw_cmp_compare_l (hKP : M.Models KP) {k U R P x y}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_domain_d U P)
    (hx : ∃ p, M.mem p P ∧ Rw_fun_d k U p x) (hy : ∃ p, M.mem p P ∧ Rw_fun_d k U p y) :
    x = y ∨ Rw_cmp_d k U R P x y ∨ Rw_cmp_d k U R P y x := by
  obtain ⟨p, hx⟩ := rw_min_exists_l hKP hr hp hx
  obtain ⟨q, hy⟩ := rw_min_exists_l hKP hr hp hy
  rcases rw_lex_compare_l hKP hr ((hp p).mp hx.1) ((hp q).mp hy.1) with he | he | he
  · subst q; exact Or.inl (rw_fun_unique_l hKP.1 hx.2.1 hy.2.1)
  · exact Or.inr (Or.inl ⟨p, hx.1, q, hy.1, hx, hy, he⟩)
  · exact Or.inr (Or.inr ⟨q, hy.1, p, hx.1, hy, hx, he⟩)

theorem rw_cmp_min_l (hKP : M.Models KP) {k U R P Y X}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_domain_d U P)
    (hy : Rw_image_d k U P Y) (hx : M.MemberSubset X Y) (hn : ∃ x, M.mem x X) : Po_min_d (Rw_cmp_d k U R P) X := by
  let ρ : Env M 2 := (⟨fun _ => U, fun _ => U⟩ : Env M 1).push X
  let φ : Delta0UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (rw_fun_m k (.bound 3) (.bound 1) .newest)
    delta0 := .existsMem _ (rw_fun_delta_l ..) }
  obtain ⟨A, ha⟩ := KP.separation_exists_d hKP φ ρ P
  have hA p : M.mem p A ↔ M.mem p P ∧ ∃ x, M.mem x X ∧ Rw_fun_d k U p x := by
    rw [ha p]
    apply and_congr_right; intro _
    simp only [φ, Formula.satisfies_existsMem_iff, rw_fun_formula_l hKP]; rfl
  have nonempty : ∃ p, M.mem p A := by
    obtain ⟨x, hxX⟩ := hn
    obtain ⟨p, hpP, hpx⟩ := (hy x).mp (hx x hxX)
    exact ⟨p, (hA p).mpr ⟨hpP, x, hxX, hpx⟩⟩
  obtain ⟨p, hpA, hmin⟩ := rw_lex_min_l hKP hr (fun p hpA => (hp p).mp ((hA p).mp hpA).1) nonempty
  obtain ⟨hpP, x, hxX, hpx⟩ := (hA p).mp hpA
  have hpx' : Rw_min_d k U R P p x := by
    refine ⟨hpP, hpx, fun q hq hqp hqx => ?_⟩
    rcases hmin q ((hA q).mpr ⟨hq, x, hxX, hqx⟩) with he | he
    · subst q; exact rw_lex_irrefl_l hKP hr hqp
    · exact rw_lex_irrefl_l hKP hr (rw_lex_trans_l hKP hr he hqp)
  refine ⟨x, hxX, fun y hyX => ?_⟩
  obtain ⟨q, hqy⟩ := rw_min_exists_l hKP hr hp ((hy y).mp (hx y hyX))
  rcases hmin q ((hA q).mpr ⟨hqy.1, y, hyX, hqy.2.1⟩) with he | he
  · subst q; exact Or.inl (rw_fun_unique_l hKP.1 hpx hqy.2.1)
  · exact Or.inr ⟨p, hpP, q, hqy.1, hpx', hqy, he⟩

theorem rw_image_rel_exists_l (hKP : M.Models KP) (k : Rd_sym) (U R P Y : M.Domain) :
    ∃ S, Rw_rel_d (Rw_cmp_d k U R P) Y S := by
  let ρ : Env M 3 := ⟨Fin.cases U (Fin.cases R (fun _ => P)), fun _ => U⟩
  obtain ⟨S, hs⟩ := rw_rel_exists_l hKP (rw_cmp_s k) ρ Y
  have hS : Rw_rel_d (Rw_cmp_d k U R P) Y S := fun p => (hs p).trans
    (exists_congr fun x => and_congr_right fun _ => exists_congr fun y => and_congr_right fun _ =>
      and_congr_right fun _ => rw_cmp_sat_l hKP k ρ x y)
  exact ⟨S, hS⟩

theorem rw_image_wellorder_l (hKP : M.Models KP) {k U R P Y S}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_domain_d U P) (hy : Rw_image_d k U P Y)
    (hS : Rw_rel_d (Rw_cmp_d k U R P) Y S) : M.IsSetCodedWellOrder (kp_pair_l hKP) S Y :=
  hS.wellorder_l hKP (fun _ _ => rw_cmp_irrefl_l hKP hr hp)
    (fun _ _ _ _ _ _ h g => rw_cmp_trans_l hKP hr hp h g)
    (fun x hx y hyY => rw_cmp_compare_l hKP hr hp ((hy x).mp hx) ((hy y).mp hyY))
    (fun _ hx hn => rw_cmp_min_l hKP hr hp hy hx hn)

end YesMetaZFC.SetTheory.InnerModel
