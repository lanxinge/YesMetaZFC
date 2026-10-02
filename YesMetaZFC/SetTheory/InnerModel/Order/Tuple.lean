import YesMetaZFC.SetTheory.InnerModel.Order.Coordinates
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph
import YesMetaZFC.SetTheory.Ord.OrderType

/-! # 任意模型内集合良序的三元字典序

逐坐标取像和最小纤维，证明每个非空三元组族有字典最小元；不枚举模型元素，
也不使用外部良基性。此序随后用于十三个实际 rud 运算的最小生成参数。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rw_tuple_d (U p : M.Domain) : Prop := ∃ a, M.mem a U ∧ ∃ b, M.mem b U ∧ ∃ c, M.mem c U ∧ Rd_triple_d p a b c
def Rw_domain_d (U P : M.Domain) : Prop := ∀ p, M.mem p P ↔ Rw_tuple_d U p
def Rw_lex_d (U R p q : M.Domain) : Prop := ∃ a, M.mem a U ∧ ∃ b, M.mem b U ∧ ∃ c, M.mem c U ∧
  ∃ x, M.mem x U ∧ ∃ y, M.mem y U ∧ ∃ z, M.mem z U ∧ Rd_triple_d p a b c ∧ Rd_triple_d q x y z ∧
    Po_lex_d (fun a b => Rd_entry_d a b R) a b c x y z

def rw_lex_s : Delta0BinarySchema 2 where
  body := Formula.existsMem (.bound 2) <| Formula.existsMem (.bound 3) <| Formula.existsMem (.bound 4) <|
    Formula.existsMem (.bound 5) <| Formula.existsMem (.bound 6) <| Formula.existsMem (.bound 7) <|
      .conj (rd_triple0_m (.bound 7) (.bound 5) (.bound 4) (.bound 3)) <|
        .conj (rd_triple0_m (.bound 6) (.bound 2) (.bound 1) .newest) <|
          .disj (rd_entry0_m (.bound 5) (.bound 2) (.bound 9)) <|
            .conj (Formula.extensionalEq (.bound 5) (.bound 2)) <|
              .disj (rd_entry0_m (.bound 4) (.bound 1) (.bound 9)) <|
                .conj (Formula.extensionalEq (.bound 4) (.bound 1)) (rd_entry0_m (.bound 3) .newest (.bound 9))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
  delta0 := .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (rd_triple0_delta_l ..) (.conj (rd_triple0_delta_l ..) (.disj (rd_entry0_delta_l ..)
      (.conj (.atom _ _ _) (.disj (rd_entry0_delta_l ..) (.conj (.atom _ _ _) (rd_entry0_delta_l ..))))))))))))
theorem rw_lex_sat_l (hE : Extensional M) (ρ : Env M 2) (p q : M.Domain) :
    rw_lex_s.toBinarySchema.denote ρ p q ↔ Rw_lex_d (ρ.bound 0) (ρ.bound 1) p q := by
  simp only [BinarySchema.denote, rw_lex_s, Rw_lex_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_disj_iff, rd_triple0_sat_l hE,
    Formula.satisfies_extensionalEq_iff_eq hE, rd_entry0_sat_l hE]; rfl
def rw_lex_m {n} (U R p q : Term n) : Formula 1 n := binary_pred_m rw_lex_s.toBinarySchema (Fin.cases U (fun _ => R)) p q
@[simp] theorem rw_lex_closed_l {n} (U R p q : Term n)
    (hu : U.freeSupport = []) (hr : R.freeSupport = []) (hp : p.freeSupport = []) (hq : q.freeSupport = []) :
    (rw_lex_m U R p q).FreeClosed := binary_pred_closed_l _ _ _ _ (Fin.cases hu (fun _ => hr)) hp hq
theorem rw_lex_delta_l {n} (U R p q : Term n) : (rw_lex_m U R p q).IsDelta0 := rw_lex_s.delta0.bind_l _
theorem rw_lex_formula_l (hE : Extensional M) {n} (ρ : Env M n) (U R p q : Term n) :
    Formula.satisfies ρ (rw_lex_m U R p q) ↔ Rw_lex_d (U.eval ρ) (R.eval ρ) (p.eval ρ) (q.eval ρ) := by
  rw [rw_lex_m, binary_pred_sat_l, rw_lex_sat_l hE]; rfl

theorem rw_lex_eq_l {U R p q a b c x y z : M.Domain} (hp : Rd_triple_d p a b c) (hq : Rd_triple_d q x y z) :
    Rw_lex_d U R p q ↔ M.mem a U ∧ M.mem b U ∧ M.mem c U ∧ M.mem x U ∧ M.mem y U ∧ M.mem z U ∧
      Po_lex_d (fun a b => Rd_entry_d a b R) a b c x y z := by
  constructor
  · rintro ⟨a', ha, b', hb, c', hc, x', hx, y', hy, z', hz, hp', hq', h⟩
    obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hp' hp
    obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hq' hq
    exact ⟨ha, hb, hc, hx, hy, hz, h⟩
  · rintro ⟨ha, hb, hc, hx, hy, hz, h⟩
    exact ⟨a, ha, b, hb, c, hc, x, hx, y, hy, z, hz, hp, hq, h⟩

theorem rw_lex_irrefl_l (hKP : M.Models KP) {U R p : M.Domain}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) : ¬ Rw_lex_d U R p p := by
  rintro ⟨a, ha, b, hb, c, hc, x, _, y, _, z, _, hp, hq, h⟩
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hq hp
  exact h.elim (hr.linear.2.1.1 _ ha) (fun h => h.2.elim (hr.linear.2.1.1 _ hb) (fun h => hr.linear.2.1.1 _ hc h.2))

theorem rw_lex_trans_l (hKP : M.Models KP) {U R p q r : M.Domain}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (h : Rw_lex_d U R p q) (g : Rw_lex_d U R q r) : Rw_lex_d U R p r := by
  obtain ⟨a, ha, b, hb, c, hc, x, hx, y, hy, z, hz, hp, hq, h⟩ := h
  obtain ⟨x', _, y', _, z', _, s, hs, t, ht, v, hv, hq', hr', g⟩ := g
  obtain ⟨rfl, rfl, rfl⟩ := pc_triple_inj_l hq' hq
  exact ⟨a, ha, b, hb, c, hc, s, hs, t, ht, v, hv, hp, hr', po_lex_trans_l
    (hr.linear.2.1.2 a ha x' hx s hs) (hr.linear.2.1.2 b hb y' hy t ht) (hr.linear.2.1.2 c hc z' hz v hv) h g⟩

theorem rw_lex_compare_l (hKP : M.Models KP) {U R p q : M.Domain}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hp : Rw_tuple_d U p) (hq : Rw_tuple_d U q) :
    p = q ∨ Rw_lex_d U R p q ∨ Rw_lex_d U R q p := by
  obtain ⟨a, ha, b, hb, c, hc, hp⟩ := hp
  obtain ⟨x, hx, y, hy, z, hz, hq⟩ := hq
  have cmp a ha b hb := (hr.linear.2.2 a ha b hb).imp_left (hKP.1.eq_of_same_members _ _)
  have go (h : Po_lex_d (fun a b => Rd_entry_d a b R) a b c x y z) : Rw_lex_d U R p q :=
    ⟨a, ha, b, hb, c, hc, x, hx, y, hy, z, hz, hp, hq, h⟩
  have back (h : Po_lex_d (fun a b => Rd_entry_d a b R) x y z a b c) : Rw_lex_d U R q p :=
    ⟨x, hx, y, hy, z, hz, a, ha, b, hb, c, hc, hq, hp, h⟩
  rcases cmp a ha x hx with he | he | he
  · subst x
    rcases cmp b hb y hy with hf | hf | hf
    · subst y
      rcases cmp c hc z hz with hg | hg | hg
      · subst z; exact Or.inl (pn_triple_unique_l hKP.1 hp hq)
      · exact Or.inr (Or.inl (go (Or.inr ⟨rfl, Or.inr ⟨rfl, hg⟩⟩)))
      · exact Or.inr (Or.inr (back (Or.inr ⟨rfl, Or.inr ⟨rfl, hg⟩⟩)))
    · exact Or.inr (Or.inl (go (Or.inr ⟨rfl, Or.inl hf⟩)))
    · exact Or.inr (Or.inr (back (Or.inr ⟨rfl, Or.inl hf⟩)))
  · exact Or.inr (Or.inl (go (Or.inl he)))
  · exact Or.inr (Or.inr (back (Or.inl he)))

theorem rw_lex_min_l (hKP : M.Models KP) {U R X : M.Domain}
    (hr : M.IsSetCodedWellOrder (kp_pair_l hKP) R U) (hx : ∀ p, M.mem p X → Rw_tuple_d U p)
    (hn : ∃ p, M.mem p X) : Po_min_d (Rw_lex_d U R) X := by
  let ρ : Env M 1 := ⟨fun _ => U, fun _ => U⟩
  have total (i : Fin 3) p (hp : M.mem p X) : ∃ a, Pn_proj_d i U p a := by
    obtain ⟨a, ha, b, hb, c, hc, hp⟩ := hx p hp
    exact ⟨_, a, ha, b, hb, c, hc, hp, rfl⟩
  have select (i : Fin 3) V (hv : M.MemberSubset V X) (hn : ∃ p, M.mem p V) :
      ∃ a A, (∀ p, M.mem p A ↔ M.mem p V ∧ Pn_proj_d i U p a) ∧ (∃ p, M.mem p A) ∧
        ∀ p, M.mem p V → ∀ b, Pn_proj_d i U p b → a = b ∨ Rd_entry_d a b R := by
    have sat p a := pn_proj_sat_l hKP.1 i ρ p a
    obtain ⟨a, A, hA, hAn, hm⟩ := po_minfiber_l hKP (pn_proj_s i) ρ V
      (fun p hp => (total i p (hv p hp)).imp (fun a ha => (sat p a).mpr ha))
      (fun p _ a b ha hb => pn_proj_unique_l i ((sat p a).mp ha) ((sat p b).mp hb)) (by
        intro Y hY
        have sub y hy : M.mem y U := ((hY y).mp hy).elim (fun p hp => ((sat p y).mp hp.2).bound_l)
        have hnY : ∃ y, M.mem y Y := by
          obtain ⟨p, hp⟩ := hn
          obtain ⟨a, ha⟩ := total i p (hv p hp)
          exact ⟨a, (hY a).mpr ⟨p, hp, (sat p a).mpr ha⟩⟩
        obtain ⟨a, ha, hm⟩ := hr.least Y sub hnY
        exact ⟨a, ha, fun b hb => (hm b hb).imp_left (hKP.1.eq_of_same_members _ _)⟩)
    exact ⟨a, A, fun p => (hA p).trans (and_congr_right fun _ => sat p a), hAn, fun p hp b hb => hm p hp b ((sat p b).mpr hb)⟩
  obtain ⟨a, A, hA, hAn, ha⟩ := select 0 X (fun _ h => h) hn
  have ax p hp := ((hA p).mp hp).1
  obtain ⟨b, B, hB, hBn, hb⟩ := select 1 A ax hAn
  have ba p hp := ((hB p).mp hp).1
  obtain ⟨c, C, hC, ⟨p, hpC⟩, hc⟩ := select 2 B (fun p hp => ax p (ba p hp)) hBn
  have hpB := ((hC p).mp hpC).1
  have hpA := ba p hpB
  have hpX := ax p hpA
  obtain ⟨a', ha', b', hb', c', hc', hp⟩ := hx p hpX
  have he : a = a' := pn_proj_value_l 0 hp ((hA p).mp hpA).2; subst a'
  have he : b = b' := pn_proj_value_l 1 hp ((hB p).mp hpB).2; subst b'
  have he : c = c' := pn_proj_value_l 2 hp ((hC p).mp hpC).2; subst c'
  refine ⟨p, hpX, fun q hqX => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hq⟩ := hx q hqX
  have field i : Pn_proj_d i U q (Fin.cases x (Fin.cases y (fun _ => z)) i) := ⟨x, hx, y, hy, z, hz, hq, rfl⟩
  have less (h : Po_lex_d (fun a b => Rd_entry_d a b R) a b c x y z) : Rw_lex_d U R p q :=
    ⟨a, ha', b, hb', c, hc', x, hx, y, hy, z, hz, hp, hq, h⟩
  rcases ha q hqX x (field 0) with he | he
  · have hqA := (hA q).mpr ⟨hqX, he.symm ▸ field 0⟩
    rcases hb q hqA y (field 1) with hf | hf
    · have hqB := (hB q).mpr ⟨hqA, hf.symm ▸ field 1⟩
      rcases hc q hqB z (field 2) with hg | hg
      · subst x; subst y; subst z; exact Or.inl (pn_triple_unique_l hKP.1 hp hq)
      · exact Or.inr (less (Or.inr ⟨he, Or.inr ⟨hf, hg⟩⟩))
    · exact Or.inr (less (Or.inr ⟨he, Or.inl hf⟩))
  · exact Or.inr (less (Or.inl he))

end YesMetaZFC.SetTheory.InnerModel
