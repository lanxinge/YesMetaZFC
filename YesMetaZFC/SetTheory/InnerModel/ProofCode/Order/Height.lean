import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Minimum

/-! # 可提高的内部语法高度界 -/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Ps_height_d (h c : M.Domain) : Prop := ∃ n, (M.mem n h ∨ n = h) ∧ Ps_rank_d n c

def ps_height_m {n} (h c : Term n) : Formula 1 n := .existsE
  (.conj (.disj (.mem .newest h.weaken) (Formula.extensionalEq .newest h.weaken)) (ps_rank_m .newest c.weaken))
derive_free_closed ps_height_m

theorem ps_height_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (h c : Term n) :
    Formula.satisfies ρ (ps_height_m h c) ↔ Ps_height_d (h.eval ρ) (c.eval ρ) := by
  simp only [ps_height_m, Ps_height_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hKP.1,
    ps_rank_formula_l hKP, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem Ps_height_d.valid_l {h c : M.Domain} (hc : Ps_height_d h c) : Ps_valid_d c := hc.imp (fun _ h => h.2)

theorem ps_height_unfold_l {h c : M.Domain} (hh : KP.N0_d h) (hc : Ps_height_d h c) :
    (∃ T a, Pc_leaf_d T c a ∧ M.IsOrdinal a) ∨
      ∃ T k a b d, Pc_node_d T k c a b d ∧
        (∃ m, M.mem m h ∧ Ps_rank_d m a) ∧ (∃ m, M.mem m h ∧ Ps_rank_d m b) ∧
          (∃ m, M.mem m h ∧ Ps_rank_d m d) := by
  obtain ⟨n, hn, hc⟩ := hc
  have sub m (hm : M.mem m n) : M.mem m h := hn.elim (fun hn => hh.1 n hn m hm) (fun hn => hn ▸ hm)
  rcases ps_rank_unfold_l hc with hl | ⟨T, k, a, b, d, hc, ha, hb, hd⟩
  · exact Or.inl hl
  · exact Or.inr ⟨T, k, a, b, d, hc, ha.imp (fun m hm => ⟨sub m hm.1, hm.2⟩),
      hb.imp (fun m hm => ⟨sub m hm.1, hm.2⟩), hd.imp (fun m hm => ⟨sub m hm.1, hm.2⟩)⟩

theorem ps_height_children_l (hKP : M.Models KP) {h p T c a b d : M.Domain} {k}
    (hh : KP.N0_d h) (hp : M.SuccessorOf h p) (hc : Ps_height_d h c) (hn : Pc_node_d T k c a b d) :
    Ps_height_d p a ∧ Ps_height_d p b ∧ Ps_height_d p d := by
  have lift {c} (hc : ∃ m, M.mem m h ∧ Ps_rank_d m c) : Ps_height_d p c :=
    hc.imp (fun m hm => ⟨((hp m).mp hm.1).imp_right (hKP.1.eq_of_same_members _ _), hm.2⟩)
  rcases ps_height_unfold_l hh hc with ⟨U, x, hc, _⟩ | ⟨U, l, x, y, z, hc, hx, hy, hz⟩
  · exact (pc_leaf_node_false_l hKP hc hn).elim
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := pc_node_inj_l hKP hc hn
    exact ⟨lift hx, lift hy, lift hz⟩

end YesMetaZFC.SetTheory.InnerModel
