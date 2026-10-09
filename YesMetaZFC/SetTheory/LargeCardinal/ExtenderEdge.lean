import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystem

/-! # 极限边的共同有限支撑约束

把任意两个已选源代表之间的极限边，变成一个实际测度一集合上的统一点态
关系；共同纤维的解释与两个坐标投影交换，因此不会更换下降链的代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ee_constraint_d (κ L X R a f b g c E : M.Domain) : Prop := ∃ m n l q r f' g',
  Fn0_d m l q ∧ Fn0_d n l r ∧ Fn0_d l L c ∧ Cp0_d m l L q c a ∧ Cp0_d n l L r c b ∧
  Ep_pull_d κ X m l q f f' ∧ Ep_pull_d κ X n l r g g' ∧
    ∀ s, M.mem s E → Rp_atom_d I false X R f' g' s

def ee_constraint_m {d} (κ L X R a f b g c E : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+7) := x.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (fn0_m (.bound 6) (.bound 4) (.bound 3)) (.conj (fn0_m (.bound 5) (.bound 4) (.bound 2))
      (.conj (fn0_m (.bound 4) (w L) (w c)) (.conj (cp0_m (.bound 6) (.bound 4) (w L) (.bound 3) (w c) (w a))
        (.conj (cp0_m (.bound 5) (.bound 4) (w L) (.bound 2) (w c) (w b))
          (.conj (ep_pull_m (w κ) (w X) (.bound 6) (.bound 4) (.bound 3) (w f) (.bound 1))
            (.conj (ep_pull_m (w κ) (w X) (.bound 5) (.bound 4) (.bound 2) (w g) .newest)
              (Formula.forallMem (w E) (rp_atom_m (𝒞 := kpair_convention_l) false (w X).weaken (w R).weaken
                (.bound 2) (.bound 1) .newest)))))))))))))))
derive_free_closed ee_constraint_m

theorem ee_constraint_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L X R a f b g c E : Term d) :
    Formula.satisfies ρ (ee_constraint_m κ L X R a f b g c E) ↔
      Ee_constraint_d I (κ.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (a.eval ρ) (f.eval ρ)
        (b.eval ρ) (g.eval ρ) (c.eval ρ) (E.eval ρ) := by
  simp only [ee_constraint_m, Ee_constraint_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, cp0_sat_l hE, ep_pull_sat_l hE, Formula.satisfies_forallMem_iff,
    rp_atom_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ee_common_edge_l (hZF : M.Models ZF) {ω κ L X R F J O Z A p T S u v a b B C f g c w z : M.Domain}
    (hF : Em_source_d ω κ L X F) (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z A p T S)
    (hu : KPair_d M u a B) (hv : KPair_d M v b C) (hf : M.mem f B) (hg : M.mem g C)
    (hwc : Rd_entry_d w c p) (hzc : Rd_entry_d z c p) (huw : Rd_entry_d u w T)
    (hvz : Rd_entry_d v z T) (hwz : Rd_entry_d w z S) : ∃ E U, Rd_entry_d c U F ∧ M.mem E U ∧
      Ee_constraint_d (kp_pair_l (ZF.modelsKP hZF)) κ L X R a f b g c E := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨Q, hz, models⟩ := h.models
  obtain ⟨D, hw, hatD⟩ := h.toEp_graph_d.label_l hwc
  obtain ⟨E, he, hatE⟩ := h.toEp_graph_d.label_l hzc
  obtain ⟨m, l, q, f', _, hl, hq, hlc, hqa, hf', hff'⟩ := h.representatives u w a c B D hu hw huw f hf
  obtain ⟨n, l', r, g', _, _, hr, hlc', hrb, hg', hgg'⟩ := h.representatives v z b c C E hv he hvz g hg
  have el := hlc'.domain_eq_l hZF.1 hlc
  subst l'
  obtain ⟨d, Y, V, hcd, hcM, hm, hDY⟩ := ep_at_model_l hZF models hatD
  have hEY := (ep_at_read_l hz hcd hm.1).mp hatE
  have rel := (ep_rel_read_l hz hcd hm.1).mp (((h.toEp_graph_d.relation_l hw he).mp hwz).2.2)
  obtain ⟨U, hcU⟩ := hF.total l c hl hlc
  obtain ⟨H, hHU, point⟩ := (ep_relation_l I hZF.1 hF hcM hm hDY hEY hf' hg' hcU).mp rel
  exact ⟨H, U, hcU, hHU, m, n, l, q, r, f', g', hq, hr, hlc, hqa, hrb, hff', hgg', point⟩

theorem Ee_constraint_d.realize_l (hKP : M.Models KP) {ω κ L X R a f b g c E H K s : M.Domain}
    (hh : Fn0_d ω L H) (hk : Fn0_d ω κ K) (he : Ee_constraint_d I κ L X R a f b g c E)
    (hs : M.mem s E) (eval : Ec_eval_d ω κ L H K c s) : ∃ r t x y,
      Ec_eval_d ω κ L H K a r ∧ Ec_eval_d ω κ L H K b t ∧
      Rd_entry_d r x f ∧ Rd_entry_d t y g ∧ M.PairMember I x y R := by
  obtain ⟨m, n, l, q, p, f', g', hq, hp, hc, hqa, hpb, hf, hg, point⟩ := he
  obtain ⟨l', u, _, hu, hsfn⟩ := eval
  have el := hu.1.domain_eq_l hKP.1 hc
  subst l'
  obtain ⟨r, hr⟩ := cp0_exists_l hKP hq hsfn.1
  obtain ⟨t, ht⟩ := cp0_exists_l hKP hp hsfn.1
  obtain ⟨x, _, y, _, hsx, hsy, hxy⟩ := point s hs
  have ev : Ec_eval_d ω κ L H K c s := ⟨l, u, ‹Fn0_d l ω u›, hu, hsfn⟩
  exact ⟨r, t, x, y, ec_eval_comp_l hKP hh hk hc hq hqa hr ev, ec_eval_comp_l hKP hh hk hc hp hpb ht ev,
    (hf.2.2 s r hsfn.1 hr x).mp hsx, (hg.2.2 s t hsfn.1 ht y).mp hsy, hxy⟩

end YesMetaZFC.SetTheory.LargeCardinal
