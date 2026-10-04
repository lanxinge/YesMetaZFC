import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEdge
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.AscendingDescent
import YesMetaZFC.SetTheory.CountableChoice
import YesMetaZFC.SetTheory.Fiber

/-! # 极限下降链及其点态约束的原公式

代表选择、测度一集合和最后的求值图都用下列真实公式收集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ee_hit_d (κ L X R a f b g c s : M.Domain) : Prop :=
  ∃ E, M.mem s E ∧ Ee_constraint_d I κ L X R a f b g c E
def ee_hit_m {d} (κ L X R a f b g c s : Term d) : Formula 1 d := .existsE (.conj (.mem s.weaken .newest)
  (ee_constraint_m κ.weaken L.weaken X.weaken R.weaken a.weaken f.weaken b.weaken g.weaken c.weaken .newest))
derive_free_closed ee_hit_m
theorem ee_hit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L X R a f b g c s : Term d) :
    Formula.satisfies ρ (ee_hit_m κ L X R a f b g c s) ↔
      Ee_hit_d I (κ.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (a.eval ρ) (f.eval ρ) (b.eval ρ) (g.eval ρ) (c.eval ρ) (s.eval ρ) := by
  simp only [ee_hit_m, Ee_hit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, ee_constraint_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ee_hit_length_l (hE : Extensional M) {κ L X R a f b g c s n : M.Domain}
    (hc : Fn0_d n L c) (hh : Ee_hit_d I κ L X R a f b g c s) : Fn0_d n κ s := by
  obtain ⟨E, hs, m, k, l, q, r, f', g', _, _, hlc, _, _, hf, _, point⟩ := hh
  have en := hlc.domain_eq_l hE hc
  subst l
  obtain ⟨D, hD, hff⟩ := hf.2.1
  obtain ⟨x, _, _, _, hsx, _⟩ := point s hs
  exact (hD s).mp (hff.bound_l hsx).1

def Ee_rep_d (H i a f : M.Domain) : Prop := ∃ u B, Rd_entry_d i u H ∧ KPair_d M u a B ∧ M.mem f B
def ee_rep_m {d} (H i a f : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (rd_entry_m i.weaken.weaken (.bound 1) H.weaken.weaken)
    (.conj (kpair_m (.bound 1) a.weaken.weaken .newest) (.mem f.weaken.weaken .newest))))
derive_free_closed ee_rep_m
theorem ee_rep_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H i a f : Term d) :
    Formula.satisfies ρ (ee_rep_m H i a f) ↔ Ee_rep_d (H.eval ρ) (i.eval ρ) (a.eval ρ) (f.eval ρ) := by
  simp only [ee_rep_m, Ee_rep_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, kpair_sat_l M hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

def Ee_row_d (H G i a f : M.Domain) : Prop := Rd_entry_d i f G ∧ Ee_rep_d H i a f
def ee_row_m {d} (H G i a f : Term d) : Formula 1 d := .conj (rd_entry_m i f G) (ee_rep_m H i a f)
derive_free_closed ee_row_m
theorem ee_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H G i a f : Term d) :
    Formula.satisfies ρ (ee_row_m H G i a f) ↔ Ee_row_d (H.eval ρ) (G.eval ρ) (i.eval ρ) (a.eval ρ) (f.eval ρ) := by
  simp only [ee_row_m, Ee_row_d, Formula.satisfies_conj_iff, rd_entry_sat_l hE, ee_rep_sat_l hE]

theorem ee_row_unique_l {ω A X H G i a b f g : M.Domain} (hH : Fn0_d ω A H) (hG : Fn0_d ω X G)
    (hf : Ee_row_d H G i a f) (hg : Ee_row_d H G i b g) : a = b ∧ f = g := by
  obtain ⟨hif, u, B, hiu, hu, _⟩ := hf
  obtain ⟨hig, v, C, hiv, hv, _⟩ := hg
  have e := hH.2.2 i (hH.bound_l hiu).1 v (hH.bound_l hiv).2 u (hH.bound_l hiu).2 hiv hiu
  exact ⟨(kpair_injective_l M hu (e ▸ hv)).1,
    hG.2.2 i (hG.bound_l hif).1 f (hG.bound_l hif).2 g (hG.bound_l hig).2 hif hig⟩

def Ee_test_d (κ L X R H G A i s : M.Domain) : Prop := ∃ m a b f g c, M.SuccessorOf m i ∧
  Ee_row_d H G i a f ∧ Ee_row_d H G m b g ∧ Rd_entry_d i c A ∧ Ee_hit_d I κ L X R b g a f c s
def ee_test_m {d} (κ L X R H G A i s : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+6) := x.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (Formula.isSuccessor (.bound 5) (w i))
    (.conj (ee_row_m (w H) (w G) (w i) (.bound 4) (.bound 2))
      (.conj (ee_row_m (w H) (w G) (.bound 5) (.bound 3) (.bound 1))
        (.conj (rd_entry_m (w i) .newest (w A))
          (ee_hit_m (w κ) (w L) (w X) (w R) (.bound 3) (.bound 1) (.bound 4) (.bound 2) .newest (w s)))))))))))
derive_free_closed ee_test_m
theorem ee_test_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L X R H G A i s : Term d) :
    Formula.satisfies ρ (ee_test_m κ L X R H G A i s) ↔
      Ee_test_d I (κ.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (H.eval ρ) (G.eval ρ) (A.eval ρ) (i.eval ρ) (s.eval ρ) := by
  simp only [ee_test_m, Ee_test_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, ee_row_sat_l hE, rd_entry_sat_l hE, ee_hit_sat_l I hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
