import YesMetaZFC.SetTheory.LargeCardinal.RankTransport
import YesMetaZFC.SetTheory.Card.SmallEnumeration
import YesMetaZFC.SetTheory.HereditaryFunction

/-! # 秩层最小枚举的有界读取

枚举包存实际序数域和满射图。最小性只比较临界点以下的候选域，候选满射
作为一个自由实参，故整条阶段检验仍为 Δ₀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Su0_d (D X f : M.Domain) : Prop := Fn0_d D X f ∧ ∀ x, M.mem x X → ∃ a, M.mem a D ∧ Rd_entry_d a x f
def su0_m {d} (D X f : Term d) : Formula 1 d := .conj (fn0_m D X f)
  (Formula.forallMem X (Formula.existsMem D.weaken (rd_entry0_m .newest (.bound 1) f.weaken.weaken)))
derive_free_closed su0_m
theorem su0_delta_l {d} (D X f : Term d) : (su0_m D X f).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.existsMem _ (rd_entry0_delta_l ..)))
theorem su0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (D X f : Term d) :
    Formula.satisfies ρ (su0_m D X f) ↔ Su0_d (D.eval ρ) (X.eval ρ) (f.eval ρ) := by
  simp only [su0_m, Su0_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Er_enum_d (I : kpair_convention_l.Interpretation M) (α p : M.Domain) : Prop :=
  ∃ V μ g, V_d I α V ∧ KPair_d M p μ g ∧ M.IsCardinal I μ ∧ M.IsSetBijectionFromTo I g μ V
def er_enum_m {d} (α p : Term d) : Formula 1 d := .existsE (.existsE (.existsE
  (.conj (v_m kpair_convention_l α.weaken.weaken.weaken (.bound 2))
    (.conj (kpair_m p.weaken.weaken.weaken (.bound 1) .newest) (.conj
      (Formula.isCardinal kpair_convention_l (.bound 1))
      (Formula.isBijectionFromTo kpair_convention_l .newest (.bound 1) (.bound 2)))))))
derive_free_closed er_enum_m
theorem er_enum_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (α p : Term d) : Formula.satisfies ρ (er_enum_m α p) ↔ Er_enum_d I (α.eval ρ) (p.eval ρ) := by
  simp only [er_enum_m, Er_enum_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, v_sat_l I hE,
    kpair_sat_l M hE, Formula.satisfies_isCardinal_iff I hE, Formula.satisfies_isBijectionFromTo_iff I hE,
    Definitional.Term.eval_weaken]; rfl

def Er_stage_d (κ H F T G h : M.Domain) : Prop := ∀ α, M.mem α κ → ∀ U, M.mem U H → ∀ p, M.mem p T →
  Rd_entry_d α U F → Rd_entry_d α p G → ∃ μ, M.mem μ T ∧ ∃ g, M.mem g T ∧ KPair_d M p μ g ∧
    Su0_d μ U g ∧ ∀ ν, M.mem ν κ → Su0_d ν U h → M.MemberSubset μ ν
def er_stage_m {d} (κ H F T G h : Term d) : Formula 1 d :=
  Formula.forallMem κ (Formula.forallMem H.weaken (Formula.forallMem T.weaken.weaken
    (.imp (rd_entry0_m (.bound 2) (.bound 1) F.weaken.weaken.weaken)
      (.imp (rd_entry0_m (.bound 2) .newest G.weaken.weaken.weaken)
        (Formula.existsMem T.weaken.weaken.weaken (Formula.existsMem T.weaken.weaken.weaken.weaken
          (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (.conj (su0_m (.bound 1) (.bound 3) .newest)
            (Formula.forallMem κ.weaken.weaken.weaken.weaken.weaken
              (.imp (su0_m .newest (.bound 4) h.weaken.weaken.weaken.weaken.weaken.weaken)
                (Formula.subset (.bound 2) .newest)))))))))))
derive_free_closed er_stage_m
theorem er_stage_delta_l {d} (κ H F T G h : Term d) : (er_stage_m κ H F T G h).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..)
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.conj (su0_delta_l ..)
      (.forallMem _ (.imp (su0_delta_l ..) (.atom _ _ _)))))))))))
theorem er_stage_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ H F T G h : Term d) :
    Formula.satisfies ρ (er_stage_m κ H F T G h) ↔
      Er_stage_d (κ.eval ρ) (H.eval ρ) (F.eval ρ) (T.eval ρ) (G.eval ρ) (h.eval ρ) := by
  simp only [er_stage_m, Er_stage_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, kpair0_sat_l hE,
    su0_sat_l hE, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
