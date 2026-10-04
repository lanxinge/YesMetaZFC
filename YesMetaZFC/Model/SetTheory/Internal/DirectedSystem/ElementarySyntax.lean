import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Stages

/-! # 同时量化全部分量的内部初等性归纳公式 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Di_row_d (I : kpair_convention_l.Interpretation M) (ω A p R C V K F n q r : M.Domain) : Prop :=
  ∀ i c X S E, Di_stage_d I A p R i c X S → M.IsFunctionSpace I E ω X →
    Smap_row_d I ω X S E C V K F n q r

def di_row_m {d} (ω A p R C V K F n q r : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+5) := x.weaken.weaken.weaken.weaken.weaken
  .forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (di_stage_m (w A) (w p) (w R) (.bound 4) (.bound 3) (.bound 2) (.bound 1))
    (.imp (Formula.isFunctionSpace kpair_convention_l .newest (w ω) (.bound 2))
      (smap_row_m (𝒞 := kpair_convention_l) (w ω) (.bound 2) (.bound 1) .newest
        (w C) (w V) (w K) (w F) (w n) (w q) (w r))))))))
@[simp] theorem di_row_closed_l {d} (ω A p R C V K F n q r : Term d)
    (hω : ω.freeSupport = []) (hA : A.freeSupport = []) (hp : p.freeSupport = []) (hR : R.freeSupport = [])
    (hC : C.freeSupport = []) (hV : V.freeSupport = []) (hK : K.freeSupport = []) (hF : F.freeSupport = [])
    (hn : n.freeSupport = []) (hq : q.freeSupport = []) (hr : r.freeSupport = []) :
    (di_row_m ω A p R C V K F n q r).FreeClosed := by
  simp -implicitDefEqProofs [di_row_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed,
    hω, hA, hp, hR, hC, hV, hK, hF, hn, hq, hr]
theorem di_row_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {d} (ρ : Env M d)
    (ω A p R C V K F n q r : Term d) : Formula.satisfies ρ (di_row_m ω A p R C V K F n q r) ↔
      Di_row_d I (ω.eval ρ) (A.eval ρ) (p.eval ρ) (R.eval ρ) (C.eval ρ) (V.eval ρ) (K.eval ρ)
        (F.eval ρ) (n.eval ρ) (q.eval ρ) (r.eval ρ) := by
  simp only [di_row_m, Di_row_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    di_stage_sat_l I hE, Formula.satisfies_isFunctionSpace_iff I hE, smap_row_sat_l I hE,
    Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Internal
