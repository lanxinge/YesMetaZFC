import YesMetaZFC.SetTheory.Descriptive.LegalHistory

/-! # 集合字母表与固定时序上的内部策略

J 指定玩家 I 的时刻，补集指定玩家 II。策略仍是全部有限历史上的实际
集合编码函数，服从条件逐个内部时刻检查；允许同一玩家连续负责两个阶段。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Cg_follows_d (p : Bool) (ω J σ f : M.Domain) : Prop :=
  ∀ i, M.mem i ω → (if p then M.mem i J else ¬ M.mem i J) →
    ∀ h, M.IsRestrictionOf I h f i → ∀ v, Rd_entry_d i v f → Rd_entry_d h v σ

def Cg_win_d (p : Bool) (ω X F J B W σ : M.Domain) : Prop := Fn0_d F X σ ∧
  ∀ f, M.mem f B → Cg_follows_d I p ω J σ f → if p then M.mem f W else ¬ M.mem f W

def cg_follows_m (p : Bool) {d} (ω J σ f : Term d) : Formula 1 d :=
  Formula.forallMem ω (.imp (if p then .mem .newest J.weaken else .neg (.mem .newest J.weaken))
    (.forallE (.imp (Formula.isRestriction kpair_convention_l .newest f.weaken.weaken (.bound 1))
      (.forallE (.imp (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken)
        (rd_entry0_m (.bound 1) .newest σ.weaken.weaken.weaken))))))

@[simp] theorem cg_follows_closed_l (p : Bool) {d} (ω J σ f : Term d)
    (hw : ω.freeSupport = []) (hj : J.freeSupport = []) (hs : σ.freeSupport = []) (hf : f.freeSupport = []) :
    (cg_follows_m p ω J σ f).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [cg_follows_m, Definitional.Formula.FreeClosed, hw, hj, hs, hf]

theorem cg_follows_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω J σ f : Term d) :
    Formula.satisfies ρ (cg_follows_m p ω J σ f) ↔ Cg_follows_d I p (ω.eval ρ) (J.eval ρ) (σ.eval ρ) (f.eval ρ) := by
  cases p <;> simp only [cg_follows_m, Cg_follows_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_isRestriction_iff I,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] <;> rfl

def cg_win_m (p : Bool) {d} (ω X F J B W σ : Term d) : Formula 1 d :=
  .conj (fn0_m F X σ) (Formula.forallMem B (.imp
    (cg_follows_m p ω.weaken J.weaken σ.weaken .newest)
    (if p then .mem .newest W.weaken else .neg (.mem .newest W.weaken))))

@[simp] theorem cg_win_closed_l (p : Bool) {d} (ω X F J B W σ : Term d)
    (hw : ω.freeSupport = []) (hx : X.freeSupport = []) (hf : F.freeSupport = []) (hj : J.freeSupport = [])
    (hb : B.freeSupport = []) (ha : W.freeSupport = []) (hs : σ.freeSupport = []) :
    (cg_win_m p ω X F J B W σ).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [cg_win_m, Definitional.Formula.FreeClosed, hw, hx, hf, hj, hb, ha, hs]

theorem cg_win_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω X F J B W σ : Term d) :
    Formula.satisfies ρ (cg_win_m p ω X F J B W σ) ↔ Cg_win_d I p
      (ω.eval ρ) (X.eval ρ) (F.eval ρ) (J.eval ρ) (B.eval ρ) (W.eval ρ) (σ.eval ρ) := by
  cases p <;> simp only [cg_win_m, Cg_win_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    cg_follows_sat_l I hE, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken] <;> rfl

end YesMetaZFC.SetTheory.Descriptive
