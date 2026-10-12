import YesMetaZFC.SetTheory.Descriptive.ScheduledGame

/-! # 固定局面之后的内部获胜策略

续局只约束包含给定历史的后续决策。策略仍在全部有限历史上有定义；
获胜局面由原公式分离得到，存在量词遍历模型自己的策略图。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Cg_tail_follows_d (p : Bool) (ω J s σ f : M.Domain) : Prop :=
  ∀ i, M.mem i ω → (if p then M.mem i J else ¬ M.mem i J) →
    ∀ h, M.IsRestrictionOf I h f i → M.MemberSubset s h →
      ∀ v, Rd_entry_d i v f → Rd_entry_d h v σ

def cg_tail_follows_m (p : Bool) {d} (ω J s σ f : Term d) : Formula 1 d :=
  Formula.forallMem ω (.imp (if p then .mem .newest J.weaken else .neg (.mem .newest J.weaken))
    (.forallE (.imp (Formula.isRestriction kpair_convention_l .newest f.weaken.weaken (.bound 1))
      (.imp (Formula.subset s.weaken.weaken .newest) (.forallE (.imp
        (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken)
        (rd_entry0_m (.bound 1) .newest σ.weaken.weaken.weaken)))))))

@[simp] theorem cg_tail_follows_closed_l (p : Bool) {d} (ω J s σ f : Term d)
    (hw : ω.freeSupport = []) (hj : J.freeSupport = []) (hs : s.freeSupport = [])
    (hσ : σ.freeSupport = []) (hf : f.freeSupport = []) :
    (cg_tail_follows_m p ω J s σ f).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [cg_tail_follows_m, Definitional.Formula.FreeClosed, hw, hj, hs, hσ, hf]

theorem cg_tail_follows_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω J s σ f : Term d) :
    Formula.satisfies ρ (cg_tail_follows_m p ω J s σ f) ↔ Cg_tail_follows_d I p
      (ω.eval ρ) (J.eval ρ) (s.eval ρ) (σ.eval ρ) (f.eval ρ) := by
  cases p <;> simp only [cg_tail_follows_m, Cg_tail_follows_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_forall_iff, Formula.satisfies_isRestriction_iff I,
    Formula.satisfies_subset_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest] <;> rfl

def Cg_tail_win_d (p : Bool) (ω X F J B W s σ : M.Domain) : Prop := Fn0_d F X σ ∧
  ∀ f, M.mem f B → M.MemberSubset s f → Cg_tail_follows_d I p ω J s σ f →
    if p then M.mem f W else ¬ M.mem f W

def cg_tail_win_m (p : Bool) {d} (ω X F J B W s σ : Term d) : Formula 1 d :=
  .conj (fn0_m F X σ) (Formula.forallMem B (.imp (Formula.subset s.weaken .newest) (.imp
    (cg_tail_follows_m p ω.weaken J.weaken s.weaken σ.weaken .newest)
    (if p then .mem .newest W.weaken else .neg (.mem .newest W.weaken)))))

@[simp] theorem cg_tail_win_closed_l (p : Bool) {d} (ω X F J B W s σ : Term d)
    (hw : ω.freeSupport = []) (hx : X.freeSupport = []) (hf : F.freeSupport = []) (hj : J.freeSupport = [])
    (hb : B.freeSupport = []) (ha : W.freeSupport = []) (hs : s.freeSupport = []) (hσ : σ.freeSupport = []) :
    (cg_tail_win_m p ω X F J B W s σ).FreeClosed := by
  cases p <;> simp -implicitDefEqProofs [cg_tail_win_m, Definitional.Formula.FreeClosed, hw, hx, hf, hj, hb, ha, hs, hσ]

theorem cg_tail_win_sat_l (hE : Extensional M) (p : Bool) {d} (ρ : Env M d) (ω X F J B W s σ : Term d) :
    Formula.satisfies ρ (cg_tail_win_m p ω X F J B W s σ) ↔ Cg_tail_win_d I p
      (ω.eval ρ) (X.eval ρ) (F.eval ρ) (J.eval ρ) (B.eval ρ) (W.eval ρ) (s.eval ρ) (σ.eval ρ) := by
  cases p <;> simp only [cg_tail_win_m, Cg_tail_win_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, cg_tail_follows_sat_l I hE, Formula.satisfies_mem_iff,
    Formula.satisfies_neg_iff, Definitional.Term.eval_weaken] <;> rfl

theorem Cg_tail_win_d.root_l {p ω X F J B W e σ}
    (win : Cg_tail_win_d I p ω X F J B W e σ) (he : ∀ x, ¬ M.mem x e) : Cg_win_d I p ω X F J B W σ :=
  ⟨win.1, fun f hf follows => win.2 f hf (fun x hx => (he x hx).elim)
    (fun i hi turn h hr _ v hv => follows i hi turn h hr v hv)⟩

def Cg_ii_d (ω X F J B W Q : M.Domain) : Prop := ∀ s,
  M.mem s Q ↔ M.mem s F ∧ ∃ σ, Cg_tail_win_d I false ω X F J B W s σ

theorem cg_ii_l (hZF : M.Models ZF) (ω X F J B W : M.Domain) : ∃ Q, Cg_ii_d I ω X F J B W Q := by
  let ρ : Env M 6 := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push F).push J).push B).push W
  let φ : UnarySchema 6 := { body := .existsE (cg_tail_win_m false
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  obtain ⟨Q, sep⟩ := ZF.separation_exists_d hZF φ ρ F
  refine ⟨Q, fun s => (sep s).trans (and_congr Iff.rfl ?_)⟩
  simp only [φ, Formula.satisfies_exists_iff, cg_tail_win_sat_l I hZF.1]
  rfl

end YesMetaZFC.SetTheory.Descriptive
