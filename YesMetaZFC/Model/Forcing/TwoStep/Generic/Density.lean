import YesMetaZFC.Model.Forcing.TwoStep.Generic.Projection
import YesMetaZFC.Model.Forcing.Internal.Forcing.Congruence

/-! # 第二阶段稠密集的地模型提升

第二阶段的稠密性先由真实公式表示。存在量词的见证经内部支撑收紧，产生
二步条件中的加强；因而无需对地模型外部的名称类进行选择或分离。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Stage_dense_d (Q D F s : M.Domain) : Prop :=
  ∀ t, M.mem t Q → Entry_d M t s D → ∃ v, M.mem v Q ∧ Entry_d M v t D ∧ M.mem v F

def stage_dense_m {n} (Q D F s : Term n) : Formula 1 n :=
  .forallE (.imp (.conj (.mem .newest Q.weaken) (rel_at_m .newest s.weaken D.weaken))
    (.existsE (.conj (.mem .newest Q.weaken.weaken)
      (.conj (rel_at_m .newest (.bound 1) D.weaken.weaken) (.mem .newest F.weaken.weaken)))))
derive_free_closed stage_dense_m

theorem stage_dense_sat_l (hE : Extensional M) {n} (ρ : Env M n) (Q D F s : Term n) :
    Formula.satisfies ρ (stage_dense_m Q D F s) ↔
      Stage_dense_d M (Q.eval ρ) (D.eval ρ) (F.eval ρ) (s.eval ρ) := by
  simp only [stage_dense_m, Stage_dense_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
    rel_at_sat_l hE, Definitional.Term.eval_newest, Definitional.Term.eval_weaken, and_imp]
  rfl

def stage_env_l (A T F s : M.Domain) : Env M 4 :=
  (((⟨fun _ => A, fun _ => A⟩ : Env M 1).push T).push F).push s

def Step_hits_d (B R z F x : M.Domain) : Prop :=
  ∃ p s, KPair_d M x p s ∧ Mem_force_d M B R z p s F

def step_hits_m {n} (B R z F x : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m x.weaken.weaken (.bound 1) .newest)
    (mem_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken (.bound 1) .newest F.weaken.weaken)))
derive_free_closed step_hits_m

theorem step_hits_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z F x : Term n) :
    Formula.satisfies ρ (step_hits_m B R z F x) ↔
      Step_hits_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (F.eval ρ) (x.eval ρ) := by
  simp only [step_hits_m, Step_hits_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, mem_force_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem step_hits_defined_l (hE : Extensional M) (B R z F : M.Domain) :
    Defined_d M (Step_hits_d M B R z F) := by
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F
  let φ : UnarySchema 4 := { body := step_hits_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  exact ⟨4, φ, ρ, fun x => step_hits_sat_l M hE (ρ.push x) _ _ _ _ _⟩

variable {M} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

/-- 一个条件迫使第二阶段稠密，便产生该条件以下的实际二步稠密集。 -/
theorem two_step_dense_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hT : Name_d M B T) {F} (hF : Name_d M B F) {x y p s q t}
    (hx : M.mem x C) (hy : M.mem y C) (hxp : KPair_d M x p s) (hyq : KPair_d M y q t)
    (hyx : Entry_d M y x S)
    (hD : Forces_d M B R z (stage_dense_m (.bound 3) (.bound 2) (.bound 1) (.bound 0))
      (stage_env_l M A T F s) q) : Dense_d M C S C (Step_hits_d M B R z F) y := by
  have hs := ((two_step_mem_l h hxp).mp hx).1
  have hq := ((two_step_mem_l h hyq).mp hy).2.1
  let ρ := stage_env_l M A T F s
  have hρ : ∀ a : Term 4, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact ⟨W, h.root, h.closed⟩
    | bound i => exact Fin.cases ⟨W, hs, h.closed⟩ (Fin.cases hF (Fin.cases hT (fun _ => ⟨W, h.root, h.closed⟩))) i
  intro v hv
  obtain ⟨r, w, hvr, hw, hrb, hwm⟩ := (h.conditions v).mp hv.1
  have hrq := ((two_step_le_l h hv.1 hy hvr hyq).mp hv.2.2).1
  have hws := ((two_step_le_l h hv.1 hx hvr hxp).mp (L.trans v y x hv.1 hy hx hv.2.2 hyx)).2
  have hrD := (forces_regular_l O hZF _ ρ hρ).1 q r hq.1 hrq hD
  have hδ : ∀ a : Term 5, Name_d M B (a.eval (ρ.push w)) := by
    intro a
    cases a with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases ⟨W, hw, h.closed⟩ (fun i => hρ (.bound i)) i
  have hi := (forces_all_l hZF.1 _ ρ r).mp hrD w ⟨W, hw, h.closed⟩
  have he := forces_mp_l hZF.1 (forces_regular_l O hZF _ _ hδ).1 (forces_regular_l O hZF _ _ hδ)
    hrb.1 hrb.2.1 hi (by
      rw [forces_conj_l, forces_mem_l hZF.1, force_rel_at_l M hZF.1]
      exact ⟨hwm, hws⟩)
  let φ : Formula 1 6 := .conj (rel_at_m .newest (.bound 1) (.bound 4)) (.mem .newest (.bound 3))
  have he : Forces_d M B R z (.existsE (.conj (.mem .newest (Term.bound 4).weaken) φ)) (ρ.push w) r := he
  obtain ⟨d, hd, a, haW, ham, hφ⟩ := bounded_exists_l O hZF φ (ρ.push w) (.bound 4) hδ h.closed h.root he
    r (below_refl_l O hrb.1 hrb.2.1)
  have ha : Rel_force_d M B R z T d a w ∧ Mem_force_d M B R z d a F := by
    simpa only [φ, forces_conj_l, force_rel_at_l M hZF.1, forces_mem_l hZF.1] using! hφ
  obtain ⟨k, hk⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total d a
  have hkC := (two_step_mem_l h hk).mpr ⟨haW, below_trans_l O h.base hd hrb, ham⟩
  refine ⟨k, ⟨hkC, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) C (he ▸ hkC), ?_⟩, d, a, hk, ha.2⟩
  exact (two_step_le_l h hkC hv.1 hk hvr).mpr ⟨hd, ha.1⟩

end YesMetaZFC.Model.Forcing.Internal
