import YesMetaZFC.Model.Forcing.TwoStep.Generic.Projection

/-! # 后继阶段的顶名称

顶条件使用实际原公式及名称力迫。名称库显式包含顶名称时，二步偏序中的
最大条件由首阶段基条件与顶名称配对取得。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def top_m {n} (A T t : Term n) : Formula 1 n :=
  .conj (.mem t A) (.forallE (.imp (.mem .newest A.weaken)
    (rel_at_m .newest t.weaken T.weaken)))
derive_free_closed top_m

theorem top_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n}
    (ρ : Env M n) (A T t : Term n) : Formula.satisfies ρ (top_m A T t) ↔
      M.mem (t.eval ρ) (A.eval ρ) ∧ ∀ s, M.mem s (A.eval ρ) → Entry_d M s (t.eval ρ) (T.eval ρ) := by
  simp only [top_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, rel_at_sat_l hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)

def top_env_l (A T t : M.Domain) : Env M 3 := (ord_env_l M A T).push t

include O hZF

theorem forced_top_l {t p} (hA : Name_d M B A) (hT : Name_d M B T) (ht : Name_d M B t)
    (hp : M.mem p B) (hz : p ≠ z)
    (h : Forces_d M B R z (top_m (.bound 1) (.bound 2) .newest) (top_env_l A T t) p) :
    Mem_force_d M B R z p t A ∧
      ∀ s, Name_d M B s → Mem_force_d M B R z p s A → Rel_force_d M B R z T p s t := by
  obtain ⟨hm, hf⟩ := (forces_conj_l _ _ _ p).mp h
  refine ⟨(forces_mem_l hZF.1 _ _ _ p).mp hm, fun s hs hsm => ?_⟩
  have hn : ∀ v : Term 4, Name_d M B (v.eval ((top_env_l A T t).push s)) := by
    intro v
    cases v with
    | free _ => exact hT
    | bound i => exact Fin.cases hs (Fin.cases ht (Fin.cases hA (fun _ => hT))) i
  have h := (forces_all_l hZF.1 _ _ p).mp hf s hs
  have h := forces_mp_l hZF.1 (forces_regular_l O hZF _ _ hn).1
    (forces_regular_l O hZF _ _ hn) hp hz h ((forces_mem_l hZF.1 _ _ _ p).mpr hsm)
  exact (force_rel_at_l M hZF.1 ((top_env_l A T t).push s) p .newest (.bound 1) (.bound 3)).mp h

/-- 先在整个首阶段锥下传递顶名称性质，再取得二步最大条件。 -/
theorem two_step_top_l (h : Two_step_d M B R z b A T W C S) (hT : Name_d M B T)
    {t} (ht : M.mem t W) (hb : b ≠ z)
    (hf : Forces_d M B R z (top_m (.bound 1) (.bound 2) .newest) (top_env_l A T t) b) :
    ∃ x, KPair_d M x b t ∧ M.mem x C ∧ ∀ y, M.mem y C → Entry_d M y x S := by
  have hA : Name_d M B A := ⟨W, h.root, h.closed⟩
  have htN : Name_d M B t := ⟨W, ht, h.closed⟩
  have hn : ∀ v : Term 3, Name_d M B (v.eval (top_env_l A T t)) := by
    intro v
    cases v with
    | free _ => exact hT
    | bound i => exact Fin.cases htN (Fin.cases hA (fun _ => hT)) i
  have top {p} (hp : Below_d M B R z p b) := forced_top_l O hZF hA hT htN hp.1 hp.2.1
    ((forces_regular_l O hZF _ _ hn).1 b p h.base hp hf)
  obtain ⟨x, hx⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total b t
  have hxC := (two_step_mem_l h hx).mpr ⟨ht, below_refl_l O h.base hb, (top (below_refl_l O h.base hb)).1⟩
  refine ⟨x, hx, hxC, fun y hy => ?_⟩
  obtain ⟨p, s, hyps, hs, hp, hm⟩ := (h.conditions y).mp hy
  exact (two_step_le_l h hy hxC hyps hx).mpr ⟨hp, (top hp).2 s ⟨W, hs, h.closed⟩ hm⟩

/-- 名称库由条件集名称与顶名称唯一确定，并对混合闭合；后继同时给出实际最大条件。 -/
theorem two_step_pointed_l {t} (hA : Name_d M B A) (hT : Name_d M B T) (ht : Name_d M B t)
    (hb : M.mem b B) (hz : b ≠ z)
    (hP : Forces_d M B R z (preord_m .newest (.bound 1)) (ord_env_l M A T) b)
    (hf : Forces_d M B R z (top_m (.bound 1) (.bound 2) .newest) (top_env_l A T t) b) :
    ∃ W C S, Two_step_d M B R z b A T W C S ∧ Cond_order_d M C S C ∧ Name_pool_d M B A t W ∧
      ∃ x, KPair_d M x b t ∧ M.mem x C ∧ ∀ y, M.mem y C → Entry_d M y x S := by
  obtain ⟨W, hW⟩ := name_pool_exists_l M hZF hA ht
  obtain ⟨C, S, h, L⟩ := two_step_on_l O hZF hW.closed hW.left hT hb hP
  exact ⟨W, C, S, h, L, hW, two_step_top_l O hZF h hT hW.right hz hf⟩

end YesMetaZFC.Model.Forcing.Internal
