import YesMetaZFC.Model.Forcing.Internal.Check.Relation
import YesMetaZFC.Model.Forcing.Internal.Maximum.Pool

/-! # 地函数应用于任意名称

在决定输入旧值的分支上读取真实函数图，再混合输出规范名称。函数单值性
保证分支相容，所以整个构造只需 ZF，无须为唯一值调用选择公理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

def Check_app_d (M : SetTheory.Structure.{u}) (B R z b f τ σ : M.Domain) : Prop :=
  ∀ p x y s t, Below_d M B R z p b → Entry_d M x y f → Check_d M b x s → Check_d M b y t →
    Eq_force_d M B R z p τ s → Eq_force_d M B R z p σ t

def check_app_m {n} (B R z b f τ σ : Term n) : Formula 1 n :=
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (below_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken
      z.weaken.weaken.weaken.weaken.weaken (.bound 4) b.weaken.weaken.weaken.weaken.weaken)
      (.imp (entry_m (.bound 3) (.bound 2) f.weaken.weaken.weaken.weaken.weaken)
        (.imp (check_m b.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 1))
          (.imp (check_m b.weaken.weaken.weaken.weaken.weaken (.bound 2) .newest)
            (.imp (eq_force_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken
              z.weaken.weaken.weaken.weaken.weaken (.bound 4) τ.weaken.weaken.weaken.weaken.weaken (.bound 1))
              (eq_force_m B.weaken.weaken.weaken.weaken.weaken R.weaken.weaken.weaken.weaken.weaken
                z.weaken.weaken.weaken.weaken.weaken (.bound 4) σ.weaken.weaken.weaken.weaken.weaken .newest))))))))))
derive_free_closed check_app_m

theorem check_app_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z b f τ σ : Term n) :
    Formula.satisfies ρ (check_app_m B R z b f τ σ) ↔
      Check_app_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (f.eval ρ) (τ.eval ρ) (σ.eval ρ) := by
  simp only [check_app_m, Check_app_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    below_sat_l M hE, entry_sat_l M hE, check_sat_l M hE, eq_force_sat_l M hE, Definitional.Term.eval_weaken]
  rfl

private theorem check_apply_mix_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b f X Y τ}
    (hb : M.mem b B)
    (hf : M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) f X Y)
    (hτ : Name_d M B τ) : ∃ σ, Name_d M B σ ∧ Check_app_d M B R z b f τ σ := by
  obtain ⟨d, hd, hdn, _⟩ := zf_check_l M hZF hb Y
  obtain ⟨W, hW⟩ := name_pool_exists_l M hZF hdn hdn
  let ρ₀ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let ρ : Env M 6 := ((ρ₀.push b).push f).push τ
  let φ : BinarySchema 6 := {
    body := .existsE (.existsE (.existsE (.conj (entry_m (.bound 2) (.bound 1) (.bound 6))
      (.conj (check_m (.bound 7) (.bound 2) .newest) (.conj (check_m (.bound 7) (.bound 1) (.bound 4))
        (.conj (below_m (.bound 10) (.bound 9) (.bound 8) (.bound 3) (.bound 7))
          (eq_force_m (.bound 10) (.bound 9) (.bound 8) (.bound 3) (.bound 5) .newest))))))) }
  have hφ t p : φ.denote ρ t p ↔ ∃ x y s, Entry_d M x y f ∧ Check_d M b x s ∧ Check_d M b y t ∧
      Below_d M B R z p b ∧ Eq_force_d M B R z p τ s := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      entry_sat_l M hZF.1, check_sat_l M hZF.1, below_sat_l M hZF.1, eq_force_sat_l M hZF.1]
    rfl
  have hn t (ht : M.mem t W) : Name_d M B t := ⟨W, ht, hW.closed⟩
  have checkn x s (hs : Check_d M b x s) := check_name_l M (check_range_l M hZF) hb hs
  obtain ⟨σ, hσ, hm⟩ := name_pool_mix_l O hZF hW φ ρ (by
    intro p q s t r hp hq hs ht hps hqt hrp hrq
    obtain ⟨x, y, a, hxy, hxa, hys, hpb, hτa⟩ := (hφ s p).mp hps
    obtain ⟨x', y', a', hxy', hxa', hyt, _, hτa'⟩ := (hφ t q).mp hqt
    have haa := eq_force_trans_l O hZF (checkn x a hxa) hτ (checkn x' a' hxa')
      (eq_force_symm_l hZF hτ (checkn x a hxa) (eq_force_lower_l O hZF hτ (checkn x a hxa) p r hp hrp hτa))
      (eq_force_lower_l O hZF hτ (checkn x' a' hxa') q r hq hrq hτa')
    have hxx := check_force_reflect_l O hZF hb hxa hxa' (below_trans_l O hb hrp hpb) haa
    subst x'
    have hyy := hf.1.2 x y y' hxy hxy'
    subst y'
    have hst := check_unique_l M hZF.1 (check_ind_l M hZF) b y s t hys hyt
    exact hst ▸ eq_force_refl_l O hZF hrp.1 (hn s hs))
  refine ⟨σ, hn σ hσ, fun p x y s t hp hxy hs ht he => ?_⟩
  have htd := (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) hd t b).mpr
    ⟨rfl, y, hf.output_mem_of_pairMember hxy, ht⟩
  have htW := (supp_entry_l M hW.closed hW.left htd).1
  exact hm p t hp.1 htW ((hφ t p).mpr ⟨x, y, s, hxy, hs, ht, hp, he⟩)

/-- 实际地函数作用于名称：自动构造输出名称及全部正条件上的函数值力迫。 -/
theorem check_apply_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b f X Y τ}
    (hb : M.mem b B)
    (hf : M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) f X Y)
    (hτ : Name_d M B τ) : ∃ σ c d F, Name_d M B σ ∧ Check_d M b X c ∧ Check_d M b Y d ∧ Check_d M b f F ∧
      (∀ p, Below_d M B R z p b → Mem_force_d M B R z p τ c →
        Mem_force_d M B R z p σ d ∧ Rel_force_d M B R z F p τ σ) ∧
      Check_app_d M B R z b f τ σ := by
  obtain ⟨σ, hσ, he⟩ := check_apply_mix_l O hZF hb hf hτ
  obtain ⟨c, hc, _, _⟩ := zf_check_l M hZF hb X
  obtain ⟨d, hd, hdn, _⟩ := zf_check_l M hZF hb Y
  obtain ⟨F, hF, hFn, _⟩ := zf_check_l M hZF hb f
  refine ⟨σ, c, d, F, hσ, hc, hd, hF, fun p hp hτc => ?_, he⟩
  apply (regular_conj_l (regular_mem_l O σ d) (rel_force_regular_l O hZF hFn hτ hσ)).2 p hp.1 hp.2.1
  intro q hq
  obtain ⟨r, s, a, hrq, hsa, _, hτs⟩ := hτc.2 q hq
  obtain ⟨_, x, hx, hxs⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) hc s a).mp hsa
  obtain ⟨y, hy, hxy⟩ := hf.2.2 x hx
  obtain ⟨t, hyt, htn, _⟩ := zf_check_l M hZF hb y
  have hsn := check_name_l M (check_range_l M hZF) hb hxs
  have hrb := below_trans_l O hb (below_trans_l O hp.1 hrq hq) hp
  have hσt := he r x y s t hrb hxy hxs hyt hτs
  have hσd := mem_force_left_l O hZF htn hσ hdn (eq_force_symm_l hZF hσ htn hσt)
    (check_mem_force_l O hZF hb hyt hd hrq.1 hrb.2.2 hy)
  have hst := check_rel_force_l O hZF hb hF hxs hyt hrb hxy
  let φ : UnarySchema 2 := { body := rel_at_m .newest (.bound 1) (.bound 2) }
  let ρ := ord_env_l M t F
  have hτt := (force_rel_at_l M hZF.1 (ρ.push τ) r .newest (.bound 1) (.bound 2)).mp
    ((forces_name_congr_l O hZF φ ρ (Fin.cases htn (fun _ => hFn)) hsn hτ hrq.1 hrq.2.1
      (eq_force_symm_l hZF hτ hsn hτs)).mp
        ((force_rel_at_l M hZF.1 (ρ.push s) r .newest (.bound 1) (.bound 2)).mpr hst))
  let ψ : UnarySchema 2 := { body := rel_at_m (.bound 1) .newest (.bound 2) }
  let η := ord_env_l M τ F
  have hτσ := (force_rel_at_l M hZF.1 (η.push σ) r (.bound 1) .newest (.bound 2)).mp
    ((forces_name_congr_l O hZF ψ η (Fin.cases hτ (fun _ => hFn)) htn hσ hrq.1 hrq.2.1
      (eq_force_symm_l hZF hσ htn hσt)).mp
        ((force_rel_at_l M hZF.1 (η.push t) r (.bound 1) .newest (.bound 2)).mpr hτt))
  exact ⟨r, hrq, hσd, hτσ⟩

end YesMetaZFC.Model.Forcing.Internal
