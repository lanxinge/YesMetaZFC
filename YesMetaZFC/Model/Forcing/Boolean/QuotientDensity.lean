import YesMetaZFC.Model.Forcing.Boolean.QuotientName
import YesMetaZFC.Model.Forcing.TwoStep.Generic.Density
import YesMetaZFC.Model.Forcing.Check.Order

/-! # 商内稠密性的旧条件见证

任意商内稠密集的名称，均可在加强首条件后，用真正的旧目标条件命中。
见证直接从商名字的加权条目取得；不预设中间模型稠密集属于原模型。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

theorem Qname_d.dense_witness_l {Q T w c L d P τ V ν σ x t x₀ t₀ q : M.Domain}
    (O : Cond_order_d M Q T w) (hc : M.mem c Q) (name : Qname_d Q c L d P τ)
    (relation : Check_d M c V ν) (hσ : Name_d M Q σ) (check : Check_d M c x t)
    (check₀ : Check_d M c x₀ t₀) (bound : Entry_d M x x₀ V)
    (hq : Below_d M Q T w q c) (member : Mem_force_d M Q T w q t τ)
    (dense : Forces_d M Q T w (stage_dense_m (.bound 3) (.bound 2) (.bound 1) (.bound 0))
      (stage_env_l M τ ν σ t₀) q) :
    ∃ r y s, Below_d M Q T w r q ∧ M.mem y L ∧ y ≠ d ∧ Check_d M c y s ∧
      Mem_force_d M Q T w r s τ ∧ Entry_d M y x V ∧ Mem_force_d M Q T w r s σ := by
  have nt := check_name_l M (check_range_l M hZF) hc check
  have nt₀ := check_name_l M (check_range_l M hZF) hc check₀
  have nv := check_name_l M (check_range_l M hZF) hc relation
  let ρ := stage_env_l M τ ν σ t₀
  have names : ∀ a : Term 4, Name_d M Q (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact name.1
    | bound i => exact Fin.cases nt₀ (Fin.cases hσ (Fin.cases nv (fun _ => name.1))) i
  have pushed : ∀ a : Term 5, Name_d M Q (a.eval (ρ.push t)) := by
    intro a
    cases a with
    | free i => exact names (.free i)
    | bound i => exact Fin.cases nt (fun i => names (.bound i)) i
  have all := (forces_all_l hZF.1 _ ρ q).mp dense t nt
  have xx := check_rel_force_l O hZF hc relation check check₀ hq bound
  have ex := forces_mp_l hZF.1 (forces_regular_l O hZF _ _ pushed).1
    (forces_regular_l O hZF _ _ pushed) hq.1 hq.2.1 all (by
      rw [forces_conj_l,forces_mem_l hZF.1,force_rel_at_l M hZF.1]
      exact ⟨member,xx⟩)
  obtain ⟨r,hr,s,ns,body⟩ := forces_exists_dense_l hZF.1 ex q (below_refl_l O hq.1 hq.2.1)
  have parts : Mem_force_d M Q T w r s τ ∧ Rel_force_d M Q T w ν r s t ∧ Mem_force_d M Q T w r s σ := by
    simpa only [forces_conj_l,forces_mem_l hZF.1,force_rel_at_l M hZF.1] using! body
  obtain ⟨v,a,b,hv,ab,vb,eq⟩ := parts.1.2 r (below_refl_l O hr.1 hr.2.1)
  obtain ⟨hb,y,_,hy,yz,checkY,_,_⟩ := (name.2 a b).mp ab
  have na := check_name_l M (check_range_l M hZF) hc checkY
  let η : Env M 3 := ⟨Fin.cases ν (Fin.cases t (fun _ => σ)),fun _ => ν⟩
  let φ : UnarySchema 3 := {
    body := .conj (rel_at_m .newest (.bound 2) (.bound 1)) (.mem .newest (.bound 3)) }
  have named : ∀ i, Name_d M Q (η.bound i) := Fin.cases nv (Fin.cases nt (fun _ => hσ))
  have body' : Forces_d M Q T w φ.body (η.push s) r := by
    rw [forces_conj_l,force_rel_at_l M hZF.1,forces_mem_l hZF.1]
    exact parts.2
  have lowered := (forces_regular_l O hZF φ.body (η.push s) (by
    intro a
    cases a with
    | free _ => exact nv
    | bound i => exact Fin.cases ns named i)).1 r v hr.1 hv body'
  have transferred := (forces_name_congr_l O hZF φ η named ns na hv.1 hv.2.1 eq).mp lowered
  have final : Rel_force_d M Q T w ν v a t ∧ Mem_force_d M Q T w v a σ := by
    simpa only [φ,forces_conj_l,force_rel_at_l M hZF.1,forces_mem_l hZF.1] using! transferred
  have vq := below_trans_l O hq.1 hv hr
  exact ⟨v,y,a,vq,hy,yz,checkY,mem_force_entry_l O hZF hv.1 na hb ab vb,
    check_rel_reflect_l O hZF hc relation checkY check (below_trans_l O hc vq hq) final.1,final.2⟩

end YesMetaZFC.Model.Forcing.Internal
