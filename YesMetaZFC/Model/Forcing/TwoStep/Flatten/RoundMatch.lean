import YesMetaZFC.Model.Forcing.TwoStep.Flatten.RoundSyntax
import YesMetaZFC.Model.Forcing.TwoStep.Generic.Projection

/-! # 摊平后第二阶段等号的双向条目匹配

原条目由三层后继名称代表；首阶段关系真值给出可加入摊平名称的真实二步条件。
反向展开摊平条目即可恢复原条目，两侧子名称等号都由同一内部归纳假设给出。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

theorem round_force_truth_l {x t} {Q D a d : (E).Domain}
    (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    (hx : Qval_d M B R z U x a) (ht : Qval_d M B R z U t d) :
    (∃ p, U p ∧ Round_force_d M B R z A T p x t) ↔
      (Name_d E Q a → ∀ q, q ∈ Q → Eq_force_d E Q D Q q a d) := by
  let ρ := round_env_l A T x t
  let η := round_env_l Q D a d
  have hρ : Env_val_d hZF ρ η := by
    intro w
    cases w with
    | free _ => exact hA
    | bound i => exact Fin.cases ht (Fin.cases hx (Fin.cases hT (fun _ => hA))) i
  exact (forcing_truth_l O hZF hU round_body_m round_closed_l ρ η hρ).trans
    (round_body_sat_l (extension_ext_l O hZF hU) η)

theorem flat_round_step_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hb : U b) {Q D : (E).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    {x f t} (hx : Name_d M B x) (hf : Flat_d M B R z C x f) (ht : Curry_d M B C f t)
    {a d : (E).Domain} (hxa : Qval_d M B R z U x a) (htd : Qval_d M B R z U t d) (ha : Name_d E Q a)
    (ih : ∀ y, Entry_path_d M 3 x y → Flat_round_d M B R z b A T C y)
    (q : (E).Domain) (hq : q ∈ Q) : Eq_force_d E Q D Q q a d := by
  let hI : Mem_ind_d M := check_ind_l M hZF
  let hPair := KP.exists_pair (ZF.modelsKP hZF)
  have hEN := preserves_zf_l O hZF hU
  have refl (r : (E).Domain) (hr : r ∈ Q) : Entry_d E r r D := by
    obtain ⟨c, p, s, hc, hp, hcp, hs⟩ := (two_step_fiber_l O hZF hU h hb hA r).mp hr
    exact (rel_force_truth_l O hZF hU hs hs hT).mp ⟨p, hp, ((two_step_le_l h hc hc hcp hcp).mp (L.refl c hc)).2⟩
  have child {y fy ty} {v w : (E).Domain} (hy : Entry_path_d M 3 x y)
      (hfy : Flat_d M B R z C y fy) (hty : Curry_d M B C fy ty)
      (hyv : Qval_d M B R z U y v) (htw : Qval_d M B R z U ty w) (hv : Name_d E Q v)
      (r : (E).Domain) (hr : r ∈ Q) : Eq_force_d E Q D Q r v w :=
    (round_force_truth_l O hZF hU hA hT hyv htw).mp
      ⟨b, hb, ih y hy (qval_name_l hyv) fy ty b ⟨hfy, hty, below_refl_l O (hU.proper b hb).1 (hU.proper b hb).2⟩⟩ hv r hr
  apply (eq_force_unfold_l E hEN ha (curry_second_name_l O hZF hU h (flat_name_l M hZF hf) ht hA htd)).mpr
  refine ⟨hq, ?_, ?_⟩
  · intro v w hvw r hr hrw
    obtain ⟨y, hy, hyv⟩ := qval_entry_path_l O hZF hU hxa hvw
    obtain ⟨c, p, s, hc, hp, hcp, hsw⟩ := (two_step_fiber_l O hZF hU h hb hA w).mp (name_entry_l E ha hvw).2
    obtain ⟨j, hj, hjp, hfRel⟩ := rel_force_below_l O hZF hU hp hyv hsw hxa hvw
    obtain ⟨c', hcj, hc'⟩ := two_step_lift_l O hZF h L (qval_name_l hT) hc hcp hjp
    obtain ⟨fy, hfy⟩ := flat_exists_l M hZF B R z C y
    obtain ⟨ty, hty, htyN, _⟩ := two_step_curry_l M hZF h fy
    obtain ⟨v', htv⟩ := name_value_l (R := R) (z := z) (U := U) htyN
    have hfc := (flat_entry_l M hZF.1 hI hPair hf fy c').mpr ⟨y, j, s, hy, hc'.1, hcj, hfRel, hfy⟩
    have hv'w := (curry_val_entry_l O hZF hU h ht htd).mpr ⟨fy, c', ty, j, s, hfc, hc'.1, hcj, hj, hty, htv, hsw⟩
    exact ⟨r, v', w, ⟨hr.1, hr.2.1, refl r hr.1⟩, hv'w, hrw,
      child hy hfy hty hyv htv (name_entry_l E ha hvw).1 r hr.1⟩
  · intro v w hvw r hr hrw
    obtain ⟨fy, c, ty, p, s, hfc, hc, hcp, hp, hty, htv, hsw⟩ :=
      (curry_val_entry_l O hZF hU h ht htd).mp hvw
    obtain ⟨y, p', s', hy, _, hcp', hfRel, hfy⟩ := (flat_entry_l M hZF.1 hI hPair hf fy c).mp hfc
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hcp hcp'
    obtain ⟨v', hyv⟩ := name_value_l (R := R) (z := z) (U := U) (entry_path_name_l 3 hx hy)
    have hv'w := (rel_force_truth_l O hZF hU hyv hsw hxa).mp ⟨p, hp, hfRel⟩
    exact ⟨r, v', w, ⟨hr.1, hr.2.1, refl r hr.1⟩, hv'w, hrw,
      child hy hfy hty hyv htv (name_entry_l E ha hv'w).1 r hr.1⟩

end YesMetaZFC.Model.Forcing.Internal
