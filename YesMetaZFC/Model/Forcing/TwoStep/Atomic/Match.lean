import YesMetaZFC.Model.Forcing.TwoStep.Atomic.Syntax
import YesMetaZFC.Model.Forcing.TwoStep.Atomic.Witness

/-! # 两阶段等号的子名称匹配

先把第二阶段的共同加强提升回二步条件，再选取首坐标仍在泛型中的等号见证。
子名称的内部归纳结论经第一次真值定理，成为第二阶段所需的等号匹配。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hZF hU

/-- 首阶段真值定理精确解释并反射第二阶段的内部等号力迫。 -/
theorem iter_eq_truth_l {s u v} {Q D q a d : (E).Domain}
    (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    (hs : Qval_d M B R z U s q) (hu : Qval_d M B R z U u a) (hv : Qval_d M B R z U v d) :
    (∃ p, U p ∧ Iter_eq_d M B R z A T p s u v) ↔ Eq_force_d E Q D Q q a d := by
  let ρ := iter_eq_env_l A T s u v
  let η := iter_eq_env_l Q D q a d
  have hρ : Env_val_d hZF ρ η := by
    intro t
    cases t with
    | free _ => exact hA
    | bound i => exact Fin.cases hv (Fin.cases hu (Fin.cases hs (Fin.cases hT (fun _ => hA)))) i
  exact (forcing_truth_l O hZF hU iter_eq_body_m iter_eq_closed_l ρ η hρ).trans
    (eq_force_sat_l E (extension_ext_l O hZF hU) η _ _ _ _ _ _)

/-- 两个方向共用同一匹配构造；k 指定内部归纳假设位于源侧还是目标侧。 -/
theorem curry_eq_match_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (k : Bool) {Q D : (E).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    {x y c p s u v} (hx : Name_d M C x) (hy : Name_d M C y) (he : Eq_force_d M C S C c x y)
    (hcp : KPair_d M c p s) (hp : U p) (hu : Curry_d M B C x u) (hv : Curry_d M B C y v)
    {q a d : (E).Domain} (hsq : Qval_d M B R z U s q)
    (hua : Qval_d M B R z U u a) (hvd : Qval_d M B R z U v d)
    (ih : ∀ e f, Entry_d M e f (if k then y else x) → Curry_eq_d M B R z A T C S e) :
    Eq_match_d E k Q D Q q a d := by
  intro a' f' haf r hr hrf
  obtain ⟨a₀, f₀, u₀, p₀, s₀, haf₀, hf₀, hfp, hp₀, hau, hua', hsf'⟩ :=
    (curry_val_entry_l O hZF hU h hu hua).mp haf
  obtain ⟨w, j, t, hwj, hj, htr, hwc, hwf⟩ := two_step_common_l O hZF hU h L hA hT
    he.1 hf₀ hcp hfp hp hp₀ hsq hsf' hr.1 hr.2.2 hrf
  obtain ⟨v₀, l, t₀, d₀, e₀, hvw, hvl, hl, hde, hve, had⟩ :=
    two_step_eq_pick_l O hZF hU h L (qval_name_l hT) hx hy he haf₀ hwc hwf.2.2 hwj hj
  obtain ⟨ht₀, _, htm⟩ := (two_step_mem_l h hvl).mp hvw.1
  obtain ⟨r', htr'⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B t₀ from ⟨W, ht₀, h.closed⟩)
  have hr'Q := (qval_mem_forcing_l O hZF hU htr' hA).mp ⟨l, hl, htm⟩
  have hr'r := (rel_force_truth_l O hZF hU htr' htr hT).mp
    ⟨l, hl, ((two_step_le_l h hvw.1 hwc.1 hvl hwj).mp hvw.2.2).2⟩
  have he₀C := (name_entry_l M hy hde).2
  obtain ⟨l₀, s₁, he₀, hs₁, hl₀, _⟩ := (h.conditions e₀).mp he₀C
  have hle := (two_step_le_l h hvw.1 he₀C hvl he₀).mp hve
  have hl₀U := hU.upward l l₀ hl hl₀.1 hle.1.2.2
  obtain ⟨e', hs₁e⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B s₁ from ⟨W, hs₁, h.closed⟩)
  obtain ⟨v₁, hdv, hv₁, _⟩ := two_step_curry_l M hZF h d₀
  obtain ⟨d', hvd'⟩ := name_value_l (R := R) (z := z) (U := U) hv₁
  have hd'e' := (curry_val_entry_l O hZF hU h hv hvd).mpr
    ⟨d₀, e₀, v₁, l₀, s₁, hde, he₀C, he₀, hl₀U, hdv, hvd', hs₁e⟩
  have hr'e' := (rel_force_truth_l O hZF hU htr' hs₁e hT).mp ⟨l, hl, hle.2⟩
  refine ⟨r', d', e', ⟨hr'Q, ?_, hr'r⟩, hd'e', hr'e', ?_⟩
  · intro hh
    exact KP.mem_irrefl_d (ZF.modelsKP (preserves_zf_l O hZF hU)) Q (hh ▸ hr'Q)
  · have haN := (name_entry_l M hx haf₀).1
    have hdN := (name_entry_l M hy hde).1
    cases k
    · exact (iter_eq_truth_l O hZF hU hA hT htr' hua' hvd').mp
        ⟨l, hl, ih a₀ f₀ haf₀ haN d₀ v₀ l t₀ u₀ v₁ ⟨hdN, hvl, had, hau, hdv⟩⟩
    · exact (iter_eq_truth_l O hZF hU hA hT htr' hvd' hua').mp
        ⟨l, hl, ih d₀ e₀ hde hdN a₀ v₀ l t₀ v₁ u₀
          ⟨haN, hvl, eq_force_symm_l hZF haN hdN had, hdv, hau⟩⟩

/-- 内部条目归纳的一步：两侧匹配只使用同一个源名称的子名称归纳假设。 -/
theorem curry_eq_step_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    {Q D : (E).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    {x y c p s u v} (hx : Name_d M C x) (hy : Name_d M C y) (he : Eq_force_d M C S C c x y)
    (hcp : KPair_d M c p s) (hp : U p) (hu : Curry_d M B C x u) (hv : Curry_d M B C y v)
    {q a d : (E).Domain} (hsq : Qval_d M B R z U s q)
    (hua : Qval_d M B R z U u a) (hvd : Qval_d M B R z U v d)
    (ih : ∀ e f, Entry_d M e f x → Curry_eq_d M B R z A T C S e) : Eq_force_d E Q D Q q a d := by
  apply (eq_force_unfold_l E (preserves_zf_l O hZF hU)
    (curry_second_name_l O hZF hU h hx hu hA hua) (curry_second_name_l O hZF hU h hy hv hA hvd)).mpr
  exact ⟨(qval_mem_forcing_l O hZF hU hsq hA).mp ⟨p, hp, ((two_step_mem_l h hcp).mp he.1).2.2⟩,
    curry_eq_match_l O hZF hU h L false hA hT hx hy he hcp hp hu hv hsq hua hvd ih,
    curry_eq_match_l O hZF hU h L true hA hT hy hx (eq_force_symm_l hZF hx hy he) hcp hp hv hu hsq hvd hua ih⟩

end YesMetaZFC.Model.Forcing.Internal
