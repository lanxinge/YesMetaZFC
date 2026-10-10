import YesMetaZFC.Model.Forcing.TwoStep.Generic.Density

/-! # 地模型稠密集在第二阶段的名称像

将二步稠密集的第二坐标收集成加权名称。第一阶段泛型遇到其条件投影，保证
这个名称像在第二阶段仍然稠密，供两阶段泛型的反向组合使用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Proj_below_d (C S D x p : M.Domain) : Prop :=
  ∃ y s, M.mem y C ∧ M.mem y D ∧ KPair_d M y p s ∧ Entry_d M y x S

theorem proj_below_defined_l (hE : Extensional M) (C S D x : M.Domain) :
    Defined_d M (Proj_below_d M C S D x) := by
  let ρ : Env M 4 := (((⟨fun _ => C, fun _ => C⟩ : Env M 1).push S).push D).push x
  let φ : UnarySchema 4 := { body := .existsE (.existsE
    (.conj (.mem (.bound 1) (.bound 6)) (.conj (.mem (.bound 1) (.bound 4))
      (.conj (kpair_m (.bound 1) (.bound 2) .newest) (entry_m (.bound 1) (.bound 3) (.bound 5)))))) }
  refine ⟨4, φ, ρ, fun p => ?_⟩
  simp only [UnarySchema.denote, φ, Proj_below_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, kpair_sat_l M hE, entry_sat_l M hE]
  rfl

variable {M} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

theorem two_step_projection_dense_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hT : Name_d M B T) {D x p s} (hx : M.mem x C) (hxp : KPair_d M x p s)
    (hd : Dense_d M C S C (fun y => M.mem y D) x) :
    Dense_d M B R z (Proj_below_d M C S D x) p := by
  intro q hq
  obtain ⟨y, hyq, hyx⟩ := two_step_lift_l O hZF h L hT hx hxp hq
  obtain ⟨v, hvy, hvD⟩ := hd y hyx
  obtain ⟨r, t, hvr, _, _, _⟩ := (h.conditions v).mp hvy.1
  have hrq := ((two_step_le_l h hvy.1 hyx.1 hvr hyq).mp hvy.2.2).1
  exact ⟨r, hrq, v, t, hvy.1, hvD, hvr, L.trans v y x hvy.1 hyx.1 hx hvy.2.2 hyx.2.2⟩

variable {U : M.Domain → Prop} (hU : Generic_d M B R z U)
include hU
local notation "E" => extension_l M hZF B R z U

/-- 任意地模型二步集合都有实际第二坐标名称像，系数保留其首坐标条件。 -/
theorem two_step_image_l (h : Two_step_d M B R z b A T W C S) (D : M.Domain) :
    ∃ F : (E).Domain, ∀ a : (E).Domain, a ∈ F ↔
      ∃ x p s, M.mem x C ∧ M.mem x D ∧ U p ∧ KPair_d M x p s ∧ Qval_d M B R z U s a := by
  let ρ : Env M 2 := (⟨fun _ => C, fun _ => C⟩ : Env M 1).push D
  let φ : BinarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 4))
    (.conj (.mem .newest (.bound 3)) (kpair_m .newest (.bound 1) (.bound 2)))) }
  have hφ s p : φ.denote ρ s p ↔ ∃ x, M.mem x C ∧ M.mem x D ∧ KPair_d M x p s := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, kpair_sat_l M hZF.1]
    rfl
  obtain ⟨f, hf, _, hfE⟩ := name_comp_l M hZF φ ρ B W (fun s hs => ⟨W, hs, h.closed⟩)
  obtain ⟨F, hF⟩ := name_value_l (R := R) (z := z) (U := U) hf
  refine ⟨F, fun a => ?_⟩
  constructor
  · intro ha
    obtain ⟨s, p, hsp, hp, hs⟩ := (qval_mem_l O hZF hU hF).mp ha
    obtain ⟨_, _, hφ'⟩ := (hfE s p).mp hsp
    obtain ⟨x, hxC, hxD, hxp⟩ := (hφ s p).mp hφ'
    exact ⟨x, p, s, hxC, hxD, hp, hxp, hs⟩
  · rintro ⟨x, p, s, hxC, hxD, hp, hxp, hs⟩
    exact (qval_mem_l O hZF hU hF).mpr ⟨s, p,
      (hfE s p).mpr ⟨((two_step_mem_l h hxp).mp hxC).1, (hU.proper p hp).1,
        (hφ s p).mpr ⟨x, hxC, hxD, hxp⟩⟩, hp, hs⟩

/-- 二步稠密集合的名称像在每个已接受第二坐标以下稠密。 -/
theorem two_step_image_dense_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    {Q J F : (E).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T J)
    {D : M.Domain} (hF : ∀ a : (E).Domain, a ∈ F ↔
      ∃ x p s, M.mem x C ∧ M.mem x D ∧ U p ∧ KPair_d M x p s ∧ Qval_d M B R z U s a)
    {x p s a} (hx : M.mem x C) (hxp : KPair_d M x p s) (hp : U p) (hs : Qval_d M B R z U s a)
    (hd : Dense_d M C S C (fun y => M.mem y D) x) : Stage_dense_d E Q J F a := by
  have hb := hU.upward p b hp h.base ((two_step_mem_l h hxp).mp hx).2.1.2.2
  intro v hv hva
  obtain ⟨y, q, t, hy, hq, hyq, ht⟩ := (two_step_fiber_l O hZF hU h hb hA v).mp hv
  obtain ⟨r, hr, hrq, hrp⟩ := hU.directed q p hq hp
  have hr' := hU.proper r hr
  obtain ⟨d, hdU, hdr, hts⟩ := rel_force_below_l O hZF hU hr ht hs hT hva
  have hdq := below_trans_l O (hU.proper q hq).1 hdr ⟨hr'.1, hr'.2, hrq⟩
  have hdp := below_trans_l O (hU.proper p hp).1 hdr ⟨hr'.1, hr'.2, hrp⟩
  obtain ⟨w, hwd, hwy⟩ := two_step_lift_l O hZF h L (qval_name_l hT) hy hyq hdq
  have hwx : Below_d M C S C w x := ⟨hwy.1, hwy.2.1, (two_step_le_l h hwy.1 hx hwd hxp).mpr ⟨hdp, hts⟩⟩
  have hdw := dense_lower_l L (fun y => M.mem y D) x w hx hwx hd
  obtain ⟨k, hk, u, c, huC, huD, huk, huw⟩ := generic_pick_l hZF hU
    (proj_below_defined_l M hZF.1 C S D w) hdU (two_step_projection_dense_l O hZF h L (qval_name_l hT) hwy.1 hwd hdw)
  obtain ⟨hcW, _, hcm⟩ := (two_step_mem_l h huk).mp huC
  obtain ⟨e, hce⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B c from ⟨W, hcW, h.closed⟩)
  have heQ := (qval_mem_forcing_l O hZF hU hce hA).mp ⟨k, hk, hcm⟩
  have hev := (rel_force_truth_l O hZF hU hce ht hT).mp
    ⟨k, hk, ((two_step_le_l h huC hwy.1 huk hwd).mp huw).2⟩
  exact ⟨e, heQ, hev, (hF e).mpr ⟨u, k, c, huC, huD, hk, huk, hce⟩⟩

end YesMetaZFC.Model.Forcing.Internal
