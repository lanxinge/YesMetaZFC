import YesMetaZFC.Model.Forcing.TwoStep.Order
import YesMetaZFC.Model.Forcing.Internal.Extension.Generic

/-! # 二步迭代的第一阶段投影与实际名称实例

第一坐标的任意加强均能提升为二步加强，故二步泛型投影为原地模型泛型。
扩张内的任意非空预序由真值定理局部表示为本层二步偏序，无需额外名称选择合同。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

/-- 第一坐标可任意加强，并保留原第二坐标名称。 -/
theorem two_step_lift_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hT : Name_d M B T) {x p s r} (hx : M.mem x C) (hxp : KPair_d M x p s)
    (hr : Below_d M B R z r p) : ∃ y, KPair_d M y r s ∧ Below_d M C S C y x := by
  obtain ⟨hs, hp, hm⟩ := (two_step_mem_l h hxp).mp hx
  obtain ⟨y, hy⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total r s
  have hyC := (two_step_mem_l h hy).mpr ⟨hs, below_trans_l O h.base hr hp,
    (regular_mem_l O s A).1 p r hp.1 hr hm⟩
  have hss := ((two_step_le_l h hx hx hxp hxp).mp (L.refl x hx)).2
  exact ⟨y, hy, hyC, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) C (he ▸ hyC),
    (two_step_le_l h hyC hx hy hxp).mpr ⟨hr,
      (rel_force_regular_l O hZF hT ⟨W, hs, h.closed⟩ ⟨W, hs, h.closed⟩).1 p r hp.1 hr hss⟩⟩

def First_generic_d (M : SetTheory.Structure.{u}) (B R : M.Domain) (V : M.Domain → Prop) (q : M.Domain) : Prop :=
  M.mem q B ∧ ∃ x p s, V x ∧ KPair_d M x p s ∧ Entry_d M p q R

/-- 二步泛型的第一坐标向上闭包是原偏序上的地模型泛型。 -/
theorem two_step_generic_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hT : Name_d M B T) {V : M.Domain → Prop} (hV : Generic_d M C S C V) :
    Generic_d M B R z (First_generic_d M B R V) := by
  have coords {x} (hx : V x) := (h.conditions x).mp (hV.proper x hx).1
  have mem {x p s} (hx : V x) (hxp : KPair_d M x p s) :=
    (two_step_mem_l h hxp).mp (hV.proper x hx).1
  have liftD (D : M.Domain) : ∃ F, ∀ x, M.mem x F ↔ M.mem x C ∧
      ∃ p s, KPair_d M x p s ∧ M.mem p D := by
    let ρ : Env M 1 := ⟨fun _ => D, fun _ => D⟩
    let φ : UnarySchema 1 := { body := .existsE (.existsE
      (.conj (kpair_m (.bound 2) (.bound 1) .newest) (.mem (.bound 1) (.bound 3)))) }
    obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF φ ρ C
    refine ⟨F, fun x => (hF x).trans (and_congr_right fun _ => ?_)⟩
    simp only [φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, Formula.satisfies_mem_iff]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro q ⟨hq, x, p, s, hx, hxp, hpq⟩
    have hp := (mem hx hxp).2.1
    exact ⟨hq, fun he => hp.2.1 (O.zero p hp.1 (he ▸ hpq))⟩
  · obtain ⟨x, hx⟩ := hV.inhabited
    obtain ⟨p, s, hxp, _, hp, _⟩ := coords hx
    exact ⟨p, hp.1, x, p, s, hx, hxp, O.refl p hp.1⟩
  · rintro q r ⟨hq, x, p, s, hx, hxp, hpq⟩ hr hqr
    exact ⟨hr, x, p, s, hx, hxp, O.trans p q r (mem hx hxp).2.1.1 hq hr hpq hqr⟩
  · rintro q r ⟨hq, x, p, s, hx, hxp, hpq⟩ ⟨hr, y, t, v, hy, hyt, htr⟩
    obtain ⟨w, hw, hwx, hwy⟩ := hV.directed x y hx hy
    obtain ⟨d, a, hwd, _, hd, _⟩ := coords hw
    have hdp := ((two_step_le_l h (hV.proper w hw).1 (hV.proper x hx).1 hwd hxp).mp hwx).1
    have hdt := ((two_step_le_l h (hV.proper w hw).1 (hV.proper y hy).1 hwd hyt).mp hwy).1
    exact ⟨d, ⟨hd.1, w, d, a, hw, hwd, O.refl d hd.1⟩,
      O.trans d p q hd.1 (mem hx hxp).2.1.1 hq hdp.2.2 hpq,
      O.trans d t r hd.1 (mem hy hyt).2.1.1 hr hdt.2.2 htr⟩
  · rintro q ⟨hq, x, p, s, hx, hxp, hpq⟩ D hd
    obtain ⟨F, hF⟩ := liftD D
    obtain ⟨y, hy, hyF⟩ := hV.meets x hx F (by
      intro y hy
      obtain ⟨r, t, hyr, _, hr, _⟩ := (h.conditions y).mp hy.1
      have hrp := ((two_step_le_l h hy.1 (hV.proper x hx).1 hyr hxp).mp hy.2.2).1
      obtain ⟨d, hd', hdD⟩ := hd r ⟨hr.1, hr.2.1, O.trans r p q hr.1 (mem hx hxp).2.1.1 hq hrp.2.2 hpq⟩
      obtain ⟨w, hwd, hwy⟩ := two_step_lift_l O hZF h L hT hy.1 hyr hd'
      exact ⟨w, hwy, (hF w).mpr ⟨hwy.1, d, t, hwd, hdD⟩⟩)
    obtain ⟨_, r, t, hyr, hrD⟩ := (hF y).mp hyF
    have hr := (mem hy hyr).2.1
    exact ⟨r, ⟨hr.1, y, r, t, hy, hyr, O.refl r hr.1⟩, hrD⟩

variable {U : M.Domain → Prop} (hU : Generic_d M B R z U)
include hU
local notation "E" => extension_l M hZF B R z U

/-- 有界名称库仍覆盖第二阶段的每个条件，且只接受真实的第二阶段成员。 -/
theorem two_step_fiber_l (h : Two_step_d M B R z b A T W C S) (hb : U b)
    {Q : (E).Domain} (hA : Qval_d M B R z U A Q) (q : (E).Domain) :
    (E).mem q Q ↔ ∃ x p s, M.mem x C ∧ U p ∧ KPair_d M x p s ∧ Qval_d M B R z U s q := by
  constructor
  · intro hq
    obtain ⟨s, d, hsd, _, hs⟩ := (qval_mem_l O hZF hU hA).mp hq
    obtain ⟨r, hr, hm⟩ := (qval_mem_forcing_l O hZF hU hs hA).mpr hq
    obtain ⟨p, hp, hpb, hpr⟩ := hU.directed b r hb hr
    have hp' := hU.proper p hp
    obtain ⟨x, hx⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total p s
    have hxC := (two_step_mem_l h hx).mpr ⟨(supp_entry_l M h.closed h.root hsd).1,
      ⟨hp'.1, hp'.2, hpb⟩, (regular_mem_l O s A).1 r p hm.1 ⟨hp'.1, hp'.2, hpr⟩ hm⟩
    exact ⟨x, p, s, hxC, hp, hx, hs⟩
  · rintro ⟨x, p, s, hx, hp, hxp, hs⟩
    exact (qval_mem_forcing_l O hZF hU hs hA).mp ⟨p, hp, ((two_step_mem_l h hxp).mp hx).2.2⟩

/-- 第二阶段的共同加强可提升为真实二步共同加强，首坐标仍被原泛型接受。 -/
theorem two_step_common_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    {Q D : (E).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    {x p s y q t} (hx : M.mem x C) (hy : M.mem y C) (hxp : KPair_d M x p s) (hyq : KPair_d M y q t)
    (hp : U p) (hq : U q) {a c v : (E).Domain} (hs : Qval_d M B R z U s a)
    (ht : Qval_d M B R z U t c) (hv : v ∈ Q) (hva : Entry_d E v a D) (hvc : Entry_d E v c D) :
    ∃ j r u, KPair_d M j r u ∧ U r ∧ Qval_d M B R z U u v ∧
      Below_d M C S C j x ∧ Below_d M C S C j y := by
  have hb := hU.upward p b hp h.base ((two_step_mem_l h hxp).mp hx).2.1.2.2
  obtain ⟨z', r, u, hz', hr, hzr, hu⟩ := (two_step_fiber_l O hZF hU h hb hA v).mp hv
  obtain ⟨k, hk, hkp, hkq⟩ := hU.directed p q hp hq
  obtain ⟨w, hw, hwk, hwr⟩ := hU.directed k r hk hr
  have hw' := hU.proper w hw
  have hwp : Below_d M B R z w p :=
    ⟨hw'.1, hw'.2, O.trans w k p hw'.1 (hU.proper k hk).1 (hU.proper p hp).1 hwk hkp⟩
  have hwq : Below_d M B R z w q :=
    ⟨hw'.1, hw'.2, O.trans w k q hw'.1 (hU.proper k hk).1 (hU.proper q hq).1 hwk hkq⟩
  obtain ⟨d, hd, hdw, hus⟩ := rel_force_below_l O hZF hU hw hu hs hT hva
  obtain ⟨e, he, hed, hut⟩ := rel_force_below_l O hZF hU hd hu ht hT hvc
  have hew := below_trans_l O hw'.1 hed hdw
  have her := below_trans_l O (hU.proper r hr).1 hew ⟨hw'.1, hw'.2, hwr⟩
  obtain ⟨j, hje, hjz⟩ := two_step_lift_l O hZF h L (qval_name_l hT) hz' hzr her
  have hjs := (rel_force_regular_l O hZF (qval_name_l hT) (qval_name_l hu) (qval_name_l hs)).1
    d e (hU.proper d hd).1 hed hus
  exact ⟨j, e, u, hje, he, hu,
    ⟨hjz.1, hjz.2.1, (two_step_le_l h hjz.1 hx hje hxp).mpr ⟨below_trans_l O (hU.proper p hp).1 hew hwp, hjs⟩⟩,
    ⟨hjz.1, hjz.2.1, (two_step_le_l h hjz.1 hy hje hyq).mpr ⟨below_trans_l O (hU.proper q hq).1 hew hwq, hut⟩⟩⟩

/-- 扩张内任意非空预序均有实际二步名称呈现；首阶段可缩到泛型中的一个条件。 -/
theorem two_step_local_l (Q D : (E).Domain) (hQ : Preord_d E Q D) (hne : ∃ q, (E).mem q Q) :
    ∃ b A T W C S, U b ∧ Qval_d M B R z U A Q ∧ Qval_d M B R z U T D ∧
      Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b ∧
      Two_step_d M B R z b A T W C S ∧ Cond_order_d M C S C ∧ ∃ x, M.mem x C ∧ x ≠ C := by
  let φ : Formula 1 2 := preord_m (.bound 0) (.bound 1)
  have hφ : φ.FreeClosed := preord_m_freeClosed _ _ rfl rfl
  let η := ord_env_l E Q D
  obtain ⟨ρ, hρ⟩ := lift_env_l hZF η
  have hA := hρ (.bound 0)
  have hT := hρ (.bound 1)
  have hh : Formula.satisfies η φ := (preord_sat_l (extension_ext_l O hZF hU) η _ _).mpr hQ
  obtain ⟨b, hb, hp⟩ := (forcing_truth_l O hZF hU φ hφ ρ η hρ).mpr hh
  have hp : Forces_d M B R z φ (ord_env_l M (ρ.bound 0) (ρ.bound 1)) b :=
    (forces_env_l hZF.1 φ hφ ρ _ (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) b).mp hp
  obtain ⟨W, C, S, _, h, L⟩ := two_step_l O hZF (qval_name_l hA) (qval_name_l hT) (hU.proper b hb).1 hp
  obtain ⟨q, hq⟩ := hne
  obtain ⟨x, _, _, hxC, _⟩ := (two_step_fiber_l O hZF hU h hb hA q).mp hq
  exact ⟨b, ρ.bound 0, ρ.bound 1, W, C, S, hb, hA, hT, hp, h, L, x, hxC,
    fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) C (he ▸ hxC)⟩

/-- 被泛型接受的名称预序在扩张内成为实际预序。 -/
theorem two_step_preord_l {Q D : (E).Domain} (hA : Qval_d M B R z U A Q) (hT : Qval_d M B R z U T D)
    (hb : U b) (hP : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b) :
    Preord_d E Q D := by
  have hρ : Env_val_d hZF (ord_env_l M A T) (ord_env_l E Q D) := by
    intro t
    cases t with
    | free _ => exact hT
    | bound i => exact Fin.cases hA (fun _ => hT) i
  exact (preord_sat_l (extension_ext_l O hZF hU) _ _ _).mp
    ((forcing_truth_l O hZF hU _ (preord_m_freeClosed _ _ rfl rfl) _ _ hρ).mp ⟨b, hb, hP⟩)

end YesMetaZFC.Model.Forcing.Internal
