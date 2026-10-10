import YesMetaZFC.Model.Forcing.TwoStep.Top
import YesMetaZFC.Model.Forcing.Stage.Embedding

/-! # 二步迭代的实际阶段完全嵌入

首阶段锥中的 p 映到 (p,顶名称)。映射图由原替换构造；任意二步条件的第一坐标
是其约减，且精确刻画它与阶段像的相容性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}

/-- 实际模型内函数图实现阶段嵌入，且每个二步条件由其第一坐标约减。 -/
theorem two_step_embed_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hT : Name_d M B T) {t} (ht : M.mem t W)
    (hTop : Forces_d M B R z (top_m (.bound 1) (.bound 2) .newest) (top_env_l A T t) b) :
    ∃ P F, (∀ p, M.mem p P ↔ Below_d M B R z p b) ∧
      (∀ p x, Entry_d M p x F ↔ Below_d M B R z p b ∧ KPair_d M x p t) ∧
      Reg_embed_d M P R z C S C F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  have hA : Name_d M B A := ⟨W, h.root, h.closed⟩
  have htN : Name_d M B t := ⟨W, ht, h.closed⟩
  have hn : ∀ v : Term 3, Name_d M B (v.eval (top_env_l A T t)) := by
    intro v
    cases v with
    | free _ => exact hT
    | bound i => exact Fin.cases htN (Fin.cases hA (fun _ => hT)) i
  have top {p} (hp : Below_d M B R z p b) := forced_top_l O hZF hA hT htN hp.1 hp.2.1
    ((forces_regular_l O hZF _ _ hn).1 b p h.base hp hTop)
  have mem {p x} (hp : Below_d M B R z p b) (hx : KPair_d M x p t) : M.mem x C :=
    (two_step_mem_l h hx).mpr ⟨ht, hp, (top hp).1⟩
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b
  let φ : UnarySchema 4 := { body := below_m (.bound 4) (.bound 3) (.bound 2) .newest (.bound 1) }
  obtain ⟨P, hP'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hP p : M.mem p P ↔ Below_d M B R z p b := by
    refine (hP' p).trans ?_
    rw [below_sat_l M hZF.1]
    exact ⟨And.right, fun hp => ⟨hp.1, hp⟩⟩
  let η : Env M 1 := ⟨fun _ => t, fun _ => t⟩
  let ψ : BinarySchema 1 := { body := kpair_m .newest (.bound 1) (.bound 2) }
  have hψ p x : ψ.denote η p x ↔ KPair_d M x p t :=
    kpair_sat_l M hZF.1 ((η.push p).push x) _ _ _
  obtain ⟨F, hFunction, hF'⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η
    (source := P) (target := C) (fun p _ => by
      obtain ⟨x, hx⟩ := I.total p t
      exact ⟨x, (hψ p x).mpr hx⟩)
    (fun p _ x y hx hy => kpair_unique_l M hZF.1 ((hψ p x).mp hx) ((hψ p y).mp hy))
    (fun p x hp hx => mem ((hP p).mp hp) ((hψ p x).mp hx))
  have hF p x : Entry_d M p x F ↔ Below_d M B R z p b ∧ KPair_d M x p t :=
    (hF' p x).trans (and_congr (hP p) (hψ p x))
  have cmp {x p s q y} (hx : M.mem x C) (hxp : KPair_d M x p s)
      (hy : Entry_d M q y F) : Cmp_d M C S C x y ↔ Cmp_d M P R z p q := by
    obtain ⟨hq, hyq⟩ := (hF q y).mp hy
    have hyC := mem hq hyq
    constructor
    · rintro ⟨v, hvx, hvy⟩
      obtain ⟨r, a, hvr, _, hr, _⟩ := (h.conditions v).mp hvx.1
      have hrp := ((two_step_le_l h hvx.1 hx hvr hxp).mp hvx.2.2).1
      have hrq := ((two_step_le_l h hvx.1 hyC hvr hyq).mp hvy).1
      exact ⟨r, ⟨(hP r).mpr hr, hr.2.1, hrp.2.2⟩, hrq.2.2⟩
    · rintro ⟨r, hrp, hrq⟩
      have hr := (hP r).mp hrp.1
      obtain ⟨v, hvr, hvx⟩ := two_step_lift_l O hZF h L hT hx hxp ⟨hr.1, hr.2.1, hrp.2.2⟩
      have hm := ((two_step_mem_l h hvr).mp hvx.1).2.2
      have hs := ((two_step_mem_l h hxp).mp hx).1
      exact ⟨v, hvx, (two_step_le_l h hvx.1 hyC hvr hyq).mpr
        ⟨⟨hr.1, hr.2.1, hrq⟩, (top hr).2 s ⟨W, hs, h.closed⟩ hm⟩⟩
  refine ⟨P, F, hP, hF, {
    graph := hFunction.1.1, total := ?_, domain := ?_, functional := ?_, injective := ?_,
    order := ?_, compat := ?_, reduction := ?_ }⟩
  · intro p hp _
    obtain ⟨x, hx⟩ := I.total p t
    exact ⟨x, (hF p x).mpr ⟨(hP p).mp hp, hx⟩⟩
  · intro p x hpx
    obtain ⟨hp, hx⟩ := (hF p x).mp hpx
    have hxC := mem hp hx
    exact ⟨(hP p).mpr hp, hp.2.1, hxC,
      fun e => KP.mem_irrefl_d (ZF.modelsKP hZF) C (e ▸ hxC)⟩
  · intro p x y hx hy
    exact kpair_unique_l M hZF.1 ((hF p x).mp hx).2 ((hF p y).mp hy).2
  · intro p q x hp hq
    exact (kpair_injective_l M ((hF p x).mp hp).2 ((hF q x).mp hq).2).1
  · intro p q x y hpx hqy
    obtain ⟨hp, hx⟩ := (hF p x).mp hpx
    obtain ⟨hq, hy⟩ := (hF q y).mp hqy
    refine (two_step_le_l h (mem hp hx) (mem hq hy) hx hy).trans ⟨fun h => h.1.2.2, fun hpq => ?_⟩
    exact ⟨⟨hp.1, hp.2.1, hpq⟩, (top hp).2 t htN (top hp).1⟩
  · intro p q x y hpx hqy
    have hp := (hF p x).mp hpx
    exact cmp (mem hp.1 hp.2) hp.2 hqy
  · intro x hx _
    obtain ⟨p, s, hxp, _, hp, _⟩ := (h.conditions x).mp hx
    refine ⟨p, (hP p).mpr hp, hp.2.1, fun q y hqy hqp => ?_⟩
    have hq := ((hF q y).mp hqy).1
    exact (cmp hx hxp hqy).mpr ⟨q, ⟨(hP q).mpr hq, hq.2.1, hqp⟩, O.refl q hq.1⟩

end YesMetaZFC.Model.Forcing.Internal
