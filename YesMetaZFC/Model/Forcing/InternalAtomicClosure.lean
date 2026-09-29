import YesMetaZFC.Model.Forcing.InternalAtomicSyntax
import YesMetaZFC.Model.Forcing.InternalClosure
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 内部最大带条件双模拟

在内部三元组集合的幂集中分离双模拟，再取并。最大关系满足原子等号的匹配方程；
证明只用实际分离公式与集合运算，不预设递归解、真值引理或外部完备性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Triple_carrier_d (B S X : M.Domain) : Prop := ∀ q, M.mem q X ↔
  ∃ p s t, M.mem p B ∧ M.mem s S ∧ M.mem t S ∧ Triple_d M q p s t

theorem triple_exists_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (p s t : M.Domain) : ∃ q, Triple_d M q p s t := by
  obtain ⟨a, ha⟩ := (kpair_interpretation_l M hE hP).total s t
  obtain ⟨q, hq⟩ := (kpair_interpretation_l M hE hP).total p a
  exact ⟨q, a, ha, hq⟩

theorem triple_carrier_l (hZF : M.Models ZF) (B S : M.Domain) :
    ∃ X, Triple_carrier_d M B S X := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨T, hT⟩ := ZF.exists_cartesianProduct hZF I S S
  obtain ⟨X, hX⟩ := ZF.exists_cartesianProduct hZF I B T
  refine ⟨X, fun q => (hX q).trans ?_⟩
  constructor
  · rintro ⟨p, hp, a, ha, hq⟩
    obtain ⟨s, hs, t, ht, ha⟩ := (hT a).mp ha
    exact ⟨p, s, t, hp, hs, ht, a, ha, hq⟩
  · rintro ⟨p, s, t, hp, hs, ht, a, ha, hq⟩
    exact ⟨p, hp, a, (hT a).mpr ⟨s, hs, t, ht, ha⟩, hq⟩

structure Max_bisim_d (B R z X F : M.Domain) : Prop where
  subset : ∀ q, M.mem q F → M.mem q X
  bisim : Bisim_d M B R z F
  greatest : ∀ G, (∀ q, M.mem q G → M.mem q X) → Bisim_d M B R z G →
    ∀ q, M.mem q G → M.mem q F

/-- 内部幂集分离出的所有双模拟的并，仍然是双模拟。 -/
theorem bisim_max_l (hZF : M.Models ZF) (B R z X : M.Domain) :
    ∃ F, Max_bisim_d M B R z X F := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF X
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let φ : UnarySchema 3 := { body := bisim_m (.bound 3) (.bound 2) (.bound 1) (.bound 0) }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ P
  have hc G : M.mem G C ↔ (∀ q, M.mem q G → M.mem q X) ∧ Bisim_d M B R z G := by
    rw [hC G, hP G]
    exact and_congr_right fun _ => bisim_sat_l M hZF.1 (ρ.push G) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  obtain ⟨F, hF⟩ := KP.exists_union (ZF.modelsKP hZF) C
  have hg {G} (hG : M.mem G C) : ∀ q, M.mem q G → M.mem q F :=
    fun q hq => (hF q).mpr ⟨G, hG, hq⟩
  refine ⟨F, ⟨?_, ?_, fun G hG hb => hg ((hc G).mpr ⟨hG, hb⟩)⟩⟩
  · intro q hq
    obtain ⟨G, hG, hq⟩ := (hF q).mp hq
    exact ((hc G).mp hG).1 q hq
  · rintro p s t ⟨q, hq, hqF⟩
    obtain ⟨G, hG, hqG⟩ := (hF q).mp hqF
    obtain ⟨hl, hr⟩ := ((hc G).mp hG).2 p s t ⟨q, hq, hqG⟩
    exact ⟨match_mono_l M (hg hG) false hl, match_mono_l M (hg hG) true hr⟩

/-- 最大关系的反向匹配方程：把满足一步匹配的新三元组加入即可。 -/
theorem bisim_unfold_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hU : ∀ F, ∃ S, M.IsUnionOf S F) {B R z S X F}
    (hX : Triple_carrier_d M B S X) (hF : Max_bisim_d M B R z X F)
    {p s t} (hp : M.mem p B) (hs : M.mem s S) (ht : M.mem t S) :
    Rel_d M F p s t ↔ Match_d M false B R z F p s t ∧ Match_d M true B R z F p t s := by
  refine ⟨hF.bisim p s t, fun h => ?_⟩
  obtain ⟨q, hq⟩ := triple_exists_l M hE hP p s t
  have hqX := (hX q).mpr ⟨p, s, t, hp, hs, ht, hq⟩
  obtain ⟨G, hG⟩ := set_insert_l M hP hU F q
  have hi r (hr : M.mem r F) : M.mem r G := (hG r).mpr (Or.inl hr)
  have hg : Bisim_d M B R z G := by
    rintro a b c ⟨r, hr, hrG⟩
    rcases (hG r).mp hrG with hrF | rfl
    · have k := hF.bisim a b c ⟨r, hr, hrF⟩
      exact ⟨match_mono_l M hi false k.1, match_mono_l M hi true k.2⟩
    · obtain ⟨rfl, rfl, rfl⟩ := triple_inj_l M hr hq
      exact ⟨match_mono_l M hi false h.1, match_mono_l M hi true h.2⟩
  have hb r (hr : M.mem r G) : M.mem r X :=
    ((hG r).mp hr).elim (hF.subset r) (fun e => e ▸ hqX)
  exact ⟨q, hq, hF.greatest G hb hg q ((hG q).mpr (Or.inr rfl))⟩

/-- 三元组关系限制到一个闭支撑；匹配到的子名称仍在同一支撑中。 -/
theorem bisim_restrict_l (hZF : M.Models ZF) {B R z S X F}
    (hS : Supp_d M B S) (hX : Triple_carrier_d M B S X) (hF : Bisim_d M B R z F) :
    ∃ G, (∀ q, M.mem q G ↔ M.mem q F ∧ M.mem q X) ∧ Bisim_d M B R z G := by
  obtain ⟨G, hG⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) F X
  refine ⟨G, hG, ?_⟩
  rintro p s t ⟨q, hq, hqG⟩
  obtain ⟨hqF, hqX⟩ := (hG q).mp hqG
  obtain ⟨p', s', t', hp, hs, ht, hq'⟩ := (hX q).mp hqX
  obtain ⟨rfl, rfl, rfl⟩ := triple_inj_l M hq hq'
  have hm (k : Bool) {s t} (hs : M.mem s S) (ht : M.mem t S)
      (h : Match_d M k B R z F p s t) : Match_d M k B R z G p s t := by
    intro a b hab r hr hrb
    obtain ⟨v, d, c, hv, hd, hvc, hvF⟩ := h a b hab r hr hrb
    have ha := (supp_entry_l M hS hs hab).1
    have hdS := (supp_entry_l M hS ht hd).1
    refine ⟨v, d, c, hv, hd, hvc, ?_⟩
    cases k <;> obtain ⟨w, hw, hwF⟩ := hvF
    · exact ⟨w, hw, (hG w).mpr ⟨hwF, (hX w).mpr ⟨v, a, d, hv.1, ha, hdS, hw⟩⟩⟩
    · exact ⟨w, hw, (hG w).mpr ⟨hwF, (hX w).mpr ⟨v, d, a, hv.1, hdS, ha, hw⟩⟩⟩
  have h := hF p s t ⟨q, hq, hqF⟩
  exact ⟨hm false hs ht h.1, hm true ht hs h.2⟩

/-- 任意闭支撑上的最大关系计算全局内部等号力迫；支撑选择不改变结果。 -/
theorem eq_force_local_l (hZF : M.Models ZF) {B R z S X F}
    (hS : Supp_d M B S) (hX : Triple_carrier_d M B S X) (hF : Max_bisim_d M B R z X F)
    {p s t} (hp : M.mem p B) (hs : M.mem s S) (ht : M.mem t S) :
    Eq_force_d M B R z p s t ↔ Rel_d M F p s t := by
  constructor
  · rintro ⟨_, G, hg, q, hq, hqG⟩
    obtain ⟨H, hH, hh⟩ := bisim_restrict_l M hZF hS hX hg
    have hi r (hr : M.mem r H) := ((hH r).mp hr).2
    exact ⟨q, hq, hF.greatest H hi hh q
      ((hH q).mpr ⟨hqG, (hX q).mpr ⟨p, s, t, hp, hs, ht, hq⟩⟩)⟩
  · exact fun h => ⟨hp, F, hF.bisim, h⟩

end YesMetaZFC.Model.Forcing.Internal
