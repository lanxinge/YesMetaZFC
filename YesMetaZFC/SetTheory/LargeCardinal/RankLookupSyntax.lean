import YesMetaZFC.SetTheory.LargeCardinal.RankEnumerationSyntax

/-! # 用两个有限坐标读取秩层枚举包 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Er_hit_d (T G i r s x : M.Domain) : Prop := ∃ α, M.mem α T ∧ ∃ β, M.mem β T ∧
  ∃ p, M.mem p T ∧ ∃ μ, M.mem μ T ∧ ∃ g, M.mem g T ∧ Rd_entry_d i α s ∧ Rd_entry_d r β s ∧
    Rd_entry_d α p G ∧ KPair_d M p μ g ∧ Rd_entry_d β x g
def er_hit_m {d} (T G i r s x : Term d) : Formula 1 d :=
  let w (t : Term d) : Term (d+5) := t.weaken.weaken.weaken.weaken.weaken
  Formula.existsMem T (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken
    (Formula.existsMem T.weaken.weaken.weaken (Formula.existsMem T.weaken.weaken.weaken.weaken
      (.conj (rd_entry0_m (w i) (.bound 4) (w s)) (.conj (rd_entry0_m (w r) (.bound 3) (w s))
        (.conj (rd_entry0_m (.bound 4) (.bound 2) (w G))
          (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (rd_entry0_m (.bound 3) (w x) .newest)))))))))
derive_free_closed er_hit_m
theorem er_hit_delta_l {d} (T G i r s x : Term d) : (er_hit_m T G i r s x).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
      (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..)))))))))
theorem er_hit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T G i r s x : Term d) :
    Formula.satisfies ρ (er_hit_m T G i r s x) ↔
      Er_hit_d (T.eval ρ) (G.eval ρ) (i.eval ρ) (r.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [er_hit_m, Er_hit_d, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Er_hit_d.bound_l {T G i r s x : M.Domain} (hT : M.TransitiveSet T) (h : Er_hit_d T G i r s x) : M.mem x T := by
  obtain ⟨_, _, _, _, _, _, _, _, g, hg, _, _, _, _, p, hp, hpg⟩ := h
  exact (hp.mem_l M hT (hT g hg p hpg)).2

theorem er_hit_unique_l (hKP : M.Models KP) {T G i r s x y n κ : M.Domain}
    (hs : Fn0_d n κ s) (hG : Fn0_d κ T G)
    (enums : ∀ α p, Rd_entry_d α p G → Er_enum_d (kp_pair_l hKP) α p)
    (hx : Er_hit_d T G i r s x) (hy : Er_hit_d T G i r s y) : x = y := by
  obtain ⟨α, _, β, _, p, _, μ, _, g, _, hi, hr, hαp, hp, hgx⟩ := hx
  obtain ⟨α', _, β', _, p', _, μ', _, g', _, hi', hr', hαp', hp', hgy⟩ := hy
  have eq := (fn0_function_l hKP hs).1.2 i α' α hi' hi
  subst α'
  have eq := (fn0_function_l hKP hs).1.2 r β' β hr' hr
  subst β'
  have eq := (fn0_function_l hKP hG).1.2 α p' p hαp' hαp
  subst p'
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
  obtain ⟨V, ν, f, _, hp'', _, bij⟩ := enums α p hαp
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp''
  exact bij.1.1.1.2 β x y hgx hgy

end YesMetaZFC.SetTheory.LargeCardinal
