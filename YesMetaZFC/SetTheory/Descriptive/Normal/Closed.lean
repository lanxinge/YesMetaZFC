import YesMetaZFC.SetTheory.Descriptive.Normal.Observation
import YesMetaZFC.SetTheory.Descriptive.Closed

/-! # 无违规证书组成实际闭集 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Nc_d (B J T R N F E z p : M.Domain) : Prop := ∃ x w,
  M.mem x B ∧ M.mem w B ∧ Rp_d I J x w p ∧ ¬ Nb_d I T R N F E z x w
def nc_m {d} (B J T R N F E z p : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (.mem (.bound 1) B.weaken.weaken) (.conj (.mem .newest B.weaken.weaken) (.conj
  (rp_m (𝒞 := 𝒞) J.weaken.weaken (.bound 1) .newest p.weaken.weaken)
  (.neg (nb_m (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken N.weaken.weaken F.weaken.weaken E.weaken.weaken z.weaken.weaken (.bound 1) .newest))))))
derive_free_closed nc_m
theorem nc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B J T R N F E z p : Term d) :
    Formula.satisfies ρ (nc_m (𝒞 := 𝒞) B J T R N F E z p) ↔
      Nc_d I (B.eval ρ) (J.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (E.eval ρ) (z.eval ρ) (p.eval ρ) := by
  simp only [nc_m, Nc_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, rp_sat_l I, Formula.satisfies_neg_iff, nb_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem nc_closed_l (hZF : M.Models ZF) {ω A B J T R N F} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hc : Btree_d I ω A A T R N F) (E z : M.Domain) :
    ∃ C, Cl_d A B C ∧ ∀ p, M.mem p C ↔ M.mem p B ∧ Nc_d I B J T R N F E z p := by
  classical
  let ρ : Env M 8 := (((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push J).push T).push R).push N).push F).push E).push z
  let φ : UnarySchema 8 := { body := nc_m (𝒞 := 𝒞) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hC p : M.mem p C ↔ M.mem p B ∧ Nc_d I B J T R N F E z p :=
    (hC' p).trans (and_congr_right fun _ => nc_sat_l I hZF.1 _ _ _ _ _ _ _ _ _ _)
  obtain ⟨U, hU⟩ := cm_exists_l (ZF.modelsKP hZF) B C
  refine ⟨C, ⟨fun p hp => ((hC p).mp hp).1, U, hU, ⟨fun p hp => ((hU p).mp hp).1, ?_⟩⟩, hC⟩
  intro p hp
  obtain ⟨hpB, hpC⟩ := (hU p).mp hp
  obtain ⟨x, w, hx, hw, hpair⟩ := rp_decode_l I hZF hJ ((hB.2 p).mp hpB)
  have bad : Nb_d I T R N F E z x w := Classical.byContradiction
    (fun h => hpC ((hC p).mpr ⟨hpB, x, w, (hB.2 x).mpr hx, (hB.2 w).mpr hw, hpair, h⟩))
  obtain ⟨n, s, t, hn, hs, ht, obs⟩ := nb_observe_l I hZF hB.1 hA hc hx hw bad
  have hsf := hs.isSetFunctionFromTo hx (hB.1.transitive hZF n hn)
  have htf := ht.isSetFunctionFromTo hw (hB.1.transitive hZF n hn)
  obtain ⟨r, hrf, hr⟩ := rp_exists_l I hZF hJ hsf htf
  refine ⟨r, (hA r).mpr ⟨n, hn, hrf⟩, (rp_subset_l I hJ hsf htf hr hpair).mpr
    ⟨(ds_restrict_iff_l I hsf hx.1).mp hs, (ds_restrict_iff_l I htf hw.1).mp ht⟩, fun q hq hrq => ?_⟩
  apply (hU q).mpr
  refine ⟨hq, fun hqC => ?_⟩
  obtain ⟨_, y, v, hy, hv, hqpair, hn⟩ := (hC q).mp hqC
  obtain ⟨hsy, htv⟩ := (rp_subset_l I hJ hsf htf hr hqpair).mp hrq
  exact hn (obs y v hsy htv)

/-- 每个 Borel 解释都是一个实际闭证书集的投影。 -/
theorem borel_closed_proj_l (hZF : M.Models ZF) {ω A B J K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hk : Borel_d I ω A A B K) : ∃ C, Cl_d A B C ∧ Pr_d I B J C K := by
  obtain ⟨c, hc, hk⟩ := hk
  obtain ⟨T, R, N, F, hpack, hc⟩ := hc
  obtain ⟨G, hg⟩ := ha
  obtain ⟨E, hE⟩ := ZF.exists_restriction hZF I G T
  have he : M.IsSetInjectionFromTo I E T ω := ⟨hE.isSetFunctionFromTo hg.1 hc.tree.1,
    fun a b i hai hbi => hg.2 a b i ((hE.2 a i).mp hai).2 ((hE.2 b i).mp hbi).2⟩
  obtain ⟨z, hz, hzω⟩ := hB.1.1.1
  obtain ⟨C, hC, eqn⟩ := nc_closed_l I hZF hB hA hJ hc E z
  refine ⟨C, hC, fun x => ⟨?_, ?_⟩⟩
  · intro hxK
    obtain ⟨hxB, hx⟩ := (hk x).mp hxK
    obtain ⟨w, hw, hn⟩ := nb_complete_l I hZF hB.1 hc hpack he hz hzω ((hB.2 x).mp hxB) hx
    obtain ⟨p, hp, hpair⟩ := rp_exists_l I hZF hJ ((hB.2 x).mp hxB) hw
    exact ⟨hxB, w, p, (hB.2 w).mpr hw, (hB.2 p).mpr hp, hpair,
      (eqn p).mpr ⟨(hB.2 p).mpr hp, x, w, hxB, (hB.2 w).mpr hw, hpair, hn⟩⟩
  · rintro ⟨hxB, w, p, hwB, _, hpair, hpC⟩
    obtain ⟨_, y, v, hyB, hvB, hp, hn⟩ := (eqn p).mp hpC
    obtain ⟨ex, ew⟩ := rp_injective_l I hZF.1 hJ ((hB.2 x).mp hxB) ((hB.2 w).mp hwB)
      ((hB.2 y).mp hyB) ((hB.2 v).mp hvB) hpair hp
    subst y v
    exact (hk x).mpr ⟨hxB, nb_sound_l I hZF hB.1 hA hc hpack he.1 hz ((hB.2 x).mp hxB) ((hB.2 w).mp hwB) hn⟩

end YesMetaZFC.SetTheory.Descriptive
