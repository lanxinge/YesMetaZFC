import YesMetaZFC.SetTheory.Descriptive.RealPair.Maps

/-! # 实数参数截面及其与补、投影的交换 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sect_d (B J U p K : M.Domain) : Prop := M.mem p B ∧ ∀ x q,
  M.mem x B → Rp_d I J p x q → (M.mem q U ↔ M.mem x K)
def sect_m {d} (B J U p K : Term d) : Formula 1 d := .conj (.mem p B) (.forallE (.forallE
  (.imp (.mem (.bound 1) B.weaken.weaken) (.imp (rp_m (𝒞 := 𝒞) J.weaken.weaken p.weaken.weaken (.bound 1) .newest)
    (.iff (.mem .newest U.weaken.weaken) (.mem (.bound 1) K.weaken.weaken))))))
derive_free_closed sect_m
theorem sect_sat_l {d} (ρ : Env M d) (B J U p K : Term d) :
    Formula.satisfies ρ (sect_m (𝒞 := 𝒞) B J U p K) ↔
      Sect_d I (B.eval ρ) (J.eval ρ) (U.eval ρ) (p.eval ρ) (K.eval ρ) := by
  simp only [sect_m, Sect_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, rp_sat_l I, Formula.satisfies_iff_iff, Definitional.Term.eval_weaken]; rfl

theorem sect_compl_l (hZF : M.Models ZF) {ω B J U V K L p} (hB : Baire_d I ω B)
    (hJ : Npair_d I ω J) (h : Sect_d I B J U p K) (hu : Cm_d B U V) (hk : Cm_d B K L) : Sect_d I B J V p L := by
  refine ⟨h.1, fun x q hx hp => ?_⟩
  have hq := (hB.2 q).mpr (rp_type_l I hZF hJ ((hB.2 p).mp h.1) ((hB.2 x).mp hx) hp)
  exact (hu q).trans ((and_congr (iff_of_true hq hx) (not_congr (h.2 x q hx hp))).trans (hk x).symm)

theorem sect_project_l (hZF : M.Models ZF) {ω B J f R D U K L p} (hB : Baire_d I ω B)
    (hJ : Npair_d I ω J) (ef : ∀ q r, M.PairMember I q r f ↔ M.mem q B ∧ Ac_d I ω J ω r q)
    (hD : Ip_d I B f R D) (hU : Pr_d I B J D U) (h : Sect_d I B J R p K) (hL : Pr_d I B J K L) :
    Sect_d I B J U p L := by
  refine ⟨h.1, fun x z hx hp => ?_⟩
  have hpf := (hB.2 p).mp h.1
  have hxf := (hB.2 x).mp hx
  have hzf := rp_type_l I hZF hJ hpf hxf hp
  have hz := (hB.2 z).mpr hzf
  constructor
  · intro hzU
    obtain ⟨_, y, q, hy, hq, hzy, hqD⟩ := (hU z).mp hzU
    obtain ⟨_, r, hqr, hrR⟩ := (hD q).mp hqD
    obtain ⟨_, p', x', y', u, v, hpf', hxf', hyf', huf, hvf, hxy, hpu, hpx, hvy⟩ := (ef q r).mp hqr
    obtain ⟨ev, ey⟩ := rp_injective_l I hZF.1 hJ hvf hyf' hzf ((hB.2 y).mp hy) hvy hzy
    subst v y'
    obtain ⟨ep, ex⟩ := rp_injective_l I hZF.1 hJ hpf' hxf' hpf hxf hpx hp
    subst p' x'
    have hu := (hB.2 u).mpr huf
    exact (hL x).mpr ⟨hx, y, u, hy, hu, hxy, (h.2 u r hu hpu).mp hrR⟩
  · intro hxL
    obtain ⟨_, y, u, hy, hu, hxy, huK⟩ := (hL x).mp hxL
    have hyf := (hB.2 y).mp hy
    have huf := (hB.2 u).mp hu
    obtain ⟨r, _, hpu⟩ := rp_exists_l I hZF hJ hpf huf
    obtain ⟨q, hqf, hzy⟩ := rp_exists_l I hZF hJ hzf hyf
    have hq := (hB.2 q).mpr hqf
    have hqr := (ef q r).mpr ⟨hq, p, x, y, u, z, hpf, hxf, hyf, huf, hzf, hxy, hpu, hp, hzy⟩
    exact (hU z).mpr ⟨hz, y, q, hy, hq, hzy, (hD q).mpr ⟨hq, r, hqr, (h.2 u r hu hpu).mpr huK⟩⟩

end YesMetaZFC.SetTheory.Descriptive
