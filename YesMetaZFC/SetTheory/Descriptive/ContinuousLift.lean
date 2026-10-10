import YesMetaZFC.SetTheory.Descriptive.MapIteration
import YesMetaZFC.SetTheory.Descriptive.Normal.Observation

/-! # 将连续映射提升到量词之下：f×id -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Lv_d (B J f p q : M.Domain) : Prop := ∃ x y z,
  M.mem x B ∧ M.mem y B ∧ M.PairMember I x z f ∧ Rp_d I J x y p ∧ Rp_d I J z y q
def lv_m {d} (B J f p q : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (.mem (.bound 2) B.weaken.weaken.weaken) (.conj (.mem (.bound 1) B.weaken.weaken.weaken) (.conj
  (Formula.orderedPairMem 𝒞 (.bound 2) .newest f.weaken.weaken.weaken) (.conj
  (rp_m (𝒞 := 𝒞) J.weaken.weaken.weaken (.bound 2) (.bound 1) p.weaken.weaken.weaken)
  (rp_m (𝒞 := 𝒞) J.weaken.weaken.weaken .newest (.bound 1) q.weaken.weaken.weaken)))))))
derive_free_closed lv_m
theorem lv_sat_l {d} (ρ : Env M d) (B J f p q : Term d) :
    Formula.satisfies ρ (lv_m (𝒞 := 𝒞) B J f p q) ↔
      Lv_d I (B.eval ρ) (J.eval ρ) (f.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [lv_m, Lv_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, rp_sat_l I, Definitional.Term.eval_weaken]; rfl

def Lift_d (B J f g : M.Domain) : Prop := M.IsSetFunctionFromTo I g B B ∧
  ∀ p q, M.PairMember I p q g ↔ Lv_d I B J f p q
def lift_m {d} (B J f g : Term d) : Formula 1 d := .conj (Formula.isFunctionFromTo 𝒞 g B B)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken)
    (lv_m (𝒞 := 𝒞) B.weaken.weaken J.weaken.weaken f.weaken.weaken (.bound 1) .newest))))
derive_free_closed lift_m
theorem lift_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B J f g : Term d) :
    Formula.satisfies ρ (lift_m (𝒞 := 𝒞) B J f g) ↔ Lift_d I (B.eval ρ) (J.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [lift_m, Lift_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    lv_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem lift_unique_l (hE : Extensional M) {B J f g h} (hg : Lift_d I B J f g) (hh : Lift_d I B J f h) : g = h :=
  hg.1.1.1.eq_of_pairMember_iff hE hh.1.1.1 (fun p q => (hg.2 p q).trans (hh.2 p q).symm)

theorem lift_exists_l (hZF : M.Models ZF) {ω B J f} (hB : Baire_d I ω B) (hJ : Npair_d I ω J)
    (hf : M.IsSetFunctionFromTo I f B B) : ∃ g, Lift_d I B J f g := by
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push J).push f
  let φ : BinarySchema 3 := { body := lv_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp p q : φ.denote ρ p q ↔ Lv_d I B J f p q := lv_sat_l I _ _ _ _ _ _
  obtain ⟨g, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := B)
    (by
      intro p hpB
      obtain ⟨x, y, hx, hy, hxy⟩ := rp_decode_l I hZF hJ ((hB.2 p).mp hpB)
      obtain ⟨z, hz, hxz⟩ := hf.2.2 x ((hB.2 x).mpr hx)
      obtain ⟨q, _, hzy⟩ := rp_exists_l I hZF hJ ((hB.2 z).mp hz) hy
      exact ⟨q, (hp p q).mpr ⟨x, y, z, (hB.2 x).mpr hx, (hB.2 y).mpr hy, hxz, hxy, hzy⟩⟩)
    (by
      intro p _ q r hq hr
      obtain ⟨x, y, z, hx, hy, hxz, hxy, hzy⟩ := (hp p q).mp hq
      obtain ⟨x', y', z', hx', hy', hxz', hxy', hzy'⟩ := (hp p r).mp hr
      obtain ⟨ex, ey⟩ := rp_injective_l I hZF.1 hJ ((hB.2 x').mp hx') ((hB.2 y').mp hy')
        ((hB.2 x).mp hx) ((hB.2 y).mp hy) hxy' hxy
      subst x' y'
      exact rp_unique_l I hZF.1 hzy (hf.1.2 x z' z hxz' hxz ▸ hzy'))
    (by
      intro p q _ hq
      obtain ⟨_, y, z, _, hy, hxz, _, hzy⟩ := (hp p q).mp hq
      exact (hB.2 q).mpr (rp_type_l I hZF hJ ((hB.2 z).mp (hf.output_mem_of_pairMember hxz)) ((hB.2 y).mp hy) hzy))
  refine ⟨g, hg, fun p q => ((eg p q).trans (and_congr_right fun _ => hp p q)).trans ⟨And.right, fun h => ?_⟩⟩
  obtain ⟨x, y, z, hx, hy, hxz, hxy, hzy⟩ := h
  exact ⟨(hB.2 p).mpr (rp_type_l I hZF hJ ((hB.2 x).mp hx) ((hB.2 y).mp hy) hxy), x, y, z, hx, hy, hxz, hxy, hzy⟩

theorem lift_cont_l (hZF : M.Models ZF) {ω A B J f g} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hf : Cont_d I A B f) (hg : Lift_d I B J f g) : Cont_d I A B g := by
  refine ⟨hg.1, fun p q s hpq hs hsq => ?_⟩
  obtain ⟨x, y, z, hx, hy, hxz, hxy, hzy⟩ := (hg.2 p q).mp hpq
  obtain ⟨n, hn, hsf⟩ := (hA s).mp hs
  obtain ⟨u, v, hu, hv, huv⟩ := rp_decode_l I hZF hJ hsf
  obtain ⟨huz, hvy⟩ := (rp_subset_l I hJ hu hv huv hzy).mp hsq
  obtain ⟨t, ht, htx, cov⟩ := hf.2 x z u hxz ((hA u).mpr ⟨n, hn, hu⟩) huz
  have obs := no_sub_l I hZF hB.1 hA ((hB.2 x).mp hx) ((hB.2 y).mp hy) ht htx
  have obs' : No_d I ω x y (fun _ y' => M.MemberSubset v y') := by
    obtain ⟨m, a, b, hm, ha, hb, h⟩ := no_sub_l I hZF hB.1 hA ((hB.2 y).mp hy) ((hB.2 x).mp hx) ((hA v).mpr ⟨n, hn, hv⟩) hvy
    exact ⟨m, b, a, hm, hb, ha, fun x' y' hx' hy' => h y' x' hy' hx'⟩
  obtain ⟨m, a, b, hm, ha, hb, near⟩ := no_and_l I hZF hB.1 ((hB.2 x).mp hx) ((hB.2 y).mp hy) obs obs'
  have haf := ha.isSetFunctionFromTo ((hB.2 x).mp hx) (hB.1.transitive hZF m hm)
  have hbf := hb.isSetFunctionFromTo ((hB.2 y).mp hy) (hB.1.transitive hZF m hm)
  obtain ⟨r, hr, hab⟩ := rp_exists_l I hZF hJ haf hbf
  refine ⟨r, (hA r).mpr ⟨m, hm, hr⟩, (rp_subset_l I hJ haf hbf hab hxy).mpr
    ⟨(ds_restrict_iff_l I haf ((hB.2 x).mp hx).1).mp ha, (ds_restrict_iff_l I hbf ((hB.2 y).mp hy).1).mp hb⟩, ?_⟩
  intro p' q' hpq' hrp
  obtain ⟨x', y', z', _, _, hxz', hxy', hzy'⟩ := (hg.2 p' q').mp hpq'
  obtain ⟨hax, hby⟩ := (rp_subset_l I hJ haf hbf hab hxy').mp hrp
  have h := near x' y' hax hby
  exact (rp_subset_l I hJ hu hv huv hzy').mpr ⟨cov x' z' hxz' h.1, h.2⟩

/-- 连续函数的量词提升与“补后投影”交换。 -/
theorem lift_step_l (hZF : M.Models ZF) {ω B J f g K L U V} (hB : Baire_d I ω B)
    (hJ : Npair_d I ω J) (hf : M.IsSetFunctionFromTo I f B B) (hg : Lift_d I B J f g)
    (hKL : Ip_d I B g K L) (hU : Pstep_d I B J K U) (hV : Pstep_d I B J L V) : Ip_d I B f U V := by
  obtain ⟨C, hc, hu⟩ := hU
  obtain ⟨D, hd, hv⟩ := hV
  intro x
  constructor
  · intro hx
    obtain ⟨hxB, y, p, hy, hp, hxy, hpD⟩ := (hv x).mp hx
    obtain ⟨z, hz, hxz⟩ := hf.2.2 x hxB
    obtain ⟨q, hq, hzy⟩ := rp_exists_l I hZF hJ ((hB.2 z).mp hz) ((hB.2 y).mp hy)
    have hpq := (hg.2 p q).mpr ⟨x, y, z, hxB, hy, hxz, hxy, hzy⟩
    have hqC := (hc q).mpr ⟨(hB.2 q).mpr hq, fun hk => ((hd p).mp hpD).2 ((ip_mem_l I hg.1 hKL hpq).mpr hk)⟩
    exact ⟨hxB, z, hxz, (hu z).mpr ⟨hz, y, q, hy, (hB.2 q).mpr hq, hzy, hqC⟩⟩
  · rintro ⟨hxB, z, hxz, hzU⟩
    obtain ⟨_, y, q, hy, _, hzy, hqC⟩ := (hu z).mp hzU
    obtain ⟨p, hp, hxy⟩ := rp_exists_l I hZF hJ ((hB.2 x).mp hxB) ((hB.2 y).mp hy)
    have hpq := (hg.2 p q).mpr ⟨x, y, z, hxB, hy, hxz, hxy, hzy⟩
    exact (hv x).mpr ⟨hxB, y, p, hy, (hB.2 p).mpr hp, hxy,
      (hd p).mpr ⟨(hB.2 p).mpr hp, fun hl => ((hc q).mp hqC).2 ((ip_mem_l I hg.1 hKL hpq).mp hl)⟩⟩

end YesMetaZFC.SetTheory.Descriptive
