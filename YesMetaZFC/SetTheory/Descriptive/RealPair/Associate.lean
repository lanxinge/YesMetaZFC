import YesMetaZFC.SetTheory.Descriptive.Closed

/-! # 实数配对的重括号

(x,(y,w)) 与 ((x,y),w) 的转换逐坐标进行，并保持前缀包含。
因此闭关系的重括号仍闭，可把两个 Baire 见证合并成一个。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ac_d (ω J D p q : M.Domain) : Prop := ∃ x y w u v,
  M.IsSetFunctionFromTo I x D ω ∧ M.IsSetFunctionFromTo I y D ω ∧ M.IsSetFunctionFromTo I w D ω ∧
  M.IsSetFunctionFromTo I u D ω ∧ M.IsSetFunctionFromTo I v D ω ∧
  Rp_d I J y w u ∧ Rp_d I J x u p ∧ Rp_d I J x y v ∧ Rp_d I J v w q
def ac_m {d} (ω J D p q : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (Formula.isFunctionFromTo 𝒞 (.bound 4) D.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken) (.conj
  (Formula.isFunctionFromTo 𝒞 (.bound 3) D.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken) (.conj
  (Formula.isFunctionFromTo 𝒞 (.bound 2) D.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken) (.conj
  (Formula.isFunctionFromTo 𝒞 (.bound 1) D.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken) (.conj
  (Formula.isFunctionFromTo 𝒞 .newest D.weaken.weaken.weaken.weaken.weaken ω.weaken.weaken.weaken.weaken.weaken) (.conj
  (rp_m (𝒞 := 𝒞) J.weaken.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1)) (.conj
  (rp_m (𝒞 := 𝒞) J.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 1) p.weaken.weaken.weaken.weaken.weaken) (.conj
  (rp_m (𝒞 := 𝒞) J.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) .newest)
  (rp_m (𝒞 := 𝒞) J.weaken.weaken.weaken.weaken.weaken .newest (.bound 2) q.weaken.weaken.weaken.weaken.weaken)))))))))))))
derive_free_closed ac_m
theorem ac_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J D p q : Term d) :
    Formula.satisfies ρ (ac_m (𝒞 := 𝒞) ω J D p q) ↔
      Ac_d I (ω.eval ρ) (J.eval ρ) (D.eval ρ) (p.eval ρ) (q.eval ρ) := by
  simp only [ac_m, Ac_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, rp_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem ac_exists_l (hZF : M.Models ZF) {ω J D p} (hJ : Npair_d I ω J) (hp : M.IsSetFunctionFromTo I p D ω) :
    ∃ q, M.IsSetFunctionFromTo I q D ω ∧ Ac_d I ω J D p q := by
  obtain ⟨x, u, hx, hu, hxu⟩ := rp_decode_l I hZF hJ hp
  obtain ⟨y, w, hy, hw, hyw⟩ := rp_decode_l I hZF hJ hu
  obtain ⟨v, hv, hxy⟩ := rp_exists_l I hZF hJ hx hy
  obtain ⟨q, hq, hvw⟩ := rp_exists_l I hZF hJ hv hw
  exact ⟨q, hq, x, y, w, u, v, hx, hy, hw, hu, hv, hyw, hxu, hxy, hvw⟩

theorem ac_unique_l (hE : Extensional M) {ω J D p q r} (hJ : Npair_d I ω J)
    (h : Ac_d I ω J D p q) (k : Ac_d I ω J D p r) : q = r := by
  obtain ⟨x, y, w, u, v, hx, hy, hw, hu, _, hyw, hxu, hxy, hvw⟩ := h
  obtain ⟨x', y', w', u', v', hx', hy', hw', hu', _, hyw', hxu', hxy', hvw'⟩ := k
  obtain ⟨ex, eu⟩ := rp_injective_l I hE hJ hx hu hx' hu' hxu hxu'
  subst x' u'
  obtain ⟨ey, ew⟩ := rp_injective_l I hE hJ hy hw hy' hw' hyw hyw'
  subst y' w'
  have ev := rp_unique_l I hE hxy hxy'
  subst v'
  exact rp_unique_l I hE hvw hvw'

theorem ac_sub_l {ω J D D' p q r s} (hJ : Npair_d I ω J)
    (h : Ac_d I ω J D p q) (k : Ac_d I ω J D' r s) (hp : M.MemberSubset p r) : M.MemberSubset q s := by
  obtain ⟨x, y, w, u, v, hx, hy, hw, hu, hv, hyw, hxu, hxy, hvw⟩ := h
  obtain ⟨x', y', w', u', v', _, _, _, _, _, hyw', hxu', hxy', hvw'⟩ := k
  obtain ⟨hxx, huu⟩ := (rp_subset_l I hJ hx hu hxu hxu').mp hp
  obtain ⟨hyy, hww⟩ := (rp_subset_l I hJ hy hw hyw hyw').mp huu
  exact (rp_subset_l I hJ hv hw hvw hvw').mpr ⟨(rp_subset_l I hJ hx hy hxy hxy').mpr ⟨hxx, hyy⟩, hww⟩

theorem ac_closed_l (hZF : M.Models ZF) {ω A B J C} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) (hC : Cl_d A B C) : ∃ D,
      Cl_d A B D ∧ ∀ p, M.mem p D ↔ M.mem p B ∧ ∃ q, M.mem q B ∧ Ac_d I ω J ω p q ∧ M.mem q C := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push B).push J).push C
  let φ : UnarySchema 4 := { body := Formula.existsMem (.bound 3) (.conj
    (ac_m (𝒞 := 𝒞) (.bound 5) (.bound 3) (.bound 5) (.bound 1) .newest) (.mem .newest (.bound 2))) }
  obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hD p : M.mem p D ↔ M.mem p B ∧ ∃ q, M.mem q B ∧ Ac_d I ω J ω p q ∧ M.mem q C := by
    simpa only [φ, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      ac_sat_l I hZF.1, Formula.satisfies_mem_iff] using! hD' p
  obtain ⟨_, U, hU, ho⟩ := hC
  obtain ⟨V, hV⟩ := cm_exists_l (ZF.modelsKP hZF) B D
  refine ⟨D, ⟨fun p hp => ((hD p).mp hp).1, V, hV, ⟨fun p hp => ((hV p).mp hp).1, ?_⟩⟩, hD⟩
  intro p hp
  obtain ⟨hpB, hpD⟩ := (hV p).mp hp
  have hpf := (hB.2 p).mp hpB
  obtain ⟨q, hqf, hq⟩ := ac_exists_l I hZF hJ hpf
  have hqB := (hB.2 q).mpr hqf
  obtain ⟨r, hrA, hrq, near⟩ := ho.2 q ((hU q).mpr ⟨hqB, fun h => hpD ((hD p).mpr ⟨hpB, q, hqB, hq, h⟩)⟩)
  obtain ⟨n, hn, hrf⟩ := (hA r).mp hrA
  obtain ⟨s, hsf, hs, _⟩ := ds_prefix_l I hZF hB.1 hpf hn
  have hsp := (ds_restrict_iff_l I hsf hpf.1).mp hs
  obtain ⟨t, htf, hst⟩ := ac_exists_l I hZF hJ hsf
  have etr := ((ds_restrict_iff_l I htf hqf.1).mpr (ac_sub_l I hJ hst hq hsp)).eq hZF.1
    ((ds_restrict_iff_l I hrf hqf.1).mpr hrq)
  refine ⟨s, (hA s).mpr ⟨n, hn, hsf⟩, hsp, fun u hu hsu => (hV u).mpr ⟨hu, fun hud => ?_⟩⟩
  obtain ⟨_, v, hvB, huv, hvC⟩ := (hD u).mp hud
  exact ((hU v).mp (near v hvB (etr ▸ ac_sub_l I hJ hst huv hsu))).2 hvC

end YesMetaZFC.SetTheory.Descriptive
