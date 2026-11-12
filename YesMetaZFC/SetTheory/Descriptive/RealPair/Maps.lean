import YesMetaZFC.SetTheory.Descriptive.Game.Closed
import YesMetaZFC.SetTheory.Descriptive.Topology.Continuous

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

/-! ## 通用集构造所用的实际连续图：逆重括号、对角与第一投影 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ai_exists_l (hZF : M.Models ZF) {ω J D q} (hJ : Npair_d I ω J) (hq : M.IsSetFunctionFromTo I q D ω) :
    ∃ p, M.IsSetFunctionFromTo I p D ω ∧ Ac_d I ω J D p q := by
  obtain ⟨v, w, hv, hw, hvw⟩ := rp_decode_l I hZF hJ hq
  obtain ⟨x, y, hx, hy, hxy⟩ := rp_decode_l I hZF hJ hv
  obtain ⟨u, hu, hyw⟩ := rp_exists_l I hZF hJ hy hw
  obtain ⟨p, hp, hxu⟩ := rp_exists_l I hZF hJ hx hu
  exact ⟨p, hp, x, y, w, u, v, hx, hy, hw, hu, hv, hyw, hxu, hxy, hvw⟩

theorem ai_sub_l {ω J D D' p q r s} (hJ : Npair_d I ω J)
    (h : Ac_d I ω J D p q) (k : Ac_d I ω J D' r s) (hq : M.MemberSubset q s) : M.MemberSubset p r := by
  obtain ⟨x, y, w, u, v, hx, hy, hw, hu, hv, hyw, hxu, hxy, hvw⟩ := h
  obtain ⟨x', y', w', u', v', _, _, _, _, _, hyw', hxu', hxy', hvw'⟩ := k
  obtain ⟨hvv, hww⟩ := (rp_subset_l I hJ hv hw hvw hvw').mp hq
  obtain ⟨hxx, hyy⟩ := (rp_subset_l I hJ hx hy hxy hxy').mp hvv
  exact (rp_subset_l I hJ hx hu hxu hxu').mpr ⟨hxx, (rp_subset_l I hJ hy hw hyw hyw').mpr ⟨hyy, hww⟩⟩

theorem ai_unique_l (hE : Extensional M) {ω J D p q r} (hJ : Npair_d I ω J)
    (h : Ac_d I ω J D p q) (k : Ac_d I ω J D r q) : p = r :=
  hE.eq_of_same_members p r (fun x => ⟨ai_sub_l I hJ h k (fun _ => id) x, ai_sub_l I hJ k h (fun _ => id) x⟩)

theorem ai_graph_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : ∃ f, Cont_d I A B f ∧
      ∀ q p, M.PairMember I q p f ↔ M.mem q B ∧ Ac_d I ω J ω p q := by
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J
  let φ : BinarySchema 2 := { body := ac_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 3) .newest (.bound 1) }
  have hp q p : φ.denote ρ q p ↔ Ac_d I ω J ω p q := ac_sat_l I hZF.1 _ _ _ _ _ _
  obtain ⟨f, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := B)
    (fun q hq => (ai_exists_l I hZF hJ ((hB.2 q).mp hq)).imp fun p h => (hp q p).mpr h.2)
    (fun _ _ _ _ h k => ai_unique_l I hZF.1 hJ ((hp _ _).mp h) ((hp _ _).mp k)) (by
      intro q p hq h
      obtain ⟨r, hr, hk⟩ := ai_exists_l I hZF hJ ((hB.2 q).mp hq)
      exact ai_unique_l I hZF.1 hJ hk ((hp q p).mp h) ▸ (hB.2 r).mpr hr)
  have ep q p := (ef q p).trans (and_congr_right fun _ => hp q p)
  refine ⟨f, ⟨hf, fun q p s hqp hs hsp => ?_⟩, ep⟩
  obtain ⟨n, hn, hs⟩ := (hA s).mp hs
  have hq := (hB.2 q).mp (hf.input_mem_of_pairMember hqp)
  have hp := (hB.2 p).mp (hf.output_mem_of_pairMember hqp)
  obtain ⟨t, ht, hr, _⟩ := ds_prefix_l I hZF hB.1 hq hn
  have htq := (ds_restrict_iff_l I ht hq.1).mp hr
  obtain ⟨u, hu, hut⟩ := ai_exists_l I hZF hJ ht
  have eu := ((ds_restrict_iff_l I hu hp.1).mpr (ai_sub_l I hJ hut ((ep q p).mp hqp).2 htq)).eq hZF.1
    ((ds_restrict_iff_l I hs hp.1).mpr hsp)
  exact ⟨t, (hA t).mpr ⟨n, hn, ht⟩, htq,
    fun q' p' hqp' htq' => eu ▸ ai_sub_l I hJ hut ((ep q' p').mp hqp').2 htq'⟩

theorem dg_graph_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : ∃ f, Cont_d I A B f ∧
      ∀ x y, M.PairMember I x y f ↔ M.mem x B ∧ Rp_d I J x x y := by
  let ρ : Env M 1 := ⟨fun _ => J, fun _ => J⟩
  let φ : BinarySchema 1 := { body := rp_m (𝒞 := 𝒞) (.bound 2) (.bound 1) (.bound 1) .newest }
  have hp x y : φ.denote ρ x y ↔ Rp_d I J x x y := rp_sat_l I _ _ _ _ _
  obtain ⟨f, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := B)
    (fun x hx => (rp_exists_l I hZF hJ ((hB.2 x).mp hx) ((hB.2 x).mp hx)).imp fun y h => (hp x y).mpr h.2)
    (fun _ _ _ _ h k => rp_unique_l I hZF.1 ((hp _ _).mp h) ((hp _ _).mp k))
    (fun x y hx h => (hB.2 y).mpr (rp_type_l I hZF hJ ((hB.2 x).mp hx) ((hB.2 x).mp hx) ((hp x y).mp h)))
  have ep x y := (ef x y).trans (and_congr_right fun _ => hp x y)
  refine ⟨f, ⟨hf, fun x y s hxy hs hsy => ?_⟩, ep⟩
  obtain ⟨n, hn, hs⟩ := (hA s).mp hs
  have hx := (hB.2 x).mp (hf.input_mem_of_pairMember hxy)
  have hy := (hB.2 y).mp (hf.output_mem_of_pairMember hxy)
  obtain ⟨t, ht, hr, _⟩ := ds_prefix_l I hZF hB.1 hx hn
  have htx := (ds_restrict_iff_l I ht hx.1).mp hr
  obtain ⟨u, hu, htu⟩ := rp_exists_l I hZF hJ ht ht
  have eu := ((ds_restrict_iff_l I hu hy.1).mpr ((rp_subset_l I hJ ht ht htu ((ep x y).mp hxy).2).mpr ⟨htx, htx⟩)).eq hZF.1
    ((ds_restrict_iff_l I hs hy.1).mpr hsy)
  exact ⟨t, (hA t).mpr ⟨n, hn, ht⟩, htx, fun x' y' hxy' htx' =>
    eu ▸ (rp_subset_l I hJ ht ht htu ((ep x' y').mp hxy').2).mpr ⟨htx', htx'⟩⟩

theorem fst_graph_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (hJ : Npair_d I ω J) : ∃ f, Cont_d I A B f ∧
      ∀ p x, M.PairMember I p x f ↔ M.mem p B ∧ M.mem x B ∧ ∃ y, M.mem y B ∧ Rp_d I J x y p := by
  let ρ : Env M 2 := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push J
  let φ : BinarySchema 2 := {
    body := .conj (.mem .newest (.bound 3))
      (Formula.existsMem (.bound 3) (rp_m (𝒞 := 𝒞) (.bound 3) (.bound 1) .newest (.bound 2))) }
  have hp p x : φ.denote ρ p x ↔ M.mem x B ∧ ∃ y, M.mem y B ∧ Rp_d I J x y p := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_existsMem_iff, rp_sat_l I]; rfl
  obtain ⟨f, hf, ef⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := B) (by
    intro p hpB
    obtain ⟨x, y, hx, hy, pair⟩ := rp_decode_l I hZF hJ ((hB.2 p).mp hpB)
    exact ⟨x, (hp p x).mpr ⟨(hB.2 x).mpr hx, y, (hB.2 y).mpr hy, pair⟩⟩) (by
    intro p _ x u hx hu
    obtain ⟨hx, y, hy, hp'⟩ := (hp p x).mp hx
    obtain ⟨hu, v, hv, hq'⟩ := (hp p u).mp hu
    exact (rp_injective_l I hZF.1 hJ ((hB.2 x).mp hx) ((hB.2 y).mp hy) ((hB.2 u).mp hu) ((hB.2 v).mp hv) hp' hq').1)
    (fun p x _ h => ((hp p x).mp h).1)
  have ep p x := (ef p x).trans (and_congr_right fun _ => hp p x)
  refine ⟨f, ⟨hf, fun p x s hpx hs hsx => ?_⟩, ep⟩
  obtain ⟨_, hx, y, hy, pair⟩ := (ep p x).mp hpx
  obtain ⟨n, hn, hs⟩ := (hA s).mp hs
  obtain ⟨t, ht, hr, _⟩ := ds_prefix_l I hZF hB.1 ((hB.2 y).mp hy) hn
  obtain ⟨r, hr, pr⟩ := rp_exists_l I hZF hJ hs ht
  refine ⟨r, (hA r).mpr ⟨n, hn, hr⟩, (rp_subset_l I hJ hs ht pr pair).mpr
    ⟨hsx, (ds_restrict_iff_l I ht ((hB.2 y).mp hy).1).mp ‹M.IsRestrictionOf I t y n›⟩, ?_⟩
  intro p' x' hpx' hrp'
  obtain ⟨_, _, y', _, pair'⟩ := (ep p' x').mp hpx'
  exact ((rp_subset_l I hJ hs ht pr pair').mp hrp').1

end YesMetaZFC.SetTheory.Descriptive
