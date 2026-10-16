import YesMetaZFC.Model.SetTheory.Internal.PointwiseValue
import YesMetaZFC.Model.SetTheory.Internal.Support

/-! # 逐点满足的赋值无关性与逻辑方程

代表函数在给定点的值唯一，故任意两份逐点赋值在整个支撑上相同。
随后直接读取原程序的 Tarski 方程；本层全部保持 ZF 强度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Pe_repr_d.update_l {b D X R a i g a'} (h : Pe_repr_d I b D X R a)
    (hg : Rf_fun_d I X R D g) (ha : Senv_update_d I a i g a') : Pe_repr_d I b D X R a' := by
  intro j f hj hf
  rcases (ha.2 j f).mp hf with ⟨_, rfl⟩ | ⟨_, hf⟩
  · exact hg
  · exact h j f hj hf

theorem Pe_assign_d.value_l {b D X R a f p i g x} (h : Pe_assign_d I b D X R a f p)
    (ext : Rf_ext_d I X R) (ha : M.IsSetFunction I a) (hf : M.IsSetFunction I f) (hi : M.mem i b) (hg : M.PairMember I i g a) :
    M.PairMember I i x f ↔ Rf_val_d I X R p x g := by
  obtain ⟨g', y, hg', hG, hy, hiy⟩ := h i hi
  have eq := ha.2 i g' g hg' hg
  subst g'
  exact ⟨fun hx => (hf.2 i x y hx hiy).symm ▸ hy,
    fun hx => (hG.unique_l I ext hx hy).symm ▸ hiy⟩

theorem Pe_assign_d.agree_right_l {b D X R a f g p} (h : Pe_assign_d I b D X R a f p)
    (k : Pe_assign_d I b D X R a g p) (ext : Rf_ext_d I X R) (ha : M.IsSetFunction I a)
    (hf : M.IsSetFunction I f) (hg : M.IsSetFunction I g) : Senv_agree_d I b f g := by
  intro i x hi
  obtain ⟨s, _, hs, _⟩ := h i hi
  exact (h.value_l I ext ha hf hi hs).trans (k.value_l I ext ha hg hi hs).symm

theorem pe_sat_value_l (hZF : M.Models ZF) {ω b D X R E F n r a p f}
    (ext : Rf_ext_d I X R) (hF : Sfm_d I ω n F) (hB : Sbound_d I F b) (hr : M.mem r n) (hE : M.IsFunctionSpace I E ω X)
    (ha : M.mem a E) (hf : M.mem f E) (he : Pe_assign_d I b D X R a f p) :
    Pe_sat_d I b D X R E F n r a p ↔ Ssat_d I X R E F n r f := by
  refine ⟨fun ⟨g, hg, hk, hs⟩ => ?_, fun hs => ⟨f, hf, he, hs⟩⟩
  exact (ssat_agree_l I hZF hF hB hE hr hg hf
    (hk.agree_right_l I he ext ((hE a).mp ha).1 ((hE g).mp hg).1 ((hE f).mp hf).1)).mp hs

theorem pe_sat_full_l (hZF : M.Models ZF) {ω b D X R E F n r a p}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F)
    (hB : Sbound_d I F b) (hb : M.MemberSubset b ω) (hr : M.mem r n)
    (ha : M.mem a E) (hh : Pe_repr_d I ω D X R a) (hp : M.mem p X) (hd : M.PairMember I p D R) :
    Pe_sat_d I b D X R E F n r a p ↔ Pe_sat_d I ω D X R E F n r a p := by
  obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF ext hE ha (fun _ h => h) hp hd hh
  exact ⟨fun ht => ⟨f, hf, he, (pe_sat_value_l I hZF ext hF hB hr hE ha hf (fun i hi => he i (hb i hi))).mp ht⟩,
    fun ⟨g, hg, hk, ht⟩ => ⟨g, hg, fun i hi => hk i (hb i hi), ht⟩⟩

theorem pe_sat_atom_l (hZF : M.Models ZF) {ω b D X R E F n H r z i j a p g l x y}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F)
    (hH : Seval_d I X R E F n H) (hB : Sbound_d I F b) (hb : M.MemberSubset b ω)
    (ha : M.mem a E) (hh : Pe_repr_d I b D X R a) (hp : M.mem p X) (hd : M.PairMember I p D R)
    (hc : M.PairMember I r z F) (e : Bool) (hs : Sop_d I (if e then 1 else 0) z i j)
    (hig : M.PairMember I i g a) (hjl : M.PairMember I j l a) (hx : Rf_val_d I X R p x g) (hy : Rf_val_d I X R p y l) :
    Pe_sat_d I b D X R E F n r a p ↔ if e then x = y else M.PairMember I x y R := by
  obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF ext hE ha hb hp hd hh
  have hix := (he.value_l I ext ((hE a).mp ha).1 ((hE f).mp hf).1 (hB.operands_l I hc hs).1 hig).mpr hx
  have hjy := (he.value_l I ext ((hE a).mp ha).1 ((hE f).mp hf).1 (hB.operands_l I hc hs).2 hjl).mpr hy
  apply (pe_sat_value_l I hZF ext hF hB ((hF.2.1.2.2 r).mpr ⟨z, hc⟩) hE ha hf he).trans
  cases e
  · exact ssat_rel_l I hZF hF hH hc hs hE hf hix hjy
  · exact ssat_eq_l I hZF hF hH hc hs hE hf hix hjy

theorem pe_sat_nor_l (hZF : M.Models ZF) {ω b D X R E F n H r z i j a p}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F)
    (hH : Seval_d I X R E F n H) (hB : Sbound_d I F b) (hb : M.MemberSubset b ω)
    (ha : M.mem a E) (hh : Pe_repr_d I b D X R a) (hp : M.mem p X) (hd : M.PairMember I p D R)
    (hc : M.PairMember I r z F) (hs : Sop_d I 2 z i j) (hi : M.mem i n) (hj : M.mem j n) :
    Pe_sat_d I b D X R E F n r a p ↔ ¬ (Pe_sat_d I b D X R E F n i a p ∨ Pe_sat_d I b D X R E F n j a p) := by
  obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF ext hE ha hb hp hd hh
  exact (pe_sat_value_l I hZF ext hF hB ((hF.2.1.2.2 r).mpr ⟨z, hc⟩) hE ha hf he).trans
    ((ssat_nor_l I hZF hF hH hc hs hf).trans (not_congr (or_congr
      (pe_sat_value_l I hZF ext hF hB hi hE ha hf he).symm (pe_sat_value_l I hZF ext hF hB hj hE ha hf he).symm)))

theorem pe_sat_ex_intro_l (hZF : M.Models ZF) {ω b D X R E F n H r z i j a a' g p}
    (ext : Rf_ext_d I X R) (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F)
    (hH : Seval_d I X R E F n H) (hB : Sbound_d I F b) (hb : M.MemberSubset b ω)
    (ha : M.mem a E) (hh : Pe_repr_d I b D X R a) (hp : M.mem p X) (hd : M.PairMember I p D R)
    (hc : M.PairMember I r z F) (hs : Sop_d I 3 z i j) (hi : M.mem i ω) (hj : M.mem j n)
    (hg : Rf_fun_d I X R D g) (hu : Senv_update_d I a i g a') (ht : Pe_sat_d I b D X R E F n j a' p) :
    Pe_sat_d I b D X R E F n r a p := by
  obtain ⟨f, hf, he⟩ := pe_value_exists_l I hZF ext hE ha hb hp hd hh
  obtain ⟨x, hpx⟩ := hg.value_l I ext hp hd
  have hx := (hpx.bounds_l I).2.1
  obtain ⟨f', hff, hf'⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
  have body := (pe_sat_value_l I hZF ext hF hB hj hE
    ((hE a').mpr (hu.function_l I ((hE a).mp ha) hi (hg.mem_l I))) ((hE f').mpr hf') (he.update_l I hg hpx hu hff)).mp ht
  exact ⟨f, hf, he, (ssat_exists_l I hZF hF hH hc hs hf).mpr ⟨x, f', hx, hff, body⟩⟩

end YesMetaZFC.SetTheory.Internal
