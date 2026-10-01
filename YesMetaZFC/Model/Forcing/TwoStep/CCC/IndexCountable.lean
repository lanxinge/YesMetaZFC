import YesMetaZFC.Model.Forcing.TwoStep.CCC.Index
import YesMetaZFC.Model.Forcing.TwoStep.Generic.Projection
import YesMetaZFC.Model.Forcing.CCC.Basic

/-! # 二步反链在第一扩张中的可数索引集

第二坐标图是从被接受索引集到第二偏序反链的实际单射。第二坐标的共同加强
提升为二步共同加强，所以原反链排除重复索引及相容的不同像。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S D t g : M.Domain}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) {U} (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U

theorem step_index_countable_l (h : Two_step_d M B R z b A T W C S) (L : Cond_order_d M C S C)
    (hd : Antichain_d M C S C D) (htg : Step_index_d M B b D t g)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ x c, Check_d M b x c → Qval_d M B R z U c (e x))
    {Q V I G ν : (E).Domain} (hQ : Qval_d M B R z U A Q) (hV : Qval_d M B R z U T V)
    (ht : Qval_d M B R z U t I) (hg : Qval_d M B R z U g G) (hp : ∀ v, v ∈ Q → Entry_d E v v V)
    (hc : Ccc_d E (kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)) ν Q V Q) :
    (E).CardinalLessOrEqual (kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)) I ν := by
  have hE := preserves_zf_l O hZF hU
  let J := kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hE))
  have hsn {x p s} (hx : M.mem x D) (hxp : KPair_d M x p s) : Name_d M B s :=
    ⟨W, ((two_step_mem_l h hxp).mp (hd.1 x hx).1).1, h.closed⟩
  have member y : y ∈ I ↔ ∃ x p s, M.mem x D ∧ KPair_d M x p s ∧ U p ∧ e x = y := by
    constructor
    · intro hy
      obtain ⟨a, p, hap, hp, hay⟩ := (qval_mem_l O hZF hU ht).mp hy
      obtain ⟨x, s, hx, hxp, hxa⟩ := (htg.1 a p).mp hap
      exact ⟨x, p, s, hx, hxp, hp, qval_unique_l (he x a hxa) hay⟩
    · rintro ⟨x, p, s, hx, hxp, hp, rfl⟩
      obtain ⟨a, hxa, _, _⟩ := zf_check_l M hZF h.base x
      exact (qval_mem_l O hZF hU ht).mpr ⟨a, p, (htg.1 a p).mpr ⟨x, s, hx, hxp, hxa⟩, hp, he x a hxa⟩
  have graph y : y ∈ G ↔ ∃ x p s v, M.mem x D ∧ KPair_d M x p s ∧ U p ∧
      Qval_d M B R z U s v ∧ KPair_d E y (e x) v := by
    constructor
    · intro hy
      obtain ⟨a, p, hap, hp, hay⟩ := (qval_mem_l O hZF hU hg).mp hy
      obtain ⟨x, s, c, hx, hxp, hxc, hcs⟩ := (htg.2 a p).mp hap
      obtain ⟨v, hsv⟩ := name_value_l (R := R) (z := z) (U := U) (hsn hx hxp)
      exact ⟨x, p, s, v, hx, hxp, hp, hsv, nkpair_val_l O hZF hU hcs (he x c hxc) hsv hay⟩
    · rintro ⟨x, p, s, v, hx, hxp, hp, hsv, hy⟩
      obtain ⟨c, hxc, hcn, _⟩ := zf_check_l M hZF h.base x
      obtain ⟨a, hcs⟩ := nkpair_l M hZF B c s
      obtain ⟨y', hay⟩ := name_value_l (R := R) (z := z) (U := U) (nkpair_name_l M hZF hcn (hsn hx hxp) hcs)
      have heq := kpair_unique_l E hE.1 (nkpair_val_l O hZF hU hcs (he x c hxc) hsv hay) hy
      exact (qval_mem_l O hZF hU hg).mpr ⟨a, p, (htg.2 a p).mpr ⟨x, s, c, hx, hxp, hxc, hcs⟩, hp, heq ▸ hay⟩
  have edge a v : Entry_d E a v G ↔ ∃ x p s, M.mem x D ∧ KPair_d M x p s ∧ U p ∧ e x = a ∧ Qval_d M B R z U s v := by
    constructor
    · rintro ⟨y, hy, hyG⟩
      obtain ⟨x, p, s, w, hx, hxp, hp, hsw, hy'⟩ := (graph y).mp hyG
      obtain ⟨ha, hv⟩ := kpair_injective_l E hy' hy
      exact ⟨x, p, s, hx, hxp, hp, ha, hv ▸ hsw⟩
    · rintro ⟨x, p, s, hx, hxp, hp, rfl, hsv⟩
      obtain ⟨y, hy⟩ := J.total (e x) v
      exact ⟨y, hy, (graph y).mpr ⟨x, p, s, v, hx, hxp, hp, hsv, hy⟩⟩
  have value {x p s v} (hx : M.mem x D) (hxp : KPair_d M x p s) (hp : U p) (hsv : Qval_d M B R z U s v) : v ∈ Q :=
    (qval_mem_forcing_l O hZF hU hsv hQ).mp ⟨p, hp, ((two_step_mem_l h hxp).mp (hd.1 x hx).1).2.2⟩
  have old_eq {x p s y q a v w} (hx : M.mem x D) (hy : M.mem y D)
      (hxp : KPair_d M x p s) (hyq : KPair_d M y q a) (hp : U p) (hq : U q)
      (hsv : Qval_d M B R z U s v) (haw : Qval_d M B R z U a w)
      (hvw : Cmp_d E Q V Q v w) : x = y := by
    obtain ⟨r, hrv, hrw⟩ := hvw
    obtain ⟨j, _, _, _, _, _, hjx, hjy⟩ := two_step_common_l O hZF hU h L hQ hV
      (hd.1 x hx).1 (hd.1 y hy).1 hxp hyq hp hq hsv haw hrv.1 hrv.2.2 hrw
    exact hd.2 x y hx hy ⟨j, hjx, hjy.2.2⟩
  have hF : (E).IsSetFunctionFromTo J G I Q := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro y hy
      obtain ⟨x, _, _, v, _, _, _, _, hy⟩ := (graph y).mp hy
      exact ⟨e x, v, hy⟩
    · intro x v w hxv hxw
      obtain ⟨a, p, s, ha, hap, _, hax, hsv⟩ := (edge x v).mp hxv
      obtain ⟨b, q, t, _, hbq, _, hbx, htw⟩ := (edge x w).mp hxw
      have heq := hi (hax.trans hbx.symm)
      subst b
      have heq := (kpair_injective_l M hap hbq).2
      subst t
      exact qval_unique_l hsv htw
    · intro x
      constructor
      · intro hx
        obtain ⟨a, p, s, ha, hap, hp, rfl⟩ := (member x).mp hx
        obtain ⟨v, hsv⟩ := name_value_l (R := R) (z := z) (U := U) (hsn ha hap)
        exact ⟨v, (edge _ _).mpr ⟨a, p, s, ha, hap, hp, rfl, hsv⟩⟩
      · rintro ⟨v, hxv⟩
        obtain ⟨a, p, s, ha, hap, hp, hax, _⟩ := (edge x v).mp hxv
        exact (member x).mpr ⟨a, p, s, ha, hap, hp, hax⟩
    · intro x hx
      obtain ⟨a, p, s, ha, hap, hp, rfl⟩ := (member x).mp hx
      obtain ⟨v, hsv⟩ := name_value_l (R := R) (z := z) (U := U) (hsn ha hap)
      exact ⟨v, value ha hap hp hsv, (edge _ _).mpr ⟨a, p, s, ha, hap, hp, rfl, hsv⟩⟩
  obtain ⟨K, hK⟩ := ZF.exists_range_of_setFunction hE J hF.1 hF.2.1
  have hInj : (E).IsSetInjectionFromTo J G I K := by
    refine ⟨⟨hF.1, hF.2.1, fun x hx => ?_⟩, fun x y v hx hy => ?_⟩
    · obtain ⟨v, _, hxv⟩ := hF.2.2 x hx
      exact ⟨v, (hK v).mpr ⟨x, hxv⟩, hxv⟩
    · obtain ⟨a, p, s, ha, hap, hpU, hax, hsv⟩ := (edge x v).mp hx
      obtain ⟨b, q, t, hb, hbq, hqU, hby, htv⟩ := (edge y v).mp hy
      have hvQ := value ha hap hpU hsv
      have heq := old_eq ha hb hap hbq hpU hqU hsv htv
        ⟨v, ⟨hvQ, fun he => KP.mem_irrefl_d (ZF.modelsKP hE) Q (he ▸ hvQ), hp v hvQ⟩, hp v hvQ⟩
      exact hax.symm.trans ((congrArg e heq).trans hby)
  have ha : Antichain_d E Q V Q K := by
    refine ⟨fun v hv => ?_, fun v w hv hw hvw => ?_⟩
    · obtain ⟨x, hx⟩ := (hK v).mp hv
      have hvQ := hF.output_mem_of_pairMember hx
      exact ⟨hvQ, fun he => KP.mem_irrefl_d (ZF.modelsKP hE) Q (he ▸ hvQ)⟩
    · obtain ⟨x, hx⟩ := (hK v).mp hv
      obtain ⟨y, hy⟩ := (hK w).mp hw
      obtain ⟨a, p, s, ha, hap, hpU, _, hsv⟩ := (edge x v).mp hx
      obtain ⟨b, q, t, hb, hbq, hqU, _, htw⟩ := (edge y w).mp hy
      have heq := old_eq ha hb hap hbq hpU hqU hsv htw hvw
      subst b
      have heq := (kpair_injective_l M hap hbq).2
      subst t
      exact qval_unique_l hsv htw
  obtain ⟨f, hf⟩ := hc K ha
  exact ZF.exists_compositionInjection hE J hInj hf

end YesMetaZFC.Model.Forcing.Internal
