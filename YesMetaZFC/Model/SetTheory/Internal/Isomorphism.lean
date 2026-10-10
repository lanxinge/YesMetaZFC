import YesMetaZFC.Model.SetTheory.Internal.PredicateEmbedding
import YesMetaZFC.Model.SetTheory.Internal.Induction
import YesMetaZFC.Model.SetTheory.Internal.TruthRules
import YesMetaZFC.Model.SetTheory.Internal.Elementary

/-! # 内部同构保持全部公式码的真值

对实际程序行作原公式强归纳。存在量词的两个方向分别沿双射送出及回拉见证，
同步更新两张赋值图；不要求公式码外部标准，也不在元层选择赋值函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Smap_assign_d.update_l {ω j f g i x y f' g'} (h : Smap_assign_d I ω j f g)
    (hj : M.IsSetFunction I j) (hxy : M.PairMember I x y j)
    (hf : Senv_update_d I f i x f') (hg : Senv_update_d I g i y g') : Smap_assign_d I ω j f' g' := by
  intro k hk a b ha hb
  rcases (hf.2 k a).mp ha with ⟨hki, hax⟩ | ⟨hne, ha⟩
  · exact (hg.2 k b).mpr (Or.inl ⟨hki, hj.2 x b y (hax ▸ hb) hxy⟩)
  · exact (hg.2 k b).mpr (Or.inr ⟨hne, h k hk a b ha hb⟩)

def Smap_row_d (ω X R E Y S K F n j r : M.Domain) : Prop := ∀ f g,
  M.mem f E → M.mem g K → Smap_assign_d I ω j f g →
    (Ssat_d I X R E F n r f ↔ Ssat_d I Y S K F n r g)

def smap_row_m {d} (ω X R E Y S K F n j r : Term d) : Formula 1 d :=
  Formula.forallMem E (Formula.forallMem K.weaken
    (.imp (smap_assign_m (𝒞 := 𝒞) ω.weaken.weaken j.weaken.weaken (.bound 1) .newest)
      (.iff (ssat_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken E.weaken.weaken
        F.weaken.weaken n.weaken.weaken r.weaken.weaken (.bound 1))
        (ssat_m (𝒞 := 𝒞) Y.weaken.weaken S.weaken.weaken K.weaken.weaken
          F.weaken.weaken n.weaken.weaken r.weaken.weaken .newest))))
derive_free_closed smap_row_m

theorem smap_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R E Y S K F n j r : Term d) :
    Formula.satisfies ρ (smap_row_m (𝒞 := 𝒞) ω X R E Y S K F n j r) ↔
      Smap_row_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (E.eval ρ) (Y.eval ρ) (S.eval ρ)
        (K.eval ρ) (F.eval ρ) (n.eval ρ) (j.eval ρ) (r.eval ρ) := by
  simp only [smap_row_m, Smap_row_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    smap_assign_sat_l I, Formula.satisfies_iff_iff, ssat_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h f g hf hg => h f hf g hg, fun h f hf g hg => h f g hf hg⟩

theorem smap_row_l (hZF : M.Models ZF) {ω X R E Y S K F n j r}
    (hj : M.IsSetBijectionFromTo I j X Y)
    (hm : ∀ a b x y, M.PairMember I a x j → M.PairMember I b y j →
      (M.PairMember I a b R ↔ M.PairMember I x y S))
    (hE : M.IsFunctionSpace I E ω X) (hK : M.IsFunctionSpace I K ω Y)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) : Smap_row_d I ω X R E Y S K F n j r := by
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF Y S K F hF.2.1.1
  let ρ : Env M 10 := ⟨Fin.cases j (Fin.cases n (Fin.cases F (Fin.cases K (Fin.cases S
    (Fin.cases Y (Fin.cases E (Fin.cases R (Fin.cases X (fun _ => ω))))))))), fun _ => ω⟩
  let φ : UnarySchema 10 := {
    body := smap_row_m (𝒞 := 𝒞) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat s : φ.denote ρ s ↔ Smap_row_d I ω X R E Y S K F n j s := smap_row_sat_l I hZF.1 ..
  apply (sat r).mp (sfm_induction_l I hZF hF φ ρ ?_ hr)
  intro r hr ih
  apply (sat r).mpr
  intro f g hf hg hfg
  have point i (hi : M.mem i ω) : ∃ x y,
      M.PairMember I i x f ∧ M.PairMember I x y j ∧ M.PairMember I i y g := by
    obtain ⟨x, hx, hix⟩ := ((hE f).mp hf).2.2 i hi
    obtain ⟨y, _, hxy⟩ := hj.1.1.2.2 x hx
    exact ⟨x, y, hix, hxy, hfg i hi x y hix hxy⟩
  obtain ⟨o, ho⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r o ho with ⟨a, b, hs, ha, hb⟩ | ⟨a, b, hs, ha, hb⟩ |
    ⟨a, b, hs, ha, hb⟩ | ⟨a, b, hs, ha, hb⟩
  · obtain ⟨x, x', hax, hxx, hax'⟩ := point a ha
    obtain ⟨y, y', hby, hyy, hby'⟩ := point b hb
    exact (ssat_rel_l I hZF hF hH ho hs hE hf hax hby).trans
      ((hm x y x' y' hxx hyy).trans (ssat_rel_l I hZF hF hJ ho hs hK hg hax' hby').symm)
  · obtain ⟨x, x', hax, hxx, hax'⟩ := point a ha
    obtain ⟨y, y', hby, hyy, hby'⟩ := point b hb
    have he : x = y ↔ x' = y' := ⟨fun h => hj.1.1.1.2 y x' y' (h ▸ hxx) hyy,
      fun h => hj.1.2 x y y' (h ▸ hxx) hyy⟩
    exact (ssat_eq_l I hZF hF hH ho hs hE hf hax hby).trans
      (he.trans (ssat_eq_l I hZF hF hJ ho hs hK hg hax' hby').symm)
  · exact (ssat_nor_l I hZF hF hH ho hs hf).trans ((not_congr (or_congr
      ((sat a).mp (ih a ha) f g hf hg hfg) ((sat b).mp (ih b hb) f g hf hg hfg))).trans
        (ssat_nor_l I hZF hF hJ ho hs hg).symm)
  · rw [ssat_exists_l I hZF hF hH ho hs hf, ssat_exists_l I hZF hF hJ ho hs hg]
    constructor
    · rintro ⟨x, f', hx, hu, ht⟩
      obtain ⟨y, hy, hxy⟩ := hj.1.1.2.2 x hx
      obtain ⟨g', hv, hgv⟩ := senv_update_exists_l I hZF ((hK g).mp hg) ha hy
      exact ⟨y, g', hy, hv, ((sat b).mp (ih b hb) f' g'
        ((hE f').mpr (hu.function_l I ((hE f).mp hf) ha hx)) ((hK g').mpr hgv)
        (hfg.update_l I hj.1.1.1 hxy hu hv)).mp ht⟩
    · rintro ⟨y, g', hy, hv, ht⟩
      obtain ⟨x, hx, hxy⟩ := hj.2 y hy
      obtain ⟨f', hu, hfu⟩ := senv_update_exists_l I hZF ((hE f).mp hf) ha hx
      exact ⟨x, f', hx, hu, ((sat b).mp (ih b hb) f' g' ((hE f').mpr hfu)
        ((hK g').mpr (hv.function_l I ((hK g).mp hg) ha hy))
        (hfg.update_l I hj.1.1.1 hxy hu hv)).mpr ht⟩

/-- 真实双射及原子关系同构自动给出全内部初等性。 -/
theorem smap_of_iso_l (hZF : M.Models ZF) {ω c d X R Y S j} (hω : M.IsOmega ω)
    (hX : Smdl_d I c X R) (hY : Smdl_d I d Y S) (hj : M.IsSetBijectionFromTo I j X Y)
    (hm : ∀ a b x y, M.PairMember I a x j → M.PairMember I b y j →
      (M.PairMember I a b R ↔ M.PairMember I x y S)) : Smap_d I ω c d X Y j := by
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω Y
  refine ⟨hj.1, C, hC, fun a f g ha hf hg hfg => ?_⟩
  obtain ⟨n, F, r, hr⟩ := (hC a).mp ha
  exact (satisfies_decode_l I hZF.1 hX hr hE).trans
    ((smap_row_l I hZF hj hm hE hK hr.2.1 hr.2.2 f g ((hE f).mpr hf) ((hK g).mpr hg) hfg).trans
      (satisfies_decode_l I hZF.1 hY hr hK).symm)

/-- 初等嵌入的目标是一个初等子结构时，同一张图也是到大结构的初等嵌入。 -/
theorem Smap_d.target_sub_l (hE : Extensional M) {ω c d e X Y R N S j}
    (h : Smap_d I ω e d X N j) (hs : Ssub_d I c d Y R N S) (he : Selem_d I ω c d) :
    Smap_d I ω e c X Y j := by
  obtain ⟨hj, C, hC, hh⟩ := h
  refine ⟨⟨hj.1.mono_target_l I hs.subset, hj.2⟩, C, hC, fun a f g ha hf hg hfg => ?_⟩
  have hgN : M.IsSetFunctionFromTo I g ω N := ⟨hg.1, hg.2.1, fun i hi => by
    obtain ⟨x, hx, hix⟩ := hf.2.2 i hi
    obtain ⟨y, hy, hxy⟩ := hj.1.2.2 x hx
    exact ⟨y, hy, hfg i hi x y hix hxy⟩⟩
  exact (hh a f g ha hf hgN hfg).trans ((selem_decode_l I hE hs hC).mp he a g ha hgN).symm

/-- 同一内部理论的全部赋值真值沿初等嵌入回拉；赋值复合由实际集合图构造。 -/
theorem Smap_d.models_l (hZF : M.Models ZF) {ω c d X R Y S j T}
    (h : Smap_d I ω c d X Y j) (hc : Smdl_d I c X R) (hd : Smdl_d I d Y S)
    (ht : Smodels_d I ω d T) : Smodels_d I ω c T := by
  obtain ⟨Z, Q, K, C, hm, hK, hC, hTC, hT⟩ := ht
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I hd hm
  obtain ⟨hj, A, hA, hh⟩ := h
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  refine ⟨X, R, E, C, hc, hE, hC, hTC, fun a ha f hf => ?_⟩
  obtain ⟨g, hg, hfg⟩ := smap_assign_exists_l I hZF hj.1 ((hE f).mp hf)
  exact (hh a f g ((hA a).mpr ((hC a).mp (hTC a ha))) ((hE f).mp hf) hg hfg).mpr
    (hT a ha g ((hK g).mpr hg))

end YesMetaZFC.SetTheory.Internal
