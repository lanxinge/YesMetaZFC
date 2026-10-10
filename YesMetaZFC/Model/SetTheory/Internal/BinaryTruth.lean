import YesMetaZFC.Model.SetTheory.Internal.Support

/-! # 内部公式的两个实参

依次更新两个坐标，把统一满足关系作为实际二元公式使用。原程序和参数赋值
都保留为模型内集合，供内部收集与见证统一化消费。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sbin_d (X R E F n r i j f x y : M.Domain) : Prop := ∃ g h,
  Senv_update_d I f i x g ∧ Senv_update_d I g j y h ∧ Ssat_d I X R E F n r h

def sbin_m {d} (X R E F n r i j f x y : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (senv_update_m (𝒞 := 𝒞) f.weaken.weaken i.weaken.weaken x.weaken.weaken (.bound 1))
    (.conj (senv_update_m (𝒞 := 𝒞) (.bound 1) j.weaken.weaken y.weaken.weaken .newest)
      (ssat_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken E.weaken.weaken
        F.weaken.weaken n.weaken.weaken r.weaken.weaken .newest))))
derive_free_closed sbin_m

theorem sbin_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X R E F n r i j f x y : Term d) :
    Formula.satisfies ρ (sbin_m (𝒞 := 𝒞) X R E F n r i j f x y) ↔
      Sbin_d I (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ) (n.eval ρ) (r.eval ρ)
        (i.eval ρ) (j.eval ρ) (f.eval ρ) (x.eval ρ) (y.eval ρ) := by
  simp only [sbin_m, Sbin_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    senv_update_sat_l I hE, ssat_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem sbin_update_l (hE : Extensional M) {X R E F n r i j f x y g} (hu : Senv_update_d I f i x g) :
    Sbin_d I X R E F n r i j f x y ↔ ∃ h, Senv_update_d I g j y h ∧ Ssat_d I X R E F n r h := by
  refine ⟨?_, fun ⟨h, hh, ht⟩ => ⟨g, h, hu, hh, ht⟩⟩
  rintro ⟨g', h, hg, hh, ht⟩
  exact ⟨h, senv_update_unique_l I hE hg hu ▸ hh, ht⟩

theorem sbin_value_l (hE : Extensional M) {X R E F n r i j f x y g h}
    (hu : Senv_update_d I f i x g) (hv : Senv_update_d I g j y h) :
    Sbin_d I X R E F n r i j f x y ↔ Ssat_d I X R E F n r h :=
  (sbin_update_l I hE hu).trans ⟨fun ⟨_, hh, ht⟩ => senv_update_unique_l I hE hh hv ▸ ht,
    fun ht => ⟨h, hv, ht⟩⟩

theorem sbin_agree_l (hZF : M.Models ZF) {ω X R E F n r i j f g b x y}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hE : M.IsFunctionSpace I E ω X)
    (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g) (hx : M.mem x X) (hy : M.mem y X) :
    Sbin_d I X R E F n r i j f x y ↔ Sbin_d I X R E F n r i j g x y := by
  obtain ⟨u, hu, huf⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
  obtain ⟨v, hv, hvf⟩ := senv_update_exists_l I hZF huf hj hy
  obtain ⟨w, hw, hwf⟩ := senv_update_exists_l I hZF ((hE g).mp hg) hi hx
  obtain ⟨z, hz, hzf⟩ := senv_update_exists_l I hZF hwf hj hy
  exact (sbin_value_l I hZF.1 hu hv).trans ((ssat_agree_l I hZF hF hb hE hr
    ((hE v).mpr hvf) ((hE z).mpr hzf) ((ha.update_l I hu hw).update_l I hv hz)).trans
      (sbin_value_l I hZF.1 hw hz).symm)

def Scollect_d (X R E F n r i j f D C : M.Domain) : Prop := ∀ x, M.mem x D →
  ∃ y, M.mem y C ∧ Sbin_d I X R E F n r i j f x y

theorem scollect_agree_l (hZF : M.Models ZF) {ω X R E F n r i j f g b D C}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hE : M.IsFunctionSpace I E ω X)
    (hf : M.mem f E) (hg : M.mem g E) (ha : Senv_agree_d I b f g)
    (hD : M.MemberSubset D X) (hC : M.MemberSubset C X) :
    Scollect_d I X R E F n r i j f D C ↔ Scollect_d I X R E F n r i j g D C :=
  forall_congr' fun x => imp_congr_right fun hx => exists_congr fun y => and_congr_right fun hy =>
    sbin_agree_l I hZF hF hb hr hi hj hE hf hg ha (hD x hx) (hC y hy)

end YesMetaZFC.SetTheory.Internal
