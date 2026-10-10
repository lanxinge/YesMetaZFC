import YesMetaZFC.Model.SetTheory.Internal.Support

/-! # 不同变量域上的同一内部公式

赋值空间只需包含程序实际读取的坐标。对原指令作内部强归纳，有限赋值
与完整 ω 赋值具有相同真值；量词步同时更新两份赋值，不引入外部递归。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ssat_spaces_l (hZF : M.Models ZF) {ω X R E D V W F n b r f g : M.Domain}
    (hF : Sfm_d I ω n F) (hb : Sbound_d I F b)
    (hE : M.IsFunctionSpace I E V X) (hD : M.IsFunctionSpace I D W X)
    (hV : M.MemberSubset b V) (hW : M.MemberSubset b W) (hr : M.mem r n)
    (hf : M.mem f E) (hg : M.mem g D) (agree : Senv_agree_d I b f g) :
    Ssat_d I X R E F n r f ↔ Ssat_d I X R D F n r g := by
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.1
  obtain ⟨J, hJ⟩ := seval_exists_l I hZF X R D F hF.2.1.1
  let ρ : Env M 7 := ⟨Fin.cases b (Fin.cases n (Fin.cases F (Fin.cases D
    (Fin.cases E (Fin.cases R (fun _ => X)))))), fun _ => X⟩
  let φ : UnarySchema 7 := {
    body := Formula.forallMem (.bound 5) (Formula.forallMem (.bound 5)
      (.imp (senv_agree_m (𝒞 := 𝒞) (.bound 3) (.bound 1) .newest)
        (.iff (ssat_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 7) (.bound 5) (.bound 4) (.bound 2) (.bound 1))
          (ssat_m (𝒞 := 𝒞) (.bound 9) (.bound 8) (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest)))) }
  have sat k : φ.denote ρ k ↔ ∀ f, M.mem f E → ∀ g, M.mem g D → Senv_agree_d I b f g →
      (Ssat_d I X R E F n k f ↔ Ssat_d I X R D F n k g) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, senv_agree_sat_l I, ssat_sat_l I hZF.1]; rfl
  apply (sat r).mp (sfm_induction_l I hZF hF φ ρ ?_ hr) f hf g hg agree
  intro k hk ih
  apply (sat k).mpr
  intro f hf g hg ha
  obtain ⟨c, hc⟩ := (hF.2.1.2.2 k).mp hk
  rcases hF.2.2 k c hc with ⟨i, j, hs, _, _⟩ | ⟨i, j, hs, _, _⟩ |
    ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, _, hj⟩
  · obtain ⟨hi, hj⟩ := hb.operands_l I hc hs
    obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 i (hV i hi)
    obtain ⟨y, _, hy⟩ := ((hE f).mp hf).2.2 j (hV j hj)
    exact (ssat_rel_l I hZF hF hH hc hs hE hf hx hy).trans
      (ssat_rel_l I hZF hF hJ hc hs hD hg ((ha i x hi).mp hx) ((ha j y hj).mp hy)).symm
  · obtain ⟨hi, hj⟩ := hb.operands_l I hc hs
    obtain ⟨x, _, hx⟩ := ((hE f).mp hf).2.2 i (hV i hi)
    obtain ⟨y, _, hy⟩ := ((hE f).mp hf).2.2 j (hV j hj)
    exact (ssat_eq_l I hZF hF hH hc hs hE hf hx hy).trans
      (ssat_eq_l I hZF hF hJ hc hs hD hg ((ha i x hi).mp hx) ((ha j y hj).mp hy)).symm
  · rw [ssat_nor_l I hZF hF hH hc hs hf, ssat_nor_l I hZF hF hJ hc hs hg]
    exact not_congr (or_congr ((sat i).mp (ih i hi) f hf g hg ha) ((sat j).mp (ih j hj) f hf g hg ha))
  · have hi := (hb.operands_l I hc hs).1
    rw [ssat_exists_l I hZF hF hH hc hs hf, ssat_exists_l I hZF hF hJ hc hs hg]
    constructor
    · rintro ⟨x, u, hx, hu, truth⟩
      obtain ⟨v, hv, hvf⟩ := senv_update_exists_l I hZF ((hD g).mp hg) (hW i hi) hx
      exact ⟨x, v, hx, hv, ((sat j).mp (ih j hj) u
        ((hE u).mpr (hu.function_l I ((hE f).mp hf) (hV i hi) hx)) v ((hD v).mpr hvf)
        (ha.update_l I hu hv)).mp truth⟩
    · rintro ⟨x, v, hx, hv, truth⟩
      obtain ⟨u, hu, huf⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (hV i hi) hx
      exact ⟨x, u, hx, hu, ((sat j).mp (ih j hj) u ((hE u).mpr huf) v
        ((hD v).mpr (hv.function_l I ((hD g).mp hg) (hW i hi) hx)) (ha.update_l I hu hv)).mpr truth⟩

end YesMetaZFC.SetTheory.Internal
