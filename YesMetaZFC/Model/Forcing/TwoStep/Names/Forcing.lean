import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.Forcing.TwoStep.Presentation
import YesMetaZFC.Model.Forcing.TwoStep.Names.Interpretation

/-! # 二步名称转换的全局名称力迫

实际转换证书、原名称性及完整二步装配同时作有限参数反射。转换值在每个泛型
下已验证为第二阶段名称，因此每个正条件都迫使这个原名称谓词。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z b A T W C S : M.Domain}

theorem curry_forces_name_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (h : Two_step_d M B R z b A T W C S) {x t p} (hx : Name_d M C x) (ht : Curry_d M B C x t)
    (hp : M.mem p B) (hz : p ≠ z) :
    Forces_d M B R z (name_m (.bound 1) .newest) ((⟨fun _ => A, fun _ => A⟩ : Env M 1).push t) p := by
  let φ : Formula 1 2 := name_m (.bound 1) .newest
  let α : Formula 1 12 := .conj
    (two_step_m (.bound 9) (.bound 8) (.bound 7) (.bound 5) (.bound 11) (.bound 4) (.bound 3) (.bound 2) (.bound 1))
    (.conj (name_m (.bound 2) .newest) (curry_m (.bound 9) (.bound 2) .newest (.bound 10)))
  have hα : α.FreeClosed := by
    simp only [α, Definitional.Formula.FreeClosed]
    exact ⟨two_step_m_freeClosed _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl,
      name_m_freeClosed _ _ rfl rfl, curry_m_freeClosed _ _ _ _ rfl rfl rfl rfl⟩
  let e : Fin 2 → Term 12 := fun i => .bound ⟨i.val + 10, by omega⟩
  let ρ₀ : Env M 2 := (⟨fun _ => A, fun _ => A⟩ : Env M 1).push t
  let ρ := ((((((fenv_l ρ₀ B R z p).push b).push T).push W).push C).push S).push x
  have htN : Name_d M B t := curry_name_l M hZF (fun c q s hc hcs => by
    obtain ⟨hs, hq, _⟩ := (two_step_mem_l h hcs).mp hc
    exact ⟨hq.1, W, hs, h.closed⟩) ht
  apply forces_of_generics_l φ (name_m_freeClosed _ _ rfl rfl) α hα e
    (.bound 9) (.bound 8) (.bound 7) (.bound 6) (fun _ => rfl) rfl rfl rfl rfl
    ?_ hZF ρ O (Fin.cases htN (fun _ => ⟨W, h.root, h.closed⟩)) hp hz ?_
  · intro N hN η L _ _ _ hraw U hU _ ξ hξ
    have hh := (Formula.satisfies_conj_iff η _ _).mp hraw
    have hstep := (two_step_sat_l hN.1 η _ _ _ _ _ _ _ _ _).mp hh.1
    have hh := (Formula.satisfies_conj_iff η _ _).mp hh.2
    have hx' := (name_sat_l N hN.1 η _ _).mp hh.1
    have ht' := (curry_sat_l N hN.1 η _ _ _ _).mp hh.2
    let E := extension_l N hN (η.bound 9) (η.bound 8) (η.bound 7) U
    exact (name_sat_l E (extension_ext_l L hN hU) ξ (.bound 1) .newest).mpr
      (curry_second_name_l L hN hU hstep hx' ht' (hξ 1) (hξ 0))
  · exact (Formula.satisfies_conj_iff ρ _ _).mpr ⟨(two_step_sat_l hZF.1 ρ _ _ _ _ _ _ _ _ _).mpr h,
      (Formula.satisfies_conj_iff ρ _ _).mpr ⟨(name_sat_l M hZF.1 ρ _ _).mpr hx, (curry_sat_l M hZF.1 ρ _ _ _ _).mpr ht⟩⟩

end YesMetaZFC.Model.Forcing.Internal
