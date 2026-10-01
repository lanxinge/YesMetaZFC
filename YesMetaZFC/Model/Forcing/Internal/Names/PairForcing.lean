import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Internal.Names.PairConstruction

/-! # 规范名称配对的全局力迫证书

名称配对在每个泛型下的实际解释，经带参数可数反射给出每个正条件上的原公式
证书。这里仅使用原 ZF，不调用依赖选择公理的最大值原理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

def npair_env_l (a b t : M.Domain) : Env M 3 := ((⟨fun _ => a, fun _ => a⟩ : Env M 1).push b).push t

theorem npair_forces_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {a b t p}
    (ha : Name_d M B a) (hb : Name_d M B b) (ht : Npair_d M B a b t) (hp : M.mem p B) (hz : p ≠ z) :
    Forces_d M B R z (Formula.isUnorderedPair .newest (.bound 2) (.bound 1)) (npair_env_l a b t) p := by
  let φ : Formula 1 3 := Formula.isUnorderedPair .newest (.bound 2) (.bound 1)
  let α : Formula 1 7 := npair_m (.bound 3) (.bound 6) (.bound 5) (.bound 4)
  let e : Fin 3 → Term 7 := fun i => .bound (param_shift_l i)
  let ρ := fenv_l (npair_env_l a b t) B R z p
  apply forces_of_generics_l φ (Formula.isUnorderedPair_freeClosed _ _ _ rfl rfl rfl)
    α (npair_m_freeClosed _ _ _ _ rfl rfl rfl rfl) e (.bound 3) (.bound 2) (.bound 1) .newest
    (fun _ => rfl) rfl rfl rfl rfl ?_ hZF ρ O ?_ hp hz ((npair_sat_l M hZF.1 ρ _ _ _ _).mpr ht)
  · intro N hN η L _ _ _ hα U hU _ ξ hξ
    let E := extension_l N hN (η.bound 3) (η.bound 2) (η.bound 1) U
    have hn := (npair_sat_l N hN.1 η _ _ _ _).mp hα
    exact (pair_sat_l E (extension_ext_l L hN hU) ξ .newest (.bound 2) (.bound 1)).mpr
      (npair_val_l L hN hU hn (hξ 2) (hξ 1) (hξ 0))
  · exact Fin.cases (npair_name_l M hZF ha hb ht) (Fin.cases hb (fun _ => ha))

theorem nkpair_forces_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {a b t p}
    (ha : Name_d M B a) (hb : Name_d M B b) (ht : Nkpair_d M B a b t) (hp : M.mem p B) (hz : p ≠ z) :
    Forces_d M B R z (kpair_m .newest (.bound 2) (.bound 1)) (npair_env_l a b t) p := by
  let φ : Formula 1 3 := kpair_m .newest (.bound 2) (.bound 1)
  let α : Formula 1 7 := nkpair_m (.bound 3) (.bound 6) (.bound 5) (.bound 4)
  let e : Fin 3 → Term 7 := fun i => .bound (param_shift_l i)
  let ρ := fenv_l (npair_env_l a b t) B R z p
  apply forces_of_generics_l φ (kpair_m_freeClosed _ _ _ rfl rfl rfl)
    α (nkpair_m_freeClosed _ _ _ _ rfl rfl rfl rfl) e (.bound 3) (.bound 2) (.bound 1) .newest
    (fun _ => rfl) rfl rfl rfl rfl ?_ hZF ρ O ?_ hp hz ((nkpair_sat_l M hZF.1 ρ _ _ _ _).mpr ht)
  · intro N hN η L _ _ _ hα U hU _ ξ hξ
    let E := extension_l N hN (η.bound 3) (η.bound 2) (η.bound 1) U
    have hn := (nkpair_sat_l N hN.1 η _ _ _ _).mp hα
    exact (kpair_sat_l E (extension_ext_l L hN hU) ξ .newest (.bound 2) (.bound 1)).mpr
      (nkpair_val_l L hN hU hn (hξ 2) (hξ 1) (hξ 0))
  · exact Fin.cases (nkpair_name_l M hZF ha hb ht) (Fin.cases hb (fun _ => ha))

end YesMetaZFC.Model.Forcing.Internal
