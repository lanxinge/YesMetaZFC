import YesMetaZFC.Model.Forcing.Internal.Check.Relation
import YesMetaZFC.Model.Forcing.TwoStep.Basic

/-! # 旧预序在规范名称下的实际力迫证书

规范嵌入的成员满性把旧载体的每个扩张元素拉回地模型，关系条目的双向保持
据此传输自反性与传递性。有限参数泛型判据消去外部可数性，只需原 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem check_preord_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b D V C T p}
    (hb : M.mem b B) (hC : Check_d M b D C) (hT : Check_d M b V T)
    (hV : Preord_d M D V) (hp : Below_d M B R z p b) :
    Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M C T) p := by
  let ρ : Env M 9 := ((((((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push D).push V).push C).push T).push p
  let e : Fin 2 → Term 9 := Fin.cases (.bound 2) (fun _ => .bound 1)
  let φ : Formula 1 2 := preord_m (.bound 0) (.bound 1)
  let α : Formula 1 9 := .conj (.mem (.bound 5) (.bound 8))
    (.conj (check_m (.bound 5) (.bound 4) (.bound 2)) (.conj (check_m (.bound 5) (.bound 3) (.bound 1))
      (.conj (preord_m (.bound 4) (.bound 3)) (below_m (.bound 8) (.bound 7) (.bound 6) (.bound 0) (.bound 5)))))
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α, Definitional.Formula.FreeClosed]
  have raw (K : SetTheory.Structure.{u}) (hE : Extensional K) (η : Env K 9) : Formula.satisfies η α ↔
      K.mem (η.bound 5) (η.bound 8) ∧ Check_d K (η.bound 5) (η.bound 4) (η.bound 2) ∧
      Check_d K (η.bound 5) (η.bound 3) (η.bound 1) ∧ Preord_d K (η.bound 4) (η.bound 3) ∧
      Below_d K (η.bound 8) (η.bound 7) (η.bound 6) (η.bound 0) (η.bound 5) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, check_sat_l K hE,
      preord_sat_l hE, below_sat_l K hE]
    rfl
  have names : ∀ i, Name_d M B ((e i).eval ρ) := Fin.cases
    (check_name_l M (check_range_l M hZF) hb hC) (fun _ => check_name_l M (check_range_l M hZF) hb hT)
  have hf := forces_of_generics_l φ (preord_m_freeClosed _ _ rfl rfl) α hα e
    (.bound 8) (.bound 7) (.bound 6) (.bound 0) (Fin.cases rfl (fun _ => rfl)) rfl rfl rfl rfl
    (fun K hK η L _ _ _ hh U hU hpU ξ hξ => ?_) hZF ρ O names hp.1 hp.2.1
      ((raw M hZF.1 ρ).mpr ⟨hb, hC, hT, hV, hp⟩)
  · exact (forces_env_l hZF.1 φ (preord_m_freeClosed _ _ rfl rfl)
      ⟨fun i => (e i).eval ρ, ρ.free⟩ (ord_env_l M C T) (Fin.cases rfl (fun _ => rfl)) p).mp hf
  · obtain ⟨hb', hC', hT', hv', hp'⟩ := (raw K hK.1 η).mp hh
    obtain ⟨f, hval, hmem, hinj⟩ := check_map_l L hK hU (hU.upward _ _ hpU hb' hp'.2.2)
    have hCv := qval_unique_l (hval _ _ hC') (hξ 0)
    have hTv := qval_unique_l (hval _ _ hT') (hξ 1)
    apply (preord_sat_l (extension_ext_l L hK hU) ξ (.bound 0) (.bound 1)).mpr
    change Preord_d _ (ξ.bound 0) (ξ.bound 1)
    rw [← hCv, ← hTv]
    have rel a b := image_entry_iff_l f hinj hmem (KP.exists_pair (ZF.modelsKP hK)) (extension_ext_l L hK hU) a b (η.bound 3)
    constructor
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := (hmem (η.bound 4) x).mp hx
      exact (rel a a).mp (hv'.1 a ha)
    · intro x y z hx hy hz hxy hyz
      obtain ⟨a, ha, rfl⟩ := (hmem (η.bound 4) x).mp hx
      obtain ⟨b, hb, rfl⟩ := (hmem (η.bound 4) y).mp hy
      obtain ⟨c, hc, rfl⟩ := (hmem (η.bound 4) z).mp hz
      exact (rel a c).mp (hv'.2 a b c ha hb hc ((rel a b).mpr hxy) ((rel b c).mpr hyz))

end YesMetaZFC.Model.Forcing.Internal
