import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer
import YesMetaZFC.Model.Forcing.Internal.Functions.Rules

/-! # 旧成员与关系的规范名称力迫

成员由规范名称的条目直接得到；关系条目由真实泛型中的规范嵌入核验，再用
有限参数反射消去外部可数性。两者均只需 ZF。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem check_mem_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b x y s t p}
    (hb : M.mem b B) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : M.mem p B) (hpb : Entry_d M p b R) (hxy : M.mem x y) : Mem_force_d M B R z p s t :=
  mem_force_entry_l O hZF hp (check_name_l M (check_range_l M hZF) hb hs) hb
    ((check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht s b).mpr ⟨rfl, x, hxy, hs⟩) hpb

/-- 规范名称的成员力迫在每个正条件下反射真实旧成员关系。 -/
theorem check_mem_reflect_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b x y s t p}
    (hb : M.mem b B) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : Below_d M B R z p b) (hm : Mem_force_d M B R z p s t) : M.mem x y := by
  obtain ⟨q, a, c, hq, ha, _, he⟩ := hm.2 p (below_refl_l O hp.1 hp.2.1)
  obtain ⟨_, u, huy, hu⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF)) ht a c).mp ha
  exact (check_force_reflect_l O hZF hb hs hu (below_trans_l O hb hq hp) he).symm ▸ huy

theorem check_rel_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b F x y T s t p}
    (hb : M.mem b B) (hF : Check_d M b F T) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : Below_d M B R z p b) (hxy : Entry_d M x y F) : Rel_force_d M B R z T p s t := by
  let ρ₀ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b
  let ρ₁ : Env M 7 := ((ρ₀.push F).push x).push y
  let ρ : Env M 11 := (((ρ₁.push T).push s).push t).push p
  let φ : Formula 1 3 := entry_m (.bound 1) (.bound 0) (.bound 2)
  let e : Fin 3 → Term 11 := Fin.cases (.bound 1) (Fin.cases (.bound 2) (fun _ => .bound 3))
  let α : Formula 1 11 := .conj (.mem (.bound 7) (.bound 10)) (.conj (check_m (.bound 7) (.bound 6) (.bound 3))
    (.conj (check_m (.bound 7) (.bound 5) (.bound 2)) (.conj (check_m (.bound 7) (.bound 4) (.bound 1))
      (.conj (entry_m (.bound 5) (.bound 4) (.bound 6)) (below_m (.bound 10) (.bound 9) (.bound 8) (.bound 0) (.bound 7))))))
  have hφ : φ.FreeClosed := entry_m_freeClosed _ _ _ rfl rfl rfl
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α, Definitional.Formula.FreeClosed]
  have raw (K : SetTheory.Structure.{u}) (hE : Extensional K) (η : Env K 11) : Formula.satisfies η α ↔
      K.mem (η.bound 7) (η.bound 10) ∧ Check_d K (η.bound 7) (η.bound 6) (η.bound 3) ∧ Check_d K (η.bound 7) (η.bound 5) (η.bound 2) ∧
      Check_d K (η.bound 7) (η.bound 4) (η.bound 1) ∧ Entry_d K (η.bound 5) (η.bound 4) (η.bound 6) ∧
      Below_d K (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 0) (η.bound 7) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, check_sat_l K hE, entry_sat_l K hE, below_sat_l K hE]
    rfl
  have names : ∀ i, Name_d M B ((e i).eval ρ) :=
    Fin.cases (check_name_l M (check_range_l M hZF) hb ht)
      (Fin.cases (check_name_l M (check_range_l M hZF) hb hs) (fun _ => check_name_l M (check_range_l M hZF) hb hF))
  have hf := forces_of_generics_l φ hφ α hα e (.bound 10) (.bound 9) (.bound 8) (.bound 0)
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl rfl rfl rfl
    (fun K hK η O' _ _ _ hh U hU hpU ξ hξ => ?_) hZF ρ O names hp.1 hp.2.1
      ((raw M hZF.1 ρ).mpr ⟨hb, hF, hs, ht, hxy, hp⟩)
  · exact (force_entry_l hZF.1 ⟨fun i => (e i).eval ρ, ρ.free⟩ p (.bound 1) (.bound 0) (.bound 2)).mp hf
  · obtain ⟨hbB, hF', hs', ht', hxy', hp'⟩ := (raw K hK.1 η).mp hh
    have hb' := hU.upward _ _ hpU hbB hp'.2.2
    obtain ⟨f, hv, he, _⟩ := check_map_l O' hK hU hb'
    have hFv := qval_unique_l (hv _ _ hF') (hξ 2)
    have hxv := qval_unique_l (hv _ _ hs') (hξ 1)
    have hyv := qval_unique_l (hv _ _ ht') (hξ 0)
    apply (entry_sat_l _ (extension_ext_l O' hK hU) ξ (.bound 1) (.bound 0) (.bound 2)).mpr
    change Entry_d _ (ξ.bound 1) (ξ.bound 0) (ξ.bound 2)
    rw [← hFv, ← hxv, ← hyv]
    obtain ⟨v, hvp, hvF⟩ := hxy'
    exact ⟨f v, image_kpair_l f he hvp, (he _ _).mpr ⟨v, hvF, rfl⟩⟩

/-- 正条件迫使两个规范名称满足旧关系，当且仅当旧对象确实满足该关系；此处给出反射方向。 -/
theorem check_rel_reflect_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {b F x y T s t p}
    (hb : M.mem b B) (hF : Check_d M b F T) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : Below_d M B R z p b) (hrel : Rel_force_d M B R z T p s t) : Entry_d M x y F := by
  let ρ₀ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b
  let ρ₁ : Env M 7 := ((ρ₀.push F).push x).push y
  let ρ : Env M 11 := (((ρ₁.push T).push s).push t).push p
  let α : Formula 1 11 := .conj (.mem (.bound 7) (.bound 10)) (.conj (check_m (.bound 7) (.bound 6) (.bound 3))
    (.conj (check_m (.bound 7) (.bound 5) (.bound 2)) (.conj (check_m (.bound 7) (.bound 4) (.bound 1))
      (.conj (below_m (.bound 10) (.bound 9) (.bound 8) (.bound 0) (.bound 7))
        (rel_force_m (.bound 10) (.bound 9) (.bound 8) (.bound 3) (.bound 0) (.bound 2) (.bound 1))))))
  let β : Formula 1 11 := entry_m (.bound 5) (.bound 4) (.bound 6)
  have hα : α.FreeClosed := by simp -implicitDefEqProofs [α, Definitional.Formula.FreeClosed]
  have hβ : β.FreeClosed := entry_m_freeClosed _ _ _ rfl rfl rfl
  have raw (K : SetTheory.Structure.{u}) (hE : Extensional K) (η : Env K 11) : Formula.satisfies η α ↔
      K.mem (η.bound 7) (η.bound 10) ∧ Check_d K (η.bound 7) (η.bound 6) (η.bound 3) ∧
      Check_d K (η.bound 7) (η.bound 5) (η.bound 2) ∧ Check_d K (η.bound 7) (η.bound 4) (η.bound 1) ∧
      Below_d K (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 0) (η.bound 7) ∧
      Rel_force_d K (η.bound 10) (η.bound 9) (η.bound 8) (η.bound 3) (η.bound 0) (η.bound 2) (η.bound 1) := by
    simp only [α, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, check_sat_l K hE,
      below_sat_l K hE, rel_force_sat_l K hE]
    rfl
  have h := source_of_generics_l α β hα hβ (.bound 10) (.bound 9) (.bound 8) (.bound 0) rfl rfl rfl rfl
    (fun K hK η O' hh U hU hpU => ?_) hZF ρ O hp.1 hp.2.1 ((raw M hZF.1 ρ).mpr ⟨hb, hF, hs, ht, hp, hrel⟩)
  · exact (entry_sat_l M hZF.1 ρ (.bound 5) (.bound 4) (.bound 6)).mp h
  · obtain ⟨hb', hF', hs', ht', hp', hr'⟩ := (raw K hK.1 η).mp hh
    have hbU := hU.upward _ _ hpU hb' hp'.2.2
    obtain ⟨e, hv, hm, hi⟩ := check_map_l O' hK hU hbU
    have he := (rel_force_truth_l O' hK hU (hv _ _ hs') (hv _ _ ht') (hv _ _ hF')).mp ⟨η.bound 0, hpU, hr'⟩
    exact (entry_sat_l K hK.1 η (.bound 5) (.bound 4) (.bound 6)).mpr
      ((image_entry_iff_l e hi hm (KP.exists_pair (ZF.modelsKP hK)) (extension_ext_l O' hK hU) _ _ _).mpr he)

end YesMetaZFC.Model.Forcing.Internal
