import YesMetaZFC.SetTheory.InnerModel.HOD.Closure

/-! # 两种遗传参数类的全分离与全收集

分离集从原参数唯一可定义。收集先在背景取见证界，再以 H∩Vα 代替见证池；
这个秩切片已经属于 H，所以无需挑选参数列或假设选择公理。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem ha_model_separation_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {n} (φ : UnarySchema n)
    (ρ : Env (ha_model_l hZF k A) n) (X : (ha_model_l hZF k A).Domain) :
    ∃ Y : (ha_model_l hZF k A).Domain, ∀ x,
      M.mem x.val Y.val ↔ M.mem x.val X.val ∧ φ.denote ρ x := by
  let η := (image_env_l (N := M) Subtype.val ρ).push A
  let e : Fin (n+1) → Term (n+2) := Fin.cases .newest (fun i => .bound ⟨i.val+2, by omega⟩)
  let ψ : UnarySchema (n+1) := {
    body := ha_rel_m k φ.body (.bound 1) e
    freeClosed := ha_rel_closed_l k _ φ.freeClosed _ _ rfl (Fin.cases rfl (fun _ => rfl)) }
  obtain ⟨Y, hy, hY⟩ := oa_separation_l hZF k A ψ η
    (Fin.cases (oa_parameter_l hZF k A) (fun i => ha_oa_l (ρ.bound i).property)) (ha_oa_l X.property)
  have hHY : Ha_d k A Y := ha_of_members_l hZF hy (fun x hx => ha_trans_l X.property ((hY x).mp hx).1)
  refine ⟨⟨Y, hHY⟩, fun x => (hY x.val).trans (and_congr_right fun _ => ?_)⟩
  exact ha_rel_sat_l hZF k A φ.body φ.freeClosed (ρ.push x) (η.push x.val) (.bound 1) e
    rfl (Fin.cases rfl (fun _ => rfl))

theorem ha_model_collection_l (hZF : M.Models ZF) (k : Bool) (A : M.Domain) {n} (φ : BinarySchema n)
    (ρ : Env (ha_model_l hZF k A) n) (X : (ha_model_l hZF k A).Domain)
    (ht : ∀ x, M.mem x.val X.val → ∃ y, φ.denote ρ x y) :
    ∃ Y : (ha_model_l hZF k A).Domain, ∀ x, M.mem x.val X.val → ∃ y,
      M.mem y.val Y.val ∧ φ.denote ρ x y := by
  let η := (image_env_l (N := M) Subtype.val ρ).push A
  let e : Fin (n+2) → Term (n+3) := Fin.cases .newest (Fin.cases (.bound 1) (fun i => .bound ⟨i.val+3, by omega⟩))
  let ψ : BinarySchema (n+1) := {
    body := .conj (ha_m k (.bound 2) .newest) (ha_rel_m k φ.body (.bound 2) e)
    freeClosed := by
      simp only [Definitional.Formula.FreeClosed]
      exact ⟨ha_closed_l k _ _ rfl rfl,
        ha_rel_closed_l k _ φ.freeClosed _ _ rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))⟩ }
  have sat x y : ψ.denote η x y ↔ Ha_d k A y ∧
      Formula.satisfies ((η.push x).push y) (ha_rel_m k φ.body (.bound 2) e) := by
    simp only [BinarySchema.denote, ψ, Formula.satisfies_conj_iff, ha_sat_l hZF.1]
    rfl
  have tr (x y : (ha_model_l hZF k A).Domain) :
      Formula.satisfies ((η.push x.val).push y.val) (ha_rel_m k φ.body (.bound 2) e) ↔ φ.denote ρ x y :=
    ha_rel_sat_l hZF k A φ.body φ.freeClosed ((ρ.push x).push y) ((η.push x.val).push y.val)
      (.bound 2) e rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  obtain ⟨B, hB⟩ := ZF.collection_exists_d hZF ψ η X.val (fun x hx => by
    let z : (ha_model_l hZF k A).Domain := ⟨x, ha_trans_l X.property hx⟩
    obtain ⟨y, hy⟩ := ht z hx
    exact ⟨y.val, (sat x y.val).mpr ⟨y.property, (tr z y).mpr hy⟩⟩)
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨a, V, hv, hBV⟩ := ZF.v_cover_l I hZF B
  obtain ⟨S, hs, hS⟩ := ha_cut_l hZF k A hv
  refine ⟨⟨S, hs⟩, fun x hx => ?_⟩
  obtain ⟨y, hyB, hy⟩ := hB x.val hx
  obtain ⟨hyH, hyφ⟩ := (sat x.val y).mp hy
  exact ⟨⟨y, hyH⟩, (hS y).mpr ⟨ZF.v_transitive_l I hZF hv B hBV y hyB, hyH⟩,
    (tr x ⟨y, hyH⟩).mp hyφ⟩

end YesMetaZFC.SetTheory.InnerModel
