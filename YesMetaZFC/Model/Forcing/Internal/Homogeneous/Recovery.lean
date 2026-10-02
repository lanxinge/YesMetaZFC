import YesMetaZFC.Model.Forcing.Internal.Homogeneous.Truth
import YesMetaZFC.Model.Forcing.Internal.Ground.Ordinals
import YesMetaZFC.SetTheory.InnerModel.OD.Separation

/-! # 弱齐性下的可定义旧集合子集恢复

对地模型定义的 Gforce 原公式作分离。弱齐性真值对应证明所得旧集合的像恰为
目标子集；若完整力迫呈现与定义参数在 OD[A] 中，同一分离定义仍在 OD[A] 中。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
variable {b : M.Domain} (hb : U b) (e : M.Domain → (extension_l M hZF B R z U).Domain)
  (hv : ∀ x t, Check_d M b x t → Qval_d M B R z U t (e x))
  (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y)
local notation "E" => extension_l M hZF B R z U
include O hU hb hv he

/-- 更一般的恢复：旧集合中、由旧参数定义的子集在弱齐性扩张中仍是旧集合。 -/
theorem whom_definable_subset_l (hH : Whom_d M B R z) {A D}
    (hB : Ob_d A B) (hR : Ob_d A R) (hz : Ob_d A z) (hD : Ob_d A D)
    {n} (φ : UnarySchema n) (ρ : Env M n) (η : Env E n)
    (hρ : ∀ i, Ob_d A (ρ.bound i)) (hη : ∀ i, e (ρ.bound i) = η.bound i)
    {X : (E).Domain} (hX : (E).MemberSubset X (e D))
    (hφ : ∀ y, φ.denote η y ↔ y ∈ X) : ∃ Y, Ob_d A Y ∧ e Y = X := by
  let δ := ((ρ.push B).push R).push z
  let ψ : UnarySchema (n+3) := {
    body := gforce_m φ.body (.bound 3) (.bound 2) (.bound 1)
      (Fin.cases .newest (fun i => .bound ⟨i.val+4, by omega⟩))
    freeClosed := gforce_closed_l _ _ _ _ _ φ.freeClosed rfl rfl rfl (Fin.cases rfl (fun _ => rfl)) }
  have hψ a : ψ.denote δ a ↔ Gforce_d M B R z φ.body (ρ.push a).bound := by
    let f : Fin (n+1) → Term (n+4) := Fin.cases .newest (fun i => .bound ⟨i.val+4, by omega⟩)
    have hf : (fun i => (f i).eval (δ.push a)) = (ρ.push a).bound :=
      funext (Fin.cases rfl (fun _ => rfl))
    exact (gforce_sat_l hZF.1 φ.body φ.freeClosed (δ.push a) (.bound 3) (.bound 2) (.bound 1) f).trans
      (by change Gforce_d M B R z φ.body _ ↔ _; rw [hf])
  obtain ⟨Y, hy⟩ := ZF.separation_exists_d hZF ψ δ D
  have defn T : (oa_sep_s ψ).denote (δ.push D) T ↔ T = Y :=
    (oa_sep_schema_l ψ δ D T).trans
      ⟨fun ht => hZF.1.eq_of_same_members T Y (fun a => (ht a).trans (hy a).symm), fun ht => ht.symm ▸ hy⟩
  have hY := ob_closed_l hZF A (oa_sep_s ψ) (δ.push D)
    (Fin.cases hD (Fin.cases hz (Fin.cases hR (Fin.cases hB hρ)))) defn
  have truth a : ψ.denote δ a ↔ e a ∈ X := (hψ a).trans
    ((whom_ground_truth_l O hZF hU hb e hv hH φ.body φ.freeClosed (ρ.push a).bound (η.push (e a))
      (Fin.cases rfl hη)).trans (hφ (e a)))
  refine ⟨Y, hY, (extension_ext_l O hZF hU).eq_of_same_members (e Y) X (fun y => ?_)⟩
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := (he Y y).mp h
    exact (truth a).mp ((hy a).mp ha).2
  · intro h
    obtain ⟨a, ha, rfl⟩ := (he D y).mp (hX y h)
    exact (he Y (e a)).mpr ⟨a, (hy a).mpr ⟨ha, (truth a).mpr h⟩, rfl⟩

/-- 唯一定义某集合的正文，转为定义该集合成员的正文。 -/
def od_member_s {n} (φ : UnarySchema n) : UnarySchema n := {
  body := .existsE (.conj (pred_m φ (fun i => .bound ⟨i.val+2, by omega⟩) .newest)
    (.mem (.bound 1) .newest)) }

omit O hU hb e hv he in
theorem od_member_sat_l {N : SetTheory.Structure.{u}} {n} (φ : UnarySchema n) (η : Env N n)
    {X} (h : ∀ y, φ.denote η y ↔ y = X) (x : N.Domain) :
    (od_member_s φ).denote η x ↔ N.mem x X := by
  simp only [od_member_s, UnarySchema.denote, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, pred_sat_l, Formula.satisfies_mem_iff]
  change (∃ y, φ.denote η y ∧ N.mem x y) ↔ N.mem x X
  exact ⟨fun ⟨y, hy, hx⟩ => (h y).mp hy ▸ hx, fun hx => ⟨X, (h X).mpr rfl, hx⟩⟩

end YesMetaZFC.Model.Forcing.Internal
