import YesMetaZFC.Model.Forcing.Internal.Homogeneous.Recovery

/-! # OD 序数子集的恢复

先用不增加序数把序数参数与子集的序数界拉回地模型，再用弱齐性真值公式作分离。
相对版本保留固定的整个集合参数 A；无参数结论只需完整力迫呈现在地模型中 OD。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
variable {b : M.Domain} (hb : U b) (e : M.Domain → (extension_l M hZF B R z U).Domain)
  (hv : ∀ x t, Check_d M b x t → Qval_d M B R z U t (e x))
  (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) (hi : Function.Injective e)
local notation "E" => extension_l M hZF B R z U
include O hU hb hv he hi

/-- 扩张中的任意序数集合都包含于一个旧序数，不预先要求给出界。 -/
theorem ordinal_set_ground_bound_l (X : (E).Domain) (hX : ∀ x, x ∈ X → (E).IsOrdinal x) :
    ∃ α, M.IsOrdinal α ∧ (E).MemberSubset X (e α) := by
  let hE := preserves_zf_l O hZF hU
  obtain ⟨T, hT⟩ := KP.exists_union (ZF.modelsKP hE) X
  have hTo := Structure.IsOrdinal.of_union (ZF.modelsKP hE) hT hX
  obtain ⟨D, hD⟩ := KP.exists_successor (ZF.modelsKP hE) T
  have hDo := KP.successor_isOrdinal (ZF.modelsKP hE) hTo hD
  obtain ⟨α, hα, hαD⟩ := no_new_ordinals_l O hZF hU (hU.proper b hb).1 e hv he hi hDo
  refine ⟨α, hα, fun x hx => ?_⟩
  rw [hαD]
  have hsub : (E).MemberSubset x T := fun y hy => (hT y).mpr ⟨x, hx, hy⟩
  rcases ordinal_subset_cases_l (ZF.modelsKP hE) (hX x hx) hTo hsub with hh | hh
  · exact hh.symm ▸ hD.predecessor_mem
  · exact (hD x).mpr (Or.inl hh)

/-- 弱齐性、OD[A] 呈现的扩张中，每个 OD[e(A)] 序数子集来自地模型 OD[A]。 -/
theorem whom_ob_ordinal_subset_l (hH : Whom_d M B R z) {A}
    (hB : Ob_d A B) (hR : Ob_d A R) (hz : Ob_d A z)
    {X : (E).Domain} (hX : Ob_d (e A) X) (hOrd : ∀ x, x ∈ X → (E).IsOrdinal x) :
    ∃ Y, Ob_d A Y ∧ e Y = X := by
  let hE := preserves_zf_l O hZF hU
  obtain ⟨α, hα, hXα⟩ := ordinal_set_ground_bound_l O hZF hU hb e hv he hi X hOrd
  obtain ⟨n, φ, η, hη, hdef⟩ := (ob_iff_external_l hE).mp hX
  obtain ⟨v, hv'⟩ := Classical.axiomOfChoice (fun i =>
    no_new_ordinals_l O hZF hU (hU.proper b hb).1 e hv he hi (hη i))
  let ρ : Env M n := ⟨v, fun _ => A⟩
  let ψ : UnarySchema (n+1) := ⟨φ.body, φ.freeClosed⟩
  have hψ y : ψ.denote (η.push (e A)) y ↔ y = X := hdef y
  exact whom_definable_subset_l O hZF hU hb e hv he hH hB hR hz (ob_ordinal_l hZF A hα)
    (od_member_s ψ) (ρ.push A) (η.push (e A))
    (Fin.cases (ob_parameter_l hZF A) (fun i => ob_ordinal_l hZF A (hv' i).1))
    (Fin.cases rfl (fun i => (hv' i).2)) hXα (od_member_sat_l ψ _ hψ)

/-- 无参数版本：OD 弱齐性力迫不增加 OD 序数子集，且原像仍是地模型中的 OD 集。 -/
theorem whom_od_ordinal_subset_l (hH : Whom_d M B R z)
    (hB : Od_d B) (hR : Od_d R) (hz : Od_d z)
    {X : (E).Domain} (hX : Od_d X) (hOrd : ∀ x, x ∈ X → (E).IsOrdinal x) :
    ∃ Y, Od_d Y ∧ e Y = X := by
  let hE := preserves_zf_l O hZF hU
  obtain ⟨A, hA⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨Y, hY, hYX⟩ := whom_ob_ordinal_subset_l O hZF hU hb e hv he hi hH
    (ob_of_od_l hZF A hB) (ob_of_od_l hZF A hR) (ob_of_od_l hZF A hz) (ob_of_od_l hE (e A) hX) hOrd
  obtain ⟨n, φ, ρ, hρ, hdef⟩ := (ob_iff_external_l hZF).mp hY
  let ψ : UnarySchema (n+1) := ⟨φ.body, φ.freeClosed⟩
  exact ⟨Y, od_of_unique_l hZF ψ (ρ.push A)
    (Fin.cases (Structure.IsOrdinal.of_no_members hA) hρ) hdef, hYX⟩

end YesMetaZFC.Model.Forcing.Internal
