import YesMetaZFC.Model.Forcing.Internal.Homogeneous.OrdinalSubsets
import YesMetaZFC.Model.Forcing.Internal.Ground.Collapse
import YesMetaZFC.SetTheory.InnerModel.HOD.Presentation

/-! # 弱齐性力迫的 HOD 比较

把 HOD[e(A)] 对象呈现为序数代码上的隶属关系，用弱齐性恢复载体与关系，再在
地模型内部坍塌。目标模型的内部唯一性把原对象识别为地模型 HOD[A] 对象的像。
全程只需背景 ZF，不要求模型外部良基，也不要求偏序具有最大条件。
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

/-- 固定参数比较：HOD[e(A)] 的每个对象来自地模型 HOD[A]。 -/
theorem whom_hb_l (hH : Whom_d M B R z) {A}
    (hB : Ob_d A B) (hR : Ob_d A R) (hz : Ob_d A z)
    {x : (E).Domain} (hx : Hb_d (e A) x) : ∃ y, Hb_d A y ∧ e y = x := by
  let hE := preserves_zf_l O hZF hU
  -- 先把整个遗传容器的隶属关系呈现在有界序数码上。
  obtain ⟨κ, C, S, T, F, hκ, hCκ, hS, hoC, hoS, fn, hg, hx⟩ := hb_presentation_l hE hx
  obtain ⟨α, hα, hακ⟩ := no_new_ordinals_l O hZF hU (hU.proper b hb).1 e hv he hi hκ
  subst κ
  -- 载体是旧序数的可定义子集；关系是旧笛卡尔积的可定义子集。
  obtain ⟨C₀, hoC₀, eqC⟩ := whom_ob_old_subset_l O hZF hU hb e hv he hi hH hB hR hz
    (ob_ordinal_l hZF A hα) hoC hCκ
  subst C
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF (kp_pair_l (ZF.modelsKP hZF)) α α
  have hp := image_product_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) e hi he hP
  have hs : (E).MemberSubset S (e P) := by
    intro p hpS
    obtain ⟨a, b, ha, hb, hab⟩ := hS p hpS
    exact (hp p).mpr ⟨a, hCκ a ha, b, hCκ b hb, hab⟩
  obtain ⟨S₀, hoS₀, eqS⟩ := whom_ob_old_subset_l O hZF hU hb e hv he hi hH hB hR hz
    (ob_product_l hZF A (ob_ordinal_l hZF A hα) (ob_ordinal_l hZF A hα) hP) hoS hs
  subst S
  -- 对同一旧关系在两模型内坍塌，以目标模型中的唯一性识别原对象。
  exact collapse_hb_recover_l e hi he hZF hE hoC₀ hoS₀ (fun a ha => ob_ordinal_l hZF A
    (hα.mem ((image_member_l e hi he).mp (hCκ (e a) ((he C₀ (e a)).mpr ⟨a, ha, rfl⟩))))) fn hg hx

/-- 无参数比较：完整力迫呈现为 OD 时，HOD 的包含方向从扩张指向地模型。 -/
theorem whom_hod_l (hH : Whom_d M B R z) (hB : Od_d B) (hR : Od_d R) (hz : Od_d z)
    {x : (E).Domain} (hx : Hod_d x) : ∃ y, Hod_d y ∧ e y = x := by
  obtain ⟨A, hA⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨y, hy, hyx⟩ := whom_hb_l O hZF hU hb e hv he hi hH
    (ob_of_od_l hZF A hB) (ob_of_od_l hZF A hR) (ob_of_od_l hZF A hz)
    (hb_of_hod_l (preserves_zf_l O hZF hU) (e A) hx)
  exact ⟨y, (hb_ordinal_parameter_l hZF (Structure.IsOrdinal.of_no_members hA)).mp hy, hyx⟩

omit hb e hv he hi in
/-- 固定参数版本同样自动构造嵌入，呈现只需属于 OD[A]。 -/
theorem whom_hb_comparison_l (hH : Whom_d M B R z) {A}
    (hB : Ob_d A B) (hR : Ob_d A R) (hz : Ob_d A z) :
    ∃ e : M.Domain → (E).Domain, Function.Injective e ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧
      (∀ x, (E).IsOrdinal x ↔ ∃ α, M.IsOrdinal α ∧ e α = x) ∧
      ∀ x : (E).Domain, Hb_d (e A) x → ∃ y, Hb_d A y ∧ e y = x := by
  obtain ⟨b, hb⟩ := hU.inhabited
  obtain ⟨e, hv, he, hi, ho⟩ := check_map_ordinals_l O hZF hU hb
  exact ⟨e, hi, he, ho, fun _ hx => whom_hb_l O hZF hU hb e hv he hi hH hB hR hz hx⟩

omit hb e hv he hi in
/-- 自动构造地嵌入，并同时给出序数相同及 HOD 比较；无额外坍塌或编码前提。 -/
theorem whom_hod_comparison_l (hH : Whom_d M B R z) (hB : Od_d B) (hR : Od_d R) (hz : Od_d z) :
    ∃ e : M.Domain → (E).Domain, Function.Injective e ∧
      (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧
      (∀ x, (E).IsOrdinal x ↔ ∃ α, M.IsOrdinal α ∧ e α = x) ∧
      ∀ x : (E).Domain, Hod_d x → ∃ y, Hod_d y ∧ e y = x := by
  obtain ⟨b, hb⟩ := hU.inhabited
  obtain ⟨e, hv, he, hi, ho⟩ := check_map_ordinals_l O hZF hU hb
  exact ⟨e, hi, he, ho, fun _ hx => whom_hod_l O hZF hU hb e hv he hi hH hB hR hz hx⟩

end YesMetaZFC.Model.Forcing.Internal
