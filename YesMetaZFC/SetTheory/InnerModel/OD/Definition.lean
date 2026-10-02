import YesMetaZFC.SetTheory.InnerModel.OD.Code
import YesMetaZFC.SetTheory.Kuratowski
import YesMetaZFC.SetTheory.Definitional.Project.Predicate
import YesMetaZFC.SetTheory.Definitional.Project.ClosedEnv

/-! # 无参数内部 OD 类及公开接口

公开定义固定 Kuratowski 编码，不携带外部公式族或模型公理证明。ZF 用于证明
它与通常的序数可定义性等价；原公式解释与相对化本身只需相应的语义条件。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def od_s : UnarySchema 0 := { body := od_in_m (𝒞 := kpair_convention_l) .newest }

def Od_d (x : M.Domain) : Prop := od_s.denote (⟨Fin.elim0, fun _ => x⟩ : Env M 0) x

def od_m {d} (x : Term d) : Formula 1 d := pred_m od_s Fin.elim0 x
derive_free_closed od_m

theorem od_denote_l (ρ : Env M 0) (x : M.Domain) : od_s.denote ρ x ↔ Od_d x :=
  Formula.closed_env_l _ od_s.freeClosed (funext (Fin.cases rfl (fun i => Fin.elim0 i)))

theorem od_sat_l {d} (ρ : Env M d) (x : Term d) : Formula.satisfies ρ (od_m x) ↔ Od_d (x.eval ρ) :=
  (pred_sat_l M od_s ρ Fin.elim0 x).trans (od_denote_l _ _)

theorem od_internal_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {x} :
    Od_d x ↔ Od_in_d I x := od_in_sat_l I hE _ _

/-- 任意 ZF 模型中的内部 OD，恰为原语言序数参数唯一可定义的对象。 -/
theorem od_iff_external_l (hZF : M.Models ZF) {x : M.Domain} : Od_d x ↔ Od_ext_d x := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  exact (od_internal_l I hZF.1).trans (od_in_iff_external_l I hZF)

theorem od_in_iff_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF) {x} :
    Od_in_d I x ↔ Od_d x := (od_in_iff_external_l I hZF).trans (od_iff_external_l hZF).symm

theorem od_of_unique_l (hZF : M.Models ZF) {d} (φ : UnarySchema d) (ρ : Env M d)
    (hρ : ∀ i, M.IsOrdinal (ρ.bound i)) {x} (hx : ∀ y, φ.denote ρ y ↔ y = x) : Od_d x :=
  (od_iff_external_l hZF).mpr ⟨d, φ, ρ, hρ, hx⟩

theorem od_ordinal_l (hZF : M.Models ZF) {x} (hx : M.IsOrdinal x) : Od_d x := by
  let φ : UnarySchema 1 := { body := Formula.extensionalEq .newest (.bound 1) }
  exact od_of_unique_l hZF φ (⟨fun _ => x, fun _ => x⟩ : Env M 1) (fun _ => hx)
    (fun y => Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _)

theorem od_parameter_free_l (hZF : M.Models ZF) (φ : UnarySchema 0) (ρ : Env M 0)
    {x} (hx : ∀ y, φ.denote ρ y ↔ y = x) : Od_d x :=
  od_of_unique_l hZF φ ρ (fun i => Fin.elim0 i) hx

/-- 单序数解码关系的值域恰为公开 OD 类，供后续规范代表与良序使用。 -/
theorem od_code_range_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF) {x} :
    Od_d x ↔ ∃ q, Od_eval_d I q x := (od_in_iff_l I hZF).symm.trans (od_eval_range_l I hZF)

/-- OD 与任意集合的交仍是模型内的实际集合。 -/
theorem od_separation_l (hZF : M.Models ZF) (A : M.Domain) :
    ∃ B, ∀ x, M.mem x B ↔ M.mem x A ∧ Od_d x := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => A⟩
  obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF od_s ρ A
  exact ⟨B, fun x => (hB x).trans (and_congr_right fun _ => od_denote_l ρ x)⟩

/-- 原 OD 公式可在内部传递集合结构中统一相对化；不假定其 OD 与背景 OD 相同。 -/
theorem od_rel_sat_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) {c X R}
    (hM : Internal.Smem_d I c X R) (hT : M.TransitiveSet X) {d} (ρ : Env M d) (T t : Term d)
    (x : (Internal.smdl_structure_l I (R := R) hM.1.2.1).Domain)
    (hX : T.eval ρ = X) (hx : t.eval ρ = x.val) :
    Formula.satisfies ρ (lr_rel_m od_s.body T (fun _ => t)) ↔ Od_d x := by
  let η : Env (Internal.smdl_structure_l I (R := R) hM.1.2.1) 0 := ⟨Fin.elim0, fun _ => x⟩
  exact lr_rel_decode_l I hM.1 hM.2 hT od_s.body od_s.freeClosed (η.push x) ρ T (fun _ => t)
    hX (Fin.cases hx (fun i => Fin.elim0 i))

end YesMetaZFC.SetTheory.InnerModel
