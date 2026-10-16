import YesMetaZFC.Model.SetTheory.Internal.RelationRelative
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 原公式定义的实际二元关系

在指定原始关系模型内解释原公式，由背景分离构造其实际关系图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def sr_pair_env_l {N : Structure} (x y : N.Domain) : Env N 2 :=
  ⟨Fin.cases y (fun _ => x), fun _ => x⟩

theorem smdl_formula_relation_l {c X R : M.Domain} (hm : Smdl_d I c X R)
    (φ : Formula 1 2) (hc : φ.FreeClosed) :
    ∃ Q, M.IsSetRelationOn I Q X ∧ ∀ x y : (smdl_structure_l I (R := R) hm.2.1).Domain,
      Rd_entry_d x.val y.val Q ↔ Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := R) hm.2.1) x y) φ := by
  let ψ : BinarySchema 2 := {
    body := rr_rel_m kpair_convention_l φ (.bound 2) (.bound 3) (Fin.cases .newest (fun _ => .bound 1))
    freeClosed := rr_rel_closed_l kpair_convention_l φ hc _ _ _ rfl rfl (Fin.cases rfl (fun _ => rfl)) }
  let ρ : Env M 2 := ⟨Fin.cases X (fun _ => R), fun _ => X⟩
  obtain ⟨Q, hQ, spec⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ρ X
  refine ⟨Q, hQ, fun x y => ?_⟩
  exact (spec x.val y.val).trans ((and_iff_right x.property).trans ((and_iff_right y.property).trans
    (rr_rel_sat_l I hm.2.1 φ hc (sr_pair_env_l (N := smdl_structure_l I (R := R) hm.2.1) x y)
      ((ρ.push x.val).push y.val) (.bound 2) (.bound 3) _ rfl rfl (Fin.cases rfl (fun _ => rfl)))))

end YesMetaZFC.SetTheory.Internal
