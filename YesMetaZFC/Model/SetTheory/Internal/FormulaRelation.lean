import YesMetaZFC.Model.SetTheory.LevyReflection.Decode
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 原公式定义的实际二元关系

在指定传递载体内解释量词，由背景分离构造关系图；原公式保持原 AST。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def sr_pair_env_l {N : Structure} (x y : N.Domain) : Env N 2 :=
  ⟨Fin.cases y (fun _ => x), fun _ => x⟩

theorem smem_formula_relation_l {c X R : M.Domain} (hm : Smem_d I c X R)
    (hX : M.TransitiveSet X) (φ : Formula 1 2) (hc : φ.FreeClosed) :
    ∃ Q, M.IsSetRelationOn I Q X ∧ ∀ x y : (smdl_structure_l I (R := R) hm.1.2.1).Domain,
      Rd_entry_d x.val y.val Q ↔ Formula.satisfies (sr_pair_env_l (N := smdl_structure_l I (R := R) hm.1.2.1) x y) φ := by
  let ψ : BinarySchema 1 := {
    body := lr_rel_m φ (.bound 2) (Fin.cases .newest (fun _ => .bound 1))
    freeClosed := lr_rel_closed_l φ hc _ _ rfl (Fin.cases rfl (fun _ => rfl)) }
  let ρ : Env M 1 := ⟨fun _ => X, fun _ => X⟩
  obtain ⟨Q, hQ, spec⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ρ X
  refine ⟨Q, hQ, fun x y => ?_⟩
  exact (spec x.val y.val).trans ((and_iff_right x.property).trans ((and_iff_right y.property).trans
    (lr_rel_decode_l I hm.1 hm.2 hX φ hc (sr_pair_env_l (N := smdl_structure_l I (R := R) hm.1.2.1) x y)
      ((ρ.push x.val).push y.val) (.bound 2) _ rfl (Fin.cases rfl (fun _ => rfl)))))

end YesMetaZFC.SetTheory.Internal
