import YesMetaZFC.Model.SetTheory.Countable
import YesMetaZFC.Model.SmallGraph.ZFC

/-! # 原小图 ZFC 模型的可数地模型实例 -/

namespace YesMetaZFC.SetTheory
/-- 原小图 ZFC 模型的可数初等子模型，保留其外部良基性。 -/
theorem countable_ground_l : ∃ M : SetTheory.Structure.{1}, M.Models ZFC ∧
    _root_.WellFounded M.mem ∧ ∃ e : Nat → M.Domain, Function.Surjective e := by
  obtain ⟨a⟩ := (Model.SmallGraph.sg_model.{0}).nonempty .set
  obtain ⟨A, hA, _, e, he⟩ := countable_elementary_l Model.SmallGraph.sg_model.{0} (fun _ => a)
  let M := Definitional.Project.FirstOrderSemantics.reduct A.structure_m
  have hM := Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureModel.project_models
    ((A.models_iff_m hA _).mpr Model.SmallGraph.sg_models_zfc)
  refine ⟨M, hM, ?_, e, he⟩
  exact InvImage.wf (fun x : A.structure_m.Carrier .set => x.1) Model.SmallGraph.SG_set.mem_wf


end YesMetaZFC.SetTheory
