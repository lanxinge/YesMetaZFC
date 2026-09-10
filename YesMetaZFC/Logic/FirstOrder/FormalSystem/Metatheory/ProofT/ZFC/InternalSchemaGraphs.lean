import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalHornRanking
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaReflectionPlans

/-! # 模式查询所用递归图的内部正反射 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceTraceComposition
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem schema_body_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step SchemaObjectGraph.Body.rules) root) :
    HornProv 𝒩 SchemaObjectGraph.Body.rules root :=
  horn_valid_positive h𝒩 _ _ SchemaReflectionPlans.body_valid hr hg

theorem schema_rename_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step SchemaObjectGraph.Rename.rules) root) :
    HornProv 𝒩 SchemaObjectGraph.Rename.rules root :=
  horn_valid_positive h𝒩 _ _ SchemaReflectionPlans.rename_valid hr hg

theorem schema_table_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step (ObjectRangeTable.rules SchemaTable.program)) root) :
    HornProv 𝒩 (ObjectRangeTable.rules SchemaTable.program) root :=
  horn_valid_positive h𝒩 _ _ SchemaReflectionPlans.table_valid hr hg

theorem iteration_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step ObjectUnaryIteration.rules) root) :
    HornProv 𝒩 ObjectUnaryIteration.rules root :=
  horn_valid_positive h𝒩 _ _ ObjectHornRanking.iteration_valid hr hg

theorem project_quotation_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step ObjectProjectQuotation.rules) root) :
    HornProv 𝒩 ObjectProjectQuotation.rules root :=
  horn_valid_positive h𝒩 _ _ ObjectHornRanking.project_valid hr hg

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
