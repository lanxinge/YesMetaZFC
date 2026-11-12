import YesMetaZFC.Model.SetTheory.Relations.Ultrafilter
import YesMetaZFC.Model.SetTheory.Types.PointwiseWitness

/-! # 原关系源全部内部公式码的精确坐标真值集 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rc_full_trace_l {ω c' Y S D d t P E z n F r a : M.Domain}
    (hω : M.IsOmega ω) (model : Smdl_d I c' Y S) (ext : Rf_ext_d I Y S)
    (theory : Sc_theory_d I ω Y S)
    (hd : M.mem d Y) (ft : Fn0_d D Y t) (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d S)
    (hP : Rt_source_d I Y S D t P) (hE : M.IsFunctionSpace I E ω Y)
    (code : Sformula_d I ω z n F r) (ha : M.mem a E) (repr : Pe_repr_d I ω d Y S a) :
    ∃ A, M.mem A P ∧ ∀ s x, Rd_entry_d s x t →
      (M.mem s A ↔ ∃ f, M.mem f E ∧ Pe_assign_d I ω d Y S a f x ∧ Satisfies_d I ω c' z f) := by
  obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω code.2.1
  have bw := hω.transitive (ZF.modelsKP hZF) b hb
  have context := sc_pe_context_l I model ext (theory.algebra model.2.1) hd hE
  obtain ⟨B, hB, truth⟩ := sc_pe_trace_raw_l hZF hω context theory code.2.1 code.2.2 hb bound ha
    (fun i f hi hf => repr i f (bw i hi) hf)
  obtain ⟨A, trace⟩ := rt_trace_exists_l I hZF D t S B
  obtain ⟨hA, read⟩ := hP.pointwise_l I (fn0_function_l (ZF.modelsKP hZF) ft) domain hB trace truth
  refine ⟨A, hA, fun s x hsx => (read s x hsx).trans ?_⟩
  apply (pe_sat_full_l I hZF ext hE code.2.1 bound bw code.2.2 ha repr (ft.bound_l hsx).2 (domain s x hsx)).trans
  exact exists_congr fun f => and_congr_right fun _ => and_congr_right fun _ =>
    (satisfies_decode_l I hZF.1 model code hE).symm

end YesMetaZFC.SetTheory.Internal
