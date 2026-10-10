import YesMetaZFC.Model.SetTheory.Internal.FiniteEvaluationSyntax
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax

/-! # 有限真值证书与原满足关系的双向对应

有界证书精确恢复原递归图；它不是一份额外假定正确的真值表。
合法程序在有限赋值空间上的实际求值给出证书，证书也唯一决定所有行。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem fv_arg_l (hKP : M.Models KP) {b A R E n C H f i j : M.Domain}
    (hE : M.IsFunctionSpace (kp_pair_l hKP) E b A) (hf : M.mem f E) (hi : M.mem i b)
    (hH : Fn0_d n C H) (rows : ∀ r Y, Rd_entry_d r Y H → M.MemberSubset Y E) (k : Nat) :
    Fv_arg_d k b A R E C H f i j ↔ Sarg_d (kp_pair_l hKP) k A R H f i j := by
  have fn := (hE f).mp hf
  rcases k with _ | (_ | (_ | k))
  · exact ⟨fun ⟨x, _, y, _, hx, hy, h⟩ => ⟨x, y, hx, hy, h⟩,
      fun ⟨x, y, hx, hy, h⟩ => ⟨x, fn.output_mem_of_pairMember hx, y, fn.output_mem_of_pairMember hy, hx, hy, h⟩⟩
  · exact ⟨fun ⟨x, _, hx, hy⟩ => ⟨x, hx, hy⟩,
      fun ⟨x, hx, hy⟩ => ⟨x, fn.output_mem_of_pairMember hx, hx, hy⟩⟩
  · exact ⟨fun ⟨Y, _, Z, _, hY, hZ, h⟩ => ⟨Y, Z, hY, hZ, h⟩,
      fun ⟨Y, Z, hY, hZ, h⟩ => ⟨Y, (hH.bound_l hY).2, Z, (hH.bound_l hZ).2, hY, hZ, h⟩⟩
  · exact ⟨fun ⟨Y, _, hY, x, hx, g, _, hg, h⟩ =>
      ⟨Y, hY, x, g, hx, (se_update0_l hKP (fn0_of_function_l hKP fn) hi hx).mp hg, h⟩,
      fun ⟨Y, hY, x, g, hx, hg, h⟩ => ⟨Y, (hH.bound_l hY).2, hY, x, hx, g, rows j Y hY g h,
        (se_update0_l hKP (fn0_of_function_l hKP fn) hi hx).mpr hg, h⟩⟩

theorem fv_node_l (hKP : M.Models KP) {b A R E n C H c f r : M.Domain}
    (hE : M.IsFunctionSpace (kp_pair_l hKP) E b A) (hf : M.mem f E) (hc : Fb_node_d hKP b r c)
    (hH : Fn0_d n C H) (rows : ∀ r Y, Rd_entry_d r Y H → M.MemberSubset Y E) :
    Fv_node_d hKP b A R E C H c f ↔ Snode_d (kp_pair_l hKP) A R H c f := by
  refine ⟨fun ⟨k, i, hi, j, _, hs, h⟩ => ⟨k, i, j, hs, (fv_arg_l hKP hE hf hi hH rows k.val).mp h⟩, ?_⟩
  rintro ⟨k, i, j, hs, h⟩
  obtain ⟨hi, hj⟩ := hc.operands_l hKP hs
  exact ⟨k, i, hi, j, hj, hs, (fv_arg_l hKP hE hf hi hH rows k.val).mpr h⟩

theorem fv_eval_of_l (hZF : M.Models ZF) {ω b A R E n L F C H : M.Domain}
    (hω : M.IsOmega ω) (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F)
    (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E b A)
    (hH : Seval_d (kp_pair_l (ZF.modelsKP hZF)) A R E F n H) (fn : Fn0_d n C H) :
    Fv_eval_d (ZF.modelsKP hZF) b A R E n L F C H := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hF := (program.read_l hZF hω).1
  have rows r Y (hY : Rd_entry_d r Y H) : M.MemberSubset Y E := by
    obtain ⟨c, hc⟩ := (hF.2.1.2.2 r).mp (fn.bound_l hY).1
    exact fun f hf => ((seval_row_l I hZF hF hH hc hY f).mp hf).1
  refine ⟨fn, fun r hr c hc Y _ hrc hrY => ⟨rows r Y hrY, fun f hf => ?_⟩⟩
  exact (seval_row_l I hZF hF hH hrc hrY f).trans ((and_iff_right hf).trans
    (fv_node_l (ZF.modelsKP hZF) hE hf (program.2.2.2 r hr c hc hrc) fn rows).symm)

theorem Fv_eval_d.seval_l (hZF : M.Models ZF) {ω b A R E n L F C H : M.Domain}
    (hω : M.IsOmega ω) (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F)
    (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E b A)
    (h : Fv_eval_d (ZF.modelsKP hZF) b A R E n L F C H) :
    Seval_d (kp_pair_l (ZF.modelsKP hZF)) A R E F n H := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hF := (program.read_l hZF hω).1
  have rows r Y (hY : Rd_entry_d r Y H) : M.MemberSubset Y E := by
    obtain ⟨c, hc, hrc⟩ := program.2.2.1.2.1 r (h.1.bound_l hY).1
    exact (h.2 r (h.1.bound_l hY).1 c hc Y (h.1.bound_l hY).2 hrc hY).1
  have fn := fn0_function_l (ZF.modelsKP hZF) h.1
  refine ⟨⟨hF.2.1.1, fn.1, fn.2.1⟩, fun r hr Y hrY => ?_⟩
  obtain ⟨c, hc, hrc⟩ := program.2.2.1.2.1 r hr
  obtain ⟨P, hP⟩ := ZF.exists_restriction hZF I H r
  have dom := (hP.isSetFunctionFromTo fn (hF.2.1.1.transitive r hr)).2.1
  have node := h.2 r hr c hc Y (h.1.bound_l hrY).2 hrc hrY
  refine ⟨P, hP, fun f => ?_⟩
  have read : M.mem f Y ↔ M.mem f E ∧ Snode_d I A R H c f :=
    ⟨fun hf => ⟨node.1 f hf, (fv_node_l (ZF.modelsKP hZF) hE (node.1 f hf)
      (program.2.2.2 r hr c hc hrc) h.1 rows).mp ((node.2 f (node.1 f hf)).mp hf)⟩,
      fun ⟨hf, ht⟩ => (node.2 f hf).mpr ((fv_node_l (ZF.modelsKP hZF) hE hf
        (program.2.2.2 r hr c hc hrc) h.1 rows).mpr ht)⟩
  apply read.trans
  apply and_congr_right
  intro _
  refine ⟨fun ht => ⟨r, c, dom, hrc, (snode_restrict_l I (ZF.modelsKP hZF) (hF.2.2 r c hrc) hP f).mpr ht⟩, ?_⟩
  rintro ⟨k, d, hd, hkd, ht⟩
  have eq := hd.eq hZF.1 dom
  subst k
  have eq := hF.2.1.2.1.2 r d c hkd hrc
  subst d
  exact (snode_restrict_l I (ZF.modelsKP hZF) (hF.2.2 r c hrc) hP f).mp ht

theorem fv_space_l (hKP : M.Models KP) {ω b A J E : M.Domain} (hb : M.mem b ω)
    (hJ : Fseq_space_d (kp_pair_l hKP) ω A J) : Fv_space_d b A J E ↔ M.IsFunctionSpace (kp_pair_l hKP) E b A := by
  refine ⟨fun h f => ⟨fun hf => fn0_function_l hKP ((h.2 f (h.1 f hf)).mp hf), fun hf =>
    (h.2 f ((hJ f).mpr ⟨b, hb, hf⟩)).mpr (fn0_of_function_l hKP hf)⟩, fun h => ⟨?_, ?_⟩⟩
  · exact fun f hf => (hJ f).mpr ⟨b, hb, (h f).mp hf⟩
  · exact fun f _ => (h f).trans ⟨fn0_of_function_l hKP, fn0_function_l hKP⟩

theorem Fv_eval_d.truth_l (hZF : M.Models ZF) {ω b A R E n L F C H r f : M.Domain}
    (hω : M.IsOmega ω) (program : Fb_program_d (ZF.modelsKP hZF) ω b n L F)
    (hE : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) E b A)
    (h : Fv_eval_d (ZF.modelsKP hZF) b A R E n L F C H) (hr : M.mem r n) :
    Fv_at_d C H r f ↔ Ssat_d (kp_pair_l (ZF.modelsKP hZF)) A R E F n r f := by
  obtain ⟨Y, hY, hrY⟩ := h.1.2.1 r hr
  refine Iff.trans ?_ (ssat_value_l _ hZF (h.seval_l hZF hω program hE) hrY f).symm
  exact ⟨fun ⟨Y', hY', hrY', hf⟩ => h.1.2.2 r hr Y' hY' Y hY hrY' hrY ▸ hf,
    fun hf => ⟨Y, hY, hrY, hf⟩⟩

end YesMetaZFC.SetTheory.Internal
