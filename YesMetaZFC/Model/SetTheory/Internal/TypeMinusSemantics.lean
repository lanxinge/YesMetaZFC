import YesMetaZFC.Model.SetTheory.Internal.TypeMinusCode

/-! # 向前一秩层限制的语义

最大集合代码使新绑定的载体唯一等于指定小载体；限制证书随后恢复
原程序的真值；类型查询仍只使用原来的参数赋值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Sr_minus_d.correct_l (hZF : M.Models ZF) {ω F n r G m u c X R d Y S E D f : M.Domain}
    (hω : M.IsOmega ω) (hF : Sfm_d I ω n F) (h : Sr_minus_d I ω F n r G m u)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hY : M.TransitiveSet Y) (top : Sr_top_d Y X)
    (hE : M.IsFunctionSpace I E ω X) (hD : M.IsFunctionSpace I D ω Y) (hf : M.mem f E) :
    Ssat_d I X R E F n r f ↔ Ssat_d I Y S D G m u f := by
  obtain ⟨b, T, v, w, t, hb, bound, state, hrv, topcode, conj, cu, hcu, op⟩ := h
  have sub := hY X top.1
  have context := sr_context_l I hm hn sub top.1 hE hD
  have row := state.correct_l I hZF hF bound context (state.map.input_mem_of_pairMember hrv) hrv
  have ff := (hE f).mp hf
  have fg : M.IsSetFunctionFromTo I f ω Y := ⟨ff.1, ff.2.1, fun i hi =>
    (ff.2.2 i hi).imp fun x hx => ⟨sub x hx.1, hx.2⟩⟩
  have hg := (hD f).mpr fg
  obtain ⟨H, hH⟩ := seval_exists_l I hZF Y S D G state.program.2.1.1
  have read Z g (hZ : M.mem Z Y) (update : Senv_update_d I f b Z g) :
      Ssat_d I Y S D G m t g ↔ Sr_top_d Y Z ∧ Ssat_d I Y S D G m v g := by
    have hg := (hD g).mpr (update.function_l I fg hb hZ)
    exact (conj.correct_l I hZF state.program hg).trans (and_congr
      (topcode.correct_l I hZF hω state.program hn hY hD hg ((update.2 b Z).mpr (Or.inl ⟨rfl, rfl⟩))) Iff.rfl)
  rw [ssat_exists_l I hZF state.program hH hcu op hg]
  constructor
  · intro truth
    obtain ⟨g, update, fn⟩ := senv_update_exists_l I hZF fg hb top.1
    have agree := update.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    exact ⟨X, g, top.1, update, (read X g top.1 update).mpr
      ⟨top, (row f g hf ((hD g).mpr fn) ((update.2 b X).mpr (Or.inl ⟨rfl, rfl⟩)) agree).mp truth⟩⟩
  · rintro ⟨Z, g, hZ, update, truth⟩
    obtain ⟨top', truth'⟩ := (read Z g hZ update).mp truth
    have eq := top'.unique_l hZF.1 top
    subst Z
    exact (row f g hf ((hD g).mpr (update.function_l I fg hb top.1))
      ((update.2 b X).mpr (Or.inl ⟨rfl, rfl⟩)) (update.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) b))).mpr truth'

/-- 自动构造两边的赋值空间，把同一语法证书接回统一满足关系。 -/
theorem Sr_minus_d.satisfies_l (hZF : M.Models ZF) {ω F n r G m u c X R d Y S a a' f : M.Domain}
    (hω : M.IsOmega ω) (h : Sr_minus_d I ω F n r G m u)
    (ha : Sformula_d I ω a n F r) (ha' : Sformula_d I ω a' m G u)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hY : M.TransitiveSet Y) (top : Sr_top_d Y X)
    (hf : M.IsSetFunctionFromTo I f ω X) : Satisfies_d I ω c a f ↔ Satisfies_d I ω d a' f := by
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I ω Y
  exact (satisfies_decode_l I hZF.1 hm.1 ha hE).trans
    ((h.correct_l I hZF hω ha.2.1 hm hn hY top hE hD ((hE f).mpr hf)).trans
      (satisfies_decode_l I hZF.1 hn.1 ha' hD).symm)

theorem sr_minus_formula_l (hZF : M.Models ZF) {ω a n F r : M.Domain} (hω : M.IsOmega ω)
    (ha : Sformula_d I ω a n F r) : ∃ a' m G u, Sformula_d I ω a' m G u ∧ Sr_minus_d I ω F n r G m u := by
  obtain ⟨m, G, u, h⟩ := sr_minus_build_l I hZF hω ha.2.1 ha.2.2
  obtain ⟨a', code⟩ := I.total G u
  have shape := h.program_l I
  exact ⟨a', m, G, u, ⟨code, shape.1, shape.2⟩, h⟩

end YesMetaZFC.SetTheory.Internal
