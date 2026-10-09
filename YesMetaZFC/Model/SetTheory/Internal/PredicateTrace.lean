import YesMetaZFC.Model.SetTheory.Internal.PredicateSource

/-! # 谓词截面的初等像

截面由集合分离实际生成。扩张语言的全称公式把它的定义送到目标载体的
全部元素，因而也控制不在嵌入像中的新参数；逐点谓词保持不足以代替这一步。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 若 t=A∩D，则 j(t)=B∩j(D)；右侧量化目标中的全部对象。 -/
theorem spred_trace_l (hZF : M.Models ZF) {ω X A Y B j D D' t t' : M.Domain}
    (hω : M.IsOmega ω) (h : Spred_emb_d I ω X A Y B j)
    (hY : M.TransitiveSet Y)
    (hD : M.PairMember I D D' j) (ht : M.PairMember I t t' j)
    (trace : ∀ x, M.mem x t ↔ M.mem x D ∧ M.mem x A) :
    ∀ y, M.mem y t' ↔ M.mem y D' ∧ M.mem y B := by
  obtain ⟨c, R, d, S, hx, hy, hj⟩ := h
  let φ : Formula 1 2 := .forallE (.iff
    (.conj (.mem .newest (.bound 1)) (.neg (.mem (.bound 1) .newest)))
    (.conj (.conj (.mem .newest (.bound 2)) (.neg (.mem (.bound 2) .newest)))
      (.mem .newest .newest)))
  let D₀ : (smdl_structure_l I (R := R) hx.1.2.1).Domain := ⟨D, hj.1.1.input_mem_of_pairMember hD⟩
  let t₀ : (smdl_structure_l I (R := R) hx.1.2.1).Domain := ⟨t, hj.1.1.input_mem_of_pairMember ht⟩
  let D₁ : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨D', hj.1.1.output_mem_of_pairMember hD⟩
  let t₁ : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨t', hj.1.1.output_mem_of_pairMember ht⟩
  have tr := smap_source_l I hZF hω hx.1 hy.1 hj φ (by simp [φ, Definitional.Formula.FreeClosed])
    ⟨Fin.cases t₀ (fun _ => D₀), fun _ => t₀⟩ ⟨Fin.cases t₁ (fun _ => D₁), fun _ => t₁⟩
    (Fin.cases ht (fun _ => hD))
  simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff] at tr
  have read (x : (smdl_structure_l I (R := R) hx.1.2.1).Domain) :=
    (spred_mem_l I (ZF.modelsKP hZF) hx x.property t₀.property).trans ((trace x.val).trans
      (and_congr (spred_mem_l I (ZF.modelsKP hZF) hx x.property D₀.property).symm
        (spred_read_l I (ZF.modelsKP hZF) hx x.val x.val).1.symm))
  have target := tr.mp read
  intro y
  have owned : M.mem y t' ∨ M.mem y D' → M.mem y Y :=
    fun hh => hh.elim (hY t' t₁.property y) (hY D' D₁.property y)
  constructor
  · intro hy'
    let y' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨y, owned (Or.inl hy')⟩
    have hh := (target y').mp ((spred_mem_l I (ZF.modelsKP hZF) hy y'.property t₁.property).mpr hy')
    exact ⟨(spred_mem_l I (ZF.modelsKP hZF) hy y'.property D₁.property).mp hh.1,
      (spred_read_l I (ZF.modelsKP hZF) hy y y).1.mp hh.2⟩
  · rintro ⟨hyD, hyB⟩
    let y' : (smdl_structure_l I (R := S) hy.1.2.1).Domain := ⟨y, owned (Or.inr hyD)⟩
    exact (spred_mem_l I (ZF.modelsKP hZF) hy y'.property t₁.property).mp ((target y').mpr
      ⟨(spred_mem_l I (ZF.modelsKP hZF) hy y'.property D₁.property).mpr hyD,
        (spred_read_l I (ZF.modelsKP hZF) hy y y).1.mpr hyB⟩)

end YesMetaZFC.SetTheory.Internal
