import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceSyntax

/-! # 源代表赋值的实际商投影

每个坐标已有一个源内代表，只需读取既有商投影。唯一值收集生成完整商赋值，
不在等价类中重新选择代表，也不要求背景的全部函数属于源。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rs_eval_exists_l (hZF : M.Models ZF) {ω D X U G p C E a}
    (hX : M.TransitiveSet X) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d D X g)
    (hp : Rp_map_d I D X U G p C) (hE : M.IsFunctionSpace I E ω X)
    (ha : M.mem a E) (hr : Pe_repr_d I ω D X a) :
    ∃ e, M.IsSetFunctionFromTo I e ω C ∧ Rs_eval_d I ω D X p a e := by
  let ρ : Env M 2 := ⟨Fin.cases a (fun _ => p), fun _ => a⟩
  let φ : BinarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 4))) }
  have sat i B : φ.denote ρ i B ↔ ∃ g, M.PairMember I i g a ∧ M.PairMember I g B p := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  have hA := (hE a).mp ha
  obtain ⟨e, he, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := C)
    (fun i hi => by
      obtain ⟨g, _, hg⟩ := hA.2.2 i hi
      have hf := hr i g hi hg
      obtain ⟨B, _, hB⟩ := hp.projection.2.2 g ((hG g).mpr ⟨hf.1, hf.function_l hX⟩)
      exact ⟨B, (sat i B).mpr ⟨g, hg, hB⟩⟩)
    (fun i _ B C hB hC => by
      obtain ⟨g, hg, hBg⟩ := (sat i B).mp hB
      obtain ⟨f, hf, hCf⟩ := (sat i C).mp hC
      exact hp.projection.1.2 g B C hBg (hA.1.2 i f g hf hg ▸ hCf))
    (fun i B _ hB => ((sat i B).mp hB).elim fun _ hg => hp.projection.output_mem_of_pairMember hg.2)
  refine ⟨e, he, fun i hi => ?_⟩
  obtain ⟨B, _, hB⟩ := he.2.2 i hi
  obtain ⟨g, hg, hgp⟩ := (sat i B).mp ((spec i B).mp hB).2
  exact ⟨g, B, hg, hr i g hi hg, hgp, hB⟩

end YesMetaZFC.SetTheory.Internal
