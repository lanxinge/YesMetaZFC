import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 实际函数图更换有序对约定

只重编码图的有序对，不改变定义域、值或逐点方程。两种约定都须已有实际解释。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 𝒟 : OrderedPairConvention}
  (I : 𝒞.Interpretation M) (J : 𝒟.Interpretation M)

theorem fn_recode_l (hZF : M.Models ZF) {A B F : M.Domain}
    (h : M.IsSetFunctionFromTo I F A B) : ∃ G, M.IsSetFunctionFromTo J G A B ∧
      ∀ x y, M.PairMember J x y G ↔ M.PairMember I x y F := by
  let φ : BinarySchema 1 := { body := Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  have read x y : φ.denote ρ x y ↔ M.PairMember I x y F :=
    Formula.satisfies_orderedPairMem_iff I ..
  obtain ⟨G, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF J φ ρ
    (fun x hx => (h.2.2 x hx).imp fun y hy => (read x y).mpr hy.2)
    (fun x _ y z hy hz => h.1.2 x y z ((read x y).mp hy) ((read x z).mp hz))
    (fun x y _ hy => h.output_mem_of_pairMember ((read x y).mp hy))
  exact ⟨G, fn, fun x y => (graph x y).trans ⟨fun h => (read x y).mp h.2,
    fun hy => ⟨h.input_mem_of_pairMember hy, (read x y).mpr hy⟩⟩⟩

end YesMetaZFC.SetTheory
