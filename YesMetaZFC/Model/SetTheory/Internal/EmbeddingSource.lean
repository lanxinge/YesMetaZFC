import YesMetaZFC.Model.SetTheory.Internal.PredicateEmbedding
import YesMetaZFC.Model.SetTheory.Internal.Compiler

/-! # 内部嵌入对原公式的实际作用

先给原公式构造内部码与有限参数赋值，再沿实际嵌入复合赋值图。
两边读取同一内部码，故全内部初等性直接给出逐公式保持，无额外语义合同。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem smap_source_l (hZF : M.Models ZF) {ω c d X Y R S j} (hω : M.IsOmega ω)
    (hX : Smdl_d I c X R) (hY : Smdl_d I d Y S) (hj : Smap_d I ω c d X Y j) {n}
    (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) hX.2.1) n)
    (η : Env (smdl_structure_l I (R := S) hY.2.1) n)
    (hp : ∀ i, M.PairMember I (ρ.bound i).val (η.bound i).val j) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨a, l, F, k, v, ha, hv, hc⟩ := source_compile_l I hZF hω φ hφ
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I ω Y
  have hi : Function.Injective v := fun i r h => Fin.ext
    (num_injective_l (ZF.modelsKP hZF) (hv i) (h.symm ▸ hv r))
  obtain ⟨f, hf, hρ⟩ := senv_params_l I hZF hE hX.2.1 v (fun i => (ρ.bound i).val)
    hi (fun i => num_mem_l hZF.1 hω (hv i)) (fun i => (ρ.bound i).property)
  obtain ⟨g, hg, hfg⟩ := smap_assign_exists_l I hZF hj.1.1 ((hE f).mp hf)
  have hη i := hfg (v i) (num_mem_l hZF.1 hω (hv i)) (ρ.bound i).val (η.bound i).val (hρ i) (hp i)
  obtain ⟨C, hC, ht⟩ := hj.2
  exact ((satisfies_decode_l I hZF.1 hX ha hE).trans (hc X R hX.2.1 E hE f hf ρ hρ)).symm.trans
    ((ht a f g ((hC a).mpr ⟨l, F, k, ha⟩) ((hE f).mp hf) hg hfg).trans
      ((satisfies_decode_l I hZF.1 hY ha hD).trans (hc Y S hY.2.1 D hD g ((hD g).mpr hg) η hη)))

end YesMetaZFC.SetTheory.Internal
