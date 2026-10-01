import YesMetaZFC.Model.SetTheory.Internal.Elementary
import YesMetaZFC.Model.SetTheory.Internal.Compiler

/-! # 完整内部初等性的原公式调用

将同一个原公式编译一次，在子结构中构造共同的参数赋值图，再分别解码两边
满足关系。存在见证因此确实落在内部子集，而不是外部选择出的较小模型。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 全内部初等性蕴含原生产公式的逐参数保持；两边使用同一组实际模型对象。 -/
theorem selem_source_l (hZF : M.Models ZF) {ω c d X R N S} (hω : M.IsOmega ω)
    (hS : Ssub_d I c d X R N S) (h : Selem_d I ω c d) {n}
    (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (ρ : Env (smdl_structure_l I (R := R) hS.source.2.1) n)
    (η : Env (smdl_structure_l I (R := S) hS.target.2.1) n)
    (hρη : ∀ i, (ρ.bound i).val = (η.bound i).val) : Formula.satisfies ρ φ ↔ Formula.satisfies η φ := by
  obtain ⟨a, l, F, k, v, ha, hv, hc⟩ := source_compile_l I hZF hω φ hφ
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I ω N
  have hi : Function.Injective v := fun i j hij => Fin.ext
    (num_injective_l (ZF.modelsKP hZF) (hv i) (hij.symm ▸ hv j))
  obtain ⟨f, hf, hp⟩ := senv_params_l I hZF hD hS.target.2.1 v (fun i => (η.bound i).val)
    hi (fun i => num_mem_l hZF.1 hω (hv i)) (fun i => (η.bound i).property)
  have hfN := (hD f).mp hf
  have hfX := (hE f).mpr (hfN.mono_target_l I hS.subset)
  have hX := (satisfies_decode_l I hZF.1 hS.source ha hE).trans
    (hc X R hS.source.2.1 E hE f hfX ρ (fun i => hρη i ▸ hp i))
  have hN := (satisfies_decode_l I hZF.1 hS.target ha hD).trans
    (hc N S hS.target.2.1 D hD f hf η hp)
  exact hX.symm.trans (((selem_decode_l I hZF.1 hS hC).mp h a f
    ((hC a).mpr ⟨l, F, k, ha⟩) hfN).trans hN)

/-- 原存在公式的实际见证回到 N，同时保持其在大结构中的原公式真值。 -/
theorem selem_witness_l (hZF : M.Models ZF) {ω c d X R N S} (hω : M.IsOmega ω)
    (hS : Ssub_d I c d X R N S) (h : Selem_d I ω c d) {n} (φ : UnarySchema n)
    (ρ : Env (smdl_structure_l I (R := R) hS.source.2.1) n)
    (η : Env (smdl_structure_l I (R := S) hS.target.2.1) n)
    (hρη : ∀ i, (ρ.bound i).val = (η.bound i).val)
    (he : ∃ x, φ.denote ρ x) : ∃ x : {x // M.mem x N},
      φ.denote ρ ⟨x.val, hS.subset x.val x.property⟩ := by
  have he' := (selem_source_l I hZF hω hS h (.existsE φ.body)
    (by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed) ρ η hρη).mp
    ((Formula.satisfies_exists_iff ρ φ.body).mpr he)
  obtain ⟨x, hx⟩ := (Formula.satisfies_exists_iff η φ.body).mp he'
  exact ⟨x, (selem_source_l I hZF hω hS h φ.body φ.freeClosed
    (ρ.push ⟨x.val, hS.subset x.val x.property⟩) (η.push x) (Fin.cases rfl hρη)).mpr hx⟩

/-- 两个存在见证依次回拉，保持其在大结构中的同一二元原公式。 -/
theorem selem_binary_witness_l (hZF : M.Models ZF) {ω c d X R N S} (hω : M.IsOmega ω)
    (hS : Ssub_d I c d X R N S) (h : Selem_d I ω c d) {n} (φ : BinarySchema n)
    (ρ : Env (smdl_structure_l I (R := R) hS.source.2.1) n)
    (η : Env (smdl_structure_l I (R := S) hS.target.2.1) n)
    (hρη : ∀ i, (ρ.bound i).val = (η.bound i).val) (he : ∃ x y, φ.denote ρ x y) :
    ∃ x y : {x // M.mem x N}, φ.denote ρ ⟨x.val, hS.subset x.val x.property⟩ ⟨y.val, hS.subset y.val y.property⟩ := by
  let ψ : UnarySchema n := {
    body := .existsE φ.body
    freeClosed := by simpa only [Definitional.Formula.FreeClosed] using φ.freeClosed }
  let θ : UnarySchema (n+1) := { body := φ.body, freeClosed := φ.freeClosed }
  obtain ⟨x, hx⟩ := selem_witness_l I hZF hω hS h ψ ρ η hρη (by
    obtain ⟨x, y, hxy⟩ := he
    exact ⟨x, (Formula.satisfies_exists_iff _ _).mpr ⟨y, hxy⟩⟩)
  obtain ⟨y, hy⟩ := selem_witness_l I hZF hω hS h θ (ρ.push ⟨x.val, hS.subset x.val x.property⟩) (η.push x)
    (Fin.cases rfl hρη) ((Formula.satisfies_exists_iff _ _).mp hx)
  exact ⟨x, y, hy⟩

end YesMetaZFC.SetTheory.Internal
