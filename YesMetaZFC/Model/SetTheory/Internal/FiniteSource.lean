import YesMetaZFC.Model.SetTheory.Internal.Compiler
import YesMetaZFC.Model.SetTheory.Internal.SkolemSyntax

/-! # 原公式的有限参数编译

原公式只编译一次。参数存入实际内部有限函数，零号位置留给待定义对象；
列外统一取空集。语义证书同时覆盖全部包含参数的集合结构及全部候选对象。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 有限原参数产生内部公式码和参数列，证书对载体、关系及候选值统一成立。 -/
theorem source_finite_compile_l (hZF : M.Models ZF) {ω e B} (hω : M.IsOmega ω)
    (he : Num_d 0 e) (heB : M.mem e B) {d} (φ : Formula 1 (d+1)) (hφ : φ.FreeClosed)
    (p : Fin d → M.Domain) (hp : ∀ i, M.mem (p i) B) :
    ∃ a n s, (∃ m F k, Sformula_d I ω a m F k) ∧ M.mem n ω ∧
      M.IsSetFunctionFromTo I s n B ∧
      ∀ X c R (hM : Smdl_d I c X R), M.MemberSubset B X →
        ∀ η : Env (smdl_structure_l I (R := R) hM.2.1) d,
          (∀ i, (η.bound i).val = p i) → ∀ y : (smdl_structure_l I (R := R) hM.2.1).Domain,
            (Ssk_wit_d I ω c X e a e s y.val ↔ Formula.satisfies (η.push y) φ) := by
  obtain ⟨a, m, F, k, v, ha, hv, hc⟩ := source_compile_l I hZF hω φ hφ
  obtain ⟨n, hn⟩ := num_exists_l (ZF.modelsKP hZF) (d+1)
  obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I n B
  have hinj : Function.Injective v := by
    intro i j h
    exact Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (h.symm ▸ hv j))
  obtain ⟨s, hsD, hs⟩ := senv_params_l I hZF hD ⟨e, heB⟩ v (Fin.cases e p) hinj
    (fun i => num_lt_l hZF.1 (hv i) hn i.isLt) (Fin.cases heB hp)
  have hsB := (hD s).mp hsD
  have hnω := num_mem_l hZF.1 hω hn
  have heω := num_mem_l hZF.1 hω he
  have hv0 : v 0 = e := num_unique_l hZF.1 (hv 0) he
  refine ⟨a, n, s, ⟨m, F, k, ha⟩, hnω, hsB, ?_⟩
  intro X c R hM hBX η hη y
  have hsX : M.IsSetFunctionFromTo I s n X :=
    ⟨hsB.1, hsB.2.1, fun i hi => (hsB.2.2 i hi).elim fun z hz => ⟨z, hBX z hz.1, hz.2⟩⟩
  obtain ⟨f, hf, hfX⟩ := senv_fill_exists_l I hZF hsX (hBX e heB)
  obtain ⟨g, hg, hgX⟩ := senv_update_exists_l I hZF hfX heω y.property
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  refine (ssk_wit_decode_l I hZF.1 hnω hsX hf hg).trans
    ((satisfies_decode_l I hZF.1 hM ha hE).trans
      (hc X R hM.2.1 E hE g ((hE g).mpr hgX) (η.push y) ?_))
  refine Fin.cases ?_ (fun i => ?_)
  · exact (hg.2 (v 0) y.val).mpr (Or.inl ⟨hv0, rfl⟩)
  · have hne : v i.succ ≠ e := by
      intro h
      have hh := num_injective_l (ZF.modelsKP hZF) (hv i.succ) (h.symm ▸ he)
      simp only [Fin.val_succ] at hh
      omega
    exact (hg.2 (v i.succ) (η.bound i).val).mpr (Or.inr ⟨hne,
      (hf.2 (v i.succ) (η.bound i).val).mpr ⟨num_mem_l hZF.1 hω (hv i.succ),
        Or.inl ⟨num_lt_l hZF.1 (hv i.succ) hn i.succ.isLt, (hη i).symm ▸ hs i.succ⟩⟩⟩)

end YesMetaZFC.SetTheory.Internal
