import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 原关系源中固定原公式的实际分离

固定公式编译到既有全内部程序，再使用原关系分离。参数与分离集均是
原关系载体中的对象，量词不借用背景成员关系。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sc_separate_raw_l (hZF : M.Models ZF) {ω c X R c' Y S q : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    {p} (φ : UnarySchema p) (ρ : Env (smdl_structure_l I (R := S) model.2.1) p)
    (D : (smdl_structure_l I (R := S) model.2.1).Domain) :
    ∃ A, M.mem A Y ∧ ∀ x : (smdl_structure_l I (R := S) model.2.1).Domain,
      M.PairMember I x.val A S ↔ M.PairMember I x.val D.val S ∧ φ.denote ρ x := by
  obtain ⟨a, n, F, r, v, hF, hv, code⟩ := source_compile_l I hZF hω φ.body φ.freeClosed
  have inj : Function.Injective v := fun i j h => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (h.symm ▸ hv j))
  have vn i := num_mem_l hZF.1 hω (hv i)
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω Y
  obtain ⟨f, hf, params⟩ := senv_params_l I hZF hE model.2.1 v
    (fun i => ((ρ.push D).bound i).val) inj vn (fun i => ((ρ.push D).bound i).property)
  -- 只改变被分离变量的槽位；任意其余原关系参数保持同一赋值。
  have read x g (hu : Senv_update_d I f (v 0) x.val g) :
      Ssat_d I Y S E F n r g ↔ φ.denote ρ x := by
    apply code Y S model.2.1 E hE g
      ((hE g).mpr (hu.function_l I ((hE f).mp hf) (vn 0) x.property)) (ρ.push x)
    exact Fin.cases ((hu.2 (v 0) x.val).mpr (Or.inl ⟨rfl, rfl⟩)) (fun i =>
      (hu.2 (v i.succ) (ρ.bound i).val).mpr
        (Or.inr ⟨fun h => Fin.succ_ne_zero i (inj h), params i.succ⟩))
  obtain ⟨A, hA, sep⟩ := sc_separation_raw_l I hZF hω hm model hq theory
    hE hF.2.1 hF.2.2 (vn 0) hf D.property
  refine ⟨A, hA, fun x => (sep x.val x.property).trans (and_congr_right fun _ => ?_)⟩
  refine ⟨fun ⟨g, hu, ht⟩ => (read x g hu).mp ht, fun ht => ?_⟩
  obtain ⟨g, hu, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (vn 0) x.property
  exact ⟨g, hu, (read x g hu).mpr ht⟩

end YesMetaZFC.SetTheory.Internal
