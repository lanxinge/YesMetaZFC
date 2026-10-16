import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Restriction
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceSatisfaction

/-! # 未坍塌商及其关系像中的完整公式 Łoś

目标保留原关系结构，量词始终在该结构中解释。源内真值集和实际代表赋值
仍由原内部 Łoś 构造；不要求目标良基、传递或具有背景中的全部函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_formula_image_l {ω a X R D U c G p C T d Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I a X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D) (hD : M.mem D X) (hU : Sf_ultra_d X D U)
    (hG : ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) (model : Rp_model_d I D X U R c G p C T)
    (target : Smdl_d I d Y S) (hj : Smap_d I ω c d C Y j)
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (f : Fin n → M.Domain) (hf : ∀ i, M.mem (f i) G)
    (ρ : Env (smdl_structure_l I (R := S) target.2.1) n)
    (values : ∀ i, ∃ B, Rd_entry_d (f i) B p ∧ Rd_entry_d B (ρ.bound i).val j) :
    Formula.satisfies ρ φ ↔ ∃ A, M.mem A X ∧ M.mem A U ∧ M.MemberSubset A D ∧
      ∀ v, M.mem v A → ∀ η : Env (smdl_structure_l I (R := R) hm.1.2.1) n,
        (∀ i, Rd_entry_d v (η.bound i).val (f i)) → Formula.satisfies η φ := by
  have ext := rf_ext_mem_l I hZF.1 hX hm
  obtain ⟨P, U', hp, hu, us, md⟩ := rs_restrict_model_l hZF hω hX hm theory hD hU hG model
  obtain ⟨z, l, F, r, w, prog, hw, compile⟩ := source_compile_l I hZF hω φ hφ
  have hωw i := num_mem_l hZF.1 hω (hw i)
  have inj : Function.Injective w := fun i k h => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hw i) (h.symm ▸ hw k))
  obtain ⟨B₀, hB₀⟩ := model.code.2.1
  obtain ⟨f₀, hf₀⟩ := (model.map.range B₀).mp hB₀
  obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω G
  obtain ⟨u, hu₀, params⟩ := senv_params_l I hZF hE₀ ⟨f₀, model.map.projection.input_mem_of_pairMember hf₀⟩ w f inj hωw hf
  have huf := (hE₀ u).mp hu₀
  obtain ⟨E, v, Z, hE, hv, eval, hZ, los⟩ := rs_los_assignment_l hZF hω hX hm theory uniform hD hp hu hG md huf
  obtain ⟨v', hv', transport⟩ := smap_assign_exists_l I hZF hj.1.1 hv
  obtain ⟨E', hE'⟩ := ZF.exists_functionSpace hZF I ω Y
  have out i : Rd_entry_d (w i) (ρ.bound i).val v' := by
    obtain ⟨g, B, hug, _, hgB, hwB⟩ := eval (w i) (hωw i)
    have eg := huf.1.2 (w i) g (f i) hug (params i)
    obtain ⟨B', hfB', hBj⟩ := values i
    have eB := model.map.projection.1.2 (f i) B B' (eg ▸ hgB) hfB'
    exact transport (w i) (hωw i) B' (ρ.bound i).val (eB ▸ hwB) hBj
  have decoded := (satisfies_decode_l I hZF.1 target prog hE').trans
    (compile Y S target.2.1 E' hE' v' ((hE' v').mpr hv') ρ out)
  obtain ⟨Z', hZ', elementary⟩ := hj.2
  have mapped := elementary z v v' ((hZ' z).mpr ⟨l, F, r, prog⟩) hv hv' transport
  have start := (mapped.trans decoded).symm.trans (los z ((hZ z).mpr ⟨l, F, r, prog⟩))
  have hux : M.IsSetFunctionFromTo I u ω X := ⟨huf.1, huf.2.1, fun i hi =>
    (huf.2.2 i hi).imp fun g hg => ⟨((hG g).mp hg.1).1, hg.2⟩⟩
  have point g (hg : M.mem g E) s (hs : Pe_assign_d I ω D X R u g s)
      (η : Env (smdl_structure_l I (R := R) hm.1.2.1) n)
      (hη : ∀ i, Rd_entry_d s (η.bound i).val (f i)) : Satisfies_d I ω a z g ↔ Formula.satisfies η φ :=
    (satisfies_decode_l I hZF.1 hm.1 prog hE).trans (compile X R hm.1.2.1 E hE g hg η
      (fun i => (hs.value_l I ext huf.1 ((hE g).mp hg).1 (hωw i) (params i)).mpr ((rf_val_mem_l I hZF.1 hX hm ((hG (f i)).mp (hf i)).1).mpr (hη i))))
  refine start.trans ⟨?_, ?_⟩
  · rintro ⟨A, hAU, holds⟩
    obtain ⟨hAP, hAU₀⟩ := (us A).mp hAU
    refine ⟨A, ((hp A).mp hAP).1, hAU₀, hu.base.bounds A hAU, fun s hs η hη => ?_⟩
    obtain ⟨g, hg, hg', truth⟩ := holds s hs
    exact (point g hg s hg' η hη).mp truth
  · rintro ⟨A, hAX, hAU, hAD, holds⟩
    refine ⟨A, (us A).mpr ⟨(hp A).mpr ⟨hAX, hAD⟩, hAU⟩, fun s hs => ?_⟩
    obtain ⟨g, hg, assign⟩ := pe_value_exists_l I hZF ext hE ((hE u).mpr hux)
      (fun _ h => h) (hX D hD s (hAD s hs)) ((hm.2 s D).mpr ⟨hX D hD s (hAD s hs), hD, hAD s hs⟩) (eval.repr_l I huf.1)
    -- 有限赋值逐项构造，不从全局代表选择中生成数据。
    have pick : ∀ {k} (v : Fin k → M.Domain), (∀ i, ∃ x, Rd_entry_d (v i) x g) →
        ∃ b : Fin k → M.Domain, ∀ i, Rd_entry_d (v i) (b i) g := by
      intro k
      induction k with
      | zero => exact fun _ _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
      | succ k ih =>
        intro v total
        obtain ⟨x, hx⟩ := total 0
        obtain ⟨b, hb⟩ := ih (fun i => v i.succ) (fun i => total i.succ)
        exact ⟨Fin.cases x b, Fin.cases hx hb⟩
    obtain ⟨b, hwb⟩ := pick w (fun i => (((hE g).mp hg).2.2 (w i) (hωw i)).imp fun _ hx => hx.2)
    obtain ⟨x, hx⟩ := hm.1.2.1
    let η : Env (smdl_structure_l I (R := R) hm.1.2.1) n :=
      ⟨fun i => ⟨b i, ((hE g).mp hg).output_mem_of_pairMember (hwb i)⟩, fun _ => ⟨x, hx⟩⟩
    have hη i : Rd_entry_d s (η.bound i).val (f i) :=
      (rf_val_mem_l I hZF.1 hX hm ((hG (f i)).mp (hf i)).1).mp
        ((assign.value_l I ext huf.1 ((hE g).mp hg).1 (hωw i) (params i)).mp (hwb i))
    exact ⟨g, hg, assign, (point g hg s assign η hη).mpr (holds s hs η hη)⟩

end YesMetaZFC.SetTheory.Internal
