import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Restriction
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceSatisfaction

/-! # 源内 Łoś 在实际传递像中的有界公式接口

固定原公式仍由原编译器产生内部程序。代表赋值、商赋值和逐点赋值都
实际构造，再应用已有的全内部 Łoś；有限参数接口不改变该归纳的范围。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_delta_image_l {ω a X R D U c G p C T d Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I a X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hU : Sf_ultra_d X D U)
    (hG : ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) (model : Rp_model_d I D X U R c G p C T)
    (hY : M.TransitiveSet Y) (target : Smem_d I d Y S) (hj : Smap_d I ω c d C Y j)
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (hd : φ.IsDelta0)
    (f : Fin n → M.Domain) (hf : ∀ i, M.mem (f i) G) (ρ : Env M n)
    (values : ∀ i, ∃ B, Rd_entry_d (f i) B p ∧ Rd_entry_d B (ρ.bound i) j) :
    Formula.satisfies ρ φ ↔ ∃ A, M.mem A X ∧ M.mem A U ∧ M.MemberSubset A D ∧
      ∀ v, M.mem v A → ∀ η : Env M n, (∀ i, Rd_entry_d v (η.bound i) (f i)) → Formula.satisfies η φ := by
  obtain ⟨P, U', hp, hu, us, md⟩ := rs_restrict_model_l hZF hω hX hm theory hD hU hG model
  obtain ⟨z, l, F, r, w, prog, hw, compile⟩ := source_compile_l I hZF hω φ hφ
  have hωw i := num_mem_l hZF.1 hω (hw i)
  have inj : Function.Injective w := fun i k h => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hw i) (h.symm ▸ hw k))
  obtain ⟨B₀, hB₀⟩ := model.code.2.1
  obtain ⟨f₀, hf₀⟩ := (model.map.range B₀).mp hB₀
  obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω G
  obtain ⟨u, hu₀, params⟩ := senv_params_l I hZF hE₀ ⟨f₀, model.map.projection.input_mem_of_pairMember hf₀⟩ w f inj hωw hf
  have huf := (hE₀ u).mp hu₀
  obtain ⟨E, v, Z, hE, hv, eval, hZ, los⟩ := rs_los_assignment_l hZF hω hX hm theory hD hp hu hG md huf
  obtain ⟨v', hv', transport⟩ := smap_assign_exists_l I hZF hj.1.1 hv
  obtain ⟨E', hE'⟩ := ZF.exists_functionSpace hZF I ω Y
  have out i : Rd_entry_d (w i) (ρ.bound i) v' := by
    obtain ⟨g, B, hug, _, hgB, hwB⟩ := eval (w i) (hωw i)
    have eg := huf.1.2 (w i) g (f i) hug (params i)
    obtain ⟨B', hfB', hBj⟩ := values i
    have eB := model.map.projection.1.2 (f i) B B' (eg ▸ hgB) hfB'
    exact transport (w i) (hωw i) B' (ρ.bound i) (eB ▸ hwB) hBj
  have decoded := (satisfies_decode_l I hZF.1 target.1 prog hE').trans
    (compile.delta_l I hφ hd ρ hY target hE' ((hE' v').mpr hv') out)
  obtain ⟨Z', hZ', elementary⟩ := hj.2
  have mapped := elementary z v v' ((hZ' z).mpr ⟨l, F, r, prog⟩) hv hv' transport
  have start := (mapped.trans decoded).symm.trans (los z ((hZ z).mpr ⟨l, F, r, prog⟩))
  have hux : M.IsSetFunctionFromTo I u ω X := ⟨huf.1, huf.2.1, fun i hi =>
    (huf.2.2 i hi).imp fun g hg => ⟨((hG g).mp hg.1).1, hg.2⟩⟩
  have point g (hg : M.mem g E) s (hs : Pe_assign_d I ω D X u g s) (η : Env M n)
      (hη : ∀ i, Rd_entry_d s (η.bound i) (f i)) : Satisfies_d I ω a z g ↔ Formula.satisfies η φ :=
    (satisfies_decode_l I hZF.1 hm.1 prog hE).trans (compile.delta_l I hφ hd η hX hm hE hg
      (fun i => (hs.value_l I huf.1 ((hE g).mp hg).1 (hωw i) (params i)).mpr (hη i)))
  refine start.trans ⟨?_, ?_⟩
  · rintro ⟨A, hAU, holds⟩
    obtain ⟨hAP, hAU₀⟩ := (us A).mp hAU
    refine ⟨A, ((hp A).mp hAP).1, hAU₀, hu.base.bounds A hAU, fun s hs η hη => ?_⟩
    obtain ⟨g, hg, hg', truth⟩ := holds s hs
    exact (point g hg s hg' η hη).mp truth
  · rintro ⟨A, hAX, hAU, hAD, holds⟩
    refine ⟨A, (us A).mpr ⟨(hp A).mpr ⟨hAX, hAD⟩, hAU⟩, fun s hs => ?_⟩
    obtain ⟨g, hg, assign⟩ := pe_value_exists_l I hZF hX hE ((hE u).mpr hux)
      (fun _ h => h) (hAD s hs) hm.1.2.1 (eval.repr_l I huf.1)
    -- 从有限个实际图条目递归组装赋值，不选择全局求值函数。
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
    let η : Env M n := ⟨b, fun _ => D⟩
    have hη i : Rd_entry_d s (η.bound i) (f i) :=
      (assign.value_l I huf.1 ((hE g).mp hg).1 (hωw i) (params i)).mp (hwb i)
    exact ⟨g, hg, assign, (point g hg s assign η hη).mpr (holds s hs η hη)⟩

end YesMetaZFC.SetTheory.Internal
