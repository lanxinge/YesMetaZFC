import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingSetRestriction
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderValueApply

/-! # 拥有集合的超幂像中的完整内部真值

把 A 的有限真值表整体送到 j(A)，再对表中条目使用源内 Łoś。
目标赋值可为任意代表的坍塌值，不要求它属于常值嵌入的像，也不要求 A 的高度正则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_value_l {ω κ K L X R F J O Z A p T V q c C W d N S μ K' e i j c₀
    a₀ A₀ R₀ a₁ A₁ R₁ n D a U b l P r g t : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' N S)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (hm : Smem_d I c₀ X R) (hn : Smem_d I d N S)
    (he : Smap_d I ω c d C N e) (hj : Smap_d I ω c₀ d X N j)
    (constants : Ep_constants_d X q i) (comp : It_comp_d i e j)
    (h₀ : Smem_d I a₀ A₀ R₀) (h₁ : Smem_d I a₁ A₁ R₁) (hA : Rd_entry_d A₀ A₁ j)
    (hnω : M.mem n ω) (haJ : M.mem a J) (ha : Fn0_d n L a) (space : Ep_space_d κ n D) (haU : Rd_entry_d a U F)
    (program : Sfm_d I ω l P) (hb : M.mem b ω) (bound : Sbound_d I P b) (hr : M.mem r l)
    (value : Ep_value_d q e a g t) : ∃ E E', M.IsFunctionSpace I E b A₀ ∧ M.IsFunctionSpace I E' b A₁ ∧
      (Ssat_d I A₁ R₁ E' P l r t ↔ ∃ B, M.mem B X ∧ M.mem B U ∧ M.MemberSubset B D ∧
        ∀ s, M.mem s B → ∀ f, Rd_entry_d s f g → Ssat_d I A₀ R₀ E P l r f) := by
  obtain ⟨E, E', C₀, H, C₁, H', hE, hE', _, hCC, hHH, old, new⟩ :=
    ep_set_tables_l hZF source target hm hn hj h₀ h₁ hA program hb bound
  have natural := hj.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  have hrω := source.omega.transitive hZF l program.1 r hr
  obtain ⟨cr, _, fr, rc, rv⟩ := ep_value_constant_l hZF source family system limit constants comp
    hnω haJ ha space (source.transitive ω source.omega_mem r hrω) (natural r hrω)
  obtain ⟨cH, _, fH, Hc, Hv⟩ := ep_value_constant_l hZF source family system limit constants comp
    hnω haJ ha space (hj.1.1.input_mem_of_pairMember hHH) hHH
  obtain ⟨cC, _, fC, Cc, Cv⟩ := ep_value_constant_l hZF source family system limit constants comp
    hnω haJ ha space (hj.1.1.input_mem_of_pairMember hCC) hCC
  have los := ep_delta_value_l hZFC source family coherent system limit model target.transitive hn he haJ ha space haU (k := 4)
    (fv_at_m (.bound 3) (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (fv_at_delta_l ..)
    (Fin.cases g (Fin.cases cr (Fin.cases cH (fun _ => cC))))
    ⟨Fin.cases t (Fin.cases r (Fin.cases H' (fun _ => C₁))), fun _ => t⟩
    (Fin.cases value (Fin.cases rv (Fin.cases Hv (fun _ => Cv))))
  simp only [fv_at_sat_l hZF.1] at los
  refine ⟨E, E', hE, hE', (new r hr t).symm.trans (los.trans ?_)⟩
  constructor
  · rintro ⟨B, hBX, hBU, sub, all⟩
    refine ⟨B, hBX, hBU, sub, fun s hs f hsf => ?_⟩
    let η : Env M 4 := ⟨Fin.cases f (Fin.cases r (Fin.cases H (fun _ => C₀))), fun _ => f⟩
    have point := all s hs η
      (Fin.cases hsf (Fin.cases (rc s (sub s hs)) (Fin.cases (Hc s (sub s hs)) (fun _ => Cc s (sub s hs)))))
    exact (old r hr f).mp point
  · rintro ⟨B, hBX, hBU, sub, all⟩
    refine ⟨B, hBX, hBU, sub, fun s hs η values => ?_⟩
    have er := (fn0_function_l (ZF.modelsKP hZF) fr).1.2 s (η.bound 1) r (values 1) (rc s (sub s hs))
    have eh := (fn0_function_l (ZF.modelsKP hZF) fH).1.2 s (η.bound 2) H (values 2) (Hc s (sub s hs))
    have ec := (fn0_function_l (ZF.modelsKP hZF) fC).1.2 s (η.bound 3) C₀ (values 3) (Cc s (sub s hs))
    change Fv_at_d (η.bound 3) (η.bound 2) (η.bound 1) (η.bound 0)
    rw [er, eh, ec]
    exact (old r hr (η.bound 0)).mpr (all s hs (η.bound 0) (values 0))

end YesMetaZFC.SetTheory.LargeCardinal
