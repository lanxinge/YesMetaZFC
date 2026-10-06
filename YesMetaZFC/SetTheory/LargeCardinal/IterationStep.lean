import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagramExtend
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLimit
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSyntax

/-! # 一条实际超幂边及其所属模型

边证书同时保留源内部代表、商、常值图和坍塌；新边就是这些实际图的
复合。所属模型对扩展器的判断使用原短扩展器公式的相对满足关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_source_d (hZF : M.Models ZF) (ω c : M.Domain) : Prop := ∃ X R K,
  Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R ∧ Ep_source_d hZF ω ω K X R

def It_local_d (ω X κ L F : M.Domain) : Prop := ∃ hω : M.mem ω X, ∃ hκ : M.mem κ X,
  ∃ hL : M.mem L X, ∃ hF : M.mem F X,
  Formula.satisfies (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, hκ⟩ (fun _ => ⟨ω, hω⟩))), fun _ => ⟨ω, hω⟩⟩ :
    Env (rt_model_l X ⟨⟨ω, hω⟩⟩) 4) (ex_short_m (.bound 3) (.bound 2) (.bound 1) (.bound 0))

def It_ultra_d (hZF : M.Models ZF) (ω κ L F c d j : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ X R Y S J O Z A p T V q b C W i e,
    Smem_d I c X R ∧ Smem_d I d Y S ∧
    Ep_system_d hZF ω κ L X R F J O Z A p T V ∧ Di_limit_d A p T V q C W ∧ Smdl_d I b C W ∧
    Wc_graph_d C W e ∧ M.IsSetBijectionFromTo I e C Y ∧ Smap_d I ω b d C Y e ∧
    Smap_d I ω c b X C i ∧ Ep_constants_d X q i ∧ Smap_d I ω c d X Y j ∧ It_comp_d i e j

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 实际超幂的塌缩证书保证目标传递，无需另加目标源证书。 -/
theorem It_ultra_d.transitive_l {ω κ L F c d j Y S : M.Domain} (h : It_ultra_d hZF ω κ L F c d j)
    (hn : Smdl_d I d Y S) : M.TransitiveSet Y := by
  obtain ⟨_, _, Y', S', _, _, _, _, _, _, _, _, _, _, _, _, _, _, my, _, _, _, wc, bij, _⟩ := h
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I my.1 hn
  intro x hx y hy
  obtain ⟨E, _, hEx⟩ := bij.2 x hx
  obtain ⟨H, _, _, hHy⟩ := ((wc.2 E x hEx).2.2 y).mp hy
  exact bij.1.1.output_mem_of_pairMember hHy

theorem It_ultra_d.elementary_l {ω κ L F c d j X R Y S : M.Domain} (h : It_ultra_d hZF ω κ L F c d j)
    (hm : Smdl_d I c X R) (hn : Smdl_d I d Y S) : Smap_d I ω c d X Y j := by
  obtain ⟨X', R', Y', S', _, _, _, _, _, _, _, _, _, _, _, _, _, mx, my, _, _, _, _, _, _, _, _, hj, _⟩ := h
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx.1 hm
  obtain ⟨rfl, rfl⟩ := smdl_unique_l I my.1 hn
  exact hj

/-- 已构造的良基超幂自动给出新模型码、实际超幂边及下一步源。 -/
theorem it_ultra_exists_l {ω κ L X R F c : M.Domain}
    (code : Smem_d I c X R)
    (built : Ep_limit_d hZF ω κ L X R F) : ∃ d j, It_ultra_d hZF ω κ L F c d j ∧ It_source_d hZF ω d := by
  obtain ⟨J, O, Z, A, p, T, V, q, b, C, W, hs, limit, model, _, _, collapse⟩ := built
  obtain ⟨_, c', i, Y, e, _, d, S, j, code', hi, constants, hY, wc, bij, target, he, _, _, _, hj, js, next⟩ := collapse
  obtain ⟨rfl, _⟩ := smem_unique_l I hZF.1 code' code
  obtain ⟨K', source'⟩ := next
  exact ⟨d, j, ⟨X, R, Y, S, J, O, Z, A, p, T, V, q, b, C, W, i, e, code, target, hs, limit, model,
      wc, bij, he, hi, constants, hj, hj.1.1.1.1, fun x y => (js x y).trans
        ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩,
    Y, S, K', target, source'⟩

/-- 模型内已实现的短扩展器直接给出所属判断，量词仍限于该模型。 -/
theorem it_local_short_l {X : M.Domain} (hn : Nonempty {x : M.Domain // M.mem x X})
    (hX : (rt_model_l X hn).Models ZF) {ω κ L F : (rt_model_l X hn).Domain}
    (h : Ex_short_d hX ω κ L F) : It_local_d ω.val X κ.val L.val F.val := by
  let ρ : Env (rt_model_l X hn) 4 := ⟨Fin.cases F (Fin.cases L (Fin.cases κ (fun _ => ω))), fun _ => ω⟩
  have hs : Formula.satisfies ρ (ex_short_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)) :=
    (ex_short_sat_l hX ρ (.bound 3) (.bound 2) (.bound 1) (.bound 0)).mpr h
  exact ⟨ω.property, κ.property, L.property, F.property, hs⟩

/-- 原所属公式沿实际全初等图搬运；可数完备性始终只在各自模型内部解释。 -/
theorem It_local_d.map_l {ω X R Y S c d σ κ κ' L L' F F' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hσ : Smap_d I ω c d X Y σ)
    (hκ : Rd_entry_d κ κ' σ) (hL : Rd_entry_d L L' σ) (hF : Rd_entry_d F F' σ)
    (loc : It_local_d ω X κ L F) : It_local_d ω Y κ' L' F' := by
  obtain ⟨ωX, κX, LX, FX, hs⟩ := loc
  have hωσ := hσ.omega_l I hZF hω hX hY hm hn ωX
  have ωY := hσ.1.1.output_mem_of_pairMember hωσ
  have κY := hσ.1.1.output_mem_of_pairMember hκ
  have LY := hσ.1.1.output_mem_of_pairMember hL
  have FY := hσ.1.1.output_mem_of_pairMember hF
  let ρ : Env (rt_model_l X ⟨⟨ω, ωX⟩⟩) 4 :=
    ⟨Fin.cases ⟨F, FX⟩ (Fin.cases ⟨L, LX⟩ (Fin.cases ⟨κ, κX⟩ (fun _ => ⟨ω, ωX⟩))), fun _ => ⟨ω, ωX⟩⟩
  let η : Env (rt_model_l Y ⟨⟨ω, ωY⟩⟩) 4 :=
    ⟨Fin.cases ⟨F', FY⟩ (Fin.cases ⟨L', LY⟩ (Fin.cases ⟨κ', κY⟩ (fun _ => ⟨ω, ωY⟩))), fun _ => ⟨ω, ωY⟩⟩
  let φ : Formula 1 4 := ex_short_m (.bound 3) (.bound 2) (.bound 1) (.bound 0)
  have image := (smap_source_l I hZF hω hm.1 hn.1 hσ φ (by simp -implicitDefEqProofs [φ])
    ⟨ρ.bound, ρ.free⟩ ⟨η.bound, η.free⟩ (Fin.cases hF (Fin.cases hL (Fin.cases hκ (fun _ => hωσ))))).mp
    ((smem_formula_l I hm _ φ ρ).mp hs)
  exact ⟨ωY, κY, LY, FY, (smem_formula_l I hn _ φ η).mpr image⟩

end YesMetaZFC.SetTheory.LargeCardinal
