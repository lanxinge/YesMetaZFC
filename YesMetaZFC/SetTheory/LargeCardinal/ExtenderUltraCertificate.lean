import YesMetaZFC.SetTheory.LargeCardinal.IterationStepSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRepresentative

/-! # 从原代数证书恢复完整超幂边

Łoś 定理恢复常值图的完整内部初等性；常值代表唯一性保证恢复的是指定
图本身。原坍塌双射再给出同构，最终保留指定复合图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_ultra_of_certificate_l {ω κ K L X R F J O Z A p T V q b C W c d Y S i e j : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I b C W) (collapse : Wc_graph_d C W e) (bij : M.IsSetBijectionFromTo I e C Y)
    (fi : Fn0_d X C i) (constants : Ep_constants_d X q i) (comp : It_comp_d i e j) :
    It_ultra_d hZF ω κ L F c d j := by
  obtain ⟨B, hB⟩ := model.2.1
  obtain ⟨u, hu⟩ := (limit.range B).mp hB
  obtain ⟨a, ha, _⟩ := system.projection.2.1 u (limit.projection.bound_l hu).1
  obtain ⟨_, maps⟩ := system.codes
  obtain ⟨v, _, hav⟩ := maps.2.1 a ha
  obtain ⟨c', i', n, D, U, G, r, H, Q, code, hi', _, hna, hd, hau, hg, quotient, values⟩ :=
    ep_constant_limit_l hZF source family system limit model
      (system.toEp_graph_d.elementary_l hZFC source family coherent) hav
  have eqc := (smem_unique_l I hZF.1 code mx).1
  subst c'
  have eqi : i = i' := fi.ext_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hi'.1.1) (fun x hx => by
    obtain ⟨E, _, hxE⟩ := fi.2.1 x hx
    obtain ⟨E', _, hxE'⟩ := hi'.1.1.2.2 x hx
    obtain ⟨u, a, B, f, D', _, sf, fc, hf, hp, huE⟩ := constants x E hxE
    obtain ⟨_, g, B', u', hgG, gc, hgr, hp', huE'⟩ := (values x E').mp hxE'
    have eq := ep_repr_constant_l hZF source family system limit (sf.function_l source.transitive)
      ((hg g).mp hgG).2 fc gc ⟨u, B, hp, hf, huE⟩
      ⟨u', B', hp', quotient.map.representative_l I (family.at_l hZF.1 hau hna hd).base hgr, huE'⟩
    exact ⟨E, hxE, eq.symm ▸ hxE'⟩)
  have hi : Smap_d I ω c b X C i := eqi.symm ▸ hi'
  have he : Smap_d I ω b d C Y e := smap_of_iso_l I hZF source.omega model my.1 bij (fun a b x y ha hb =>
    (collapse.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 ha hb).trans
      ⟨fun h => (my.2 x y).mpr ⟨bij.1.1.output_mem_of_pairMember ha, bij.1.1.output_mem_of_pairMember hb, h⟩,
        fun h => ((my.2 x y).mp h).2.2⟩)
  obtain ⟨j', hj', square⟩ := it_comp_elementary_l hZF hi he
  have hj : Smap_d I ω c d X Y j := (comp.unique_l hZF.1 square).symm ▸ hj'
  exact ⟨X, R, Y, S, J, O, Z, A, p, T, V, q, b, C, W, i, e,
    mx, my, system, limit, model, collapse, bij, he, hi, constants, hj, comp⟩

end YesMetaZFC.SetTheory.LargeCardinal
