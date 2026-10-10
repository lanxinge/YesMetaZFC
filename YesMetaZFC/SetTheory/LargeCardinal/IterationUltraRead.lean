import YesMetaZFC.SetTheory.LargeCardinal.ExtenderUltraCertificate
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystemRead
import YesMetaZFC.Model.SetTheory.Internal.TransitiveCollapse

/-! # Skolem 回拉后指定超幂边的完整恢复

相对证书提供原商、原常值函数、原坍塌和原复合方块。有限闭性恢复全部
代表，随后由实际源的 Łoś 定理证明完整初等性，不假定满足关系绝对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private theorem rt_it_comp_l (hKP : M.Models KP) {V : M.Domain} (hv : M.TransitiveSet V)
    (nv : Nonempty {x // M.mem x V})
    (pair : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b)
    (f g j : (rt_model_l V nv).Domain) (h : It_comp_d f g j) : It_comp_d f.val g.val j.val := by
  have ent := rt_entry_l hv nv hKP.1
  refine ⟨(rt_relation_l hKP.1 (KP.exists_pair hKP) hv nv pair j).mp h.1, fun x z => ⟨?_, ?_⟩⟩
  · intro hxz
    have xz := rd_entry_transitive_l hv j.property hxz
    obtain ⟨y, hxy, hyz⟩ := (h.2 ⟨x, xz.1⟩ ⟨z, xz.2⟩).mp ((ent ..).mpr hxz)
    exact ⟨y.val, (ent ..).mp hxy, (ent ..).mp hyz⟩
  · rintro ⟨y, hxy, hyz⟩
    have xy := rd_entry_transitive_l hv f.property hxy
    have yz := rd_entry_transitive_l hv g.property hyz
    exact (ent ..).mp ((h.2 ⟨x, xy.1⟩ ⟨z, yz.2⟩).mpr ⟨⟨y, xy.2⟩, (ent ..).mpr hxy, (ent ..).mpr hyz⟩)

private theorem rt_ep_constants_l (hKP : M.Models KP) {V : M.Domain} (hv : M.TransitiveSet V)
    (nv : Nonempty {x // M.mem x V})
    (pair : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b)
    (X q i : (rt_model_l V nv).Domain) (h : Ep_constants_d X q i) : Ep_constants_d X.val q.val i.val := by
  have ent := rt_entry_l hv nv hKP.1
  intro x E hxE
  have xe := rd_entry_transitive_l hv i.property hxE
  obtain ⟨u, a, B, f, D, hd, ⟨hf, C, hc, fn⟩, constant, hfb, hp, huE⟩ :=
    h ⟨x, xe.1⟩ ⟨E, xe.2⟩ ((ent ..).mpr hxE)
  exact ⟨u.val, a.val, B.val, f.val, D.val, hd, ⟨hf, C.val, hc, (rt_fn_l hv nv hKP.1 ..).mp fn⟩,
    fun v hvD => (ent ..).mp (constant ⟨v, hv D.val D.property v hvD⟩ hvD), hfb,
    (rt_kpair_l hKP.1 (KP.exists_pair hKP) hv nv pair ..).mp hp, (ent ..).mp huE⟩

theorem it_ultra_read_l (hZFC : M.Models ZFC) {ω V X R K' : M.Domain}
    (ambient : Fs_read_d ω V) (nv : Nonempty {x // M.mem x V})
    {n} (η : Env (rt_model_l V nv) n) (w μ L F c d j : Term n) (hw : (w.eval η).val = ω)
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω (μ.eval η).val K' X R)
    (mx : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (c.eval η).val X R)
    (family : Em_source_d ω (μ.eval η).val (L.eval η).val X (F.eval η).val)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
      ω (μ.eval η).val (L.eval η).val X (F.eval η).val)
    (h : Formula.satisfies η (it_ultra_m w μ L F c d j)) :
    It_ultra_d (ZFC.models_zf_l hZFC) ω (μ.eval η).val (L.eval η).val (F.eval η).val
      (c.eval η).val (d.eval η).val (j.eval η).val := by
  let hZF := ZFC.models_zf_l hZFC
  let J := rt_pair_l ambient.transitive nv hZF.1 ambient.pair
  have ext := rt_model_ext_l hZF.1 ambient.transitive nv
  simp only [it_ultra_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smem_sat_l J, ep_system_sat_l J ext, di_limit_sat_l ext, smdl_sat_l J, wc_graph_sat_l ext,
    Formula.satisfies_isBijectionFromTo_iff J ext, smap_sat_l J ext, ep_constants_sat_l ext,
    it_comp_sat_l ext, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at h
  obtain ⟨x, r, y, s, O, P, Z, A, p, T, U, q, b, C, S, i, e,
    hx, hy, system, limit, model, collapse, bij, _, hi, constants, _, comp⟩ := h
  have hx := (rt_smem_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.transitive nv ambient.pair ..).mp hx
  have hy := (rt_smem_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.transitive nv ambient.pair ..).mp hy
  obtain ⟨eqx, eqr⟩ := smdl_unique_l (kp_pair_l (ZF.modelsKP hZF)) hx.1 mx.1
  have source' : Ep_source_d hZF ω (μ.eval η).val K' x.val r.val := by simpa only [eqx, eqr] using source
  have family' : Em_source_d ω (μ.eval η).val (L.eval η).val x.val (F.eval η).val := by simpa only [eqx] using family
  have coherent' : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω (μ.eval η).val (L.eval η).val x.val (F.eval η).val := by
    simpa only [eqx] using coherent
  exact it_ultra_of_certificate_l hZFC source' family' coherent' hx hy
    (ambient.system_read_l hZF nv (w.eval η) (μ.eval η) (L.eval η) x r (F.eval η) O P Z A p T U hw system)
    (rt_di_limit_l (ZF.modelsKP hZF) ambient.transitive nv ambient.pair A p T U q C S limit)
    ((rt_smdl_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.transitive nv ambient.pair ..).mp model)
    (rt_wc_graph_l (ZF.modelsKP hZF) ambient.transitive nv ambient.pair C S e collapse)
    ((rt_bijection_l ambient.transitive nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.pair ..).mp bij)
    (fn0_of_function_l (ZF.modelsKP hZF)
      ((rt_function_from_l ambient.transitive nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) ambient.pair ..).mp hi.1.1))
    (rt_ep_constants_l (ZF.modelsKP hZF) ambient.transitive nv ambient.pair x q i constants)
    (rt_it_comp_l (ZF.modelsKP hZF) ambient.transitive nv ambient.pair i e (j.eval η) comp)

end YesMetaZFC.SetTheory.LargeCardinal
