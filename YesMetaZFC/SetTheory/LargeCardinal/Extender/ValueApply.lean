import YesMetaZFC.SetTheory.LargeCardinal.Extender.TupleValue
import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraCertificate
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Step

/-! # 同一实际超幂中的求值等式 j(f)(a)=[a,f]

恒等代表的坍塌值是原支撑列。原常值箭头在任意支撑上取同一值，
再对求值关系应用源内 Łoś，直接得到目标中的实际函数图条目。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 在指定支撑上读取原常值箭头，不改变原超幂的常值图或坍塌图。 -/
theorem ep_value_constant_l (hZ : M.Models ZF)
    {ω κ K L X R F J O Z A p T V q C W e i j n D a x y : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZ)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d (kp_pair_l (ZF.modelsKP hZ)) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (constants : Ep_constants_d X q i) (comp : It_comp_d i e j)
    (hn : M.mem n ω) (haJ : M.mem a J) (ha : Fn0_d n L a) (space : Ep_space_d κ n D)
    (hx : M.mem x X) (image : Rd_entry_d x y j) :
    ∃ f, M.mem f X ∧ Fn0_d D X f ∧ Rs_const_d D x f ∧ Ep_value_d q e a f y := by
  obtain ⟨b, code⟩ := source.code
  obtain ⟨f, B, hf, hB, ff, fs⟩ := sc_constant_l hZ source.omega source.transitive code source.theory
    (source.space_mem_l hZ hn space) hx
  have ff := ff.mono_target_l (source.transitive B hB)
  have fc : Rs_const_d D x f := fun s hs => (fs s x).mpr ⟨hs, rfl⟩
  obtain ⟨H, _, fv⟩ := ep_repr_exists_l hZ family system limit haJ ha space hf ff
  obtain ⟨H', hxH, hHy⟩ := (comp.2 x y).mp image
  obtain ⟨u, a', B', f', D', _, sf, fc', hfB, pair, huH⟩ := constants x H' hxH
  have eq := ep_repr_constant_l hZ source family system limit ff (sf.function_l source.transitive)
    fc fc' fv ⟨u, B', pair, hfB, huH⟩
  exact ⟨f, hf, ff, fc, H, fv, eq.symm ▸ hHy⟩

theorem ep_value_apply_l {ω κ K L X R F J O Z A p T V q c C W d N S e i j a f x f' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (hN : M.TransitiveSet N) (target : Smem_d I d N S)
    (he : Smap_d I ω c d C N e) (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e)
    (constants : Ep_constants_d X q i) (comp : It_comp_d i e j)
    (image : Rd_entry_d f f' j) (value : Ep_value_d q e a f x) : Rd_entry_d a x f' := by
  obtain ⟨E, rep, hEx⟩ := value
  have value : Ep_value_d q e a f x := ⟨E, rep, hEx⟩
  obtain ⟨hf, n, hn, ha, D, space, fn⟩ := rep.source_l hZF family system limit
  have haJ := rep.index_l hZF system limit
  obtain ⟨b, code⟩ := source.code
  obtain ⟨r, _, fr, rs⟩ := sc_identity_l hZF source.omega source.transitive code source.theory
    (source.transitive ω source.omega_mem n hn)
  obtain ⟨g, hg, fg, gs⟩ := sc_identity_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hn space)
  have diagonal u hu := (rs u u).mpr ⟨hu, rfl⟩
  have same s t (h : Rd_entry_d s t g) := ((gs s t).mp h).2
  have compose B s (fs : Fn0_d n B s) : Cp0_d n n B r s s := ⟨fs, fun u hu => by
    obtain ⟨v, hv, huv⟩ := fs.2.1 u hu
    exact ⟨u, hu, v, hv, diagonal u hu, huv, huv⟩⟩
  have seed := ep_tuple_value_l hZFC source family coherent system limit model hN target he fixed
    haJ hn hn ha fr (compose L a ha) space space hg fg
    (fun s t hst => same s t hst ▸ compose κ s ((space s).mp (fg.bound_l hst).1))
  obtain ⟨k, _, fk, constant, kv⟩ :=
    ep_value_constant_l hZF source family system limit constants comp hn haJ ha space hf image
  obtain ⟨U, haU⟩ := family.total n a hn ha
  have los := ep_delta_value_l hZFC source family coherent system limit model hN target he haJ ha space haU (k := 3)
    (rd_entry0_m (.bound 2) (.bound 1) (.bound 0)) (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    (Fin.cases k (Fin.cases f (fun _ => g)))
    ⟨Fin.cases f' (Fin.cases x (fun _ => a)), fun _ => a⟩ (Fin.cases kv (Fin.cases value (fun _ => seed)))
  apply (rd_entry0_sat_l hZF.1 ..).mp (los.mpr ⟨D, source.space_mem_l hZF hn space,
    (family.at_l hZF.1 haU ha space).base.top, fun _ h => h, ?_⟩)
  intro s hs η entries
  have ek := (fn0_function_l (ZF.modelsKP hZF) fk).1.2 s (η.bound 0) f (entries 0) (constant s hs)
  have eg := same s (η.bound 2) (entries 2)
  apply (rd_entry0_sat_l hZF.1 ..).mpr
  change Rd_entry_d (η.bound 2) (η.bound 1) (η.bound 0)
  rw [ek, ← eg]
  exact entries 1

end YesMetaZFC.SetTheory.LargeCardinal
