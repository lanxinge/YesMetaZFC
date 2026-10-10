import YesMetaZFC.SetTheory.LargeCardinal.ExtenderValue
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSeedCollapse

/-! # 有限坐标列的实际坍塌值

源内投影 s↦s∘r 的值是支撑列 a∘r。先由有界 Łoś 得到函数图，
再逐个内部自然数读取条目；坐标坍塌定理识别每个值，函数外延性收尾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_tuple_value_l (hZFC : M.Models ZFC) {ω κ K L X R F J O Z A p T V q c C W d N S e n m D E a r t g : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ L X F)
    (h : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W)
    (hN : M.TransitiveSet N) (target : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) d N S)
    (he : Smap_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω c d C N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e)
    (haJ : M.mem a J) (hn : M.mem n ω) (hm : M.mem m ω) (ha : Fn0_d n L a)
    (hr : Fn0_d m n r) (hrt : Cp0_d m n L r a t) (hD : Ep_space_d κ n D) (hE : Ep_space_d κ m E)
    (hgX : M.mem g X) (hg : Fn0_d D E g)
    (project : ∀ s v, Rd_entry_d s v g → Cp0_d m n κ r s v) : Ep_value_d q e a g t := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hDX := source.space_mem_l hZF hn hD
  obtain ⟨U, haU⟩ := family.total n a hn ha
  have ultra := family.at_l hZF.1 haU ha hD
  obtain ⟨H, hHC, rep⟩ := ep_repr_exists_l hZF family h limit haJ ha hD hgX
    (hg.mono_target_l (source.transitive E (source.space_mem_l hZF hm hE)))
  obtain ⟨x, _, hHx⟩ := he.1.1.2.2 H hHC
  have value : Ep_value_d q e a g x := ⟨H, rep, hHx⟩
  obtain ⟨b, j, code, hj, constants⟩ := ep_value_constants_l hZFC source family coherent h limit model he haJ ha hD
  have natural := hj.natural_l hZF source.omega source.transitive hN code target source.omega_mem
  obtain ⟨f, _, hf, fc, fv⟩ := constants m m (natural m hm)
  obtain ⟨κ', _, hκκ⟩ := hj.1.1.2.2 κ source.cardinal_mem
  obtain ⟨k, _, hk, kc, kv⟩ := constants κ κ' hκκ
  have xf : Fn0_d m κ' x := by
    have los := ep_delta_value_l hZFC source family coherent h limit model hN target he haJ ha hD haU (k := 3)
      (fn0_m (.bound 2) (.bound 1) (.bound 0)) (by simp -implicitDefEqProofs) (fn0_delta_l ..)
      (Fin.cases g (Fin.cases k (fun _ => f)))
      ⟨Fin.cases x (Fin.cases κ' (fun _ => m)), fun _ => m⟩ (Fin.cases value (Fin.cases kv (fun _ => fv)))
    apply (fn0_sat_l hZF.1 ..).mp (los.mpr ⟨D, hDX, ultra.base.top, fun _ h => h, ?_⟩)
    intro s hs η entries
    have em := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 s (η.bound 2) m (entries 2) (fc s hs)
    have ek := (fn0_function_l (ZF.modelsKP hZF) hk).1.2 s (η.bound 1) κ (entries 1) (kc s hs)
    apply (fn0_sat_l hZF.1 ..).mpr
    change Fn0_d (η.bound 2) (η.bound 1) (η.bound 0)
    rw [em, ek]
    exact (hE _).mp (hg.bound_l (entries 0)).2
  have equal : x = t := xf.ext_l hZF.1 hrt.1 fun i hi => by
    obtain ⟨α, _, hiα⟩ := hrt.1.2.1 i hi
    obtain ⟨l, hln, hil⟩ := hr.2.1 i hi
    obtain ⟨u, huX, hu⟩ := source.coordinate_l hZF hn hD hln
    obtain ⟨B, _, ub⟩ := ep_repr_exists_l hZF family h limit haJ ha hD huX
      (hu.1.mono_target_l (source.transitive κ source.cardinal_mem))
    have uv : Ep_value_d q e a u α := ⟨B, ub,
      fixed α B ⟨n, a, l, D, u, ha, (hrt.value_l hr ha hil).mp hiα, hD, hu, ub⟩⟩
    obtain ⟨fᵢ, _, hfᵢ, ic, iv⟩ := constants i i (natural i (source.omega.transitive hZF m hm i hi))
    have los := ep_delta_value_l hZFC source family coherent h limit model hN target he haJ ha hD haU (k := 3)
      (rd_entry0_m (.bound 2) (.bound 1) (.bound 0)) (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
      (Fin.cases g (Fin.cases u (fun _ => fᵢ)))
      ⟨Fin.cases x (Fin.cases α (fun _ => i)), fun _ => i⟩ (Fin.cases value (Fin.cases uv (fun _ => iv)))
    refine ⟨α, (rd_entry0_sat_l hZF.1 ..).mp (los.mpr ⟨D, hDX, ultra.base.top, fun _ h => h, ?_⟩), hiα⟩
    intro s hs η entries
    have ei := (fn0_function_l (ZF.modelsKP hZF) hfᵢ).1.2 s (η.bound 2) i (entries 2) (ic s hs)
    apply (rd_entry0_sat_l hZF.1 ..).mpr
    change Rd_entry_d (η.bound 2) (η.bound 1) (η.bound 0)
    rw [ei]
    exact ((project s _ (entries 0)).value_l hr ((hD s).mp hs) hil).mpr (((hu.2 s _).mp (entries 1)).2)
  exact equal ▸ value

end YesMetaZFC.SetTheory.LargeCardinal
