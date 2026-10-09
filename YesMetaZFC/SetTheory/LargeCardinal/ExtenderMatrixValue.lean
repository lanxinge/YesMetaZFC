import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteMatrix
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderValue

/-! # 有限转置矩阵的超幂值

矩阵逐点编码有限代表列，其坍塌值便是这些代表值组成的有限赋值。
有界 Łoś 先给出函数图，再逐坐标辨认；输入矩阵可来自更小的实际源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_matrix_value_l {ω κ K L X R F J O Z A p T V q c C W d N S e n D a b B E H G t : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (hN : M.TransitiveSet N) (target : Smem_d I d N S) (he : Smap_d I ω c d C N e)
    (haJ : M.mem a J) (ha : Fn0_d n L a) (space : Ep_space_d κ n D)
    (hb : M.mem b ω) (hB : M.mem B X) (hE : M.mem E X) (hH : M.mem H X)
    (assignments : M.IsFunctionSpace I E b B) (fh : Fn0_d D E H) (fg : Fn0_d b X G) (ft : Fn0_d b N t)
    (matrix : ∀ v s i f x, Rd_entry_d v s H → Rd_entry_d i f G → (Rd_entry_d i x s ↔ Rd_entry_d v x f))
    (values : ∀ i f x, Rd_entry_d i f G → Rd_entry_d i x t → Ep_value_d q e a f x) : Ep_value_d q e a H t := by
  obtain ⟨E₀, hE₀, rep⟩ := ep_repr_exists_l hZF family system limit haJ ha space hH
    (fh.mono_target_l (source.transitive E hE))
  obtain ⟨s, _, hEs⟩ := he.1.1.2.2 E₀ hE₀
  have value : Ep_value_d q e a H s := ⟨E₀, rep, hEs⟩
  obtain ⟨c₀, j, code, hj, constants⟩ := ep_value_constants_l hZFC source family coherent system limit model he haJ ha space
  have natural := hj.natural_l hZF source.omega source.transitive hN code target source.omega_mem
  obtain ⟨kb, _, fb, bc, bv⟩ := constants b b (natural b hb)
  obtain ⟨B', hB', hBB⟩ := hj.1.1.2.2 B hB
  obtain ⟨kB, _, fB, Bc, Bv⟩ := constants B B' hBB
  obtain ⟨_, n', hn, ha', _⟩ := rep.source_l hZF family system limit
  have en := ha'.domain_eq_l hZF.1 ha
  subst n'
  obtain ⟨U, haU⟩ := family.total n a hn ha
  have fs : Fn0_d b B' s := by
    have los := ep_delta_value_l hZFC source family coherent system limit model hN target he haJ ha space haU (k := 3)
      (fn0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (fn0_delta_l ..)
      (Fin.cases H (Fin.cases kB (fun _ => kb)))
      ⟨Fin.cases s (Fin.cases B' (fun _ => b)), fun _ => b⟩ (Fin.cases value (Fin.cases Bv (fun _ => bv)))
    apply (fn0_sat_l hZF.1 ..).mp (los.mpr ⟨D, source.space_mem_l hZF hn space,
      (family.at_l hZF.1 haU ha space).base.top, fun _ h => h, ?_⟩)
    intro v hv η entries
    have eb := (fn0_function_l (ZF.modelsKP hZF) fb).1.2 v (η.bound 2) b (entries 2) (bc v hv)
    have eB := (fn0_function_l (ZF.modelsKP hZF) fB).1.2 v (η.bound 1) B (entries 1) (Bc v hv)
    apply (fn0_sat_l hZF.1 ..).mpr
    change Fn0_d (η.bound 2) (η.bound 1) (η.bound 0)
    rw [eb, eB]
    exact fn0_of_function_l (ZF.modelsKP hZF) ((assignments _).mp (fh.bound_l (entries 0)).2)
  have eq := (fs.mono_target_l (hN B' hB')).ext_l hZF.1 ft (fun i hi => by
    obtain ⟨f, _, hif⟩ := fg.2.1 i hi
    obtain ⟨x, _, hix⟩ := ft.2.1 i hi
    obtain ⟨ki, _, fi, ic, iv⟩ := constants i i (natural i (source.omega.transitive hZF b hb i hi))
    have los := ep_delta_value_l hZFC source family coherent system limit model hN target he haJ ha space haU (k := 3)
      (rd_entry0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
      (Fin.cases H (Fin.cases f (fun _ => ki)))
      ⟨Fin.cases s (Fin.cases x (fun _ => i)), fun _ => i⟩
      (Fin.cases value (Fin.cases (values i f x hif hix) (fun _ => iv)))
    refine ⟨x, (rd_entry0_sat_l hZF.1 ..).mp (los.mpr ⟨D, source.space_mem_l hZF hn space,
      (family.at_l hZF.1 haU ha space).base.top, fun _ h => h, ?_⟩), hix⟩
    intro v hv η entries
    have ei := (fn0_function_l (ZF.modelsKP hZF) fi).1.2 v (η.bound 2) i (entries 2) (ic v hv)
    apply (rd_entry0_sat_l hZF.1 ..).mpr
    change Rd_entry_d (η.bound 2) (η.bound 1) (η.bound 0)
    rw [ei]
    exact (matrix v _ i f _ (entries 0) hif).mpr (entries 1))
  exact eq ▸ value

end YesMetaZFC.SetTheory.LargeCardinal
