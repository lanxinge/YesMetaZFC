import YesMetaZFC.SetTheory.LargeCardinal.ExtenderUltraSupport
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderValueApply
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLocalRead

/-! # 原内部短扩展器的实际临界点

κ 以下的单坐标测度由原主测度条款决定。坐标代表与常值代表在该测度下
相等，而实际坍塌把坐标代表送回原序数；故所有 α<κ 被固定，κ 则越过支撑。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_local_d.principal_l {ω κ K X R L F n a U B : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (loc : It_local_d ω X κ L F)
    (hn : M.mem n ω) (ha : Fn0_d n κ a) (haU : Rd_entry_d a U F) (hB : M.mem B X) :
    M.mem B U ↔ (∀ s, M.mem s B → Fn0_d n κ s) ∧ M.mem a B := by
  obtain ⟨_, _, hL, hF, sat⟩ := loc
  have pre := ((Formula.satisfies_conj_iff _ _ _).mp sat).1
  simp only [ex_pre_m, Formula.satisfies_conj_iff] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, principal, _⟩ := pre
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  have au := rd_entry_transitive_l source.transitive hF haU
  let n' : (rt_model_l X nx).Domain := ⟨n, source.transitive ω source.omega_mem n hn⟩
  let a' : (rt_model_l X nx).Domain := ⟨a, au.1⟩
  let k' : (rt_model_l X nx).Domain := ⟨κ, source.cardinal_mem⟩
  have read := (ex_principal_sat_l (rt_model_ext_l hZF.1 source.transitive nx) _ _ _ _).mp principal n' a' ⟨U, au.2⟩ hn
    ((rt_fn_l source.transitive nx hZF.1 n' k' a').mpr ha)
    ((rt_entry_l source.transitive nx hZF.1 ..).mpr haU) ⟨B, hB⟩
  exact read.trans (and_congr
    ⟨fun h s hs => (rt_fn_l source.transitive nx hZF.1 ..).mp (h ⟨s, source.transitive B hB s hs⟩ hs),
      fun h s hs => (rt_fn_l source.transitive nx hZF.1 ..).mpr (h s.val hs)⟩ Iff.rfl)

theorem It_ultra_d.critical_l {ω κ K L X R F c d Y S j κ' K₀ Z T : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (owner : Ep_source_d hZF ω κ K₀ Z T) (agree : Ea_agree_d ω κ X Z)
    (loc : It_local_d ω Z κ L F) (hκL : M.mem κ L)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (ultra : It_ultra_d hZF ω κ L F c d j)
    (hκj : Rd_entry_d κ κ' j) : Wd_crit_d I X j κ κ' := by
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive
  have below : M.MemberSubset ω L := fun i hi => ord.2.transitive κ hκL i (source.below i hi)
  have reverse : Ea_agree_d ω κ Z X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF)).transfer_l hZF reverse
  have atoms := loc.atoms_l hZF (owner.read_source_l hZF)
  have normal := (loc.normal_l hZF (owner.read_source_l hZF)).transfer_l hZF owner source agree.subset_l
  have bound := ultra.support_l hZF source family coherent atoms normal ord.1 ord.2 below hm hn hκj
  have hj := ultra.elementary_l hZF hm.1 hn.1
  have hY := ultra.transitive_l hZF hn.1
  refine ⟨ord.1, source.cardinal_mem, hj.ordinal_l hZF source.omega source.transitive hY hm hn hκj ord.1,
    hκj, fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) κ (eq.symm ▸ bound κ hκL), ?_⟩
  obtain ⟨X₀, R₀, Y₀, S₀, J, O, Z, A, p, T, V, q, b, C, W, i, e,
    mx, my, system, limit, _, collapse, bij, _, _, constants, _, comp⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨ey, es⟩ := smdl_unique_l I my.1 hn.1
  subst X₀ R₀ Y₀ S₀
  have seed := (ep_seed_collapse_l hZF source ord.1.transitive ord.2.transitive below family coherent atoms normal
    system limit collapse (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  intro α hα
  have hαX := source.transitive κ source.cardinal_mem α hα
  obtain ⟨α', _, image⟩ := hj.1.1.2.2 α hαX
  obtain ⟨n, ⟨o, ho, succ⟩, hnω⟩ := source.omega.exists_ordinalOne_mem
  obtain ⟨a, fn, graph⟩ := ZF.exists_constantFunction hZF I (source := n) hα
  have small := fn0_of_function_l (ZF.modelsKP hZF) fn
  have ha := small.mono_target_l (ord.2.transitive κ hκL)
  have single x (hx : M.mem x n) : x = o := ((succ x).mp hx).elim (fun h => (ho x h).elim) (hZF.1.eq_of_same_members x o)
  have haJ := (system.indices a).mpr ⟨n, hnω, ha, fun x y z hx hy =>
    (single x (fn.input_mem_of_pairMember hx)).trans (single y (fn.input_mem_of_pairMember hy)).symm⟩
  obtain ⟨D, _, space⟩ := source.space_l hZF hnω
  obtain ⟨f, hfX, coord⟩ := source.coordinate_l hZF hnω space succ.predecessor_mem
  obtain ⟨E, _, value⟩ := ep_repr_exists_l hZF family system limit haJ ha space hfX
    (coord.1.mono_target_l (source.transitive κ source.cardinal_mem))
  obtain ⟨g, _, _, constant, H, rep, hH⟩ := ep_value_constant_l hZF source family system limit constants comp hnω haJ ha space hαX image
  obtain ⟨U, haU⟩ := family.total n a hnω ha
  have haX := sc_finite_function_l hZF source.omega source.transitive source.theory.algebra.pair source.theory.algebra.union source.omega_mem
    (source.transitive κ source.cardinal_mem) hnω small
  obtain ⟨B, hBX, pair⟩ := source.theory.algebra.pair a a haX haX
  have read x : M.mem x B ↔ x = a := (pair x).trans ⟨fun h => h.elim id id, Or.inl⟩
  have hBZ := (agree n D B hnω space (fun s hs => (space s).mpr ((read s).mp hs ▸ small))).mp hBX
  have hBU := (loc.principal_l hZF owner hnω small haU hBZ).mpr
    ⟨fun s hs => (read s).mp hs ▸ small, (read a).mpr rfl⟩
  have oa := (graph o α).mpr ⟨succ.predecessor_mem, rfl⟩
  have eq := (ep_repr_atoms_l hZF family system limit haU value rep).1.mpr
    ⟨B, hBU, fun s hs => by
      have eq := (read s).mp hs
      subst s
      exact ⟨α, hαX, (coord.2 a α).mpr ⟨(space a).mpr small, oa⟩, constant a ((space a).mpr small)⟩⟩
  have hE := seed α E ⟨n, a, o, D, f, ha, oa, space, coord, value⟩
  have same := bij.1.1.1.2 E α α' hE (eq.symm ▸ hH)
  exact same.symm ▸ image

end YesMetaZFC.SetTheory.LargeCardinal
