import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraSupport
import YesMetaZFC.SetTheory.LargeCardinal.Extender.ValueApply
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalRead

/-! # 原内部短扩展器的实际临界点

κ 以下的单坐标测度由原主测度条款决定。坐标代表与常值代表在该测度下
相等，而实际坍塌把坐标代表送回原序数；故所有 α<κ 被固定，κ 则越过支撑。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 临界点计算只需源内主测度的正向条款。 -/
def Ep_positive_d (ω κ X F : M.Domain) : Prop := ∀ n a U D B,
  M.mem n ω → Fn0_d n κ a → Ep_space_d κ n D → Rd_entry_d a U F →
    M.mem B X → M.MemberSubset B D → M.mem a B → M.mem B U

def ep_positive_m {d} (ω κ X F : Term d) : Formula 1 d := set[d] ⟪
  ∀ n a U D B, n ∈ ⌜ω⌝ₛ → ⌜fn0_m⌝ₚ(n, ⌜κ⌝ₛ, a) → ⌜ep_space_m⌝ₚ(⌜κ⌝ₛ, n, D) →
    ⌜rd_entry0_m⌝ₚ(a, U, ⌜F⌝ₛ) → B ∈ ⌜X⌝ₛ → B ⊆ D → a ∈ B → B ∈ U⟫
derive_free_closed ep_positive_m

theorem ep_positive_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ X F : Term d) :
    Formula.satisfies ρ (ep_positive_m ω κ X F) ↔
      Ep_positive_d (ω.eval ρ) (κ.eval ρ) (X.eval ρ) (F.eval ρ) := by
  simp only [ep_positive_m, Ep_positive_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, ep_space_sat_l hE, rd_entry0_sat_l hE,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]
  rfl

theorem It_local_d.principal_l {ω κ K X R L F n a U B : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (loc : It_local_d I ω X R κ L F)
    (hn : M.mem n ω) (ha : Fn0_d n κ a) (haU : Rd_entry_d a U F) (hB : M.mem B X) :
    M.mem B U ↔ (∀ s, M.mem s B → Fn0_d n κ s) ∧ M.mem a B := by
  obtain ⟨_, _, hL, hF, sat⟩ := (it_local_mem_l I source.code).mp loc
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

/-- 临界点计算只读取原坐标、正规性和有界主测度条款。 -/
theorem It_ultra_d.critical_source_l {ω κ K L X R F c d Y S j κ' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (atoms : Ea_atoms_d ω κ L F)
    (normal : En_source_d ω κ L X F) (hκ : M.IsOrdinal κ) (hL : M.IsOrdinal L)
    (principal : Ep_positive_d ω κ X F)
    (hκL : M.mem κ L) (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j) (hκj : Rd_entry_d κ κ' j) : Wd_crit_d I X j κ κ' := by
  have bound := ultra.support_l hZF source family coherent atoms normal hκ hL hm hn hκj
  have hj := ultra.elementary_l hZF hm.1 hn.1
  have hY := ultra.transitive_l hZF hn.1
  refine ⟨hκ, source.cardinal_mem, hj.ordinal_l hZF source.omega source.transitive hY hm hn hκj hκ,
    hκj, fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) κ (eq.symm ▸ bound κ hκL), ?_⟩
  obtain ⟨X₀, R₀, Y₀, S₀, J, O, Z, A, p, T, V, q, b, C, W, i, e,
    mx, my, system, limit, _, collapse, bij, _, _, constants, _, comp⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨ey, es⟩ := smdl_unique_l I my.1 hn.1
  subst X₀ R₀ Y₀ S₀
  have seed := (ep_seed_collapse_l hZF source hκ.transitive hL.transitive family coherent atoms normal
    system limit collapse (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  intro α hα
  have hαX := source.transitive κ source.cardinal_mem α hα
  obtain ⟨α', _, image⟩ := hj.1.1.2.2 α hαX
  obtain ⟨n, ⟨o, ho, succ⟩, hnω⟩ := source.omega.exists_ordinalOne_mem
  obtain ⟨a, fn, graph⟩ := ZF.exists_constantFunction hZF I (source := n) hα
  have small := fn0_of_function_l (ZF.modelsKP hZF) fn
  have ha := small.mono_target_l (hL.transitive κ hκL)
  have single x (hx : M.mem x n) : x = o := ((succ x).mp hx).elim (fun h => (ho x h).elim) (hZF.1.eq_of_same_members x o)
  have haJ := (system.indices a).mpr ⟨n, hnω, ha, fun x y z hx hy =>
    (single x (fn.input_mem_of_pairMember hx)).trans (single y (fn.input_mem_of_pairMember hy)).symm⟩
  obtain ⟨D, _, space⟩ := source.space_l hZF hnω
  obtain ⟨f, hfX, coord⟩ := source.coordinate_l hZF hnω space succ.predecessor_mem
  obtain ⟨E, _, value⟩ := ep_repr_exists_l hZF family system limit haJ ha space hfX
    (coord.1.mono_target_l (source.transitive κ source.cardinal_mem))
  obtain ⟨g, _, _, constant, H, rep, hH⟩ := ep_value_constant_l hZF source family system limit constants comp hnω haJ ha space hαX image
  obtain ⟨U, haU⟩ := family.total n a hnω ha
  have haX := sc_finite_function_l (ZF.modelsKP hZF) source.omega source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair (source.algebra_l (ZF.modelsKP hZF)).union source.omega_mem
    (source.transitive κ source.cardinal_mem) hnω small
  obtain ⟨B, hBX, pair⟩ := (source.algebra_l (ZF.modelsKP hZF)).pair a a haX haX
  have read x : M.mem x B ↔ x = a := (pair x).trans ⟨fun h => h.elim id id, Or.inl⟩
  have hBU := principal n a U D B hnω small space haU hBX
    (fun s hs => (space s).mpr ((read s).mp hs ▸ small)) ((read a).mpr rfl)
  have oa := (graph o α).mpr ⟨succ.predecessor_mem, rfl⟩
  have eq := (ep_repr_atoms_l hZF family system limit haU value rep).1.mpr
    ⟨B, hBU, fun s hs => by
      have eq := (read s).mp hs
      subst s
      exact ⟨α, hαX, (coord.2 a α).mpr ⟨(space a).mpr small, oa⟩, constant a ((space a).mpr small)⟩⟩
  have hE := seed α E ⟨n, a, o, D, f, ha, oa, space, coord, value⟩
  have same := bij.1.1.1.2 E α α' hE (eq.symm ▸ hH)
  exact same.symm ▸ image

theorem It_ultra_d.critical_l {ω κ K L X R F c d Y S j κ' K₀ Z T : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ Z T) (agree : Ea_agree_d ω κ X Z)
    (loc : It_local_d I ω Z T κ L F) (hκL : M.mem κ L)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j)
    (hκj : Rd_entry_d κ κ' j) : Wd_crit_d I X j κ κ' := by
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code
  have reverse : Ea_agree_d ω κ Z X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF reverse
  have atoms := loc.atoms_l hZF (owner.read_source_l hZF) owner.code
  have normal := (loc.normal_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF owner source agree.subset_l
  apply It_ultra_d.critical_source_l hZF source family coherent atoms normal ord.1 ord.2 ?_ hκL hm hn ultra hκj
  intro n a U D B hn ha ds haU hB sub haB
  have hBZ := (agree n D B hn ds sub).mp hB
  exact (loc.principal_l hZF owner hn ha haU hBZ).mpr ⟨fun s hs => (ds s).mp (sub s hs), haB⟩

/-- 所属模型内部的真实预扩展器直接给出同一内部超幂的临界点。 -/
theorem It_ultra_d.critical_pre_l {ω κ K L X R F c d Y S j κ' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (pre : Ex_pre_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j) (hκj : Rd_entry_d κ κ' j) : Wd_crit_d I X j κ κ' := by
  apply It_ultra_d.critical_source_l hZF source (pre.measures.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) X) (pre.coherent.source_l I X)
    pre.atoms (pre.normal.source_l X) pre.critical.1 pre.length ?_ pre.above hm hn ultra hκj
  intro n a U D B hn ha ds haU _ sub haB
  exact (pre.principal n a U hn ha haU B).mpr ⟨fun s hs => (ds s).mp (sub s hs), haB⟩

end YesMetaZFC.SetTheory.LargeCardinal
