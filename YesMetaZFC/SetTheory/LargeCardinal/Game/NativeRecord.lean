import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueAbsolute

/-! # 两类实际原记录沿原树边保持严格界

施加源的候选来自当前请求或较早轮的完整回答。两类记录分别保留全部
四十六项和五十六项；沿同一原嵌入搬运原记录码，再在目标自己的反射层
解码。候选低于 δ 是记录中的事实，历史界低于 δ 由原生序数比较推出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 两种已实现记录共用的施加源接口，不把候选小于 δ 另作假设。 -/
structure Tg_record_d (I : kpair_convention_l.Interpretation M) (w X R η C κ δ r : M.Domain) : Prop where
  context : Tg_context_d I w X R η C
  data :
    (∃ v : Fin 46 → M.Domain, Rf_record_d I X R tg_issued0_m C r ∧ Rf_tuple_d I X R v r ∧
      v 0 = w ∧ v 24 = κ ∧ v 5 = δ) ∨
    (∃ v : Fin 56 → M.Domain, Rf_record_d I X R tg_saved_record0_m C r ∧ Rf_tuple_d I X R v r ∧
      v 0 = w ∧ v 17 = κ ∧ v 20 = δ)

theorem Tg_record_d.issued_l (I : kpair_convention_l.Interpretation M)
    {X R η C r : M.Domain} {v : Fin 46 → M.Domain}
    (context : Tg_context_d I (v 0) X R η C)
    (record : Rf_record_d I X R tg_issued0_m C r) (tuple : Rf_tuple_d I X R v r) :
    Tg_record_d I (v 0) X R η C (v 24) (v 5) r :=
  ⟨context, Or.inl ⟨v, record, tuple, rfl, rfl, rfl⟩⟩

theorem Tg_saved_d.control_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {w X R η C L V r : M.Domain} {v : Fin 54 → M.Domain}
    (saved : Tg_saved_d I w X R η C L V r) (code : Tg_saved_code_d X R w V r v) :
    Tg_record_d I w X R η C (v 15) (v 18) r :=
  ⟨saved.context, Or.inr ⟨Fin.cases w (Fin.cases V v), saved.record,
    ((tg_saved_code_read_l I hE).mp code).2, rfl, rfl, rfl⟩⟩

/-- 完整原请求给出候选的严格界与控制参数 δ 的原生正则性。 -/
theorem tg_issued_control_l (hKP : M.Models KP) {w η C : M.Domain}
    (rank : V_d (kp_pair_l hKP) η C) (limit : M.IsLimitOrdinal η)
    (fs : Fs_read_d w C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 46) (valid : Formula.satisfies ρ tg_issued0_m) :
    M.mem (ρ.bound 24).val (ρ.bound 5).val ∧ M.IsRegularCardinal (kp_pair_l hKP) (ρ.bound 5).val := by
  let J := rt_pair_l fs.transitive nc hKP.1 fs.pair
  have state := (tg_issued_sat_l J (rt_model_ext_l hKP.1 fs.transitive nc) ρ).mp valid
  let θ : Env (rt_model_l C nc) 19 := ⟨fun i => ρ.bound (i.castAdd 27), fun _ => ρ.bound 0⟩
  have control : Formula.satisfies θ tg_control0_m := state.control
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at control
  have rules := control.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
  exact ⟨state.bound, ti_woodin_regular_l hKP rank limit fs nc θ (.bound 5) rules.2.2.2.2.2.1⟩

/-- 实际完整回答给出新域的严格界与 δ 的原生正则性。 -/
theorem tg_round_control_l (hKP : M.Models KP) {w η C : M.Domain}
    (rank : V_d (kp_pair_l hKP) η C) (limit : M.IsLimitOrdinal η)
    (fs : Fs_read_d w C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 54) (valid : Formula.satisfies ρ tg_round0_m) :
    M.mem (ρ.bound 15).val (ρ.bound 18).val ∧ M.IsRegularCardinal (kp_pair_l hKP) (ρ.bound 18).val := by
  obtain ⟨seed, data⟩ := (Formula.satisfies_conj_iff ..).mp valid
  have seed := (Formula.satisfies_rename ..).mp seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at seed
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at data
  exact ⟨data.2.2.1, ti_woodin_regular_l hKP rank limit fs nc _ (.bound 2) seed.2.2.2.1⟩

private theorem tgr_saved_l (hKP : M.Models KP) {w η C : M.Domain}
    (rank : V_d (kp_pair_l hKP) η C) (limit : M.IsLimitOrdinal η)
    (fs : Fs_read_d w C) (nc : Nonempty {x // M.mem x C})
    (ρ : Env (rt_model_l C nc) 56) (valid : Formula.satisfies ρ tg_saved_record0_m) :
    M.mem (ρ.bound 17).val (ρ.bound 20).val ∧ M.IsRegularCardinal (kp_pair_l hKP) (ρ.bound 20).val :=
  tg_round_control_l hKP rank limit fs nc (ρ.reindex (fun i : Fin 54 => i.succ.succ))
    ((Formula.satisfies_rename ..).mp ((Formula.satisfies_conj_iff ..).mp valid).1)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 完整原记录与候选一起搬运；原生秩层给出 δ 的正则性及历史界的合法参数位置。 -/
theorem Tg_record_d.map_l
    {Ω w X R η C κ δ r c d Y S j κ' χ : M.Domain}
    (h : Tg_record_d I w X R η C κ δ r) (hΩ : M.IsOmega Ω)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (hY : (smdl_structure_l I (R := S) my.2.1).Models KP)
    (map : Smap_d I Ω c d X Y j) (hκ : Rd_entry_d κ κ' j)
    (ord : Rr_truth_d I Y S (KP.ord0_m .newest) (fun _ : Fin 1 => χ))
    (sub : ∀ x, Rd_entry_d x χ S → Rd_entry_d x κ' S) :
    ∃ w' η' C' δ' r', Rd_entry_d w w' j ∧ Rd_entry_d η η' j ∧ Rd_entry_d C C' j ∧
      Rd_entry_d δ δ' j ∧ Rd_entry_d r r' j ∧ Tg_record_d I w' Y S η' C' κ' δ' r' ∧
      Rd_entry_d κ' δ' S ∧ Rd_entry_d χ δ' S ∧ Rd_entry_d χ C' S ∧
      Rr_truth_d I Y S (Formula.isRegularCardinal kpair_convention_l .newest) (fun _ : Fin 1 => δ') := by
  obtain ⟨w', _, hw'⟩ := map.1.1.2.2 w h.context.omega_mem
  obtain ⟨η', C', hη, hC, context⟩ := h.context.map_l hZF hΩ mx my map hw'
  let N := smdl_structure_l I (R := S) my.2.1
  let D : N.Domain := ⟨C', context.member⟩
  let a : N.Domain := ⟨η', context.height⟩
  have fs : Fs_read_d (M := N) ⟨w', context.omega_mem⟩ D := context.finite_l my.2.1 hY.1
  have rank : V_d (kp_pair_l hY) a D := (rr_rank_native_l I my.2.1 hY a D).mp
    ((rr_rank_truth_l I).mpr context.rank)
  have limit : N.IsLimitOrdinal a := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I my.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => a)).mp context.limit)
  let nd : Nonempty {x : N.Domain // N.mem x D} := ⟨⟨⟨w', context.omega_mem⟩, fs.omega_mem⟩⟩
  let b : N.Domain := ⟨χ, ord.1 0⟩
  have ob : N.IsOrdinal b := (KP.ord0_sat_l hY _ .newest).mp
    ((rr_truth_native_l I my.2.1 (KP.ord0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => b)).mp ord)
  have below (a t : N.Domain) (ha : a.val = κ') (lt : N.mem a t) (ot : N.IsOrdinal t) :
      Rd_entry_d χ t.val S :=
    ordinal_down_l hY ob ot (fun x hx => by
      change Rd_entry_d x.val a.val S
      exact ha.symm ▸ sub x.val hx) lt
  have regular (t : N.Domain) (ht : N.IsRegularCardinal (kp_pair_l hY) t) :
      Rr_truth_d I Y S (Formula.isRegularCardinal kpair_convention_l .newest) (fun _ : Fin 1 => t.val) :=
    (rr_truth_native_l I my.2.1 (Formula.isRegularCardinal kpair_convention_l .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => t)).mpr
      ((Formula.satisfies_isRegularCardinal_iff (kp_pair_l hY) hY.1 _ .newest).mpr ht)
  rcases h.data with ⟨v, record, tuple, hw, hk, hd⟩ | ⟨v, record, tuple, hw, hk, hd⟩
  · obtain ⟨s, ρ, hrs, images, saved, values, valid⟩ := map.record_image_l I hZF hΩ mx my hY.1
      D hC fs.transitive nd tg_issued0_m tg_issued0_closed_l record tuple
    have ew := map.1.1.1.2 w (ρ.bound 0).val.val w' (hw ▸ images 0) hw'
    have ek := map.1.1.1.2 κ (ρ.bound 24).val.val κ' (hk ▸ images 24) hκ
    obtain ⟨lt, rt⟩ := tg_issued_control_l hY rank limit fs nd ρ valid
    have low := below (ρ.bound 24).val (ρ.bound 5).val ek lt rt.isCardinal.1
    exact ⟨w', η', C', (ρ.bound 5).val.val, s.val, hw', hη, hC, hd ▸ images 5, hrs,
      ⟨context, Or.inl ⟨_, saved, values, ew, ek, rfl⟩⟩,
      ek ▸ lt, low, fs.transitive (ρ.bound 5).val (ρ.bound 5).property b low,
      regular (ρ.bound 5).val rt⟩
  · obtain ⟨s, ρ, hrs, images, saved, values, valid⟩ := map.record_image_l I hZF hΩ mx my hY.1
      D hC fs.transitive nd tg_saved_record0_m tg_saved_record0_closed_l record tuple
    have ew := map.1.1.1.2 w (ρ.bound 0).val.val w' (hw ▸ images 0) hw'
    have ek := map.1.1.1.2 κ (ρ.bound 17).val.val κ' (hk ▸ images 17) hκ
    obtain ⟨lt, rt⟩ := tgr_saved_l hY rank limit fs nd ρ valid
    have low := below (ρ.bound 17).val (ρ.bound 20).val ek lt rt.isCardinal.1
    exact ⟨w', η', C', (ρ.bound 20).val.val, s.val, hw', hη, hC, hd ▸ images 20, hrs,
      ⟨context, Or.inr ⟨_, saved, values, ew, ek, rfl⟩⟩,
      ek ▸ lt, low, fs.transitive (ρ.bound 20).val (ρ.bound 20).property b low,
      regular (ρ.bound 20).val rt⟩

end YesMetaZFC.SetTheory.LargeCardinal
