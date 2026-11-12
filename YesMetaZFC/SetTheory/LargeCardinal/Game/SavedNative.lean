import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeRecord
import YesMetaZFC.SetTheory.LargeCardinal.Game.ImageAbsolute

/-! # 完整原回答使用自身支撑保存同一份存档

回答中的实际扩展器给出 L 及 V_L。原生秩比较把常量域放入 V_L，完整规则
(7) 把回答类型放入同一查询域；存档与后继证书因此共享这个确定的支撑。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.save_round_native_l {w N R η C : M.Domain}
    (context : Tg_context_d I w N R η C) (nx : ∃ x, M.mem x N)
    (ground : (smdl_structure_l I (R := R) nx).Models ZFC)
    (omega : (smdl_structure_l I (R := R) nx).IsOmega ⟨w, context.omega_mem⟩)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x ⟨C, context.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) nx) ⟨C, context.member⟩ nc) 54)
    (valid : Formula.satisfies ρ tg_round0_m) (hw : (ρ.bound 16).val.val = w) :
    ∃ L W : (smdl_structure_l I (R := R) nx).Domain, ∃ r,
      Tg_saved_d I w N R η C L.val W.val r ∧
      Tg_saved_code_d N R w W.val r (fun i => (ρ.bound i).val.val) ∧
      (smdl_structure_l I (R := R) nx).mem (ρ.bound 39).val L ∧
    ∃ X K R₀ F c d Y S j κ' U' D' u' : (smdl_structure_l I (R := R) nx).Domain,
      Tg_image_at_d (ZF.modelsKP (ZFC.models_zf_l ground)) ⟨w, context.omega_mem⟩
        (ρ.bound 21).val (ρ.bound 18).val (ρ.bound 23).val (ρ.bound 24).val
        (ρ.bound 31).val (ρ.bound 32).val (ρ.bound 34).val (ρ.bound 15).val
        (ρ.bound 12).val (ρ.bound 11).val (ρ.bound 36).val
        (fun i => (ρ.bound ([47,48,49,50,51,52,53].get i)).val) (ρ.bound 38).val
        ⟨(ρ.bound 2).val, (ρ.bound 1).val, (ρ.bound 0).val⟩ L W X K R₀ F c d Y S j κ' U' D' u' := by
  let N₀ := smdl_structure_l I (R := R) nx
  have native := ZFC.models_zf_l ground
  have hK := ZF.modelsKP native
  let J := kp_pair_l hK
  let w₀ : N₀.Domain := ⟨w, context.omega_mem⟩
  let C₀ : N₀.Domain := ⟨C, context.member⟩
  let η₀ : N₀.Domain := ⟨η, context.height⟩
  have fs := context.finite_l nx native.1
  have rankC := (rr_rank_native_l I nx hK η₀ C₀).mp ((rr_rank_truth_l I).mpr context.rank)
  have limitC : N₀.IsLimitOrdinal η₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I nx (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => η₀)).mp context.limit)
  have regular := (tg_round_control_l hK rankC limitC fs nc ρ valid).2
  have data := ((Formula.satisfies_conj_iff ..).mp valid).2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at data
  obtain ⟨above, _, _, _, _, _, language, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, image⟩ := data
  let s : Fin 7 → Term 54 := Fin.cases (.bound 47) (Fin.cases (.bound 48) (Fin.cases (.bound 49)
    (Fin.cases (.bound 50) (Fin.cases (.bound 51) (Fin.cases (.bound 52) (fun _ => .bound 53))))))
  obtain ⟨L, W, _, hWC, X, K, R₀, F, c, d, Y, S, j, κ', U', D', u', image⟩ := tg_image_absolute_l ground omega rankC fs nc ρ
    (.bound 16) (.bound 21) (.bound 18) (.bound 23) (.bound 24) (.bound 31) (.bound 32) (.bound 34)
    (.bound 15) (.bound 12) (.bound 11) (.bound 36) (.bound 38) (.bound 2) (.bound 1) (.bound 0)
    s (Subtype.ext hw) regular image
  have full := image
  obtain ⟨rankX, source, hLδ, hκL, hτL,
    rankW, hQW, loc, card, strong, mx, my, ultra, crit, bound, limit, iU, iD, iu, pool, reply⟩ := full
  have limitL := card.limit_l hK source.transitive (source.algebra_l hK).pair
  have high : N₀.mem (ρ.bound 39).val L :=
    limitL.1.transitive (ρ.bound 15).val hτL (ρ.bound 39).val ((Formula.satisfies_mem_iff ..).mp above)
  -- 原语言的 Vτ 与原模型的实际 Vτ 相同，故其常量域属于 V_L。
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_m, Formula.satisfies_conj_iff] at language
  obtain ⟨_, _, base, constants, _⟩ := language
  have relative := (vr_sat_l hK fs.transitive nc ρ (.bound 15) (.bound 14)).mp base
  have oτ := limitL.1.mem hτL
  obtain ⟨B, rB⟩ := ZF.v_exists_l J native oτ
  have hBC := ZF.v_mem_l J native rB rankC (ZF.v_ordinal_height_l native rankC oτ (ρ.bound 15).property)
  have eq := vr_agree_l native fs.transitive (ρ.bound 14).property rB (fs.transitive B hBC) relative
  have rτ : V_d J (ρ.bound 15).val (ρ.bound 14).val := by rw [eq]; exact rB
  have constants : Formula.satisfies ρ (tt_constants0_m (.bound 15) (.bound 14) (.bound 13)) :=
    (tt_constants0_sat_l (rt_model_ext_l native.1 fs.transitive nc) ..).mpr
      ((tt_constants0_sat_l (rt_model_ext_l native.1 fs.transitive nc) ..).mp constants)
  have cons := (rt_model_delta_l fs.transitive nc
    (tt_constants0_delta_l (.bound 15) (.bound 14) (.bound 13)) ρ).mp constants
  have cons := (tt_constants0_sat_l native.1 ..).mp cons
  have hU := tt_constants_rank_l native rankW limitL hτL rτ cons
  have hτW := ZF.v_ordinal_mem_l J native rankW hτL
  have hanswer := v_subset_mem_l J rankW hQW reply.1
  -- 同一 L、W 进入完整五十六项记录，随后返回原扩展器证书供后继构造继续使用。
  have ext : Rf_ext_d I N R := fun x hx y hy same =>
    congrArg Subtype.val (native.1.eq_of_same_members (⟨x, hx⟩ : N₀.Domain) ⟨y, hy⟩
      (fun z => same z.val z.property))
  have rank := (rr_rank_truth_l I).mp ((rr_rank_native_l I nx hK L W).mpr rankW)
  have limit : Rr_truth_d I N R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => L.val) :=
    (rr_truth_native_l I nx (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => L)).mpr ((Formula.satisfies_isLimitOrdinal_iff ..).mpr limitL)
  obtain ⟨r, saved, code⟩ := context.save_l I hZF.1 ext limit rank hWC nc ρ valid hw ⟨hτW, hU, hQW, hanswer⟩
  have slots : (fun i => ((s i).eval ρ).val) = (fun i => (ρ.bound ([47,48,49,50,51,52,53].get i)).val) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) i
  exact ⟨L, W, r, saved, code, high, X, K, R₀, F, c, d, Y, S, j, κ', U', D', u', slots ▸ image⟩

end YesMetaZFC.SetTheory.LargeCardinal
