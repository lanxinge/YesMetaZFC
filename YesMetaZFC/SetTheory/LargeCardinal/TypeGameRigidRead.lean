import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCandidate
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameQueryBase

/-! # 从当前继续输入读取唯一高度

旧回答基底已沿实际根图搬运。这里只识别同一候选的常量域，并把原
超过关系与 dcp 定义域送入高度刚性句子，得到字面的最大序数查询成员。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X C η : M.Domain} (nc : Nonempty {x // M.mem x C})
  (ρ : Env (rt_model_l C nc) 28) (χ ψ : Env (rt_model_l C nc) 12) (ε : Env (rt_model_l C nc) 7)
local notation "N" => rt_model_l C nc
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))

theorem Tg_context_d.rigid_l {κ K R γ Z : M.Domain}
    (context : Tg_context_d ω X η C) (source : Ep_source_d hZF ω κ K X R)
    (hZ : M.mem Z X) (rankZ : Vr_d X γ Z) (lower : M.MemberSubset γ (p 1))
    (low : M.mem (ψ.bound 4).val Z ∧ M.mem (ψ.bound 5).val Z ∧ M.mem (ψ.bound 6).val Z)
    (hw : p 0 = ω) (ωχ : (χ.bound 2).val = ω) (τχ : (χ.bound 3).val = p 8)
    (uχ : (χ.bound 0).val = p 13) (mχ : (χ.bound 1).val = p 9)
    (ωψ : (ψ.bound 0).val = ω) (lψ : (ψ.bound 2).val = (χ.bound 4).val)
    (nψ : (ψ.bound 3).val = p 9) (eψ : (ψ.bound 1).val = (ε.bound 1).val)
    (ωε : (ε.bound 0).val = ω) (nε : (ε.bound 3).val = p 3)
    (hi : M.mem (ε.bound 2).val (p 3)) (hh : M.mem (ε.bound 6).val (p 7))
    (seed : Formula.satisfies ρ tc_seed0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (queries : Formula.satisfies ψ tg_query_row0_m) (reply : Formula.satisfies ε tg_reply_base0_m) :
    (χ.bound 6).val = p 11 ∧
      (M.mem (ψ.bound 4).val (χ.bound 6).val ∧ M.mem (ψ.bound 5).val (χ.bound 6).val ∧
        M.mem (ψ.bound 6).val (χ.bound 6).val) ∧ M.mem (ψ.bound 8).val (p 13) := by
  have fs := (context.read_l hZF source).1
  have data := seed
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at data
  obtain ⟨omega, _, oldLanguage, _, _, oldRank, oldConstants, _, exceeds⟩ := data
  simp only [ee_language_m, Formula.satisfies_bind, ee_language0_m, ee_domain_pack_m, ee_domain_pack0_m, Formula.satisfies_conj_iff] at oldLanguage
  have oldPool := oldLanguage.1.2.1
  have hwU : M.mem (p 0) (p 5) := oldLanguage.1.1
  obtain ⟨language, elastic⟩ := (Formula.satisfies_conj_iff ..).mp candidate
  simp only [Formula.satisfies_rename, ee_language0_m, Formula.satisfies_conj_iff] at language
  obtain ⟨domain, limit, newRank, constants, _⟩ := language
  have rank₀ := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ (.bound 8) (.bound 10)).mp oldRank
  have rank₁ := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc χ (.bound 3) (.bound 5)).mp newRank
  have eqB := rank₀.unique_l hZF fs.transitive (ρ.bound 10).property (χ.bound 5).property
    (Eq.mp (congrArg (fun a => Vr_d C a (χ.bound 5).val) τχ) rank₁)
  have cons₀ := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) ρ).mp oldConstants
  have cons₁ := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 1) (.bound 3) (.bound 4))
    (χ.reindex (fun i : Fin 10 => i.succ.succ))).mp constants
  simp only [tt_constants0_sat_l hZF.1, @eval_image_env_l N M Subtype.val] at cons₀ cons₁
  have eqV : (χ.bound 6).val = p 11 := hZF.1.eq_of_same_members _ _ (fun a =>
    (cons₁ a).trans ((or_congr (Iff.of_eq (congrArg (fun B => M.mem a B) eqB.symm))
      (Iff.of_eq (congrArg (fun τ => a = τ) τχ))).trans (cons₀ a).symm))
  have hτ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) _).mp ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit)
  have rankX := context.rank.of_rank_l hZF source.transitive context.member (χ.bound 5).property rank₁
  have hBX := source.transitive C context.member (χ.bound 5).val (χ.bound 5).property
  have hκτ : M.mem (p 1) (χ.bound 3).val := τχ.symm ▸ ((Formula.satisfies_conj_iff ..).mp exceeds).1
  have sub := (rankX.compare_l hZF source.transitive hBX hZ rankZ
    (fun a ha => hτ.1.transitive (p 1) hκτ a (lower a ha))).1
  have member a (ha : M.mem a Z) := (cons₁ a).mpr (Or.inl (sub a ha))
  have scope : M.mem (ψ.bound 4).val (χ.bound 6).val ∧ M.mem (ψ.bound 5).val (χ.bound 6).val ∧
      M.mem (ψ.bound 6).val (χ.bound 6).val := ⟨member _ low.1, member _ low.2.1, member _ low.2.2⟩
  have result := context.continue_l hZF source nc ρ seed
  have fullPool := ((Formula.satisfies_conj_iff ..).mp result).2.2
  let ξ : Env N 29 := ⟨fun i => [ε.bound 0, ε.bound 1, ε.bound 2, ε.bound 3, ε.bound 4, ε.bound 5, ε.bound 6,
    ρ.bound 1, ρ.bound 2, ρ.bound 5, ρ.bound 6, ρ.bound 7, χ.bound 3, χ.bound 4, χ.bound 1, χ.bound 6,
    χ.bound 7, ρ.bound 12, χ.bound 8, χ.bound 9, χ.bound 0, ψ.bound 4, ψ.bound 5, ψ.bound 6,
    ψ.bound 7, ψ.bound 8, ψ.bound 9, ψ.bound 10, ψ.bound 11].get i, fun _ => ⟨ω, context.omega⟩⟩
  have sameω : ε.bound 0 = ρ.bound 0 := Subtype.ext (ωε.trans hw.symm)
  have sameχ : ε.bound 0 = χ.bound 2 := Subtype.ext (ωε.trans ωχ.symm)
  have sameψ : ε.bound 0 = ψ.bound 0 := Subtype.ext (ωε.trans ωψ.symm)
  have sameN : ε.bound 3 = ρ.bound 3 := Subtype.ext nε
  have raw : Formula.satisfies ξ tc_rigid_seed0_m := by
    simp only [tc_rigid_seed0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, hh, ?_, ?_, ?_, ?_, scope.1, scope.2.1, scope.2.2, ?_⟩
    · exact (Formula.satisfies_isOmega_iff ..).mpr (rt_omega_l fs.transitive nc hZF.1 _ (ωε.symm ▸ source.omega))
    · exact Eq.mpr (congrArg (fun a => M.mem (ε.bound 2).val a) nε) hi
    · exact Eq.mpr (congrArg (fun a => M.mem a (p 5)) ωε) (hw ▸ hwU)
    · obtain ⟨A, E, hA, hE, names, seq, product⟩ := (fs.pool_sat_l (ZF.modelsKP hZF) nc ρ
        (.bound 0) (.bound 3) (.bound 5) (.bound 6) hw).mp oldPool
      exact (fs.pool_sat_l (ZF.modelsKP hZF) nc ξ (.bound 0) (.bound 3) (.bound 9) (.bound 10) ωε).mpr
        ⟨A, E, hA, hE, nε.symm ▸ names, seq, product⟩
    · apply (Formula.satisfies_bind ξ (fun i => [.bound 0, .bound 1, .bound 2, .bound 3, .bound 4, .bound 5, .bound 6].get i)
        tg_reply_base0_m).mpr
      exact (Formula.closed_env_l tg_reply_base0_m tg_reply_base0_closed_l (by
        funext i
        exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i)).mp reply
    · let φ := ee_domain_pack0_m
      let f : Fin 7 → Term 10 := fun i => [.bound 0, .bound 1, .bound 2, .bound 4, .bound 5, .bound 6, .bound 7].get i
      let g : Fin 7 → Term 29 := fun i => [.bound 0, .bound 12, .bound 13, .bound 15, .bound 16, .bound 18, .bound 19].get i
      change Formula.satisfies (χ.reindex (fun i : Fin 10 => i.succ.succ)) (φ.bind f) at domain
      change Formula.satisfies ξ (φ.bind g)
      apply (Formula.satisfies_bind ξ g φ).mpr
      exact (Formula.closed_env_l φ ee_domain_pack0_closed_l (by
        funext i
        exact Fin.cases sameχ.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i)).mp
            ((Formula.satisfies_bind (χ.reindex (fun i : Fin 10 => i.succ.succ)) f φ).mp domain)
    · simp only [tg_elastic_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, ee_elastic_m,
        Formula.satisfies_mem_iff] at elastic
      obtain ⟨v, drop, ⟨hg, hd⟩, _⟩ := elastic
      simp only [Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff]
      refine ⟨v, ?_, hg, hd⟩
      have drop := (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair
        (χ.push v) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mp drop
      exact (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair
        (ξ.push v) (.bound 14) (.bound 15) (.bound 17) (.bound 21) (.bound 0)).mpr drop
    · let f : Fin 12 → Term 29 := fun i => [.bound 0, .bound 1, .bound 13, .bound 14, .bound 21, .bound 22,
        .bound 23, .bound 24, .bound 25, .bound 26, .bound 27, .bound 28].get i
      change Formula.satisfies ξ (tg_query_base0_m.bind f)
      apply (Formula.satisfies_bind ξ f tg_query_base0_m).mpr
      apply (Formula.closed_env_l tg_query_base0_m tg_query_base0_closed_l ?_).mp ((Formula.satisfies_conj_iff ..).mp queries).1
      funext i
      exact Fin.cases sameψ.symm (Fin.cases (Subtype.ext eψ) (Fin.cases (Subtype.ext lψ)
        (Fin.cases (Subtype.ext (nψ.trans mχ.symm)) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))))))))) i
    · obtain ⟨A, E, hA, hE, names, seq, product⟩ := (fs.pool_sat_l (ZF.modelsKP hZF) nc ρ
        (.bound 0) (.bound 9) (.bound 11) (.bound 12) hw).mp fullPool
      exact (fs.pool_sat_l (ZF.modelsKP hZF) nc ξ (.bound 0) (.bound 14) (.bound 15) (.bound 17) ωε).mpr
        ⟨A, E, hA, hE, eqV.symm ▸ (mχ.symm ▸ names), seq, product⟩
    · let φ := tx_exceeds0_m
      let f : Fin 12 → Term 28 := fun i => [.bound 0, .bound 2, .bound 1, .bound 3, .bound 5, .bound 6,
        .bound 7, .bound 8, .bound 9, .bound 11, .bound 12, .bound 13].get i
      let g : Fin 12 → Term 29 := fun i => [.bound 0, .bound 8, .bound 7, .bound 3, .bound 9, .bound 10,
        .bound 11, .bound 12, .bound 14, .bound 15, .bound 17, .bound 20].get i
      change Formula.satisfies ρ (φ.bind f) at exceeds
      change Formula.satisfies ξ (φ.bind g)
      apply (Formula.satisfies_bind ξ g φ).mpr
      apply (Formula.closed_env_l φ tx_exceeds0_closed_l ?_).mp ((Formula.satisfies_bind ρ f φ).mp exceeds)
      funext i
      exact Fin.cases sameω.symm (Fin.cases rfl (Fin.cases rfl (Fin.cases sameN.symm (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases (Subtype.ext τχ.symm) (Fin.cases (Subtype.ext mχ.symm)
          (Fin.cases (Subtype.ext eqV.symm) (Fin.cases rfl (Fin.cases (Subtype.ext uχ.symm) (fun j => Fin.elim0 j)))))))))))) i
  exact ⟨eqV, scope, uχ ▸ context.rigid_seed_l hZF source nc ξ raw⟩

end YesMetaZFC.SetTheory.LargeCardinal
